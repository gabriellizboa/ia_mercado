"""ROBÔ DE MERCADO 100% NA NUVEM (somente leitura + paper trading simulado).

Roda no GitHub Actions, sem PC e sem MT5. Não tem chave de corretora, não opera
dinheiro real. Tudo que chamamos de "operação" aqui é SIMULAÇÃO em R (unidades de risco).
Não é recomendação de investimento e não há garantia de resultado.

O que faz a cada execução:
 1. Baixa candles (15 min e 1 h) do Yahoo Finance para cada ativo de ATIVOS.
 2. Checa a qualidade dos dados (candles velhos, lacunas, valores incoerentes).
 3. Calcula médias, RSI e ATR (Wilder) e uma leitura descritiva.
 4. Simula operações da estratégia-base (cruzamento de médias + filtro 1 h + filtros de
    risco) e registra tudo em estado/operacoes.csv.
 5. Lê manchetes oficiais (Fed/BCE); manchete de alto impacto pausa novas entradas simuladas.
 6. Manda ao Telegram só o que importa (eventos) + um resumo diário.
"""
import csv
import hashlib
import json
import os
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

import numpy as np
import pandas as pd

# ============================ CONFIGURAÇÃO (edite aqui) ============================
ATIVOS = {  # símbolo no Yahoo : spread ASSUMIDO em pips (estimativa conservadora)
    "EURUSD=X": 1.0,
    "GBPUSD=X": 1.5,
    "USDJPY=X": 1.2,
    "AUDUSD=X": 1.5,
}
INTERVALO, SEG_INTERVALO = "15m", 900
INTERVALO_CONTEXTO = "1h"
MA_RAPIDA, MA_LENTA, RSI_N, ATR_N = 20, 50, 14, 14
STOP_ATR = 1.5                 # distância do stop simulado, em ATR
ALVO_R = 2.0                   # alvo simulado, em múltiplos do risco
MAX_CANDLES_OPERACAO = 96      # fecha a simulação após 96 candles (24 h em 15 min)
LIMITE_PERDA_DIA_R = 2.0       # após -2R no dia (UTC), sem novas entradas simuladas
MAX_SPREAD_SOBRE_ATR = 0.25    # não entra se o spread passar de 25% do ATR
PAUSA_NOTICIA_H = 2            # horas sem entradas após manchete de alto impacto
HORA_RESUMO_UTC = 21           # resumo diário (primeira execução após essa hora UTC)
FALHAS_PARA_ALERTAR = 3        # execuções seguidas com falha antes de avisar
PALAVRAS_ALTO_IMPACTO = [
    "interest rate", "rate decision", "monetary policy", "fomc", "inflation",
    "employment", "payroll", "gdp", "press conference", "emergency",
]
FONTES_NOTICIAS = {
    "Federal Reserve (política monetária)": "https://www.federalreserve.gov/feeds/press_monetary.xml",
    "Federal Reserve (comunicados)": "https://www.federalreserve.gov/feeds/press_all.xml",
    "BCE (comunicados)": "https://www.ecb.europa.eu/rss/press.xml",
}
# ===================================================================================

DIR_ESTADO = Path(os.environ.get("DIR_ESTADO", "estado"))
LIMITE_BYTES = 2_000_000
COLUNAS_OPS = ["simbolo", "lado", "entrada_utc", "saida_utc", "entrada", "saida",
               "stop", "alvo", "motivo", "r_liquido"]


def pip(simbolo):
    return 0.01 if "JPY" in simbolo.upper() else 0.0001


# ------------------------------------------------------------------- dados
def _get(url, timeout=20):
    if not url.lower().startswith("https://"):
        raise ValueError("só https")
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (robo-mercado leitura)"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        dados = r.read(LIMITE_BYTES + 1)
    if len(dados) > LIMITE_BYTES:
        raise ValueError("resposta grande demais")
    return dados


def baixar(simbolo, intervalo, periodo):
    url = ("https://query1.finance.yahoo.com/v8/finance/chart/"
           f"{urllib.parse.quote(simbolo)}?interval={intervalo}&range={periodo}")
    ultimo = None
    for tentativa in range(3):
        try:
            return json.loads(_get(url).decode("utf-8"))
        except Exception as e:  # noqa: BLE001
            ultimo = e
            time.sleep(2 * (tentativa + 1))
    raise RuntimeError(f"Yahoo indisponível ({type(ultimo).__name__})")


def para_df(js):
    res = (js.get("chart") or {}).get("result")
    if not res:
        raise ValueError("Yahoo não devolveu dados")
    res = res[0]
    q = res["indicators"]["quote"][0]
    df = pd.DataFrame({
        "time": pd.to_datetime(res["timestamp"], unit="s", utc=True),
        "open": q["open"], "high": q["high"], "low": q["low"], "close": q["close"],
    }).dropna().reset_index(drop=True)
    if len(df) < 3:
        raise ValueError("candles insuficientes")
    return df.iloc[:-1].reset_index(drop=True)  # descarta o candle ainda em formação


# -------------------------------------------------------------- indicadores
def rsi_wilder(c, n=14):
    d = c.diff()
    g = d.clip(lower=0).ewm(alpha=1 / n, min_periods=n, adjust=False).mean()
    p = (-d.clip(upper=0)).ewm(alpha=1 / n, min_periods=n, adjust=False).mean()
    with np.errstate(divide="ignore", invalid="ignore"):
        r = 100 - 100 / (1 + g / p)
    r = r.where(p != 0, 100.0)
    r = r.where(~((p == 0) & (g == 0)), 50.0)
    return r.where(g.notna() & p.notna())


def atr_wilder(df, n=14):
    pc = df["close"].shift(1)
    tr = pd.concat([df.high - df.low, (df.high - pc).abs(), (df.low - pc).abs()], axis=1).max(axis=1)
    return tr.ewm(alpha=1 / n, min_periods=n, adjust=False).mean()


def preparar(df):
    d = df.copy()
    d["mf"] = d.close.rolling(MA_RAPIDA).mean()
    d["ml"] = d.close.rolling(MA_LENTA).mean()
    d["rsi"] = rsi_wilder(d.close, RSI_N)
    d["atr"] = atr_wilder(d, ATR_N)
    return d


def mercado_aberto(agora):
    d, h = agora.weekday(), agora.hour
    return not (d == 5 or (d == 6 and h < 21) or (d == 4 and h >= 21))


def checar_dados(df, agora, seg, aberto):
    """Levanta ValueError se os dados não são confiáveis. Devolve avisos (lista)."""
    ruim = ((df.high < df[["open", "close"]].max(axis=1)) | (df.low > df[["open", "close"]].min(axis=1))).tail(200)
    if ruim.any():
        raise ValueError("candles com high/low incoerentes")
    if df.time.tail(200).duplicated().any():
        raise ValueError("candles duplicados")
    idade_min = (agora - df.time.iloc[-1]).total_seconds() / 60
    if aberto and idade_min > 6 * seg / 60:
        raise ValueError(f"dados velhos (último candle há {idade_min:.0f} min)")
    d = df.time.tail(100).diff().dt.total_seconds()
    lacunas = int(((d > 2 * seg) & (d < 40 * 3600)).sum())
    return [f"{lacunas} lacuna(s) nos últimos 100 candles"] if lacunas else []


# ---------------------------------------------------------------- leitura
def tendencia(u):
    return "alta" if u.mf > u.ml else "baixa"


def leitura(simbolo, d15, d60):
    u = d15.iloc[-1]
    if u[["mf", "ml", "rsi", "atr"]].isna().any():
        raise ValueError("indicadores insuficientes")
    med = d15.atr.dropna().tail(100).median()
    u60 = d60.iloc[-1]
    t60 = tendencia(u60) if not u60[["mf", "ml"]].isna().any() else None
    return {
        "preco": float(u.close), "tend15": tendencia(u), "tend60": t60,
        "rsi": float(u.rsi), "atr": float(u.atr), "atr_pips": float(u.atr) / pip(simbolo),
        "vol": float(u.atr / med) if med else 1.0, "candle": u.time.isoformat(),
    }


def fmt(simbolo, preco):
    return f"{preco:.3f}" if "JPY" in simbolo.upper() else f"{preco:.5f}"


# ------------------------------------------------------- paper trading (simulado)
def avaliar_aberta(sim, op, d15):
    """Aplica os candles novos à operação simulada. Stop vence se stop e alvo no mesmo candle."""
    ref = pd.Timestamp(op["ultimo_check"])
    spread = ATIVOS[sim] * pip(sim)
    for _, c in d15[d15.time > ref].iterrows():
        op["candles"] += 1
        op["ultimo_check"] = c.time.isoformat()
        compra = op["lado"] == "compra"
        stop_hit = c.low <= op["stop"] if compra else c.high >= op["stop"]
        alvo_hit = c.high >= op["alvo"] if compra else c.low <= op["alvo"]
        motivo = saida = None
        if stop_hit:
            motivo, saida = "stop", op["stop"]
        elif alvo_hit:
            motivo, saida = "alvo", op["alvo"]
        elif op["candles"] >= MAX_CANDLES_OPERACAO:
            motivo, saida = "tempo", float(c.close)
        if motivo:
            mov = (saida - op["entrada"]) if compra else (op["entrada"] - saida)
            r = (mov - spread) / op["risco"]
            return {"simbolo": sim, "lado": op["lado"], "entrada_utc": op["entrada_utc"],
                    "saida_utc": c.time.isoformat(), "entrada": op["entrada"], "saida": saida,
                    "stop": op["stop"], "alvo": op["alvo"], "motivo": motivo, "r_liquido": round(r, 3)}
    return None


def abrir(sim, lado, u):
    risco = STOP_ATR * float(u.atr)
    sinal = 1 if lado == "compra" else -1
    return {"lado": lado, "entrada_utc": u.time.isoformat(), "entrada": float(u.close),
            "stop": float(u.close) - sinal * risco, "alvo": float(u.close) + sinal * ALVO_R * risco,
            "risco": risco, "candles": 0, "ultimo_check": u.time.isoformat()}


def registrar_operacao(fechada):
    DIR_ESTADO.mkdir(parents=True, exist_ok=True)
    arq = DIR_ESTADO / "operacoes.csv"
    novo = not arq.exists()
    with arq.open("a", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLUNAS_OPS)
        if novo:
            w.writeheader()
        w.writerow(fechada)


def ler_operacoes():
    arq = DIR_ESTADO / "operacoes.csv"
    return pd.read_csv(arq) if arq.exists() else pd.DataFrame(columns=COLUNAS_OPS)


def perda_do_dia_r(agora):
    ops = ler_operacoes()
    if ops.empty:
        return 0.0
    dia = pd.to_datetime(ops.saida_utc, utc=True).dt.date == agora.date()
    return float(ops.loc[dia, "r_liquido"].sum())


def estatisticas():
    ops = ler_operacoes()
    n = len(ops)
    if n == 0:
        return {"n": 0}
    r = ops.r_liquido.astype(float)
    cum = pd.concat([pd.Series([0.0]), r.cumsum()], ignore_index=True)
    return {"n": n, "acerto": float((r > 0).mean()), "expectativa": float(r.mean()),
            "total": float(r.sum()), "dd": float((cum.cummax() - cum).max())}


def texto_stats(s):
    if s["n"] == 0:
        return "Simulação: nenhuma operação fechada ainda."
    aviso = " ⚠ amostra pequena (<30): não tire conclusões." if s["n"] < 30 else ""
    return (f"Simulação: {s['n']} op., acerto {s['acerto']:.0%}, expectativa {s['expectativa']:+.2f}R/op., "
            f"total {s['total']:+.1f}R, pior queda {s['dd']:.1f}R.{aviso}")


# ----------------------------------------------------------------- notícias
def _local(t):
    return t.rsplit("}", 1)[-1]


def interpretar_feed(conteudo):
    baixo = conteudo.lower()
    if b"<!doctype" in baixo or b"<!entity" in baixo:
        raise ValueError("feed rejeitado por segurança")
    itens = []
    for no in ET.fromstring(conteudo).iter():
        if _local(no.tag) not in ("item", "entry"):
            continue
        titulo = link = data = ""
        for f in no:
            n = _local(f.tag)
            if n == "title" and f.text:
                titulo = f.text.strip()
            elif n == "link":
                link = (f.text or "").strip() or f.get("href", "")
            elif n in ("pubDate", "published", "updated", "date") and f.text:
                data = data or f.text.strip()
        if titulo:
            itens.append({"titulo": titulo, "link": link, "data": data})
    return itens


def checar_noticias(estado, agora, buscar=_get):
    """Devolve (eventos, avisos). Primeira execução só 'semeia' o que já existe."""
    vistas = set(estado.get("noticias_vistas", []))
    primeira = "noticias_vistas" not in estado
    eventos, avisos = [], []
    for nome, url in FONTES_NOTICIAS.items():
        try:
            itens = interpretar_feed(buscar(url))
        except Exception as e:  # noqa: BLE001
            avisos.append(f"{nome}: {type(e).__name__}")
            continue
        for it in itens:
            ident = hashlib.sha1(f"{nome}|{it['link'] or it['titulo']}".encode()).hexdigest()[:16]
            if ident in vistas:
                continue
            vistas.add(ident)
            if not primeira and any(p in it["titulo"].lower() for p in PALAVRAS_ALTO_IMPACTO):
                eventos.append(f"📰 {nome}: {it['titulo']}")
    estado["noticias_vistas"] = list(vistas)[-400:]
    if eventos:
        estado["pausa_ate"] = (agora + timedelta(hours=PAUSA_NOTICIA_H)).isoformat()
    return eventos, avisos


# --------------------------------------------------------------- por ativo
def processar_ativo(sim, d15, d60, estado, agora, eventos, aberto):
    est = estado["ativos"].setdefault(sim, {})
    leit = leitura(sim, d15, d60)
    u = d15.iloc[-1]
    if est.get("ultimo_candle") == leit["candle"]:
        return leit  # nada novo desde a última execução

    # 1) acompanhar operação simulada aberta
    fechou_agora = False
    if est.get("aberta"):
        fechada = avaliar_aberta(sim, est["aberta"], d15)
        if fechada:
            registrar_operacao(fechada)
            est["aberta"] = None
            fechou_agora = pd.Timestamp(fechada["saida_utc"]) >= u.time
            eventos.append(f"🔒 {sim} simulação encerrada por {fechada['motivo']}: "
                           f"{fechada['lado']} {fmt(sim, fechada['entrada'])} → {fmt(sim, fechada['saida'])} "
                           f"({fechada['r_liquido']:+.2f}R)")

    # 2) alertas de contexto (a 1ª vez só registra o estado, sem avisar)
    if leit["rsi"] >= 70:
        zona = "sobrecompra"
    elif leit["rsi"] <= 30:
        zona = "sobrevenda"
    elif 35 < leit["rsi"] < 65:
        zona = "neutra"  # só "rearma" o alerta ao voltar para a faixa central
    else:
        zona = est.get("rsi_zona", "neutra")
    if "rsi_zona" in est and zona != est["rsi_zona"] and zona != "neutra":
        eventos.append(f"⚡ {sim}: RSI entrou em {zona} ({leit['rsi']:.0f})")
    est["rsi_zona"] = zona
    vol_alta = leit["vol"] >= 1.5 if not est.get("vol_alta") else leit["vol"] >= 1.2
    if "vol_alta" in est and vol_alta and not est["vol_alta"]:
        eventos.append(f"⚡ {sim}: volatilidade subiu ({leit['vol']:.2f}x o habitual)")
    est["vol_alta"] = bool(vol_alta)

    # 3) sinal da estratégia-base (cruzamento das médias) no último candle fechado
    p = d15.iloc[-2]
    lado = None
    if not p[["mf", "ml"]].isna().any():
        if p.mf <= p.ml and u.mf > u.ml and u.rsi < 70:
            lado = "compra"
        elif p.mf >= p.ml and u.mf < u.ml and u.rsi > 30:
            lado = "venda"
    if lado:
        motivo_bloqueio = None
        spread = ATIVOS[sim] * pip(sim)
        pausa = estado.get("pausa_ate")
        if est.get("aberta") or fechou_agora:
            motivo_bloqueio = "já há operação simulada neste ativo"
        elif not aberto:
            motivo_bloqueio = "mercado fechado"
        elif leit["tend60"] is None or (lado == "compra") != (leit["tend60"] == "alta"):
            motivo_bloqueio = f"contra a tendência de 1 h ({leit['tend60']})"
        elif spread / float(u.atr) > MAX_SPREAD_SOBRE_ATR:
            motivo_bloqueio = "spread alto frente ao ATR"
        elif pausa and agora < pd.Timestamp(pausa):
            motivo_bloqueio = "pausa por manchete de alto impacto"
        elif perda_do_dia_r(agora) <= -LIMITE_PERDA_DIA_R:
            motivo_bloqueio = "limite de perda diária simulada atingido"
        if motivo_bloqueio:
            eventos.append(f"➖ {sim}: sinal de {lado} ignorado ({motivo_bloqueio})")
        else:
            est["aberta"] = abrir(sim, lado, u)
            o = est["aberta"]
            eventos.append(f"🧪 {sim} SIMULAÇÃO {lado} a {fmt(sim, o['entrada'])} | stop {fmt(sim, o['stop'])} "
                           f"| alvo {fmt(sim, o['alvo'])} (sem dinheiro real)")
    est["ultimo_candle"] = leit["candle"]
    return leit


# ------------------------------------------------------------------ resumo
def montar_resumo(leituras, falhas, estado, agora):
    linhas = [f"📊 RESUMO {agora:%Y-%m-%d %H:%M} UTC (somente leitura/simulação)"]
    for sim, l in leituras.items():
        aberta = estado["ativos"].get(sim, {}).get("aberta")
        extra = f" | simulação aberta: {aberta['lado']}" if aberta else ""
        linhas.append(f"{sim.replace('=X', '')}: {fmt(sim, l['preco'])} | 15m {l['tend15']}, 1h {l['tend60']} "
                      f"| RSI {l['rsi']:.0f} | ATR {l['atr_pips']:.1f} pips ({l['vol']:.2f}x){extra}")
    for sim, motivo in falhas.items():
        linhas.append(f"{sim.replace('=X', '')}: sem dados ({motivo})")
    linhas += [texto_stats(estatisticas()),
               "Leitura descritiva e simulação educacional. Não é recomendação nem sinal real. "
               "Spreads são assumidos, não reais."]
    return "\n".join(linhas)


# ------------------------------------------------------------------ estado
def carregar_estado():
    arq = DIR_ESTADO / "estado.json"
    if arq.exists():
        try:
            return json.loads(arq.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print("estado.json corrompido; recomeçando o estado.")
    return {"ativos": {}, "falhas": {}}


def salvar_estado(estado):
    DIR_ESTADO.mkdir(parents=True, exist_ok=True)
    (DIR_ESTADO / "estado.json").write_text(json.dumps(estado, ensure_ascii=False, indent=1), encoding="utf-8")


def telegram(texto):
    tok, chat = os.environ.get("TELEGRAM_BOT_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    if not tok or not chat:
        print("(Telegram não configurado; mensagem só no log)")
        return
    for i in range(0, len(texto), 3800):
        dados = urllib.parse.urlencode({"chat_id": chat, "text": texto[i:i + 3800]}).encode()
        urllib.request.urlopen(f"https://api.telegram.org/bot{tok}/sendMessage", dados, timeout=15)


# -------------------------------------------------------------------- main
def executar(agora, forcar_resumo=False, baixar_fn=baixar, enviar_fn=telegram,
             noticias_fn=_get, pausa_entre=1.0):
    DIR_ESTADO.mkdir(parents=True, exist_ok=True)
    estado = carregar_estado()
    estado.setdefault("ativos", {})
    estado.setdefault("falhas", {})
    aberto = mercado_aberto(agora)
    if not aberto and not forcar_resumo:
        print("Mercado fechado; nada a fazer.")
        return 0

    eventos, leituras, falhas_agora = [], {}, {}
    ev_news, av_news = checar_noticias(estado, agora, noticias_fn)
    eventos += ev_news
    if av_news:
        print("Notícias indisponíveis:", "; ".join(av_news))

    for sim in ATIVOS:
        try:
            d15 = preparar(para_df(baixar_fn(sim, INTERVALO, "5d")))
            avisos = checar_dados(d15, agora, SEG_INTERVALO, aberto)
            d60 = preparar(para_df(baixar_fn(sim, INTERVALO_CONTEXTO, "1mo")))
            leituras[sim] = processar_ativo(sim, d15, d60, estado, agora, eventos, aberto)
            for a in avisos:
                print(f"{sim}: aviso — {a}")
            estado["falhas"][sim] = 0
        except Exception as e:  # noqa: BLE001 - um ativo ruim não derruba os outros
            n = estado["falhas"].get(sim, 0) + 1
            estado["falhas"][sim] = n
            falhas_agora[sim] = str(e)[:80]
            print(f"{sim}: FALHOU ({e})")
            if n == FALHAS_PARA_ALERTAR:
                eventos.append(f"⚠️ {sim}: {n} falhas seguidas ({str(e)[:80]})")
        time.sleep(pausa_entre)

    hoje = agora.date().isoformat()
    resumo_devido = (agora.hour >= HORA_RESUMO_UTC and estado.get("ultimo_resumo") != hoje) or forcar_resumo
    partes = ["\n".join(eventos)] if eventos else []
    if resumo_devido:
        partes.append(montar_resumo(leituras, falhas_agora, estado, agora))
        estado["ultimo_resumo"] = hoje
    salvar_estado(estado)

    if partes:
        texto = "\n\n".join(partes)
        print(texto)
        try:
            enviar_fn(texto)
        except Exception as e:  # noqa: BLE001
            print(f"Falha ao enviar ao Telegram: {type(e).__name__}")
    else:
        print("Sem eventos nesta execução.")
    return 1 if len(falhas_agora) == len(ATIVOS) else 0


def main():
    forcar = os.environ.get("FORCAR_RESUMO", "").strip().lower() == "true"
    return executar(datetime.now(timezone.utc), forcar_resumo=forcar)


if __name__ == "__main__":
    sys.exit(main())