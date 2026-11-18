

args <- commandArgs(trailingOnly = TRUE)
DATA <- "C:/Users/pc/OneDrive/Escritorio/análisis estadístico PI/proyecto_integrador"
OUT  <- "C:/Users/pc/OneDrive/Escritorio/análisis estadístico PI/salida_R"
REPS <- 300                                   # repeticiones de la prueba de permutacion
dir.create(file.path(OUT, "figuras"), recursive = TRUE, showWarnings = FALSE)
dir.create(file.path(OUT, "tablas"),  recursive = TRUE, showWarnings = FALSE)
set.seed(2026)
FIN_2025 <- as.Date("2025-12-31")
TIERS <- c("Bronze", "Silver", "Gold", "Platinum")
res_txt <- file.path(OUT, "resultados.txt")
cat("RESULTADOS - Fase 3 Elite Retail\n\n", file = res_txt)
informar <- function(titulo, obj) {
  cat("\n==", titulo, "==\n", file = res_txt, append = TRUE)
  cat(capture.output(print(obj)), sep = "\n", file = res_txt, append = TRUE)
}

# ------------------------------------------------------------- utilidades
sum_by <- function(idx, x, N) {               # suma de x por cliente (idx = posicion del cliente)
  out <- numeric(N); a <- rowsum(x, idx); out[as.integer(rownames(a))] <- a[, 1]; out
}

# MCO con errores robustos: HC3 (corte transversal) o Newey-West (series de tiempo)
ols <- function(y, X, hac = NULL) {
  n <- nrow(X); k <- ncol(X)
  XtXi <- solve(crossprod(X))
  b <- as.numeric(XtXi %*% crossprod(X, y))
  e <- as.numeric(y - X %*% b)
  if (is.null(hac)) {
    h  <- rowSums((X %*% XtXi) * X)
    Xw <- X * (e / (1 - h))
    V  <- XtXi %*% crossprod(Xw) %*% XtXi
  } else {
    Xe <- X * e
    S  <- crossprod(Xe)
    for (l in seq_len(hac)) {
      w <- 1 - l / (hac + 1)
      G <- crossprod(Xe[(l + 1):n, , drop = FALSE], Xe[1:(n - l), , drop = FALSE])
      S <- S + w * (G + t(G))
    }
    V <- XtXi %*% S %*% XtXi
  }
  se <- sqrt(diag(V)); tt <- b / se
  p  <- 2 * pt(-abs(tt), n - k)
  tc <- qt(0.975, n - k)
  sst <- sum((y - mean(y))^2); sse <- sum(e^2); r2 <- 1 - sse / sst
  Fst <- ((sst - sse) / (k - 1)) / (sse / (n - k))
  coef <- data.frame(var = colnames(X), coef = b, ee = se, t = tt, p = p,
                     ic_inf = b - tc * se, ic_sup = b + tc * se, row.names = NULL)
  list(n = n, k = k, r2 = r2, r2_adj = 1 - (1 - r2) * (n - 1) / (n - k), F = Fst,
       F_p = pf(Fst, k - 1, n - k, lower.tail = FALSE), coef = coef,
       resid = e, X = X, V = V, b = b)
}
wald <- function(res, idx) {                  # H0: coeficientes idx = 0 (covarianza robusta)
  b <- res$b[idx]; V <- res$V[idx, idx, drop = FALSE]
  W <- as.numeric(t(b) %*% solve(V, b))
  c(W = W, p = pchisq(W, length(idx), lower.tail = FALSE))
}
durbin_watson <- function(e) sum(diff(e)^2) / sum(e^2)
breusch_pagan <- function(res) {
  aux <- ols(res$resid^2, res$X); lm <- res$n * aux$r2
  c(LM = lm, p = pchisq(lm, res$k - 1, lower.tail = FALSE))
}
gini <- function(x) { x <- sort(x); n <- length(x); sum((2 * seq_len(n) - n - 1) * x) / (n * sum(x)) }
top_share <- function(g, frac = 0.20) {
  k <- floor(length(g) * frac + 1e-9); sum(sort(g, decreasing = TRUE)[seq_len(k)]) / sum(g)
}
fmt <- function(x, d = 2) formatC(x, format = "f", digits = d, big.mark = ",")

# ------------------------------------------------------------- 1. integracion
s    <- read.csv(file.path(DATA, "sales_raw_oltp.csv"),     stringsAsFactors = FALSE)
cli  <- read.csv(file.path(DATA, "customers_master.csv"),   stringsAsFactors = FALSE)
prod <- read.csv(file.path(DATA, "products_catalog.csv"),   stringsAsFactors = FALSE)
tien <- read.csv(file.path(DATA, "store_locations.csv"),    stringsAsFactors = FALSE)
cli$registration_date <- as.Date(cli$registration_date)
cli$date_of_birth     <- as.Date(cli$date_of_birth)

ip <- match(s$product_id, prod$product_id); stopifnot(!anyNA(ip))
it <- match(s$store_id,   tien$store_id);   stopifnot(!anyNA(it))
idx <- match(s$customer_id, cli$customer_id); stopifnot(!anyNA(idx))
N <- nrow(cli)

s$ventas  <- s$quantity * prod$retail_price[ip]
s$costo   <- s$quantity * prod$unit_cost[ip]
s$margen  <- s$ventas - s$costo
s$tienda_tipo <- tien$store_type[it]
fecha <- as.Date(substr(s$event_time, 1, 10))
mes_t <- as.integer(substr(s$event_time, 6, 7))
semestre <- ifelse(mes_t <= 6, 1L, 2L)

reg_t  <- cli$registration_date[idx]
antes  <- fecha < reg_t
calidad <- c(transacciones = nrow(s), clientes = N,
             nulos = sum(is.na(s)), txn_unicas = as.numeric(!anyDuplicated(s$txn_id)),
             compras_antes_registro = sum(antes),
             clientes_compra_antes_registro = length(unique(s$customer_id[antes])),
             ventas_total = sum(s$ventas), margen_total = sum(s$margen),
             margen_pct = sum(s$margen) / sum(s$ventas) * 100)
informar("Calidad de datos", calidad)
cat("Rango de fechas:", format(min(fecha)), "a", format(max(fecha)), "\n", file = res_txt, append = TRUE)

# ------------------------------------------------------------- 2. tabla por cliente
C <- data.frame(customer_id = cli$customer_id, loyalty_tier = factor(cli$loyalty_tier, levels = TIERS),
                gender = cli$gender, stringsAsFactors = FALSE)
C$G   <- sum_by(idx, s$ventas, N)
C$F   <- tabulate(idx, N)
C$M   <- sum_by(idx, s$margen, N)
C$G1  <- sum_by(idx[semestre == 1], s$ventas[semestre == 1], N)
C$G2  <- sum_by(idx[semestre == 2], s$ventas[semestre == 2], N)
C$Mg1 <- sum_by(idx[semestre == 1], s$margen[semestre == 1], N)
C$Mg2 <- C$M - C$Mg1
C$pts    <- ifelse(C$F > 0, tabulate(idx[s$payment_method == "Points"], N) / pmax(C$F, 1), NA)
C$online <- ifelse(C$F > 0, tabulate(idx[s$tienda_tipo == "Online Warehouse"], N) / pmax(C$F, 1), NA)
ult <- rep(NA_real_, N); a <- tapply(as.numeric(fecha), idx, max); ult[as.integer(names(a))] <- a
C$recencia <- as.numeric(FIN_2025) - ult
C$ticket   <- ifelse(C$F > 0, C$G / pmax(C$F, 1), NA)
C$edad     <- as.numeric(FIN_2025 - cli$date_of_birth) / 365.25
C$antig    <- as.numeric(FIN_2025 - cli$registration_date) / 365.25
sin_compras <- sum(C$F == 0)

# ------------------------------------------------------------- 3. modelo de decision A-D
orden <- order(-C$G, C$customer_id)           # empates por customer_id (reproducible)
C$pos <- NA_integer_; C$pos[orden] <- seq_len(N)
cortes <- c(0, round(N * c(0.20, 0.50, 0.80)), N)
C$grupo <- cut(C$pos, breaks = cortes, labels = c("A", "B", "C", "D"))

perfil <- function(col) {
  niv <- levels(col)
  filas <- lapply(niv, function(k) {
    d <- C[col == k, ]
    data.frame(nivel = k, clientes = nrow(d), gasto_min = min(d$G), gasto_max = max(d$G),
               gasto_medio = mean(d$G), compras = mean(d$F), ticket = mean(d$ticket, na.rm = TRUE),
               margen_medio = mean(d$M), ventas = sum(d$G), margen = sum(d$M),
               recencia = mean(d$recencia, na.rm = TRUE))
  })
  p <- do.call(rbind, filas)
  p$pct_clientes <- p$clientes / N * 100
  p$pct_ventas   <- p$ventas / sum(C$G) * 100
  p$pct_margen   <- p$margen / sum(C$M) * 100
  p$margen_pct   <- p$margen / p$ventas * 100
  p
}
perf_g <- perfil(C$grupo); perf_t <- perfil(C$loyalty_tier)
write.csv(perf_g, file.path(OUT, "tablas/perfil_grupos_AD.csv"), row.names = FALSE)
write.csv(perf_t, file.path(OUT, "tablas/perfil_niveles.csv"),   row.names = FALSE)
informar("Perfil de grupos A-D", format(perf_g, digits = 6))
informar("Perfil de niveles actuales", format(perf_t, digits = 6))

ord_m <- order(-C$M, C$customer_id)
top_v <- C$customer_id[orden[seq_len(N / 5)]]; top_m <- C$customer_id[ord_m[seq_len(N / 5)]]
conc <- c(top20_share = top_share(C$G), gini = gini(C$G), sin_compras = sin_compras,
          solape_top20_ventas_margen = length(intersect(top_v, top_m)) / (N / 5) * 100,
          spearman_ventas_margen = cor(C$G, C$M, method = "spearman"),
          corr_G_F = cor(C$G, C$F))
informar("Concentracion", conc)
informar("Participacion del top x% de clientes",
         sapply(c(.10, .20, .25, .30, .40, .50), function(f) top_share(C$G, f)))

# ------------------------------------------------------------- 4. modelos econometricos
# ---- Modelo 2: dicotomicas de lealtad (Bronze = referencia)
X2 <- cbind(Constante = 1, Silver = as.numeric(C$loyalty_tier == "Silver"),
            Gold = as.numeric(C$loyalty_tier == "Gold"),
            Platinum = as.numeric(C$loyalty_tier == "Platinum"))
M2 <- list()
for (nm in c("G", "F", "M")) {
  r <- ols(C[[nm]], X2); w <- wald(r, 2:4)
  M2[[nm]] <- r
  write.csv(r$coef, file.path(OUT, paste0("tablas/M2_", nm, ".csv")), row.names = FALSE)
  informar(paste("Modelo 2 - variable dependiente", nm),
           list(coef = r$coef, R2 = r$r2, Wald_chi2 = w[["W"]], Wald_p = w[["p"]],
                BreuschPagan_p = breusch_pagan(r)[["p"]]))
}
an <- summary(aov(G ~ loyalty_tier, data = C))[[1]]
informar("ANOVA del gasto por nivel",
         c(F = an[["F value"]][1], p = an[["Pr(>F)"]][1], eta2 = an[["Sum Sq"]][1] / sum(an[["Sum Sq"]])))
se_dif <- sqrt(2 * var(C$G) / (N / 4)); mde <- (qnorm(.975) + qnorm(.8)) * se_dif
informar("Diferencia minima detectable (80 % potencia, 5 %)",
         c(ee_dif = se_dif, mde = mde, mde_pct = mde / mean(C$G) * 100))
C$top20 <- as.integer(C$grupo == "A")
ct <- table(C$loyalty_tier, C$top20); ch <- chisq.test(ct)
informar("Nivel vs. pertenencia al top 20 %",
         list(chi2 = ch$statistic, p = ch$p.value, V_Cramer = sqrt(ch$statistic / N),
              pct_top20_por_nivel = ct[, "1"] / rowSums(ct) * 100))

# ---- Modelo 1: regresion multiple del gasto (clientes con compras)
Cm <- C[C$F > 0, ]
X1 <- cbind(Constante = 1, Frecuencia = Cm$F, Edad = Cm$edad, Antiguedad = Cm$antig,
            Mujer = as.numeric(Cm$gender == "Female"), Otro = as.numeric(Cm$gender == "Other"),
            Puntos = Cm$pts, Online = Cm$online)
r1  <- ols(Cm$G, X1)
r1b <- ols(Cm$G, cbind(Constante = 1, Frecuencia = Cm$F))
w1  <- wald(r1, 3:8)
write.csv(r1$coef, file.path(OUT, "tablas/M1_gasto.csv"), row.names = FALSE)
informar("Modelo 1 - regresion multiple del gasto",
         list(n = r1$n, coef = r1$coef, R2 = r1$r2, R2_solo_frecuencia = r1b$r2, F = r1$F,
              BreuschPagan_p = breusch_pagan(r1)[["p"]],
              Wald_controles_chi2 = w1[["W"]], Wald_controles_p = w1[["p"]]))

# ---- Modelo 3: tendencia cuadratica + estacionalidad mensual (serie diaria, millones de GBP)
dd <- tapply(s$ventas, fecha, sum) / 1e6
fechas <- as.Date(names(dd)); d <- as.numeric(dd)
stopifnot(all(diff(fechas) == 1))              # serie sin huecos
nt <- length(d); tt <- seq_len(nt)
mes <- as.integer(format(fechas, "%m")); dow <- as.integer(format(fechas, "%u"))   # lunes = 1
Dm <- sapply(2:12, function(k) as.numeric(mes == k)); colnames(Dm) <- paste0("Mes", 2:12)
Dd <- sapply(2:7,  function(k) as.numeric(dow == k)); colnames(Dd) <- paste0("Dia", 2:7)
L  <- round(4 * (nt / 100)^(2 / 9))
A  <- ols(d, cbind(Constante = 1, t = tt, t2 = tt^2), hac = L)
B  <- ols(d, cbind(Constante = 1, t = tt, t2 = tt^2, Dm), hac = L)
Bd <- ols(d, cbind(Constante = 1, t = tt, t2 = tt^2, Dm, Dd), hac = L)
wm <- wald(B, 4:14); wd <- wald(Bd, 15:20)
informar("Modelo 3 - modelo A (tendencia cuadratica)",
         list(coef = A$coef, R2 = A$r2, DW = durbin_watson(A$resid)))
informar("Modelo 3 - modelo B (tendencia + meses)",
         list(coef = B$coef, R2 = B$r2, R2_aj = B$r2_adj, DW = durbin_watson(B$resid),
              Wald_meses_chi2 = wm[["W"]], Wald_meses_p = wm[["p"]], Wald_diasemana_p = wd[["p"]]))
informar("Modelo 3 - resumen de la serie",
         c(n = nt, rezagos_NW = L, media_diaria = mean(d), sd_diaria = sd(d)))
# base 2026 (sin tendencia ni estacionalidad significativas -> promedio diario)
dias26 <- c(31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31)
tc <- qt(.975, nt - 1)
base26 <- data.frame(mes = 1:12, dias = dias26, ventas = mean(d) * dias26,
                     inf = mean(d) * dias26 - tc * sd(d) * sqrt(dias26 * (1 + dias26 / nt)),
                     sup = mean(d) * dias26 + tc * sd(d) * sqrt(dias26 * (1 + dias26 / nt)))
write.csv(base26, file.path(OUT, "tablas/base_2026.csv"), row.names = FALSE)
informar("Demanda base 2026 (millones de GBP)", base26)
informar("Total base 2026", sum(base26$ventas))

# ------------------------------------------------------------- 5. escenarios
# 5.1 contraste con el azar: se reasignan al azar las transacciones entre clientes
nulo <- replicate(REPS, top_share(sum_by(sample(idx), s$ventas, N)))
obs  <- top_share(C$G)
informar("Permutacion (reparto al azar de las compras)",
         c(media = mean(nulo), sd = sd(nulo), min = min(nulo), max = max(nulo),
           observado = obs, z = (obs - mean(nulo)) / sd(nulo), repeticiones = REPS))

# 5.2 validacion fuera de muestra: clasificar con el pasado y medir el futuro
fuera_muestra <- function(pasado, futuro) {
  top_p <- rep(FALSE, N); top_p[order(-pasado, C$customer_id)[seq_len(N / 5)]] <- TRUE
  top_f <- rep(FALSE, N); top_f[order(-futuro, C$customer_id)[seq_len(N / 5)]] <- TRUE
  tab <- table(factor(top_p, levels = c(FALSE, TRUE)), factor(top_f, levels = c(FALSE, TRUE)))
  ch <- chisq.test(tab)
  list(tabla = tab, repiten = sum(top_p & top_f), pct_repiten = sum(top_p & top_f) / (N / 5) * 100,
       pct_resto = sum(!top_p & top_f) / (N - N / 5) * 100,
       captura = sum(futuro[top_p]) / sum(futuro) * 100,
       chi2 = unname(ch$statistic), p = ch$p.value, rho = cor(pasado, futuro, method = "spearman"))
}
oos <- fuera_muestra(C$G1, C$G2)
cap_nivel <- tapply(C$G2, C$loyalty_tier, sum) / sum(C$G2) * 100
o1 <- order(-C$G1, C$customer_id)
cap_top <- sapply(c(25, 50), function(f) { sel <- rep(FALSE, N); sel[o1[seq_len(N * f / 100)]] <- TRUE
                                           sum(C$G2[sel]) / sum(C$G2) * 100 })
informar("Validacion fuera de muestra: semestre 1 -> semestre 2", oos)
informar("Captura de ventas del semestre 2 por nivel (%)", cap_nivel)
informar("Captura de ventas del semestre 2: top 25 % y top 50 % por gasto del semestre 1", cap_top)
informar("Validacion con margen: semestre 1 -> semestre 2", fuera_muestra(C$Mg1, C$Mg2))

# 5.3 ventanas moviles (escenario de actualizacion periodica)
Gm <- sapply(1:12, function(mo) sum_by(idx[mes_t == mo], s$ventas[mes_t == mo], N))
vent <- do.call(rbind, lapply(list(c(1, 3, 4, 6), c(1, 6, 7, 9), c(1, 9, 10, 12), c(1, 6, 7, 12), c(1, 3, 4, 12)),
  function(v) {
    gp <- rowSums(Gm[, v[1]:v[2], drop = FALSE]); gf <- rowSums(Gm[, v[3]:v[4], drop = FALSE])
    tp <- rep(FALSE, N); tp[order(-gp, C$customer_id)[seq_len(N / 5)]] <- TRUE
    tf <- rep(FALSE, N); tf[order(-gf, C$customer_id)[seq_len(N / 5)]] <- TRUE
    data.frame(clasifica = paste0("meses ", v[1], "-", v[2]), mide = paste0("meses ", v[3], "-", v[4]),
               captura = sum(gf[tp]) / sum(gf) * 100, repiten = sum(tp & tf) / (N / 5) * 100)
  }))
write.csv(vent, file.path(OUT, "tablas/ventanas_moviles.csv"), row.names = FALSE)
informar("Ventanas moviles", vent)

# ------------------------------------------------------------- 6. figuras (escala de grises)
NEGRO <- "#262626"; GRIS_O <- "#6E6E6E"; GRIS <- "#A6A6A6"; GRIS_C <- "#D5D5D5"
png_f <- function(nombre, w = 1300, h = 640) png(file.path(OUT, "figuras", nombre), width = w, height = h, res = 200)

# Fig 1: diferencias frente a Bronze (Modelo 2) con IC 95 %
c2 <- M2$G$coef[2:4, ]

png_f("fig1_M2_dicotomicas.png", h = 520); par(mar = c(4, 6, 1, 1))
plot(c2$coef, 1:3, xlim = c(-1500, 1500), ylim = c(3.5, 0.5), pch = 19, cex = 1.3, col = NEGRO,
     yaxt = "n", ylab = "", xlab = "Diferencia de gasto anual frente a Bronze (GBP), IC 95 %", las = 1)
segments(c2$ic_inf, 1:3, c2$ic_sup, 1:3, lwd = 2, col = NEGRO)
abline(v = 0, col = GRIS); axis(2, at = 1:3, labels = c2$var, las = 1, tick = FALSE)
text(c2$coef, 1:3 - 0.25, paste0("GBP ", round(c2$coef)), cex = 0.8); dev.off()

# Fig 2: serie diaria y ajustes
png_f("fig2_M3_serie.png", h = 600); par(mar = c(3, 4, 1, 1))
plot(fechas, d, type = "l", col = GRIS, ylim = c(22, 26), xlab = "", ylab = "Millones de GBP por dia")
lines(fechas, d - B$resid, col = NEGRO, lwd = 2)
lines(fechas, d - A$resid, col = GRIS_O, lwd = 2, lty = 2)
legend("topright", bty = "n", cex = 0.7, lwd = c(1, 2, 2), lty = c(1, 1, 2), col = c(GRIS, NEGRO, GRIS_O),
       legend = c("Ventas diarias observadas", "Tendencia cuadratica + meses", "Solo tendencia cuadratica")); dev.off()

# Fig 3: clientes vs ventas por grupo
png_f("fig3_grupos.png", h = 600); par(mar = c(3, 4, 1, 1))
bp <- barplot(rbind(perf_g$pct_clientes, perf_g$pct_ventas), beside = TRUE, ylim = c(0, 42), col = c(GRIS, NEGRO),
              names.arg = c("A - Alto valor", "B - Medio-alto", "C - Medio-bajo", "D - Bajo valor"), ylab = "%")
text(bp, rbind(perf_g$pct_clientes, perf_g$pct_ventas) + 1.5,
     paste0(round(rbind(perf_g$pct_clientes, perf_g$pct_ventas), 1), "%"), cex = 0.75)
legend("topright", bty = "n", fill = c(GRIS, NEGRO), legend = c("% de clientes", "% de ventas 2025")); dev.off()

# Fig 4: contraste con el azar
png_f("fig4_azar.png", h = 600); par(mar = c(4, 4, 1, 1))
hist(nulo * 100, breaks = 18, col = GRIS, border = "white", xlim = c(30.90, 31.20), main = "",
     xlab = "% de las ventas del 20 % de clientes con mayor gasto, si las compras se repartieran al azar",
     ylab = paste("Repeticiones (de", REPS, ")"))
abline(v = obs * 100, lwd = 3, col = NEGRO)
text(31.115, par("usr")[4] * 0.55, sprintf("Observado: %.2f %%\n(linea negra)", obs * 100), adj = 0, cex = 0.8); dev.off()

# Fig 5: captura fuera de muestra (misma cantidad de clientes)
png_f("fig5_fuera_muestra.png", h = 600); par(mar = c(4, 4, 1, 1))
cl <- c(perf_t$pct_clientes[4], 25, sum(perf_t$pct_clientes[3:4]), 50)
vs <- c(cap_nivel[["Platinum"]], cap_top[1], cap_nivel[["Gold"]] + cap_nivel[["Platinum"]], cap_top[2])
bp <- barplot(rbind(cl, vs), beside = TRUE, ylim = c(0, 66), col = c(GRIS, NEGRO),
              names.arg = c("Platinum\n(25 % de clientes)", "Top 25 % por\ngasto del sem. 1",
                            "Gold + Platinum\n(50 % de clientes)", "Top 50 % por\ngasto del sem. 1"), cex.names = 0.7)
text(bp, rbind(cl, vs) + 2, paste0(round(rbind(cl, vs), 1), "%"), cex = 0.75)
legend("topleft", bty = "n", fill = c(GRIS, NEGRO),
       legend = c("% de clientes seleccionados", "% de las ventas del semestre 2 que captura")); dev.off()

# ------------------------------------------------------------- 7. salida
write.csv(C[, c("customer_id", "loyalty_tier", "G", "F", "M", "ticket", "recencia", "pos", "grupo")],
          file.path(OUT, "tablas/clientes_con_grupo.csv"), row.names = FALSE)
cat("\nListo. Resultados en", normalizePath(OUT), "\n")
cat(sprintf("Top 20 %% = %.2f %% | Gini = %.3f | azar = %.2f %% +/- %.2f\n",
            obs * 100, gini(C$G), mean(nulo) * 100, sd(nulo) * 100))
cat(sprintf("S1->S2: repiten %.1f %%, p = %.3f; captura S2 = %.1f %%\n", oos$pct_repiten, oos$p, oos$captura))
