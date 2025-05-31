########################
# Simulations
library(VGAM)
library(copula)
library(sn)
library(survival)
library(flux)
library(tdROC)
library(survivalROC)
library(spatstat.geom)
library(risksetROC)


F.M.mix <- function(dat, parametros){
  w <- pnorm(parametros[1])
  xi1 <- parametros[2]
  o1<-exp(parametros[3])
  al1<-parametros[4]
  xi2<-parametros[5]
  o2<-exp(parametros[6])
  al2<-parametros[7]
  w*psn(dat,xi=xi1,omega=o1,alpha=al1)+
    (1-w)*psn(dat,xi=xi2,omega=o2,alpha=al2)
}
Quantile.M.mix <- function(p, parametros, br=c(-1000,1000))
{
  G = function(x) {F.M.mix(x,parametros) - p}
  return( uniroot(G,br)$root ) 
}
f.M.mix <- function(dat, parametros){
  w <- pnorm(parametros[1])
  xi1 <- parametros[2]
  o1<-exp(parametros[3])
  al1<-parametros[4]
  xi2<-parametros[5]
  o2<-exp(parametros[6])
  al2<-parametros[7]
  w*dsn(dat,xi=xi1,omega=o1,alpha=al1)+
    (1-w)*dsn(dat,xi=xi2,omega=o2,alpha=al2)
}

ROC.CD.Joe <- function(parametros, m.M, t.T){
  obs.marker <- m.M
  surv.times <- t.T
  theta <- parametros[1]
  p <- pnorm(parametros[2])
  scale.par <- exp(parametros[3])
  shape.par <- exp(parametros[4])
  w <- 1-pnorm(parametros[2]+ parametros[5])
  # w <- 1-p
  xi.1    <- parametros[6]
  omega.1 <- exp(parametros[7])
  alpha.1 <- parametros[8]
  xi.2    <- parametros[9]
  omega.2 <- parametros[10]
  alpha.2 <- parametros[11]
  f.psi <- function(x, theta){-log(1-(1-x)^theta)}
  psi.inv <- function(x, theta){1 - (1 - exp(-x))^(1/theta)}
  psi.prima <- function(x, theta){-(theta * (1 - x)^(theta - 1)) / 
                                 (1 - (1 - x)^theta)}
  Copula.Joe <- function(u, v, theta){psi.inv(f.psi(u, theta)+
                                                  f.psi(v, theta), theta)}
  C.prima <- function(u,v, theta){
  C.uv <- function(u,v, theta){psi.inv(psi(u, theta)+
                               psi(v, theta),theta)}
          psi.prima(u, theta)/psi.prima(C.uv(u,v, theta), theta)}
#
  f.M <- w*dsn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*dsn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  F.M <- w*psn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*psn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  f.T <- dweibull(surv.times, shape = shape.par, scale = scale.par)
  F.T <- pweibull(surv.times, shape = shape.par, scale = scale.par)
  ######
  H.MT.susceptible <- Copula.Joe(F.M, 1-F.T, theta)
    TP.C <- (H.MT.susceptible-F.M-(1-F.T)+1)/F.T
    G.m.t <- (1-p)*F.M + p*Copula.Joe(F.M, 1-F.T, theta)
      FP.D <-  1-(G.m.t/((1-p)+p*(1-F.T)))
  plot(c(1,FP.D,0), c(1,TP.C,0), type="l", ylim=c(0,1), xlim=c(0,1))
  #
  distances.from.0.1 <- sqrt((FP.D)^2+(1-TP.C)^2)
  which.minimum <- (1:length(distances.from.0.1))[distances.from.0.1== min(distances.from.0.1)]
  cat("auc:", auc(c(1,FP.D,0), c(1,TP.C,0)), "\n")
  cat("min:", min(distances.from.0.1), "\n")
  cat(c(FP.D[which.minimum], TP.C[which.minimum]), "\n")
  cat("cutoff:", m.M[which.minimum], "\n")
  cat("---------------------------\n")
  list(AUC.CD=auc(c(1,FP.D,0), c(1,TP.C,0)), 
       pauc.C = integrate(approxfun(c(1,FP.D,0), c(1,TP.C,0)), 
             0.2, 0.4)$value, 
       FP.D.at.cutoff=FP.D[which.minimum], 
       TP.C.at.cutoff=TP.C[which.minimum], 
       CUTOFF.CD=m.M[which.minimum],
       FP.D.CD=c(1,FP.D,0), TP.C.CD=c(1,TP.C,0))
}


ROC.CD.two.par <- function(parametros, m.M, t.T){
  obs.marker <- m.M
  surv.times <- t.T
  a.par <- exp(parametros[1])
  b.par <- exp(parametros[2])+1
  p <- pnorm(parametros[3])
  scale.par <- exp(parametros[4])
  shape.par <- exp(parametros[5])
  w <- 1-pnorm(parametros[3]+ parametros[6])
  # w <- 1-p
  xi.1    <- parametros[7]
  omega.1 <- exp(parametros[8])
  alpha.1 <- parametros[9]
  xi.2    <- parametros[10]
  omega.2 <- parametros[11]
  alpha.2 <- parametros[12]
  Copula.two.par <- function(u, v, a, b){(((u^(-a) -1)^b + (v^(-a) -1)^b)^(1/b)+1)^(-1/a)} 
  d.psi.two.par <- function(x, a, b){-a * b * x^(-a - 1) * (1 / x^a - 1)^(b - 1)}
  d.2.psi.two.par <- function(x, a, b){-(a * b * (1 / x^a - 1)^b * ((a + 1) * x^a - a * b - 1)) / (x^2 * (x^a - 1)^2)}
  C.prime.1 <- function(u, v, a, b){
    d.psi.two.par(u, a , b)/d.psi.two.par(Copula.two.par(u, v, a, b), a, b)
  }
  c.two.par <- function(u, v, a, b){-1*(d.psi.two.par(u, a , b)*d.psi.two.par(v, a , b)*
                                          d.2.psi.two.par(Copula.two.par(u, v, a, b), a, b))/
      (d.psi.two.par(Copula.two.par(u, v, a, b), a , b)^3)}
  f.M <- w*dsn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*dsn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  F.M <- w*psn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*psn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  f.T <- dweibull(surv.times, shape = shape.par, scale = scale.par)
  F.T <- pweibull(surv.times, shape = shape.par, scale = scale.par)
  f.joint.MT <- f.M*f.T*c.two.par(F.M, 1-F.T, a.par, b.par)
  diff.G.MT <- f.M*C.prime.1(F.M, 1-F.T,a.par, b.par)
  ######
#  H.MT.susceptible <- pCopula(cbind(F.M.sn, 1-F.T.wei), gumbel.cop)
  H.MT.susceptible <- Copula.two.par(F.M, 1-F.T, a.par, b.par)
    TP.C <- (H.MT.susceptible-F.M-(1-F.T)+1)/F.T
#  G.m.t <- (1-p)*F.M + 
#    p*pCopula(cbind(F.M.sn, 1-F.T.wei), gumbel.cop)
    G.m.t <- (1-p)*F.M + p*Copula.two.par(F.M, 1-F.T, a.par, b.par)
      FP.D <-  1-(G.m.t/((1-p)+p*(1-F.T)))
  plot(c(1,FP.D,0), c(1,TP.C,0), type="l", ylim=c(0,1), xlim=c(0,1))
  #
  distances.from.0.1 <- sqrt((FP.D)^2+(1-TP.C)^2)
  which.minimum <- (1:length(distances.from.0.1))[distances.from.0.1== min(distances.from.0.1)]
  cat("auc:", auc(c(1,FP.D,0), c(1,TP.C,0)), "\n")
  cat("min:", min(distances.from.0.1), "\n")
  cat(c(FP.D[which.minimum], TP.C[which.minimum]), "\n")
  cat("cutoff:", m.M[which.minimum], "\n")
  cat("---------------------------\n")
  # m.M[which.minimum]
  list(AUC.CD=auc(c(1,FP.D,0), c(1,TP.C,0)), 
       pauc.C = integrate(approxfun(c(1,FP.D,0), c(1,TP.C,0)), 
             0.2, 0.4)$value, 
       FP.D.at.cutoff=FP.D[which.minimum], 
       TP.C.at.cutoff=TP.C[which.minimum], 
       CUTOFF.CD=m.M[which.minimum],
       FP.D.CD=c(1,FP.D,0), TP.C.CD=c(1,TP.C,0))
}

#####

ROC.ID.Joe <- function(parametros, marker, time){
  obs.marker <- marker
surv.times <- time
   theta <- parametros[1]
  p <- pnorm(parametros[2])
  scale.par <- exp(parametros[3])
  shape.par <- exp(parametros[4])
  w <- 1-pnorm(parametros[2]+ parametros[5])
  # w <- 1-p
  xi.1    <- parametros[6]
  omega.1 <- exp(parametros[7])
  alpha.1 <- parametros[8]
  xi.2    <- parametros[9]
  omega.2 <- parametros[10]
  alpha.2 <- parametros[11]
  f.psi <- function(x, theta){-log(1-(1-x)^theta)}
  psi.inv <- function(x, theta){1 - (1 - exp(-x))^(1/theta)}
  psi.prima <- function(x, theta){-(theta * (1 - x)^(theta - 1)) / 
                                 (1 - (1 - x)^theta)}
  Copula.Joe <- function(u, v, theta){psi.inv(f.psi(u, theta)+
                                                  f.psi(v, theta), theta)}
  C.prima <- function(u,v, theta){
  C.uv <- function(u,v, theta){psi.inv(f.psi(u, theta)+
                               f.psi(v, theta),theta)}
          psi.prima(u, theta)/psi.prima(C.uv(u,v, theta), theta)}
#
  f.M <- w*dsn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*dsn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  F.M <- w*psn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*psn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  f.T <- dweibull(surv.times, shape = shape.par, scale = scale.par)
  F.T <- pweibull(surv.times, shape = shape.par, scale = scale.par)
  H.MT.susceptible <- Copula.Joe(F.M, 1-F.T, theta)
  TP.I <- 1-C.prima(1-F.T, F.M, theta)
  G.m.t <- (1-p)*F.M + 
    p*Copula.Joe(F.M, 1-F.T, theta)
  FP.D <-  1-(G.m.t/((1-p)+p*(1-F.T)))
#  plot(c(1,FP.D,0), c(1,TP.I,0), type="l", ylim=c(0,1), xlim=c(0,1), col=2)
  distances.from.0.1 <- sqrt((FP.D)^2+(1-TP.I)^2)
  which.minimum <- (1:length(distances.from.0.1))[distances.from.0.1== min(distances.from.0.1)]
  cat("auc:", auc(c(1,FP.D,0), c(1,TP.I,0)), "\n")
  cat("min:", min(distances.from.0.1), "\n")
  cat(c(FP.D[which.minimum], TP.I[which.minimum]), "\n")
  cat("cutoff:", marker[which.minimum], "\n")
  cat("---------------------------\n")
  # m.M[which.minimum]
  list(AUC.ID=auc(c(1,FP.D,0), c(1,TP.I,0)), 
       pauc.ID =  integrate(approxfun(c(1,FP.D,0), c(1,TP.I,0)), 
             0.2, 0.4)$value,
       CUTOFF.ID=marker[which.minimum],
       FP.D.at.cutoff=FP.D[which.minimum], 
       TP.I.at.cutoff=TP.I[which.minimum], 
       FP.D.ID=c(1,FP.D,0), TP.I.ID=c(1,TP.I,0))
}

ROC.ID.two.par <- function(parametros, m.M, t.T){
  obs.marker <- m.M
  surv.times <- t.T
  a.par <- exp(parametros[1])
  b.par <- exp(parametros[2])+1
  p <- pnorm(parametros[3])
  scale.par <- exp(parametros[4])
  shape.par <- exp(parametros[5])
  w <- 1-pnorm(parametros[3]+ parametros[6])
  # w <- 1-p
  xi.1    <- parametros[7]
  omega.1 <- exp(parametros[8])
  alpha.1 <- parametros[9]
  xi.2    <- parametros[10]
  omega.2 <- parametros[11]
  alpha.2 <- parametros[12]
  f.psi <- function(x, a, b){(x^(-a)-1)^b}
  psi.inv <- function(x, a, b){(1 + x^(1/b))^(-1/a)}
  psi.prima <- function(x, a, b){-a * b * x^(-a - 1) * (1 / x^a - 1)^(b - 1)}
  Copula.two.par <- function(u, v, a, b){psi.inv(f.psi(u, a, b)+f.psi(v, a, b), a, b)}
  C.prima <- function(u,v, a, b){
    psi.prima(u, a, b)/psi.prima(Copula.two.par(u,v, a, b), a, b)
  }
  ##########
  d.psi.two.par <- function(x, a, b){-a * b * x^(-a - 1) * (1 / x^a - 1)^(b - 1)}
  d.2.psi.two.par <- function(x, a, b){-(a * b * (1 / x^a - 1)^b * ((a + 1) * x^a - a * b - 1)) / (x^2 * (x^a - 1)^2)}
  C.prime.1 <- function(u, v, a, b){
    d.psi.two.par(u, a , b)/d.psi.two.par(Copula.two.par(u, v, a, b), a, b)
  }
  c.two.par <- function(u, v, a, b){-1*(d.psi.two.par(u, a , b)*d.psi.two.par(v, a , b)*
                                          d.2.psi.two.par(Copula.two.par(u, v, a, b), a, b))/
      (d.psi.two.par(Copula.two.par(u, v, a, b), a , b)^3)}
  f.M <- w*dsn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*dsn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  F.M <- w*psn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*psn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  f.T <- dweibull(surv.times, shape = shape.par, scale = scale.par)
  F.T <- pweibull(surv.times, shape = shape.par, scale = scale.par)
  H.MT.susceptible <- Copula.two.par(F.M, 1-F.T, a.par, b.par)
  TP.I <- 1-C.prima(1-F.T, F.M, a.par, b.par)
  G.m.t <- (1-p)*F.M + 
    p*Copula.two.par(F.M, 1-F.T, a.par, b.par)
  FP.D <-  1-(G.m.t/((1-p)+p*(1-F.T)))
#  plot(c(1,FP.D,0), c(1,TP.I,0), type="l", ylim=c(0,1), xlim=c(0,1), col=2)
  distances.from.0.1 <- sqrt((FP.D)^2+(1-TP.I)^2)
  which.minimum <- (1:length(distances.from.0.1))[distances.from.0.1== min(distances.from.0.1)]
  cat("auc:", auc(c(1,FP.D,0), c(1,TP.I,0)), "\n")
  cat("min:", min(distances.from.0.1), "\n")
  cat(c(FP.D[which.minimum], TP.I[which.minimum]), "\n")
  cat("cutoff:", m.M[which.minimum], "\n")
  cat("---------------------------\n")
  # m.M[which.minimum]
  list(AUC.ID=auc(c(1,FP.D,0), c(1,TP.I,0)), 
       pauc.ID =  integrate(approxfun(c(1,FP.D,0), c(1,TP.I,0)), 
             0.2, 0.4)$value,
       CUTOFF.ID=m.M[which.minimum],
       FP.D.at.cutoff=FP.D[which.minimum], 
       TP.I.at.cutoff=TP.I[which.minimum], 
       FP.D.ID=c(1,FP.D,0), TP.I.ID=c(1,TP.I,0))
}




# Convexity
path_length <- function(x, y) {
  sum(sqrt(diff(x)^2 + diff(y)^2))
}

conv_meas <- function(x, y) {
  ch <- chull(c(x, range(x)[2:1]), c(y, rep(min(y), 2)))
  ch <- ch[ch <= length(x)]
  pl <- path_length(x[ch], y[ch])
  (path_length(x, y) - pl)/pl
}

#################################

# time= 0.5 is approximately the 30th quantile for the susceptibles
# pweibull(0.5, shape = 1.5, scale = 1)
# 0.2978115

tau.studied <- 0.5
theta.par <- copJoe@iTau(tau = tau.studied)

t.10 <- qweibull(0.05, shape=1.5, scale=1)

true.ROC.CD.Joe <- ROC.CD.Joe(parametros=c(theta.par, -0.5,
                                             0, log(1.5),
                                             0,-7,0.7,0.5,1,1,1.5),
                                seq(from=-16, to=11, length=500), 
                                                   t.10)

cat("True cut'off marker:", true.ROC.CD.Joe$CUTOFF.CD, "\n")
cat("AUC^(CD) true:", true.ROC.CD.Joe$AUC, "\n")
plot(true.ROC.CD.Joe$FP.D.CD, true.ROC.CD.Joe$TP.C.CD, type="l", ylim=c(0,1), xlim=c(0,1),
     xlab="FP", ylab="TP(C)")
points(true.ROC.CD.Joe$FP.D.at.cutoff, true.ROC.CD.Joe$TP.C.at.cutoff, pch=1)
cat("True cut'off marker:", true.ROC.CD.Joe$CUTOFF.CD, "\n")

conv.true.ROC.CD.Joe <- conv_meas(true.ROC.CD.Joe$FP.D.CD, true.ROC.CD.Joe$TP.C.CD)


true.ROC.ID.Joe <- ROC.ID.Joe(parametros=c(theta.par, -0.5,
                                             0, log(1.5),
                                             0,-7,0.7,0.5,1,1,1.5),
                                seq(from=-16, to=11, length=500), 
                              t.10)
plot(true.ROC.ID.Joe$FP.D.ID, true.ROC.ID.Joe$TP.I.ID,
              , type="l", ylim=c(0,1), xlim=c(0,1),
     xlab="FP", ylab="TP(I)")

conv.true.ROC.ID.Joe <- conv_meas(true.ROC.ID.Joe$FP.D.ID, true.ROC.ID.Joe$TP.I.ID)

ll.joint.two.par.sim <- function(parametros, obs.marker, 
                                 surv.times, cens.status){
  a.par <- exp(parametros[1])
  b.par <- exp(parametros[2])+1
  p <- pnorm(parametros[3])
  scale.par <- exp(parametros[4])
  shape.par <- exp(parametros[5])
  w <- 1-pnorm(parametros[3]+ parametros[6])
  # w <- 1-p
  xi.1    <- parametros[7]
  omega.1 <- exp(parametros[8])
  alpha.1 <- parametros[9]
  xi.2    <- parametros[10]
  omega.2 <- parametros[11]
  alpha.2 <- parametros[12]
  Copula.two.par <- function(u, v, a, b){(((u^(-a) -1)^b + (v^(-a) -1)^b)^(1/b)+1)^(-1/a)} 
  d.psi.two.par <- function(x, a, b){-a * b * x^(-a - 1) * (1 / x^a - 1)^(b - 1)}
  d.2.psi.two.par <- function(x, a, b){-(a * b * (1 / x^a - 1)^b * ((a + 1) * x^a - a * b - 1)) / (x^2 * (x^a - 1)^2)}
  C.prime.1 <- function(u, v, a, b){
    d.psi.two.par(u, a , b)/d.psi.two.par(Copula.two.par(u, v, a, b), a, b)
  }
  c.two.par <- function(u, v, a, b){-1*(d.psi.two.par(u, a , b)*d.psi.two.par(v, a , b)*
                                          d.2.psi.two.par(Copula.two.par(u, v, a, b), a, b))/
      (d.psi.two.par(Copula.two.par(u, v, a, b), a , b)^3)}
  f.M <- w*dsn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*dsn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  F.M <- w*psn(obs.marker, xi=xi.1, omega=omega.1, alpha=alpha.1)+
    (1-w)*psn(obs.marker, xi=xi.2, omega=omega.2, alpha=alpha.2)
  f.T <- dweibull(surv.times, shape = shape.par, scale = scale.par)
  F.T <- pweibull(surv.times, shape = shape.par, scale = scale.par)
  f.joint.MT <- f.M*f.T*c.two.par(F.M, 1-F.T, a.par, b.par)
  diff.G.MT <- f.M*C.prime.1(F.M, 1-F.T,a.par, b.par)
  -1*sum(cens.status*log(p*f.joint.MT))-
    sum((1-cens.status)*
          log((1-p)*f.M +
                p*diff.G.MT))
}


#####################################
######################################
size <- 400

for(i in 1:1100){
skip_to_next <- FALSE  
tryCatch({
Joe.copula.theta <- mvdc(joeCopula(theta.par,
                                       dim= 2), 
                          c("unif", "unif"), 
                          list(list(min = 0, max = 1), 
                               list(min = 0, max = 1)), 
                          marginsIdentical = T)
sim.u1.u2 <- rMvdc(size, Joe.copula.theta)
tau.sim <- kendall.tau(sim.u1.u2[,1], sim.u1.u2[,2])
marker.sim <- 1:size
y.sim <- 1:size
status.sim <- 1:size
for(i in 1:size){
  marker.sim[i] <- Quantile.M.mix(sim.u1.u2[,1][i], 
                                  parametros=c(0.5,-7,0.7,0.5,1,1,1.5))
}
# hist(marker.sim, freq=F, xlim=c(-15, 11), ylim=c(0, 0.15))
# curve(f.M.mix(x, parametros=c(0.5,-7,0.7,0.5,1,1,1.5)), from=-15, to=11,
#      add=T)
# mle.mix.sn <- nlm(menoslog.sn,c(0.4,-6, 1,0,1.5,0.5,1),dat=marker.sim)
# curve(f.M.mix(x, parametros=mle.mix.sn$estimate), from=-15, to=11,
#      add=T, col=2)
prop.susceptible <- rbinom(n=size, size=1, 
                           prob=1-pnorm(0.5))
y.sim[prop.susceptible==0] <- Inf
y.sim[prop.susceptible==1] <- qweibull(1-
                                         sim.u1.u2[,2][prop.susceptible==1], 
                                       shape = 1.5, scale = 1)
# 40% censoring for susceptibles:
censored.sim <- runif(size, min=0, max=2.218898)
# 60% censoring for susceptibles:
# censored.sim <- runif(size, min=0, max=1.320741)
t.c.sim <- matrix(c(y.sim, censored.sim), ncol=2, byrow=F)
time.sim <- apply(t.c.sim, 1, min, na.rm = TRUE)
subst.sim <- t.c.sim-time.sim
cens.status.sim <- rep(0, nrow(subst.sim))
cens.status.sim[subst.sim[,1] == 0] <- 1
survival.sim <- data.frame(time=time.sim, censoring=cens.status.sim)

# ll.joint.two.par.sim(c(0.5, 0.5, 0.5, log(1.3), log(0.8), 0, -6, 1, 0, 1.5, 0.5, 1), 
#                     obs.marker=marker.sim,
#                     surv.times=time.sim,
#                     cens.status=cens.status.sim)
mle.Joe.two.par <- nlm(ll.joint.two.par.sim,
                         c(-1, -1.5, 0, log(1.3), log(0.8), 0, -6, 1, 0, 1.5, 0.5, 1), 
                         obs.marker=marker.sim,
                         surv.times=time.sim,
                         cens.status=cens.status.sim, gradtol=0.0001, iterlim = 250)

p.hat <- pnorm(mle.Joe.two.par$estimate[3])
scale.hat <- exp(mle.Joe.two.par$estimate[4])
shape.hat <- exp(mle.Joe.two.par$estimate[5])

KM.sim <- survfit(Surv(time, censoring)~1, data=survival.sim)
plot(KM.sim, conf.int=F)
p.sim <- 1-pnorm(0.5)
curve((1-p.sim) + (p.sim)*(1-pweibull(x, shape=1.5, scale=1)), 
      from=0.001, to=4.25, add=T, col=2)
curve((1-p.hat) + (p.hat)*(1-pweibull(x, shape=shape.hat, scale=scale.hat)), 
      from=0.001, to=4.25, add=T, col=4)
# sum(1-cens.status.sim)/size
# mle.Joe.two.par$code

a.hat <- exp(mle.Joe.two.par$estimate[1])
b.hat <- exp(mle.Joe.two.par$estimate[2])+1
tau.twopar.hat <- 1- 2/(b.hat*(2+a.hat))
cat("tau sim=", tau.sim, "\n")
cat("tau hat=", tau.twopar.hat, "\n")


est.ROC.CD.two.par <- ROC.CD.two.par(parametros=mle.Joe.two.par$estimate,
                           seq(from=-16, to=11, length=500), t.10)            
points(est.ROC.CD.two.par$FP.D.at.cutoff, est.ROC.CD.two.par$TP.C.at.cutoff)
lines(true.ROC.CD.Joe$FP.D.CD, true.ROC.CD.Joe$TP.C.CD, col=5)
points(true.ROC.CD.Joe$FP.D.at.cutoff, true.ROC.CD.Joe$TP.C.at.cutoff, pch=1, col=5)

cat("AUC^(CD) true:", true.ROC.CD.Joe$AUC, "\n")
cat("AUC^(CD) Two Parameter:", est.ROC.CD.two.par$AUC, "\n")

conv.est.ROC.CD.two.par <- conv_meas(est.ROC.CD.two.par$FP.D.CD, est.ROC.CD.two.par$TP.C.CD)


# Use Beyene's approach
try(beyene.sim <- tdROC(X=marker.sim, Y=time.sim, 
                    delta=cens.status.sim, tau=t.10), TRUE)
    cat("AUC^(CD) Beyene:", beyene.sim$main_res$AUC.integral, "\n")
lines(1-beyene.sim$main_res$ROC$spec, beyene.sim$main_res$ROC$sens, col=3)
# Find the cut-off point
distances.from.0.1.beyene <- sqrt((1-beyene.sim$main_res$ROC$spec)^2+(1-beyene.sim$main_res$ROC$sens)^2)
which.minimum.beyene <- (1:length(distances.from.0.1.beyene))[distances.from.0.1.beyene== 
                                                                min(distances.from.0.1.beyene)]
FP.D.at.cutoff.beyene <- (1-beyene.sim$main_res$ROC$spec)[which.minimum.beyene] 
TP.C.at.cutoff.beyene <- beyene.sim$main_res$ROC$sens[which.minimum.beyene]
cat(FP.D.at.cutoff.beyene[1], TP.C.at.cutoff.beyene[1], "\n")
points(FP.D.at.cutoff.beyene[1], TP.C.at.cutoff.beyene[1], pch=3)

pAUC.beyene <- AUC(1-beyene.sim$main_res$ROC$spec, beyene.sim$main_res$ROC$sens, from=0.2, to=0.4)


Heagherty.sim <- survivalROC(Stime=time.sim, status=cens.status.sim,
                             marker =  marker.sim,
                             predict.time = t.10,
                             span = 0.25*size^(-0.20) )                     
lines(Heagherty.sim$FP, Heagherty.sim$TP, col=4)

pAUC.Heagherty <-  integrate(approxfun(Heagherty.sim$FP, Heagherty.sim$TP), 
             0.2, 0.4)$value

# Find the cut-off point
distances.from.0.1.Heagherty <- sqrt((Heagherty.sim$FP)^2+
                                       (1-Heagherty.sim$TP)^2)
which.minimum.Heagherty <- (1:length(distances.from.0.1.Heagherty))[distances.from.0.1.Heagherty== 
                                                                      min(distances.from.0.1.Heagherty)]
cat(c(Heagherty.sim$FP[which.minimum.Heagherty], 
      Heagherty.sim$TP[which.minimum.Heagherty]), "\n")
points(Heagherty.sim$FP[which.minimum.Heagherty], 
       Heagherty.sim$TP[which.minimum.Heagherty], pch=4, col=6)

opt.cutoff.Heagherty <- Heagherty.sim$cut.values[which.minimum.Heagherty]
cat("cut-off Heagherty:", opt.cutoff.Heagherty, "\n")

conv.Heagherty <- conv_meas(Heagherty.sim$FP, Heagherty.sim$TP)

#Sys.sleep(5)
################
true.ROC.ID.Joe <- ROC.ID.Joe(parametros=c(theta.par,-0.5, 
                                             0, log(1.5),
                                             0,-7,0.7,0.5,1,1,1.5),
                                marker=seq(from=-16, to=11, length=500), time=t.10)
plot(true.ROC.ID.Joe$FP.D.ID, true.ROC.ID.Joe$TP.I.ID, type="l")
points(true.ROC.ID.Joe$FP.D.at.cutoff, true.ROC.ID.Joe$TP.I.at.cutoff)
# true.ROC.ID.Joe$pauc.ID

est.ROC.ID.two.par <- ROC.ID.two.par(parametros=mle.Joe.two.par$estimate,
                                     seq(from=-16, to=11, length=500), t.10)
lines(est.ROC.ID.two.par$FP.D.ID, est.ROC.ID.two.par$TP.I.ID, col=2)
points(est.ROC.ID.two.par$FP.D.at.cutoff, est.ROC.ID.two.par$TP.I.at.cutoff, col=2)

conv.ID.twopar <- conv_meas(est.ROC.ID.two.par$FP.D.ID, est.ROC.ID.two.par$TP.I.ID)

try(risksetROC.sim.ID <- risksetROC(Stime=time.sim, 
                                status=cens.status.sim,
                                marker=marker.sim, 
                                predict.time=t.10, 
                                method="LocalCox", 
                                span=(size^(-0.2)),
                                #span=0.8, 
                                plot=F), TRUE)

cat("AUC^(ID) risksetROC:", risksetROC.sim.ID$AUC, "\n")
distances.from.0.1.riskset <-  sqrt((risksetROC.sim.ID$FP)^2+(1-risksetROC.sim.ID$TP)^2)
which.minimum.riskset <- (1:length(distances.from.0.1.riskset))[distances.from.0.1.riskset== 
                                                                  min(distances.from.0.1.riskset)]
FP.D.at.cutoff.riskset <- risksetROC.sim.ID$FP[which.minimum.riskset]
TP.I.at.cutoff.riskset <- risksetROC.sim.ID$TP[which.minimum.riskset]
new.cutoff.marker <- risksetROC.sim.ID$marker[which.minimum.riskset]
which.marker.cutoff <- which.min(abs(marker.sim - new.cutoff.marker))
cutoff.risksetROC.sim <- marker.sim[which.marker.cutoff]

points(FP.D.at.cutoff.riskset, TP.I.at.cutoff.riskset)

lines(risksetROC.sim.ID$FP, risksetROC.sim.ID$TP, col=3)
conv.riskset <- conv_meas(risksetROC.sim.ID$FP, risksetROC.sim.ID$TP)
pAUC.riskset <-  integrate(approxfun(risksetROC.sim.ID$FP, 
                                     risksetROC.sim.ID$TP), 
             0.2, 0.4)$value
points(FP.D.at.cutoff.riskset, TP.I.at.cutoff.riskset, col=3)



##############
write(mle.Joe.two.par$code, file="code.txt", append = T)
####
write(est.ROC.CD.two.par$AUC, file="AUCtwoparCD.txt", append = T)
write(beyene.sim$main_res$AUC.integral, file="AUCbeyene.txt", append = T)
write(Heagherty.sim$AUC, file="AUCHeagherty.txt", append = T)

write(est.ROC.ID.two.par$AUC.ID, file="AUCtwoparID.txt", append = T)
write(risksetROC.sim.ID$AUC, file="AUCriskset.txt", append = T)
####
write(est.ROC.CD.two.par$pauc.C, file="pAUCtwoparCD.txt", append = T)
write(pAUC.beyene, file="pAUCbeyene.txt", append = T)
write(pAUC.Heagherty, file="pAUCHeagherty.txt", append = T)

write(est.ROC.ID.two.par$pauc.ID, file="pAUCtwoparID.txt", append = T)
write(pAUC.riskset, file="pAUCriskset.txt", append = T)
####
write(est.ROC.CD.two.par$FP.D.at.cutoff, file="fpCDatCutofftwopar.txt", append = T)
write(est.ROC.CD.two.par$TP.C.at.cutoff, file="tpCDatCutofftwopar.txt", append = T)
write(FP.D.at.cutoff.beyene[1], file="fpCDatCutoffbeyene.txt", append = T)
write(TP.C.at.cutoff.beyene[1], file="tpCDatCutoffbeyene.txt", append = T)
write(Heagherty.sim$FP[which.minimum.Heagherty], file="fpCDatCutoffheagherty.txt", append = T)
write(Heagherty.sim$TP[which.minimum.Heagherty], file="tpCDatCutoffheagherty.txt", append = T)
#
write(est.ROC.ID.two.par$FP.D.at.cutoff, file="fpIDatCutofftwopar.txt", append = T)
write(est.ROC.ID.two.par$TP.I.at.cutoff, file="tpIDatCutoffMLE.txt", append = T)
write(FP.D.at.cutoff.riskset, file="fpIDatCutoffRiskset.txt", append = T)
write(TP.I.at.cutoff.riskset, file="tpIDatCutoffRiskset.txt", append = T)
####
write(conv.est.ROC.CD.two.par, file="convexCDtwopar.txt", append = T)
write(conv_meas(1-beyene.sim$main_res$ROC$spec, beyene.sim$main_res$ROC$sens),
      file="convexCDbeyene.txt", append = T)
write(conv.Heagherty, file="convexCDheagherty.txt", append = T)
#
write(conv.ID.twopar, file="convexIDtwopar.txt", append = T)
write(conv.riskset, file="convexIDriskset.txt", append = T)
}, error=function(e) { skip_to_next <<- TRUE})
if(skip_to_next) { next } 
}


