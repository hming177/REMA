library(matrixStats) 
library(MASS)
library(lpSolve)  # LP
library(quadprog) # QP 
library(dfoptim)  # derivative-free optimization 
library(nloptr)   # use nloptr function for finding weights
library(SparseM)
library(quantreg)
library(denpro)
library(Runuran)
library(glmnet)
library(grpreg)
library(ggplot2)
library(ggpubr)
library(RColorBrewer)
# library(splines)
# library(fPortfolio)  # rdonlp2()

#########################################################################################  
## proposed relative error-based model averaging (REMA) #######
#########################################################################################
smat.fun = function(L, type="nested"){
  if(type=="nested"){
    ss = matrix(0, L, L)
    for(i in 1:L){
      ss[i, 1:i] = 1
    }
  }
  if(type=="full"){
    ss = matrix(0, nrow=2^L-1, ncol=L)
    num = 0
    for(j in 1:L){
      Mj = combn(1:L,j) 
      mp = ncol(Mj)
      for(k in 1:mp){
        num = num + 1
        ss[num, Mj[, k]] = 1 
      }
    }
  }
  if(type=="marginal"){
    num = 0
    ss = matrix(0, nrow=L, ncol=L)
    for(i in 1:L){
      num = num + 1
      ss[num, i] = 1
    }
  }
  return(ss)
}


LS.estfun = function(x, y){
  x00 = as.matrix(x)
  y00 = as.vector(y)
  b.est = coef(lm(y00~x00+0))
  return(b.est)
}


QR.estfun = function(x, y, tau=0.5){
  x00 = as.matrix(x)
  y00 = as.vector(y)
  b.est = coef(rq(y00~x00+0, tau=0.5, method = "br"))
  return(b.est)
}


LPRE.estfun = function(x, y){
  x00 = as.matrix(x)
  y00 = as.vector(y)
  par0 = coef(lm(log(y00)~x00+0))
  b.est = rep(1000,length(par0))
  repeat{
    f = t(x00)%*%as.matrix((1/y00)*as.vector(exp(x00%*%par0))-y00*as.vector(exp(-(x00%*%par0))))
    AA = matrix(0, length(par0), length(par0))
    for (ii in 1:length(y00)){
      tt = (1/y00[ii]*exp(x00[ii,]%*%par0)+y[ii]*exp(-x00[ii,]%*%par0))
      AA = AA+as.vector(tt)*x00[ii,]%*%t(x00[ii,])
    }
    f_diff = AA
    b.est = par0-solve(f_diff)%*%f
    
    if(sqrt(sum((b.est-par0)^2))<=10^(-5)){break}
    par0 = b.est
  }
  return(b.est)
}


LARE.estfun = function(x, y){
  x00 = as.matrix(x)
  y00 = as.vector(y)
  lare0 = function(par){
    loss = sum( abs(1-exp(x00%*%par)/y00) + abs(1-y00*exp(-x00%*%par)) ) 
    return(loss)
  }
  par0 = coef(lm(log(y00)~x00+0))
 
  b.est = optim(par=par0, fn=lare0, method="CG")$par 
  
  return(b.est)
}



etatilde.estfun = function(x, y, loss.type="LPRE"){
  if(!loss.type%in%c("LS","QR","LPRE", "LARE")){ 
    cat("Warnings: loss.type is not correctly specified");
    break 
  }
  x = as.matrix(x)
  y = as.vector(y)
  eta = rep(NA, nrow(x))
  for(i in 1:nrow(x)){
    x_i = as.matrix( x[-i, ] )
    y_i = y[-i]
    if(loss.type=="LS"){
      b.est = LS.estfun(x=x_i, y=y_i)
    } 
    if(loss.type=="QR"){
      b.est = QR.estfun(x=x_i, y=y_i)
    } 
    if(loss.type=="LPRE"){
      b.est = LPRE.estfun(x=x_i, y=y_i)
    } 
    if(loss.type=="LARE"){
      b.est = LARE.estfun(x=x_i, y=y_i)
    } 
    eta[i] = sum(x[i, ]*b.est)
  }
  list(eta=eta)
}




weightselect.fun = function(x, y, tau=0.5, cset="nested", loss.type="LPRE", smat=NULL){
  if(!loss.type%in%c("LS","QR","LPRE", "LARE")){ 
    cat("Warnings: loss.type is not correctly specified");
    break 
  }
  
  x = as.matrix(x)
  y = as.vector(y)
  
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, nrow(x), n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    xx[, m] = etatilde.estfun(x=xm, y=y, loss.type=loss.type)$eta
    if(loss.type=="LS") bbeta[id, m] = LS.estfun(x=xm, y=y)
    if(loss.type=="QR") bbeta[id, m] = QR.estfun(x=xm, y=y)
    if(loss.type=="LPRE") bbeta[id, m] = LPRE.estfun(x=xm, y=y)
    if(loss.type=="LARE") bbeta[id, m] = LARE.estfun(x=xm, y=y)
  }
  
  lpre = function(par){
    fn = mean( exp(xx%*%par)/y +y*exp(-xx%*%par) -2 ) 
    return(fn)
  }
  
  lare = function(par){
    fn = mean( abs(1- exp(xx%*%par)/y) +abs(1-y*exp(-xx%*%par)) ) 
    return(fn)
  }
  
  if(loss.type=="LS") {
    Dmat = 2*t(xx)%*%xx
    dvec = 2*t(y)%*%xx
    ## with constraint: 0 <= w_m <=1 and sum w_m=1 #############
    Amat = t(rbind(rep(1,n.models), diag(n.models)))
    bvec = c(1,rep(0, n.models))
    w.opt = solve.QP(Dmat, dvec, Amat, bvec, meq=1)$solution
    w.opt[which(w.opt<0)] = 0
    ## with constraint: 0 <= w_m <=1 ##############################
    Amat = t(rbind(diag(n.models), -diag(n.models)))
    bvec = c(rep(0, n.models),rep(-1, n.models))
    w.opt2 = solve.QP(Dmat, dvec, Amat, bvec, meq=0)$solution
    return(list(weight = w.opt, weight2 = w.opt2, bbeta=bbeta))
  }
  if(loss.type=="QR") {
    nn = nrow(x)
    # 1. objective function
    objective.in = c(rep(tau, nn), rep(1-tau, nn), rep(0, n.models), rep(0, n.models))
    # 2. with constraint: 0 <= w_m <=1 and sum w_m=1 #############
    In = diag(nn)
    const.mat1 = cbind(In, -In, xx, -xx)
    const.mat2 = cbind(diag(0,n.models,2*nn), diag(n.models), -diag(n.models))
    const.mat3 = const.mat2 
    const.mat4 = c(rep(0, 2*nn), rep(c(1, -1), each=n.models))
    const.mat = rbind(const.mat1, const.mat2, const.mat3, const.mat4)
    const.dir = c(rep("=", nn), rep(">=", n.models), rep("<=", n.models), "=")
    const.rhs = c(y, rep(0:1, each=n.models),1)
    sol = lp("min", objective.in, const.mat, const.dir, const.rhs)$solution
    eta.po = sol[(2*nn+1):(2*nn+n.models)]
    eta.ne = sol[(2*nn+n.models+1):(2*nn+2*n.models)]
    w.opt = as.matrix(eta.po-eta.ne)
    
    ##2. with constraint: 0 <= w_m <=1 ##############################
    const.mat = rbind(const.mat1, const.mat2, const.mat3)
    const.dir = c(rep("=", nrow(x)), rep(">=", n.models), rep("<=", n.models))
    const.rhs = c(y, rep(0:1, each=n.models))
    sol = lp("min", objective.in, const.mat, const.dir, const.rhs)$solution
    eta.po = sol[(2*nrow(x)+1):(2*nrow(x)+n.models)]
    eta.ne = sol[(2*nrow(x)+n.models+1):(2*nrow(x)+2*n.models)]
    w.opt2 = as.matrix(eta.po-eta.ne)
    return(list(weight = w.opt, weight2 = w.opt2, bbeta=bbeta))
  }
  if(loss.type=="LPRE") {obfun = lpre}  
  if(loss.type=="LARE") {obfun = lare}  
  
  ## find the optimal weights by minimizing the CV cirterion
  w.int = 1/rep(n.models, n.models)
  
  eval_g_ineq = function(u){
    constr <- c(sum(u)-1, 1-sum(u))
    return(constr)
  }
  lb = rep(0, n.models)
  ub = rep(1, n.models)
  opts1 = list("algorithm" = "NLOPT_LN_COBYLA",   #NLOPT_LN_COBYLA,NLOPT_GN_ISRES
               "xtol_rel" = 1.0e-15,  "maxeval"= 160000,
               "tol_constraints_ineq" = rep(1.0e-10, 2))
  
  ## with constraint: 0 <= w_m <=1 and sum w_m=1 #############
  res.opt = nloptr(x0 = w.int, eval_f = obfun, lb = lb,  ub = ub,
                   eval_g_ineq = eval_g_ineq, opts = opts1)
  w.opt = res.opt$solution
  
  ## with constraint: 0 <= w_m <=1 #############
  opts2 = list( "algorithm" = "NLOPT_LN_COBYLA",  #algorithm"="NLOPT_LN_COBYLA, 
                "xtol_rel" = 1.0e-15,  "maxeval"= 160000)
  res.opt2 = nloptr(x0 = w.int, eval_f = obfun, lb = lb, ub = ub, opts = opts2)
  w.opt2 = res.opt2$solution
  
  list(weight = w.opt, weight2 = w.opt2, bbeta=bbeta)
}


## compute the prediction error #########################
fpe = function(y0, eta0){
  pe1 = mean( (y0-exp(eta0))^2 )                           #ls
  pe2 = mean( abs(y0-exp(eta0)) )                          #qr
  pe3 = mean( exp(eta0)/y0 +y0*exp(-eta0)-2 )              #lpre 
  pe4 = mean( abs(1-exp(eta0)/y0) + abs(1-y0*exp(-eta0)) ) #lare
  Rsq1 = 1 - pe3/mean((y0-mean(y0))^2/(y0*mean(y0)))    #R^2_LPRE 
  Rsq2 = 1 - pe4/mean(abs((y0-mean(y0))/y0)+abs((y0-mean(y0))/mean(y0)))    #R^2_LARE 
  Rsq3 = 1 - pe1/mean((y0-mean(y0))^2) 
  Rsq4 = 1 - pe2/mean(abs(y0-mean(y0))) 
  pe = cbind(pe1, pe2, pe3, pe4, Rsq1, Rsq2, Rsq3,Rsq4)
  
  colnames(pe) = c("PE(mspe)", "PE(mape)", "PE(lpre)", "PE(lare)", 
                   "Rsq(LPRE)", "Rsq(LARE)","Rsq(LS)","Rsq(QR)")
  list(pe = pe)
}


REMA = function(xtrain, ytrain, xtest, ytest, cset="nested", loss.type="LPRE", smat=NULL){
  if(!loss.type%in%c("LS","QR","LPRE", "LARE")){ 
    cat("Warnings: loss.type is not correctly specified");
    break 
  }
  res = weightselect.fun(x=xtrain, y=ytrain, cset=cset, loss.type=loss.type, smat = smat)
  w.est = res$weight
  bbeta = res$bbeta
  eta.mat = xtest%*%bbeta 
  eta = eta.mat%*%w.est 
  if(loss.type %in% c("LS", "QR")){
    yhat = eta
    pe = fpe(y0=exp(ytest), eta0=eta)$pe
    pe.inf0 = apply(eta.mat, 2, function(u){ fpe(y0=exp(ytest), eta0=u)$pe}) 
  }else{
    yhat = exp(eta)
    pe = fpe(y0=ytest, eta0=eta)$pe
    pe.inf0 = apply(eta.mat, 2, function(u){ fpe(y0=ytest, eta0=u)$pe}) 
  }
  pe.inf = apply(pe.inf0, 1, min)  
  
  
  w.est2 = res$weight2
  eta2 =   eta.mat%*%w.est2
  if(loss.type %in% c("LS", "QR")){
    yhat_w2= eta2
    pe2 = fpe(y0=exp(ytest), eta0=eta2)$pe
  }else{
    yhat_w2 = exp(eta2)
    pe2 = fpe(y0=ytest, eta0=eta2)$pe
  }
  
  list(fpe = pe, fpe_w2=pe2, pe.inf=pe.inf, yhat=yhat, yhat_w2=yhat_w2, w.est=w.est, w.est2=w.est2)
}


SAIC = function(xtrain, ytrain, xtest, ytest, cset="nested", loss.type="LPRE", smat=NULL){
  if(!loss.type%in%c("LPRE", "LARE")){ 
    cat("Warnings: loss.type is not correctly specified");
    break 
  }
  x = as.matrix(xtrain)
  y = as.vector(ytrain)
  n = nrow(x)
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, n, n.models)
  aic = rep(NA, n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    if(loss.type=="LPRE"){
      bbeta[id, m] = LPRE.estfun(x=xm, y=y)
      eta = xm%*%bbeta[id, m]
      aic[m] = n*log( mean( exp(eta)/y +y*exp(-eta)-2 ) ) + 2*ncol(xm)
    }
    if(loss.type=="LARE"){ 
      bbeta[id, m] = LARE.estfun(x=xm, y=y)
      eta = xm%*%bbeta[id, m]
      aic[m] = n*log( mean( abs(1- exp(eta)/y)+ abs(1-y*exp(-eta)) ) ) + 2*ncol(xm)
    }
  }
  if(max(abs(aic))>600){ aic <- aic-mean(aic)}
  w = exp(-0.5*aic)/sum(exp(-0.5*aic))
  eta_pred = xtest%*%bbeta%*%w
  pe = fpe(y0=ytest, eta0=eta_pred)$pe
  maic.pe = fpe(y0=ytest, eta0=xtest%*%bbeta[,which.min(aic)])$pe
  list(weight=w, bbeta = bbeta, fpe = pe, maic.pe=maic.pe,
       yhat.saic=exp(eta_pred), yhat.maic= exp(xtest%*%bbeta[,which.min(aic)]))
}


SBIC = function(xtrain, ytrain, xtest, ytest, cset="nested", loss.type="LPRE", smat=NULL){
  if(!loss.type%in%c("LPRE", "LARE")){ 
    cat("Warnings: loss.type is not correctly specified");
    break 
  }
  x = as.matrix(xtrain)
  y = as.vector(ytrain)
  n = nrow(x)
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, nrow(x), n.models)
  bic = rep(NA, n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    if(loss.type=="LPRE"){
      bbeta[id, m] = LPRE.estfun(x=xm, y=y)
      eta = xm%*%bbeta[id, m]
      bic[m] = n*log( mean( exp(eta)/y +y*exp(-eta)-2 ) ) + log(n)*ncol(xm)
    }
    if(loss.type=="LARE"){ 
      bbeta[id, m] = LARE.estfun(x=xm, y=y)
      eta = xm%*%bbeta[id, m]
      bic[m] = n*log( mean( abs(1- exp(eta)/y)+ abs(1-y*exp(-eta)) ) ) + log(n)*ncol(xm)
    }
  }
  if(max(abs(bic))>600){ bic <- bic-mean(bic)}
  w = exp(-0.5*bic)/sum(exp(-0.5*bic))
  eta_pred = xtest%*%bbeta%*%w
  pe = fpe(y0=ytest, eta0=eta_pred)$pe
  mbic.pe = fpe(y0=ytest, eta0=xtest%*%bbeta[,which.min(bic)])$pe
  list(weight=w, bbeta = bbeta, fpe = pe, mbic.pe=mbic.pe, 
       yhat.sbic=exp(eta_pred), yhat.mbic= exp(xtest%*%bbeta[,which.min(bic)]))
}


Mallows = function(xtrain, ytrain, xtest, ytest, cset="nested", smat=NULL){
  x = as.matrix(xtrain)
  y = as.vector(ytrain)
  n = nrow(x)
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, nrow(x), n.models)
  K = sigma = rep(NA, n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    bbeta[id, m] = LS.estfun(x=xm, y=y)
    xx[, m] = xm%*%bbeta[id, m]
    K[m] = length(id)
    sigma[m] = sum((y - xx[, m])^2)/(n-K[m])
  }
  
  Dmat = t(xx)%*%xx
  dvec = t(y)%*%xx-sigma[which.max(K)]*t(K)
  ## with constraint: 0 <= w_m <=1 and sum w_m=1 #############
  Amat = t(rbind(rep(1,n.models), diag(n.models)))
  bvec = c(1,rep(0, n.models))
  w.opt = solve.QP(Dmat, dvec, Amat, bvec, meq=1)$solution
  w.opt[which(w.opt<0)] = 0
  ## with constraint: 0 <= w_m <=1 ##############################
  Amat = t(rbind(diag(n.models), -diag(n.models)))
  bvec = c(rep(0, n.models),rep(-1, n.models))
  w.opt2 = solve.QP(Dmat, dvec, Amat, bvec, meq=0)$solution
  
  eta_pred = xtest%*%bbeta%*%w.opt
  pe = fpe(y0=exp(ytest), eta0=eta_pred)$pe
  yhat = eta_pred
  eta_pred2 = xtest%*%bbeta%*%w.opt2
  pe2 = fpe(y0=exp(ytest), eta0=eta_pred2)$pe
  yhat_w2 = eta_pred2
  return(list(fpe = pe, fpe_w2 = pe2, weight = w.opt, weight2 = w.opt2, 
              bbeta=bbeta, yhat=yhat, yhat_w2=yhat_w2))
}


REMA_EW = function(xtrain, ytrain, xtest, ytest, cset="nested", loss.type="LPRE", smat=NULL){
  x = as.matrix(xtrain)
  y = as.vector(ytrain)
  
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, nrow(x), n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    xx[, m] = etatilde.estfun(x=xm, y=y, loss.type=loss.type)$eta
    if(loss.type=="LPRE") bbeta[id, m] = LPRE.estfun(x=xm, y=y)
    if(loss.type=="LARE") bbeta[id, m] = LARE.estfun(x=xm, y=y)
  }

  ## Set the optimal weights as equal weight
  w.est = 1/rep(n.models, n.models)
  eta.mat = xtest%*%bbeta 
  eta = eta.mat%*%w.est 
  
  yhat = exp(eta)
  pe = fpe(y0=ytest, eta0=eta)$pe
  pe.inf0 = apply(eta.mat, 2, function(u){ fpe(y0=ytest, eta0=u)$pe}) 
  pe.inf = apply(pe.inf0, 1, min)  
  
  list(fpe = pe, pe.inf=pe.inf, yhat=yhat, w.est=w.est)
}

REMA_LW = function(xtrain, ytrain, xtest, ytest, cset="nested", loss.type="LPRE", smat=NULL){
  x = as.matrix(xtrain)
  y = as.vector(ytrain)
  
  if(is.null(smat)){
    ss = smat.fun(L=ncol(x), type=cset)
  }else{
    ss = smat
  }
  
  n.models = nrow(ss)
  bbeta = matrix(0, ncol(x), n.models)
  xx = matrix(NA, nrow(x), n.models)
  for(m in 1:n.models){
    id = which(ss[m,]==1)
    xm = as.matrix(x[, id])
    xx[, m] = etatilde.estfun(x=xm, y=y, loss.type=loss.type)$eta
    if(loss.type=="LPRE") bbeta[id, m] = LPRE.estfun(x=xm, y=y)
    if(loss.type=="LARE") bbeta[id, m] = LARE.estfun(x=xm, y=y)
  }
  
  Dmat = 2*t(exp(xx))%*%exp(xx)
  dvec = 2*t(y)%*%exp(xx)
  ## with constraint: 0 <= w_m <=1 and sum w_m=1 #############
  Amat = t(rbind(rep(1,n.models), diag(n.models)))
  bvec = c(1,rep(0, n.models))
  w.est = solve.QP(Dmat, dvec, Amat, bvec, meq=1)$solution
  w.est[which(w.est<0)] = 0
  ## with constraint: 0 <= w_m <=1 ##############################
  Amat = t(rbind(diag(n.models), -diag(n.models)))
  bvec = c(rep(0, n.models), rep(-1, n.models))
  w.est2 = solve.QP(Dmat, dvec, Amat, bvec, meq=0)$solution
  
  
  
  eta.mat = exp(xtest%*%bbeta) 
  eta = eta.mat%*%w.est 
  yhat = eta
  pe = fpe(y0=ytest, eta0=log(eta))$pe
  pe.inf0 = apply(eta.mat, 2, function(u){ fpe(y0=ytest, eta0=u)$pe}) 
  pe.inf = apply(pe.inf0, 1, min)  
  
  
  eta2 = eta.mat%*%w.est2
  yhat_w2 = eta2
  pe2 = fpe(y0=ytest, eta0=log(eta2))$pe
  
  list(fpe = pe, fpe_w2=pe2, pe.inf=pe.inf, yhat=yhat, yhat_w2=yhat_w2, w.est=w.est, w.est2=w.est2)
}


readmm <- function(x, y, lambda=NULL, intercept=FALSE, normalize=TRUE, 
                   penalty=c("ALasso", "Bridge", "MCP", "SCAD"),loss=c("LPRE","LARE"),
                   gamma=switch(penalty, ALasso=1, Bridge=0.5, SCAD = 3.7, MCP = 3)){
  ##need packages "ucminf" 
  x <- as.matrix(x)
  y <- as.matrix(y)
  np <- dim(x)
  n <- np[1]
  p <- np[2]
  
  if(intercept){
    meanx <- colMeans(x)
    mprody <- prod(y^(1/n))
  }else{
    meanx <- rep(0, p)
    mprody <- 1
  }
  x <- scale(x, meanx, FALSE)
  if(normalize){normx <- sqrt(colSums(x^2)) }else{ normx <- rep(1, p)}
  x <- scale(x, FALSE, normx)
  y <- y/mprody
  tx <- t(x)
  
  if(is.null(lambda)) {
    lambda_max<-max(abs(tx%*%log(y))/n)
    lambda_min<-lambda_max * 1e-3
    lambda1<-seq(log(lambda_max), log(lambda_min), length=100)
    lambda<-exp(lambda1)
  } 
  
  weight <- function(beta0, penalty, lambdaj, gamma){
    if(penalty=="ALasso"){
      w <- lambdaj/((abs(beta0) + 1/n)^gamma)
    }else if(penalty=="SCAD"){
      w <- beta0
      po1 <- which(abs(beta0)<=lambdaj)
      po2 <- which(abs(beta0)>gamma*lambdaj)
      po3 <- setdiff(1:p, c(po1,po2))
      w[po1] <- lambdaj
      w[po2] <- 0
      w[po3] <- (gamma*lambdaj-abs(beta0)[po3])/(gamma-1)
    }else if(penalty=="Bridge"){
      w <- lambdaj*gamma*(abs(beta0) + 1/n)^(gamma-1)
    }else{
      w <- beta0
      po1 <- which(abs(beta0)<=gamma*lambdaj)
      w[po1] <- lambdaj
      w[setdiff(1:p, po1)] <- 0
    }
    return(w)
  }
  
  #Approximation algorithm to solve beta (SQP)
  solvelpre <- function(a, b, u, rho){
    D1 <- tx %*% (1/y*exp(x %*% b) - y*exp(-x %*% b))/n
    tt <- 1/y*exp(x %*% b) + y*exp(-x %*% b)
    D2 <- tx %*% diag(as.vector(tt)) %*% x/n
    D.inverse <- solve(D2+diag(rho, p))
    q <- rho * a - u + D2 %*% b - D1
    beta <- D.inverse %*% q
    return(beta)
  }
  solvelare <- function(a, b, r, e, u1, u2, u3, rho1, rho2, rho3){
    for (k in 1:30) {
      t1 <- y * exp(-x %*% b)
      t2 <- 1/y * exp(x %*% b)
      D1 <- u1 + rho1*(b-a) + tx %*% (u3 * t2 - u2 * t1) +
        + tx %*% (rho3 * (e - 1 + t2) * t2 - rho2 * (r - 1 + t1) * t1)
      tt <- u2 * t1 + u3 * t2 + rho2 * ((r-1) * t1 + 2* t1^2) + rho3 * ((e-1) * t2 + 2 * t2^2)
      D2 <- diag(rho1, p) + tx %*% diag(as.vector(tt)) %*% x
      D.inverse <- solve(D2)
      beta <- b - D.inverse %*% D1
      if(norm(beta-b,"2")<10^-4) break
      b <- beta
    }
    return(beta)
  }
  
  ##solve penlity lpre function and lare function 
  penlpre <- function(lambdaj){
    rho <- 1#; alpha <- 1.8
    ak <- bk <- uk <- rep(0,p)
    if(n > p) bk <- lm(log(y) ~ x + 0)$coef 
    maxiter <- 300
    eps1 <- sqrt(p)*10^-4; eps2 <- 10^-2
    for (k in 1 : maxiter) {
      bnew <- solvelpre(ak, bk, uk, rho)
      #bnew <- alpha * bnew + (1 - alpha) * ak
      w <- weight(bnew, penalty, lambdaj, gamma)
      s <- bnew + uk/rho
      anew <- sign(s)*pmax(abs(s)-w/rho, 0)
      unew <- uk + rho * (bnew -anew)   
      
      if(norm(bnew-anew,"2") < eps1+eps2*max(norm(bnew,"2"),norm(anew,"2")) &&
         norm(anew-ak,"2") < eps1/sqrt(rho)+eps2*norm(unew,"2")) break
      #if(norm(bnew-ak,"2")<eps2&&norm(anew-ak,"2")<eps2) break
      
      bk <- bnew
      ak <- anew
      uk <- unew
    }
    return(c(k, length(which(anew!=0)), anew))
  }
  penlare <- function(lambdaj){
    rho1<- rho2<- rho3<- 1; ak <- bk<- u1k<- rep(0,p)
    rk<- ek<- u2k<- u3k<- rep(0, n)
    if(n > p) bk <- lm(log(y) ~ x + 0)$coef 
    maxiter <- 300
    eps1<-sqrt(p)*10^-4; eps2<-10^-2
    for (k in 1 : maxiter) {
      bnew <- solvelare(ak, bk, rk, ek, u1k, u2k, u3k, rho1, rho2, rho3)
      s2 <- 1 - u2k/rho2 - y * exp(-x %*% bnew)
      rnew <- sign(s2) * pmax(abs(s2) - 1/(n*rho2), 0)
      s3 <- 1 - u3k/rho3 - 1/y * exp(x %*% bnew)
      enew <- sign(s3) * pmax(abs(s3) - 1/(n*rho3), 0)
      w <- weight(bnew, penalty, lambdaj, gamma)
      s1 <- bnew + u1k/rho1
      anew <- sign(s1)*pmax(abs(s1) - w/rho1, 0)
      t1 <- y * exp(-x %*% bnew)
      t2 <- 1/y * exp(x %*% bnew)
      u1new <- u1k + rho1 * (bnew -anew)  
      u2new <- u2k + rho2 * (y * exp(-x %*% bnew) + rnew - 1) 
      u3new <- u3k + rho3 * (1/y * exp(x %*% bnew) + enew - 1)  
      
      if(norm(bnew-anew,"2") < eps1+eps2*max(norm(bnew,"2"),norm(anew,"2")) &&
         norm(anew-ak,"2") < eps1/sqrt(rho1)+eps2*norm(u1new,"2")) break
      #if(norm(bnew-bk,"2")/norm(bk,"2")<eps2) break
      ak <- anew
      bk <- bnew
      rk <- rnew
      ek <- enew
      u1k <- u1new
      u2k <- u2new
      u3k <- u3new
    }
    return(c(k, length(which(anew!=0)), anew))
  }
  
  
  if(loss=="LPRE"){
    penloss <- penlpre
  }else{
    penloss <- penlare
  }
  para <- lapply(1:length(lambda), function(j){penloss(lambda[j])})
  para <- do.call(cbind, para)
  iter <- para[1, ]
  df <- para[2, ]
  b <- scale(t(para[-c(1,2), ]), FALSE, normx)
  esti <- rbind(log(mprody) - meanx %*% t(b), t(b))
  
  return(list(beta=esti, lambda=lambda, df=df, iter=iter))
}

ic <- function(x, y, beta, IC=c("AIC","BIC","EBIC","HBIC"),loss=c("ls","lpre","lare")){
  x <- as.matrix(cbind(1, x))
  y <- as.vector(y)
  n <- length(y)
  p <- ncol(x)
  beta <- as.matrix(beta)
  df <- sapply(1:ncol(beta), function(j)length(which(beta[-1, j]!=0)))
  ##EBIC: 0 =< a <= 1, HBIC: a >= 1
  if(IC=="EBIC") { a <- 0.5 }else if(IC=="HBIC"){ a <- 0.5*log(log(n))}
  an <- switch(IC, AIC=2, BIC=log(n)/n, EBIC=(log(n)+2*a*log(p))/n, HBIC= 2*a*log(p)/n)
  resi <- switch(loss, ls=colMeans((y - x %*% beta)^2), lpre= colMeans((y - exp(x %*% beta))^2/(y*exp(x %*% beta))),
                 lare = colMeans(abs(1 - 1/y * exp(x%*% beta)) + abs(1 - y * exp(-x %*% beta)))) 
  
  icvalue <- log(resi) + an * df
  return(coef = beta [, which.min(icvalue)])      
}





