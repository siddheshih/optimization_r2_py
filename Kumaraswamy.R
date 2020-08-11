import(stats)
import(nleqslv)
import(nloptr)
import(mgcv)

#method of moments solver for kumaraswamy distribution
kumar.MoM <- function(mu, vr) {
  
  #moment generation function
  mn <- function(a, b, n) {
    log.num <- log(b) + lgamma(1 + n/a) + lgamma(b)
    log.den <- lgamma(1 + b + n/a)
    return (exp(log.num-log.den))
  }
  
  #method of moments function
  fn.MoM <- function(par) {
    mom1 <- mn(exp(par[1]), exp(par[2]),1) - mu
    mom2 <- mn(exp(par[1]), exp(par[2]),2) - mn(exp(par[1]), exp(par[2]),1)^2 - vr
    return (c(mom1, mom2))
  }
  
  est <- as.vector(exp(nleqslv(c(0.01,0.01), fn.MoM)$x))
  return (est)
}

#' Optimization Routine - optimize for unknown values of W, R, Z respectively denoting 
#' (1) amount of trust-channel "consumed" for loan 
#' (2) desired return on loan (expected return = W*((R-Z)*P.in+Z)
#' (3) securitization rate on loan
#' Routine cannot solve for all 3 parameters simultaneusly! at least 1/3 variables must be provided
#'
#' @param corr.mtx - correlation matrix of items in loan portfolio
#' @param P.in - vector of subjective risk values , i.e. probability of repayment of item in loan portfolio
#' @param W.in - vector of current amounts in trust channel dedicated to each loan (NA denotes values to optimize)
#' @param R.in - vector of desired return on each loan (NA denotes values to optimize)
#' @param Z.in - vector of securitization rate on each loan (NA denotes values to optimize)
#' @param Wlim - for NA values of W.in, upper limit of W (maximum allowed in trust channel)
#' @param Rlim - for NA values of R.in, upper limit of R (maximum return allowed)
#' @param Zlim - for NA values of R.in, lower limit of Z (maximum securitization allowed)
#' @param k.alpha - maximum allowed probability that portfolio losses are below z.aplha
#' @param z.alpha - mazimum percentage loss of portfolio (cannot be negative)
#' @param penalty.RZ - if trying to solve for both R & Z, then a penalty term must be introduced for borrower's disutility of R & Z
#' @param elastic.RZ - if penalty.RZ>0, elasticity for borrower cobb-douglas utility function: U =-R^(elasticity)*Z^(1-elasticity)
#' @param algorithm - non-linear optimization algorithm (see documentation for NLopt)
#' @param controls  - control  parameters such as max-eval for algorithm used for non-linear optimization
#' @param S.FN  - list of loess functions that output amount demanded downstream given rate (R) and securitization (Z)
#' @param relax  - relaxes constraint 
#' @param browse - TRUE/FALSE invoke browser
#' @return
#' @export
optim.Kumar <- function(corr.mtx, P.in,
                        W.in = NA, R.in = NA, Z.in = NA,
                        Wlim = 0, Rlim = 3, Zlim = 0.01,
                        k.alpha = 0.05, z.alpha = 0.05, eps=0.05,
                        penalty.RZ = 0, elastic.RZ = 0.5,Clim=NA,CashLim=NA,
                        algorithm = "NLOPT_LD_SLSQP", controls = list(),
                        S.FN = c(), relax = FALSE, browse = FALSE) {
  
  #### Setup Default Values ####
  
  #Determine which missing values to optimize
  W.optim <- c() #Index for W elements to be optimized in the vector W.in=W in the composing the mathematical formulation
  R.optim <- c() #Index for R elements to be optimized in the vector R.in=R in the composing the mathematical formulation
  Z.optim <- c() #Index for Z elements to be optimized in the vector C.in=C in the composing the mathematical formulation
  W.indx <- integer(0) #Index for W elements to be optimized in vector passed to optimization routine
  R.indx <- integer(0) #Index for R "
  Z.indx <- integer(0) #Index for Z "
  W.TF <- FALSE #Are there W variables to be optimized?
  R.TF <- FALSE #Are there R "
  Z.TF <- FALSE #Are there Z "
  S.TF <- FALSE #Will there be novation occurring?
  C.TF <- FALSE #Only used for forward-prop because we must ensure that w_ast+w_nov=pre-defined value
  n.S <- 0 # number of supply functions passed in (should always be 1. >1 if more than one asset to optimize)      
  n.C <- 0 # Only used for forward-prop, number of combined sets passed in (should always be 1. >1 if more than one asset to optimize)     
  Cash.TF <- FALSE #is there cash constraint in the portfolio
  
  #If CashLim imposed then need to incorporate risk-free rate for holding cash into the setup
  #first elment of input vectors should always represent cash holdings
  if(!is.na(CashLim)){
    Cash.TF <- TRUE
    #(1) W.in, R.in, Z.in
    W.in <- c(CashLim,W.in)
    R.in <- c(1.01,R.in) #Assume risk free real-rate of return of 1%
    Z.in <- c(1,Z.in) #100% money back
    #(2) P.in
    if(is.matrix(P.in)) { #this should be a matrix of the kumaraswamy distribution parameters
      P.in <- rbind(matrix(c(0.9999,100,1),1,3),P.in) #first line is appending repayment probability params to 
    } else{
      P.in <- c(0.9999,P.in)
    }
    #(3) corr.mtx
    corr.mtx <- cbind(rep(0,nrow(corr.mtx)+1),rbind(rep(0,ncol(corr.mtx)),corr.mtx))
    corr.mtx[1,1] <- 1
  }
  
  #Only used for forward-prop (optimization solves for pre-specified amounts)
  if(all(!is.na(Clim))){
    C.TF <- TRUE
    n.C <- length(Clim)
  }
  
  #Which variables correspond to Supply Function (S.FN)
  if(length(S.FN)>0 & is.list(S.FN)) { #checks number of TPS function in S.FN, if>0
    S.TF <- TRUE #supply function has been passed in (which means novation is occurring)
    S.optim <- c((nrow(corr.mtx)+1-length(S.FN)):nrow(corr.mtx)) #correlation matrix is constructed s.t. last elements correspond to novation 
    W.in[S.optim] <- 0.01 #just setting a random default value for now for amount novated
    n.S <- length(S.optim) #number of supply functions
  } else {
    S.optim <- integer(0) 
  }
  
  #Which W elements to optimize
  if(any(is.na(W.in))) {
    if(length(W.in) == 1) { #this condition is essentially if W.in is a single value (NA) then we know we must solve for the whole vector W.in
      W.optim <- c(1:nrow(corr.mtx)) 
      W.in <- rep(NA, nrow(corr.mtx))
    } else {
      W.optim <- which(is.na(W.in)) #which element in W.in to optimize
    }
    W.TF <- TRUE #condition that we do have W.in elements to optimize
  }
  
  #Which R elements to optimize
  if(any(is.na(R.in))) {
    if(length(R.in) == 1) {
      R.optim <- c(1:nrow(corr.mtx))
      R.in <- rep(NA, nrow(corr.mtx))
    } else {
      R.optim <- which(is.na(R.in))
    }
    R.TF <- TRUE
  }
  
  #Which Z elements to optimize
  if(any(is.na(Z.in))) {
    if(length(Z.in) == 1) {
      Z.optim <- c(1:nrow(corr.mtx))
      Z.in <- rep(NA, nrow(corr.mtx))
    } else {
      Z.optim <- which(is.na(Z.in))
    }
    Z.TF <- TRUE
  }
  
  #Number of Variables to send to optimizer
  n.opt <- length(W.optim)+length(R.optim)+length(Z.optim)
  
  #### Create Funtions to interpolate values and gradients of S.FN from MGCV ####
  
  #Parse S.FN to create necessary functions to return amount sold given R and Z
  if(S.TF) {

    # Adjusts inputs of R & Z chosen by optimizer
    RZ.S.calc <- function(R, Z) {
      Rc <- R.in[W.optim] #[c((1+Cash.TF):length(W.indx))]
      Zc <- Z.in[W.optim] #[c((1+Cash.TF):length(W.indx))]
      
      if(is.atomic(R)) {
        return (list(Rs = Rc-R, Zs = Zc-Z))
      }
      
      m <- length(Rc)
      if(!is.matrix(R) & !is.matrix(Z)) {
        if(length(R) == m & length(Z) == m) {
          Rs <- Rc-R
          Zs <- Zc-Z
        }} else if(ncol(R) == m & ncol(Z) == m) {
          Rs <- t(as.matrix(Rc, m,1)%*%matrix(1, nrow = 1, ncol = nrow(R)))-R
          Zs <- t(as.matrix(Zc, m,1)%*%matrix(1, nrow = 1, ncol = nrow(Z)))-Z
        }
      return (list(Rs = Rs, Zs = Zs))
    }
    
    #interpolate supply at a given point
    S.intrp <- function(R, Z, inpt.adj = TRUE) {
      
      #function to interpolate set
      S.intrp.set <- function(mdls, R, Z) {
        S <- rep(0, length(R))
        ## This is at the heart of how the supply function is iterpolated!
        for(i in c(1:length(mdls))) {
          S <- S+mgcv::predict.gam(mdls[[i]], data.frame(cbind(R = R, Z = Z)),type='response') 
        }
        return (S)
      }
      
      #If inpt.adj
      if(inpt.adj) {
        RZ <- RZ.S.calc(R, Z)
        R <- RZ$R
        Z <- RZ$Z
      }
      #simple case
      m <- length(S.FN)
      if(m == 1) {
        if(any(class(S.FN[[1]])=="gam")){
          S <- S.intrp.set(S.FN[1], R, Z)
        } else {
          S <- S.intrp.set(S.FN[[1]], R, Z)
        }
        return (S)
      }
      
      if(!is.matrix(R) & !is.matrix(Z)) {
        if(length(R) == m & length(Z) == m) {
          R <- t(as.matrix(R))
          Z <- t(as.matrix(Z))
        } else {
          R <- matrix(rep(R, m), ncol = m)
          Z <- matrix(rep(Z, m), ncol = m)
        }
      }
      
      S <- matrix(nrow = nrow(R), ncol = m)
      
      for(j in c(1:m)) {
        S[, j] <- S.intrp.set(S.FN[j], R[, j], Z[, j])
      }
      return (S)
    }
    
    #Interpolate derivative w.r.t R
    S.dR.intrp <- function(R, Z, delta = 1e-6/2, inpt.adj = TRUE) {
      S.pre <- S.intrp(R-delta, Z, inpt.adj = inpt.adj)
      #S.0   <- S.intrp(R, Z, inpt.adj = inpt.adj)
      S.pst <- S.intrp(R+delta, Z, inpt.adj = inpt.adj)
      
      #Sdiff.pre <- (S.0-S.pre)/delta
      #Sdiff.pst <- (S.pst-S.0)/delta
      
      return ((S.pst-S.pre)/(2*delta))
    }
    #interpolate derivative w.r.t Z
    S.dZ.intrp <- function(R, Z, delta = 1e-6/2, inpt.adj = TRUE) {
      S.pre <- S.intrp(R, Z-delta, inpt.adj = inpt.adj)
      #S.0   <- S.intrp(R, Z, inpt.adj = inpt.adj)
      S.pst <- S.intrp(R, Z+delta, inpt.adj = inpt.adj)
      
      #Sdiff.pre <- (S.0-S.pre)/delta
      #Sdiff.pst <- (S.pst-S.0)/delta
      
      return ((S.pst-S.pre)/(2*delta))
    }
  }
  
  #### Define/Update Vectors and Vector-Derivatives ####
  
  #define derivative vectors
  dWin.dw  <- rep(0,length(W.in))#Vector derivative of W vector w.r.t w_ast
  dWin.dr <- rep(0,length(W.in)) #Vector derivative of W vector w.r.t r_nov
  dWin.dz <- rep(0,length(W.in)) #Vector derivative of W vector w.r.t c_nov
  dRin.dr <- rep(0,length(R.in)) #Vector derivative of R vector w.r.t r_nov
  dZin.dz <- rep(0,length(Z.in)) #Vector derivative of Z vector w.r.t c_nov
  
  #set values
  if(W.TF){ #If any allocations to be optimized
    dWin.dw[W.optim] <- 1
  }
  if(Cash.TF){ #if cash constraint
    dWin.dw[1] <- -1
  }
  if(S.TF){ #If supply function provided
    dRin.dr[R.optim] <- 1
    dZin.dz[Z.optim] <- 1
  }
  
  #Scoping requirement: we would like to change values of variables that are not explicitly passed into the function
  #that is they are declared outside the function, BUT, we DON'T want those changes to persist outside the function
  #e.g. suppose W.in = [1,2,3] and inside f() we modify W.in such that W.in = [1,2,4] then that change to W.in should
  #only be visible inside f() outside f() W.in remains W.in=[1,2,3]
  #in R if we want changes to persist outside f() then we do assignment W.in <<- [1,2,4] rather than W.in <- [1,2,4]
  
  #Parse X.opt, update W.in, R.in, Z.in, dWin.dw, dWin.dr, dWin.dz, dRin.dr, dZin.dz
  opt.update.WRZ <- function(X)  { # X is the vector of values returned by the optimizer
    # Update W (allocation) vector
    if(W.TF){
      W.in[W.optim] <- X[W.indx]
      if(Cash.TF){ # Impose cash limit
        W.in[1] <- CashLim-sum(X[W.indx])
      }
    }
    # Update Return vector
    if(R.TF){
      R.in[R.optim] <- X[R.indx]
    }
    # Update Collateral vector
    if(Z.TF){
      Z.in[Z.optim] <- X[Z.indx]
    }
    # If supply function has been provided
    if(S.TF){ #indices ending in 'S' indicate that its related to the supply function
      W.in[S.optim] <- S.intrp(X[RS.indx], X[ZS.indx])
      dWin.dr[S.optim] <- S.dR.intrp(X[RS.indx], X[ZS.indx])
      dWin.dz[S.optim] <- S.dZ.intrp(X[RS.indx], X[ZS.indx])
      #update terms in W vector related to cash-limit constraint
      if(Cash.TF){ 
        dWin.dz[1] <- -W.in[S.optim] #derivative = -w_nov
        W.in[1] <- ifelse(W.TF,W.in[1],CashLim)-sum(W.in[S.optim]*(-X[ZS.indx])) #For reasons to be explained later we solve for -c_nov in the optimizer
      }
    }
    return (list(W = W.in, R = R.in, Z = Z.in, 
                 dW.dw = dWin.dw, dW.dr = dWin.dr, dW.dz = dWin.dz, dR.dr = dRin.dr, dZ.dz = dZin.dz))
  }
  
  #### Objectives, Gradients, Hessian ####
  
  #objective function
  obj <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate lender profit
    prft <- t(W)%*%(P.in*(R-Z)+Z)
    
    #calculate scalaing factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    
    return(scale.fct*sqrt(Var[1,1])-prft[1,1])
  }
  
  #derivative with respect to w_ast
  d.obj.dw <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    dW.dw <- params$dW.dw
    
    #derivative of profit w.r.t w_ast
    dprft.dw <- t(dW.dw)%*%(P.in*(R-Z)+Z)
    
    ##derivative of variance w.r.t. w_ast
    #calculate terms
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std) #scalar
    dVar.df <- 2*(corr.mtx%*%(W*(R-Z)*Std)) #n x 1
    df.dw <- Std*(R-Z)*dW.dw #n x 1
    #Combine
    dVar.dw <- scale.fct*1/2*Var[1,1]^(-1/2)*dVar.df[W.optim]*(df.dw[W.optim]+df.dw[1]*Cash.TF) #%*%t(df.dw)
    #dVar.dw <- dVar.dw[W.optim]
      
    return(dVar.dw-dprft.dw)
  } 
  
  #derivative with respect to r_nov
  d.obj.dr <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    dW.dr <- params$dW.dr
    dR.dr <- params$dR.dr
    
    #derivative of profit w.r.t w_ast
    dprft.dr <- t(dW.dr)%*%(P.in*(R-Z)+Z)+t(W)%*%(P.in*dR.dr)
    
    ##derivative of variance w.r.t. w_ast
    #calculate terms
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std) #scalar
    dVar.df <- 2*(corr.mtx%*%(W*(R-Z)*Std)) #n x 1
    df.dr <- Std*((R-Z)*dW.dr+W*dR.dr) #n x 1
    #Combine
    dVar.dr <- scale.fct*1/2*Var[1,1]^(-1/2)*(dVar.df*df.dr)[R.optim]#%*%t(df.dr)
    #dVar.dw <- dVar.dw[W.optim]
    
    return(dVar.dr-dprft.dr)
  } 
  
  #derivative with respect to z_nov
  d.obj.dz <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    dW.dz <- params$dW.dz
    dZ.dz <- params$dZ.dz
    
    #derivative of profit w.r.t w_ast
    dprft.dz <- t(dW.dz)%*%(P.in*(R-Z)+Z)-t(W)%*%(P.in*dZ.dz)
    
    ##derivative of variance w.r.t. w_ast
    #calculate terms
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std) #scalar
    dVar.df <- 2*(corr.mtx%*%(W*(R-Z)*Std)) #n x 1
    df.dz <- Std*((R-Z)*dW.dz-W*dZ.dz) #n x 1
    #Combine
    dVar.dz <- scale.fct*1/2*Var[1,1]^(-1/2)*(dVar.df*df.dz)[Z.optim]#%*%t(df.dz)
    #dVar.dw <- dVar.dw[W.optim]
    
    return(dVar.dz-dprft.dz)
  } 
  
  #hessian of profit (not used)
  f.prft.hsn <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprft.dW <- P.in*(R-Z)+Z
    dprft.dR <- W*P.in
    dprft.dZ <- W*(1-P.in)
    
    dprft.dWdW <- 0
    dprft.dWdR <- P.in
    dprft.dWdZ <- 1-P.in
    dprft.dRdR <- 0
    dprft.dRdZ <- 0
    dprft.dZdZ <- 0
    
    #return list
    return(list('dWdW'=dprft.dWdW,'dWdR'=dprft.dRdR,'dWdZ'=dprft.dWdZ,
                'dRdR'=dprft.dRdR,'dRdZ'=dprft.dRdZ,'dZdZ'=dprft.dZdZ))
  }
  
  #hessian of VaR (not used)
  g.VaR.hsn <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #Helper variables
    S_W <- Std*W
    S_RZ <- (R-Z)*Std
    W_RZ_S <- W*S_RZ
    O.W_RZ_S <- corr.mtx%*%(W_RZ_S)
    W_RZ_S.O <- t(W_RZ_S)%*%corr.mtx
    
    #calculate scaling factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W_RZ_S)%*%corr.mtx%*%(W_RZ_S)
    
    #calculate derivatives of Var
    dVar.dW <-  O.W_RZ_S*S_RZ#*2
    dVar.dR <-  O.W_RZ_S*S_W #*2
    dVar.dZ <- -O.W_RZ_S*S_W #*2
    
    #Unscaled second derivatives
    dVaR.dWdW <-  Var[1,1]^(-1/2)*(diag(S_RZ)%*%corr.mtx%*%diag(S_RZ))+
                 -Var[1,1]^(-3/2)*dVar.dW%*%(W_RZ_S.O*t(S_RZ))
    dVaR.dWdR <-  Var[1,1]^(-1/2)*((diag(S_RZ)%*%corr.mtx%*%diag(S_W))+diag(O.W_RZ_S*Std))+
                 -Var[1,1]^(-3/2)*dVar.dW%*%(W_RZ_S.O*t(S_W))
    dVaR.dWdZ <- -Var[1,1]^(-1/2)*((diag(S_RZ)%*%corr.mtx%*%diag(S_W))+diag(O.W_RZ_S*Std))+
                  Var[1,1]^(-3/2)*dVar.dW%*%(W_RZ_S.O*t(S_W))
    dVaR.dRdR <-  Var[1,1]^(-1/2)*(diag(S_W)%*%corr.mtx%*%diag(S_W))+
                 -Var[1,1]^(-3/2)*dVar.dR%*%(W_RZ_S.O*t(S_W))
    dVaR.dRdZ <- -Var[1,1]^(-1/2)*(diag(S_W)%*%corr.mtx%*%diag(S_W))+
                  Var[1,1]^(-3/2)*dVar.dR%*%(W_RZ_S.O*t(S_W))
    dVaR.dZdZ <- -Var[1,1]^(-1/2)*(diag(S_W)%*%corr.mtx%*%diag(S_W))+
                  Var[1,1]^(-3/2)*dVar.dR%*%(W_RZ_S.O*t(S_W))
    
    #return list
    return(list('dWdW'=dVaR.dWdW*scale.fct,'dWdR'=dVaR.dRdR*scale.fct,'dWdZ'=dVaR.dWdZ*scale.fct,
                'dRdR'=dVaR.dRdR*scale.fct,'dRdZ'=dVaR.dRdZ*scale.fct,'dZdZ'=dVaR.dZdZ*scale.fct))
  }
  
  #### Define Constraints ####
  
  #Constraint 1: Amt Bought + (Amt Sold)*(Collateral on Amt Sold) <= Amt in Trust Channel
  cnst1.val <- function(params){ #objective
    W <- params$W
    R <- params$R
    Z <- params$Z
    val <- ifelse(W.TF,sum(W[W.optim]),0)+ #Sum all w_ast (as long as optimizing over it)
           ifelse(S.TF,W[S.optim]*(-Z[S.optim]),0)- #Add w_nov*(-)c_nov
           Wlim*W.TF  #Prespecified sum
    return(val)
  }
  cnst1.grd <- function(params){ #gradient
    W <- params$W
    R <- params$R
    Z <- params$Z
    dW.dr <- params$dW.dr
    dW.dz <- params$dW.dz
    
    dW  <- rep(1,length(W.optim)) # dcnst/dw_ast = 1  
    dRs <- ifelse(S.TF,-Z[S.optim]*dW.dr[S.optim],0) # dcnst/dr_nov = (-)c_nov*df_supply/dr_nov  
    dZs <- ifelse(S.TF,W[S.optim]+(-Z[S.optim])*dW.dz[S.optim],0) # dcnst/dc_nov = w_nov+(-)c_nov*df_supply/dc_nov  
    
    return(list('dW'=dW,'dRs'=dRs,'dZs'=dZs))
  }
  
  #Constraint 2: Amt Bought+Amt Novated = Prespecified Value (only used for frwd-prop)
  cnst2.val <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    val <- ifelse(W.TF,sum(W[W.optim]),0)- #Sum all w_ast if optimizing over it
           ifelse(S.TF,W[S.optim],0)-      #add w_nov
           ifelse(C.TF,Clim,0)             #subtract Clim=Prespecified sum
    return(val*C.TF)
  }
  cnst2.grd <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    dW.dr <- params$dW.dr
    dW.dz <- params$dW.dz
    
    dW <- rep(0,length(W.optim))
    dW[c((length(dW)-n.C):length(dW))] <- 1*C.TF
    dRs <- ifelse(S.TF*C.TF,dW.dr[S.optim],0) #0 unless S.TF and C.TF
    dZs <- ifelse(S.TF*C.TF,dW.dz[S.optim],0)
    
    return(list('dW'=dW,'dRs'=dRs,'dZs'=dZs))
  }
  
  #### Piece together above functions into optimizer inputs ####
  
  #For optimizer to fetch gradient and objective in combined list
  obj.val.grd <- function(X){
    
    #update parameters
    params <- opt.update.WRZ(X) 
    
    #calculate objective
    obj <- obj(params)
    
    #calculate gradient
    grad <- rep(0, n.opt)
    
    if(W.TF) {
      grad[W.indx] <- d.obj.dw(params)
    }
    if(R.TF) {
      grad[R.indx] <- d.obj.dr(params)
    }
    if(Z.TF) {
      grad[Z.indx] <- d.obj.dz(params)
    }
    
    return(list('objective'=obj,'gradient'=grad))
  }
  
  #For optimizer to fetch inequality constraint graident and value in combined list
  cnst.ineq.val.grd <- function(X){
    
    #update parameters
    params <- opt.update.WRZ(X) 
    c.val <- cnst1.val(params)
    c.grd <- cnst1.grd(params)
    
    #assemble jacobian
    grad <- matrix(0,nrow=1,ncol=n.opt)
    grad[1,W.indx] <- c.grd$dW
    if(S.TF){
      grad[1,RS.indx] <- c.grd$dRs
      grad[1,ZS.indx] <- c.grd$dZs
    }
    
    return(list('constraints'=c.val,'jacobian'=grad))
  }
  
  #For optimizer to fetch equality constraint graident and value in combined list
  cnst.eq.val.grd <- function(X){
    
    #update parameters
    params <- opt.update.WRZ(X) 
    c.val <- cnst2.val(params)
    c.grd <- cnst2.grd(params)
    
    #assemble jacobian
    grad <- matrix(0,nrow=1,ncol=n.opt)
    grad[1,W.indx] <- c.grd$dW
    if(S.TF){
      grad[1,RS.indx] <- c.grd$dRs
      grad[1,ZS.indx] <- c.grd$dZs
    }
    
    return(list('constraints'=c.val,'jacobian'=grad))
  }
  
  #In advent equality and inequality constraints need be combined
  cnst.cmb.val.grd <- function(X){
    
    #update parameters
    params <- opt.update.WRZ(X) 
    indx <- c(TRUE,Cash.TF,C.TF,Cash.TF,C.TF)
    
    #Inequality Value
    val.1 <- cnst1.val(params)
    #Equality Values
    val.2 <- cnst2.val(params)
    val.3 <- cnst3.val(params)
    #Equality values Reversed (for opposite inequality)
    val.4 <- -val.2
    val.5 <- -val.3
    #assemble
    val <- c(val.1,val.2,val.3,val.4,val.5)
    
    #Inequality Gradient
    grd.1 <- cnst1.grd(params)
    #Equality Gradient
    grd.2 <- cnst2.grd(params)
    grd.3 <- cnst3.grd(params)
    #Gradient values Reversed (for opposite inequality)
    grd.4 <- lapply(grd.2,function(x) -x)
    grd.5 <- lapply(grd.3,function(x) -x)
    
    #assemble jacobian
    grad <- matrix(0,nrow=5,ncol=n.opt)
    
    grad[1,W.indx] <- grd.1$dW
    grad[2,W.indx] <- grd.2$dW
    grad[3,W.indx] <- grd.3$dW
    grad[4,W.indx] <- grd.3$dW
    grad[5,W.indx] <- grd.4$dW
    
    if(S.TF){
      grad[1,RS.indx] <- grd.1$dR
      grad[1,ZS.indx] <- grd.1$dZ
      grad[2,RS.indx] <- grd.2$dR
      grad[2,ZS.indx] <- grd.2$dZ
      grad[3,RS.indx] <- grd.3$dR
      grad[3,ZS.indx] <- grd.3$dZ
      grad[4,RS.indx] <- grd.4$dR
      grad[4,ZS.indx] <- grd.4$dZ
      grad[5,RS.indx] <- grd.5$dR
      grad[5,ZS.indx] <- grd.5$dZ
    }
    
    return(list('constraints'=val[indx],'jacobian'=grad[indx,]))
  }
  
  #### Set initial varibles ####
  
  #create starting values, upper bound, lower bound, and solve for respective indices
  X0.opt <- rep(NA, n.opt)
  LB.opt <- rep(NA, n.opt)
  UB.opt <- rep(NA, n.opt)
  W.indx <- NA
  R.indx <- NA
  Z.indx <- NA
  RS.indx <- NA
  ZS.indx <- NA
  init.val.opt <- function(){
    if(W.TF) {
      W.indx <<- c(1:length(W.optim)) 
      LB.opt[W.indx] <<- round(0.01+S.TF*Wlim*0.15*0,2)
      UB.opt[W.indx] <<- Wlim #na.exclude(c(ifelse(Cash.TF,CashLim,NA),Wlim))
      X0.opt[W.indx] <<- runif(length(W.indx),LB.opt[W.indx],UB.opt[W.indx])
      X0.opt[W.indx][X0.opt[W.indx]<LB.opt[W.indx]] <<- LB.opt[W.indx][X0.opt[W.indx]<LB.opt[W.indx]]*1.01
      X0.opt[W.indx][X0.opt[W.indx]>UB.opt[W.indx]] <<- UB.opt[W.indx][X0.opt[W.indx]>UB.opt[W.indx]]*0.99
    }
    if(R.TF) {
      R.indx <<- c((length(W.optim)+1):(length(W.optim)+length(R.optim))) 
      LB.opt[R.indx] <<- 1
      UB.opt[R.indx] <<- Rlim
      X0.opt[R.indx] <<- runif(length(R.indx),LB.opt[R.indx],UB.opt[R.indx])
      X0.opt[R.indx][X0.opt[R.indx]<LB.opt[R.indx]] <<- LB.opt[R.indx][X0.opt[R.indx]<LB.opt[R.indx]]*1.01
      X0.opt[R.indx][X0.opt[R.indx]>UB.opt[R.indx]] <<- UB.opt[R.indx][X0.opt[R.indx]>UB.opt[R.indx]]*0.99
    }
    if(Z.TF) {
      Z.indx <<- c((length(W.optim)+length(R.optim)+1):(length(W.optim)+length(R.optim)+length(Z.optim)))
      LB.opt[Z.indx] <<- Zlim
      UB.opt[Z.indx] <<- 0.99
      X0.opt[Z.indx] <<- runif(length(Z.indx),LB.opt[Z.indx],UB.opt[Z.indx])
      X0.opt[Z.indx][X0.opt[Z.indx]<LB.opt[Z.indx]] <<- LB.opt[Z.indx][X0.opt[Z.indx]<LB.opt[Z.indx]]*1.01
      X0.opt[Z.indx][X0.opt[Z.indx]>UB.opt[Z.indx]] <<- UB.opt[Z.indx][X0.opt[Z.indx]>UB.opt[Z.indx]]*0.99
    }
    if(S.TF) {
      #for rates
      RS.indx <<- R.indx[R.optim %in% S.optim]
      LB.opt[RS.indx] <<- 0.000001
      UB.opt[RS.indx] <<- R.in[W.optim]-1-0.000001 #[c((1+Cash.TF):length(W.indx))] [c((1+Cash.TF):length(W.indx))]
      X0.opt[RS.indx] <<- runif(length(RS.indx),LB.opt[RS.indx],UB.opt[RS.indx])
      X0.opt[RS.indx][X0.opt[RS.indx]<LB.opt[RS.indx]] <<- LB.opt[RS.indx][X0.opt[RS.indx]<LB.opt[RS.indx]]*1.01
      X0.opt[RS.indx][X0.opt[RS.indx]>UB.opt[RS.indx]] <<- UB.opt[RS.indx][X0.opt[RS.indx]>UB.opt[RS.indx]]*0.99
      
      #for securitication
      ZS.indx <<- Z.indx[Z.optim %in% S.optim]
      LB.opt[ZS.indx] <<- Z.in[W.optim]-(1-0.001) #negative because securitization increases
      UB.opt[ZS.indx] <<- -0.001
      X0.opt[ZS.indx] <<- runif(length(ZS.indx),LB.opt[ZS.indx],UB.opt[ZS.indx])
      X0.opt[ZS.indx][X0.opt[ZS.indx]<LB.opt[ZS.indx]] <<- LB.opt[ZS.indx][X0.opt[ZS.indx]<LB.opt[ZS.indx]]*0.99
      X0.opt[ZS.indx][X0.opt[ZS.indx]>UB.opt[ZS.indx]] <<- UB.opt[ZS.indx][X0.opt[ZS.indx]>UB.opt[ZS.indx]]*1.01
    }
    if(Cash.TF){
      W.in[1] <- CashLim-sum(X0.opt[W.indx]) #[c(2:length(W.indx))]
      #X0.opt[W.indx[1]] <<- CashLim-sum(X0.opt[W.indx[c(2:length(W.indx))]])#pmax(X0.opt[W.indx[1]]*0.9,LB.opt[W.indx[1]])
    }
  }
  
  init.val.opt()
  while(any(X0.opt<LB.opt) | any(X0.opt>X0.opt)) {
    init.val.opt()
  }
  
  #Parse P.in to create Standard Deviation vector [UPDATE THIS PART]
  if(is.matrix(P.in)) {
    Std <- sqrt(P.in[,1]*(1-P.in[,1]))
    Alpha <- P.in[complete.cases(P.in),2]
    Beta <- P.in[complete.cases(P.in),3]
    Std[complete.cases(P.in)] <- sqrt(Alpha*Beta/((Alpha+Beta)^2*(Alpha+Beta+1)))
    P.in <- P.in[,1]
    rm(Alpha, Beta)
  } else {
    Std <- sqrt(P.in*(1-P.in))
  }
  
  #### Pass into Optimizer ####
  
  if(browse){browser()} #invokes trace for debugging
  
  if(algorithm == 'NLOPT_LD_SLSQP') { 
    soln <- nloptr::nloptr(x0=X0.opt, lb=LB.opt, ub=UB.opt,
                           eval_f=obj.val.grd,
                           eval_g_ineq=cnst.ineq.val.grd, 
                           eval_g_eq=switch(C.TF+1,NULL,cnst.eq.val.grd), #equality only needed if C.TF True
                           opts = c(list(algorithm = 'NLOPT_LD_SLSQP',
                                         xtol_abs=c(rep(0.001,length(W.optim)),rep(0.0001,length(R.optim)+length(Z.optim)))),
                                    controls))
  }
  if(algorithm == 'NLOPT_LD_AUGLAG') { 
    soln <- nloptr::nloptr(x0=X0.opt, lb=LB.opt, ub=UB.opt,
                           eval_f=obj.val.grd,
                           eval_g_eq=switch(C.TF+1,NULL,cnst.eq.val.grd), 
                           eval_g_ineq=cnst.ineq.val.grd,
                           opts = list(algorithm = 'NLOPT_LD_AUGLAG',
                                       local_opts=list(localsolver = 'NLOPT_LD_LBFGS',
                                                       xtol_abs=c(rep(0.01,length(W.optim)),rep(0.001,length(R.optim)+length(Z.optim))))
                                       ))
    
    soln <- nloptr::auglag(x0=X0.opt, lower=LB.opt, upper=UB.opt,
                           fn=obj.val, gr=obj.grd,
                           heq=cnst.eq.val, heqjac=cnst.eq.grd,
                           hin=function(x){-cnst.ineq.val(x)}, hinjac=function(x){-cnst.ineq.grd(x)},
                           localsolver = 'LBFGS')
  }
  if(algorithm == 'NLOPT_LD_CCSAQ') { 
    
    soln <- nloptr::nloptr(x0=X0.opt, lb=LB.opt, ub=UB.opt,
                           eval_f=obj.val.grd, #eval_grad_f=obj.grd,
                           #eval_g_eq=cnst.eq.val.grd, #eval_jac_g_eq=cnst.eq.grd,
                           eval_g_ineq=cnst.cmb.val.grd, #eval_jac_g_ineq=cnst.ineq.grd,
                           opts = c(list(algorithm = 'NLOPT_LD_CCSAQ',
                                         xtol_abs=c(rep(0.001,length(W.optim)),rep(0.0001,length(R.optim)+length(Z.optim)))),
                                    controls))
  }
  
  return (list(W = soln$solution[W.indx], #[c((1+Cash.TF):length(W.indx))] 
               R = soln$solution[R.indx],
               Z = soln$solution[Z.indx],
               S = ifelse(S.TF,S.intrp(soln$solution[RS.indx], soln$solution[ZS.indx]),NA)))
}

#### unnecessary code ####

# #Constraint 3: Amt Bought + (Amt Sold)*(Collateral on Amt Sold) + Cash New = Cash Old (not used)
# cnst3.val <- function(params){
#   W <- params$W
#   R <- params$R
#   Z <- params$Z
#   return((sum(W[W.optim])+ifelse(S.TF,W[S.optim]*(-Z[S.optim]),0)-CashLim)*Cash.TF)
# }
# cnst3.grd <- function(params){
#   W <- params$W
#   R <- params$R
#   Z <- params$Z
#   
#   dW <- rep(1,length(W.optim))*Cash.TF
#   dR <- ifelse(S.TF*Cash.TF,-Z[S.optim]*S.dR.intrp(R[S.optim],Z[S.optim]),NA)
#   dZ <- ifelse(S.TF*Cash.TF,-(W[S.optim]+Z[S.optim]*S.dZ.intrp(R[S.optim],Z[S.optim])),NA)
#   
#   return(list('dW'=dW,'dR'=dR,'dZ'=dZ))
# }
# #For optimizer to fetch optimization objective
# obj.val <- function(X){
#   #update parameters
#   params <- opt.update.WRZ (X) 
#   
#   return(-f.prft(params)+g.VaR(params))
# }
# 
# #For optimizer to fetch gradient of objective function
# obj.grd <- function(X){
#   
#   #update parameters
#   params <- opt.update.WRZ (X) 
#   
#   #calculate gradient
#   grad <- rep(0, n.opt)
#   
#   if(W.TF) {
#     grad[W.indx] <- -f.prft.dW(params)+g.VaR.dW(params)
#   }
#   if(R.TF) {
#     grad[R.indx] <- -f.prft.dR(params)+g.VaR.dR(params)
#   }
#   if(Z.TF) {
#     grad[Z.indx] <- -f.prft.dZ(params)+g.VaR.dZ(params)
#   }
#   return(grad)
# }
# 
# #For optimizer to fetch inequality constraints
# cnst.ineq.val <- function(X){
#   #update parameters
#   params <- opt.update.WRZ(X)
#   return(cnst1.val(params))
# }
# 
# #For optimizer to fetch gradient of inequality constraints
# cnst.ineq.grd <- function(X){
#   
#   #update parameters
#   params <- opt.update.WRZ(X) 
#   c.grd <- cnst1.grd(params)
#   
#   #assemble jacobian
#   grad <- matrix(0,nrow=1,ncol=n.opt)
#   grad[1,W.indx] <- c.grd$dW
#   if(S.TF){
#     grad[1,RS.indx] <- c.grd$dR
#     grad[1,ZS.indx] <- c.grd$dZ
#   }
#   return(grad)
# }
# 
# #For optimizer to fetch equality constraints
# cnst.eq.val <- function(X){
#   #update parameters
#   params <- opt.update.WRZ(X)
#   val <- c(cnst2.val(params),cnst3.val(params))
#   val <- val[c(Cash.TF,C.TF)]
#   return(val)
# }
# 
# #For optimizer to fetch gradient of equality constraints
# cnst.eq.grd <- function(X){
#   #update parameters
#   params <- opt.update.WRZ(X)
#   c2.grd <- cnst2.grd(params)
#   c3.grd <- cnst3.grd(params)
#   
#   #assemble jacobian
#   grad <- matrix(0,nrow=2,ncol=n.opt)
#   
#   grad[1,W.indx]  <- c2.grd$dW
#   grad[2,W.indx]  <- c3.grd$dW
#   if(S.TF){
#     grad[1,RS.indx] <- c2.grd$dR
#     grad[1,ZS.indx] <- c2.grd$dZ
#     grad[2,RS.indx] <- c3.grd$dR
#     grad[2,ZS.indx] <- c3.grd$dZ
#   }
#   return(grad[c(Cash.TF,C.TF),])
# }
# cnst.eq.val.grd <- function(X){
#   
#   val <- c(cnst2.val(params),cnst3.val(params))
#   val <- val[c(Cash.TF,C.TF)]
#   
#   c2.grd <- cnst2.grd(params)
#   c3.grd <- cnst3.grd(params)
#   
#   #assemble jacobian
#   grad <- matrix(0,nrow=2,ncol=n.opt)
#   
#   grad[1,W.indx]  <- c2.grd$dW
#   grad[2,W.indx]  <- c3.grd$dW
#   if(S.TF){
#     grad[1,RS.indx] <- c2.grd$dR
#     grad[1,ZS.indx] <- c2.grd$dZ
#     grad[2,RS.indx] <- c3.grd$dR
#     grad[2,ZS.indx] <- c3.grd$dZ
#   }
#   
#   return(list('constraints'=val,'jacobian'=grad[c(Cash.TF,C.TF),]))
# }


optim.Kumar.old <- function(corr.mtx, P.in,
                        W.in = NA, R.in = NA, Z.in = NA,
                        Wlim = 0, Rlim = 3, Zlim = 0.01,
                        k.alpha = 0.05, z.alpha = 0.05,
                        penalty.RZ = 0, elastic.RZ = 0.5,Clim=NA,
                        algorithm = "NLOPT_LN_COBYLA", controls = list(),
                        S.FN = c(), relax = FALSE, browse = FALSE) {
  
  #Determine which missing values to optimize
  W.optim <- c()
  R.optim <- c()
  Z.optim <- c()
  W.indx <- integer(0)
  R.indx <- integer(0)
  Z.indx <- integer(0)
  W.TF <- FALSE
  R.TF <- FALSE
  Z.TF <- FALSE
  K.TF <- TRUE
  S.TF <- FALSE
  C.TF <- FALSE
  n.S <- 0
  n.C <- 0
  
  if(all(!is.na(Clim))){
    C.TF <- TRUE
    n.C <- length(Clim)
  }
  
  #S.FN if present is a list of functions yielding supply curve (denoted by the last elements of argument vectors)
  if(length(S.FN)>0 & is.list(S.FN)) {
    S.TF <- TRUE
    S.optim <- c((nrow(corr.mtx)+1-length(S.FN)):nrow(corr.mtx))
    W.in[S.optim] <- 0.01
    n.S <- length(S.optim)
  } else {
    S.optim <- integer(0)
  }
  
  if(any(is.na(W.in))) {
    if(length(W.in) == 1) {
      W.optim <- c(1:nrow(corr.mtx))
      W.in <- rep(NA, nrow(corr.mtx))
    } else {
      W.optim <- which(is.na(W.in))
    }
    W.TF <- TRUE
  }
  
  if(any(is.na(R.in))) {
    if(length(R.in) == 1) {
      R.optim <- c(1:nrow(corr.mtx))
      R.in <- rep(NA, nrow(corr.mtx))
    } else {
      R.optim <- which(is.na(R.in))
    }
    R.TF <- TRUE
  }
  
  if(any(is.na(Z.in))) {
    if(length(Z.in) == 1) {
      Z.optim <- c(1:nrow(corr.mtx))
      Z.in <- rep(NA, nrow(corr.mtx))
    } else {
      Z.optim <- which(is.na(Z.in))
    }
    Z.TF <- TRUE
  }
  
  if(relax) {
    K.TF <- FALSE
  }
  
  #create starting values, upper bound, lower bound, and solve for respective indices
  n.opt <- length(W.optim)+length(R.optim)+length(Z.optim)+2*K.TF
  X0.opt <- rep(NA, n.opt)
  LB.opt <- rep(NA, n.opt)
  UB.opt <- rep(NA, n.opt)
  if(W.TF) {
    W.indx <- c(1:length(W.optim))
    LB.opt[W.indx] <- round(0.01+S.TF*Wlim*0.15,2)
    UB.opt[W.indx] <- Wlim
    X0.opt[W.indx] <- UB.opt[W.indx]/2*rnorm(length(W.indx),1)+runif(length(W.indx),-.5,.5)
    X0.opt[W.indx][X0.opt[W.indx]<LB.opt[W.indx]] <- LB.opt[W.indx]
    X0.opt[W.indx][X0.opt[W.indx]>UB.opt[W.indx]] <- UB.opt[W.indx]
  }
  if(R.TF) {
    R.indx <- c((length(W.optim)+1):(length(W.optim)+length(R.optim)))
    LB.opt[R.indx] <- 1
    UB.opt[R.indx] <- Rlim
    X0.opt[R.indx] <- LB.opt[R.indx]+(UB.opt[R.indx]-LB.opt[R.indx])/2+runif(length(R.indx),-.5,.5)
    X0.opt[R.indx][X0.opt[R.indx]<LB.opt[R.indx]] <- LB.opt[R.indx]
    X0.opt[R.indx][X0.opt[R.indx]>UB.opt[R.indx]] <- UB.opt[R.indx]
  }
  if(Z.TF) {
    Z.indx <- c((length(W.optim)+length(R.optim)+1):(length(W.optim)+length(R.optim)+length(Z.optim)))
    LB.opt[Z.indx] <- Zlim
    UB.opt[Z.indx] <- 0.99
    X0.opt[Z.indx] <- LB.opt[Z.indx]+(UB.opt[Z.indx]-LB.opt[Z.indx])/2+runif(length(Z.indx),-.5,.5)
    X0.opt[Z.indx][X0.opt[Z.indx]<LB.opt[Z.indx]] <- LB.opt[Z.indx]
    X0.opt[Z.indx][X0.opt[Z.indx]>UB.opt[Z.indx]] <- UB.opt[Z.indx]
  }
  if(K.TF) {
    X0.opt[c(n.opt-1, n.opt)] <- c(2.5+runif(1,0,5),2.5+runif(1,0,5))
    LB.opt[c(n.opt-1, n.opt)] <- c(0.01,0.01)
    UB.opt[c(n.opt-1, n.opt)] <- c(1000,1000)
    K.indx <- c((length(W.indx)+length(R.indx)+length(Z.indx)+1):(length(W.indx)+length(R.indx)+length(Z.indx)+2))
  }
  if(S.TF) {
    #for rates
    RS.indx <- R.indx[R.optim %in% S.optim]
    LB.opt[RS.indx] <- 0.000001
    UB.opt[RS.indx] <- R.in[W.optim]-1-0.000001
    X0.opt[RS.indx] <- LB.opt[RS.indx]+(UB.opt[RS.indx]-LB.opt[RS.indx])/2+runif(length(RS.indx),-0.05,0.05)
    X0.opt[RS.indx][X0.opt[RS.indx]<LB.opt[RS.indx]] <- LB.opt[RS.indx]
    X0.opt[RS.indx][X0.opt[RS.indx]>UB.opt[RS.indx]] <- UB.opt[RS.indx]
    
    #for securitication
    ZS.indx <- Z.indx[Z.optim %in% S.optim]
    LB.opt[ZS.indx] <- Z.in[W.optim]-(1-0.001) #negative because securitization increases
    UB.opt[ZS.indx] <- -0.001
    X0.opt[ZS.indx] <- LB.opt[ZS.indx]+(UB.opt[ZS.indx]+LB.opt[ZS.indx])/2+runif(length(ZS.indx),-0.05,0.05)
    X0.opt[ZS.indx][X0.opt[ZS.indx]<LB.opt[ZS.indx]] <- LB.opt[ZS.indx]
    X0.opt[ZS.indx][X0.opt[ZS.indx]>UB.opt[ZS.indx]] <- UB.opt[ZS.indx]
  }
  
  #Parse P.in to create Standard Deviation vector
  if(is.matrix(P.in)) {
    Std <- sqrt(P.in[,1]*(1-P.in[,1]))
    Alpha <- P.in[complete.cases(P.in),2]
    Beta <- P.in[complete.cases(P.in),3]
    Std[complete.cases(P.in)] <- sqrt(Alpha*Beta/((Alpha+Beta)^2*(Alpha+Beta+1)))
    P.in <- P.in[,1]
    rm(Alpha, Beta)
  } else {
    Std <- sqrt(P.in*(1-P.in))
  }
  
  #to reinitialize inputs (in case needed for random restarts)
  inpt.init <- function() {
    
    X0.opt <- rep(NA, n.opt)
    
    if(W.TF) {
      X0.opt[W.indx] <- UB.opt[W.indx]/2*rnorm(length(W.indx),1)+runif(length(W.indx),-.5,.5)
      X0.opt[W.indx][X0.opt[W.indx]<LB.opt[W.indx]] <- LB.opt[W.indx]
      X0.opt[W.indx][X0.opt[W.indx]>UB.opt[W.indx]] <- UB.opt[W.indx]
    }
    if(R.TF) {
      X0.opt[R.indx] <- LB.opt[R.indx]+(UB.opt[R.indx]-LB.opt[R.indx])/2+runif(length(R.indx),-.5,.5)
      X0.opt[R.indx][X0.opt[R.indx]<LB.opt[R.indx]] <- LB.opt[R.indx]
      X0.opt[R.indx][X0.opt[R.indx]>UB.opt[R.indx]] <- UB.opt[R.indx]
    }
    if(Z.TF) {
      X0.opt[Z.indx] <- LB.opt[Z.indx]+(UB.opt[Z.indx]-LB.opt[Z.indx])/2+runif(length(Z.indx),-.5,.5)
      X0.opt[Z.indx][X0.opt[Z.indx]<LB.opt[Z.indx]] <- LB.opt[Z.indx]
      X0.opt[Z.indx][X0.opt[Z.indx]>UB.opt[Z.indx]] <- UB.opt[Z.indx]
    }
    if(K.TF) {
      X0.opt[c(n.opt-1, n.opt)] <- c(2.5+runif(1,0,5),2.5+runif(1,0,5))
    }
    if(S.TF) {
      #for rates
      X0.opt[RS.indx] <- LB.opt[RS.indx]+(UB.opt[RS.indx]-LB.opt[RS.indx])/2+runif(length(RS.indx),-0.05,0.05)
      X0.opt[RS.indx][X0.opt[RS.indx]<LB.opt[RS.indx]] <- LB.opt[RS.indx]
      X0.opt[RS.indx][X0.opt[RS.indx]>UB.opt[RS.indx]] <- UB.opt[RS.indx]
      
      #for securitication
      X0.opt[ZS.indx] <- LB.opt[ZS.indx]+(UB.opt[ZS.indx]+LB.opt[ZS.indx])/2+runif(length(ZS.indx),-0.05,0.05)
      X0.opt[ZS.indx][X0.opt[ZS.indx]<LB.opt[ZS.indx]] <- LB.opt[ZS.indx]
      X0.opt[ZS.indx][X0.opt[ZS.indx]>UB.opt[ZS.indx]] <- UB.opt[ZS.indx]
    }
    return (X0.opt)
  }
  
  #Parse S.FN to create necessary functions to return amount sold given R and Z
  if(S.TF) {
    
    RZ.S.calc <- function(R, Z) {
      Rc <- R.in[W.optim]
      Zc <- Z.in[W.optim]
      
      if(is.atomic(R)) {
        return (list(Rs = Rc-R, Zs = Zc-Z))
      }
      
      m <- length(Rc)
      if(!is.matrix(R) & !is.matrix(Z)) {
        if(length(R) == m & length(Z) == m) {
          Rs <- Rc-R
          Zs <- Zc-Z
        }} else if(ncol(R) == m & ncol(Z) == m) {
          Rs <- t(as.matrix(Rc, m,1)%*%matrix(1, nrow = 1, ncol = nrow(R)))-R
          Zs <- t(as.matrix(Zc, m,1)%*%matrix(1, nrow = 1, ncol = nrow(Z)))-Z
        }
      return (list(Rs = Rs, Zs = Zs))
    }
    
    #interpolate supply at a given point
    S.intrp <- function(R, Z, inpt.adj = TRUE) {
      
      #function to interpolate set
      S.intrp.set <- function(mdls, R, Z) {
        S <- rep(0, length(R))
        for(i in c(1:length(mdls))) {
          S <- S+predict(mdls[[i]], cbind(R = R, Z = Z))
        }
        return (S)
      }

      #If inpt.adj
      if(inpt.adj) {
        RZ <- RZ.S.calc(R, Z)
        R <- RZ$R
        Z <- RZ$Z
      }
      #simple case
      m <- length(S.FN)
      if(m == 1) {
        if(class(S.FN[[1]])=="loess"){
          S <- S.intrp.set(S.FN[1], R, Z)
        } else {
          S <- S.intrp.set(S.FN[[1]], R, Z)
        }
        return (S)
      }
      
      if(!is.matrix(R) & !is.matrix(Z)) {
        if(length(R) == m & length(Z) == m) {
          R <- t(as.matrix(R))
          Z <- t(as.matrix(Z))
        } else {
          R <- matrix(rep(R, m), ncol = m)
          Z <- matrix(rep(Z, m), ncol = m)
        }
      }
      
      S <- matrix(nrow = nrow(R), ncol = m)
      
      for(j in c(1:m)) {
        S[, j] <- S.intrp.set(S.FN[j], R[, j], Z[, j])
      }
      return (S)
    }
    
    #Interpolate derivative w.r.t R
    S.dR.intrp <- function(R, Z, delta = 0.0005, inpt.adj = TRUE) {
      S.pre <- S.intrp(R-delta, Z, inpt.adj = inpt.adj)
      S.0   <- S.intrp(R, Z, inpt.adj = inpt.adj)
      S.pst <- S.intrp(R+delta, Z, inpt.adj = inpt.adj)
      
      Sdiff.pre <- (S.0-S.pre)/delta
      Sdiff.pst <- (S.pst-S.0)/delta
      
      return ((Sdiff.pre+Sdiff.pst)/2)
    }
    #interpolate derivative w.r.t Z
    S.dZ.intrp <- function(R, Z, delta = 0.0005, inpt.adj = TRUE) {
      S.pre <- S.intrp(R, Z-delta, inpt.adj = inpt.adj)
      S.0   <- S.intrp(R, Z, inpt.adj = inpt.adj)
      S.pst <- S.intrp(R, Z+delta, inpt.adj = inpt.adj)
      
      Sdiff.pre <- (S.0-S.pre)/delta
      Sdiff.pst <- (S.pst-S.0)/delta
      
      return ((Sdiff.pre+Sdiff.pst)/2)
    }
  }
  
  #Parse X.opt, update W.in, R.in, Z.in
  opt.update.WRZ <- function (X)  {
    if(W.TF) {
      W.in[W.optim] <- X[W.indx]
    }
    if(R.TF) {
      R.in[R.optim] <- X[R.indx]
    }
    if(Z.TF) {
      Z.in[Z.optim] <- X[Z.indx]
    }
    if(S.TF) {
      W.in[S.optim] <- S.intrp(X[RS.indx], X[ZS.indx])
    }
    if(K.TF) {
      a.Kum <- X[K.indx[1]]
      b.Kum <- X[K.indx[2]]
      return (list(W = W.in, R = R.in, Z = Z.in, a = a.Kum, b = b.Kum))
    } else {
      return (list(W = W.in, R = R.in, Z = Z.in)) 
    }
  }
  
  #Moment generating function for Kumaraswamy distribution
  kum.MomGen <- function(a, b, m) {
    log.num <- log(b) + lgamma(1 + m/a) + lgamma(b)
    log.den <- lgamma(1 + b + m/a)
    return (exp(log.num-log.den))
  }
  
  #expected profit objective function
  prft.obj <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate lender profit
    profit <- sum(W*(P.in*(R-Z)+Z))
    
    #calculate penalty given cobb-douglas utility function for borrowers
    if(penalty.RZ>0) {
      penalty <- penalty.RZ*sum(W*R^(elastic.RZ)*Z^(1-elastic.RZ))
    } else {
      penalty <-0
    }
    return (-(profit-penalty))
  }
  
  #derivative of profit w.r.t W
  prft.obj.dW <- function(params) {
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprofit.dW <- P.in*(R-Z)+Z
    
    #calculate derivative of penalty
    if(penalty.RZ>0) {
      dpenalty.dW <- penalty.RZ*(R^(elastic.RZ)*Z^(1-elastic.RZ))
    } else {
      dpenalty.dW <-0
    }
    return (-(dprofit.dW-dpenalty.dW)[W.optim])
  }
  
  #derivative of profit w.r.t R
  prft.obj.dR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprofit.dR <- W*P.in
    
    #calculate derivative of penalty
    if(penalty.RZ>0) {
      dpenalty.dR <- penalty.RZ*(elastic.RZ*W*R^(elastic.RZ-1)*Z^(1-elastic.RZ))
    } else {
      dpenalty.dR <-0
    }
    return (-(dprofit.dR-dpenalty.dR)[R.optim])
  }
  
  #derivative of profit w.r.t Z
  prft.obj.dZ <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprofit.dZ <- W*(1-P.in)
    
    #calculate derivative of penalty
    if(penalty.RZ>0) {
      dpenalty.dZ <- penalty.RZ*((1-elastic.RZ)*W*R^(elastic.RZ)*Z^(-elastic.RZ))
    } else {
      dpenalty.dZ <-0
    }
    return (-(dprofit.dZ-dpenalty.dZ)[Z.optim])
  }
  
  #Constraint 1: 1st moment of distribution = expected normalized profit (expected profit/max.possible.profit)
  kumMoM.1.cnst <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    a <- params$a
    b <- params$b
    
    #expected profit normalized against maximum possible profit
    muHat.norm <- sum(W*(P.in*(R-Z)+Z))/sum(W*R)
    return (kum.MomGen(a, b,1)-muHat.norm)
  }
  
  #Derivative of 1st Moment Constraint w.r.t W
  kumMoM.1.cnst.dW <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #derivative of normalized expectation
    prf.vec <- (P.in*(R-Z)+Z) #profit per unit
    prf.max <- sum(W*R) #max profit
    dg1.dW <- prf.vec/prf.max - (R%*%(t(W)%*%prf.vec))/prf.max^2 
    return (-dg1.dW[W.optim])
  }
  
  #Derivative of 1st Moment Constraint w.r.t R
  kumMoM.1.cnst.dR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #derivative of normalized expectation
    prf.vec <- (P.in*(R-Z)+Z) #profit per unit
    prf.max <- sum(W*R) #max profit
    dg1.dR <- W*P.in/prf.max - (W%*%(t(W)%*%prf.vec))/prf.max^2
    return (-dg1.dR[R.optim])
  }
  #Derivative of 1st Moment Constraint w.r.t Z
  kumMoM.1.cnst.dZ <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #derivative of normalized expectation
    prf.max <- sum(W*R) #max profit
    dg1.dZ <-(W*(1-P.in))/prf.max
    return (-dg1.dZ[Z.optim])
  }
  
  #Derivative of 1st Moment Constraint w.r.t a
  kumMoM.1.cnst.da <- function(params) {
    a <- params$a
    b <- params$b
    
    #derivatives of kumaraswamy moment generating function
    beta.kum <- beta(1+1/a, b)
    digamma.kum <- digamma(1+1/a)-digamma(1+1/a+b)
    dg1.da <- -b*(beta.kum*digamma.kum/a^2)
    return (dg1.da)
  }
  
  #Derivative of 1st Moment Constraint w.r.t b
  kumMoM.1.cnst.db <- function(params) {
    a <- params$a
    b <- params$b
    
    #derivatives of kumaraswamy moment generating function
    beta.kum <- beta(1+1/a, b)
    digamma.kum <- digamma(b)-digamma(1+1/a+b)
    dg1.db <- beta.kum*(1+b*digamma.kum)
    return (dg1.db)
  }
  
  #Constraint 2: 2nd moment of distribution = variance of normalized profit
  kumMoM.2.cnst <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    a <- params$a
    b <- params$b
    
    #vector of standard deviations
    sigma.vec <- Std*W/sum(W)*(R-Z)
    varHat.norm <- t(sigma.vec)%*%corr.mtx%*%sigma.vec
    return (kum.MomGen(a, b,2)-varHat.norm)
  }
  
  #Derivative of 2nd Moment Constraint w.r.t W
  kumMoM.2.cnst.dW <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #vector of standard deviations
    Tot <- sum(W)
    Y   <- Std*(R-Z)
    dg2.dW <- 2/Tot^2*((corr.mtx%*%(Y*W))*Y-1/Tot*matrix(1, nrow(corr.mtx),1)%*%(t(Y*W)%*%corr.mtx%*%(Y*W)))
    return (-dg2.dW[W.optim])
  }
  
  #Derivative of 2nd Moment Constraint w.r.t R
  kumMoM.2.cnst.dR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    #vector of normalized weights
    W.norm <- W/sum(W)
    sigma.P <- Std
    dg2.dR <- 2*(corr.mtx%*%(sigma.P*(R-Z)*W.norm))*sigma.P*W.norm
    return (-dg2.dR[R.optim])
  }
  
  #Derivative of 2nd Moment Constraint w.r.t Z
  kumMoM.2.cnst.dZ <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #vector of normalized weights
    W.norm <- W/sum(W)
    sigma.P <- Std
    dg2.dZ <- -2*(corr.mtx%*%(sigma.P*(R-Z)*W.norm))*sigma.P*W.norm
    return (-dg2.dZ[Z.optim])
  }
  
  #Derivative of 2nd Moment Constraint w.r.t a
  kumMoM.2.cnst.da <- function(params) {
    a <- params$a
    b <- params$b
    #derivatives of kumaraswamy moment generating function
    beta.1.kum <- beta(1+1/a, b)
    beta.2.kum <- beta(1+2/a, b)
    digamma.1.kum <- digamma(1+1/a)-digamma(1+1/a+b)
    digamma.2.kum <- digamma(1+2/a)-digamma(1+2/a+b)
    
    dm2.da <- -2*b*(beta.2.kum*digamma.2.kum/a^2)
    dm1sq.da <- -2*b^2*beta.1.kum^2*digamma.1.kum/a^2
    return (dm2.da)
  }
  
  #Derivative of 2nd Moment Constraint w.r.t b
  kumMoM.2.cnst.db <- function(params) {
    a <- params$a
    b <- params$b
    
    #derivatives of kumaraswamy moment generating function
    beta.1.kum <- beta(1+1/a, b)
    beta.2.kum <- beta(1+2/a, b)
    digamma.1.kum <- digamma(b)-digamma(1+1/a+b)
    digamma.2.kum <- digamma(b)-digamma(1+2/a+b)
    
    dm2.db <- beta.2.kum*(1+b*digamma.2.kum)
    dm1sq.db <- 2*b*beta.1.kum^2*(1+b*digamma.1.kum)
    return (dm2.db)
  }
  
  #Constraint 3: Tail of normalized profit distribution <= k.alpha
  kumTail.cnst <- function(params) {
    W <- params$W
    R <- params$R
    a <- params$a
    b <- params$b
    
    #define k.alpha % probability that losss is >= z.alpha*ValueAtRisk
    tail.losslim <- sum(W)/sum(W*R)*(1-z.alpha)
    tail.invcdf <- (1-(1-k.alpha)^(1/b))^(1/a) 
    return (tail.losslim-tail.invcdf)
  }
  
  #Derivative of Tail Constraint w.r.t W
  kumTail.cnst.dW <- function(params) {
    W <- params$W
    R <- params$R
    
    #weighted average return
    R.avg <- t(W)%*%R
    dg3.dW <- (1/(R.avg)-sum(W)*R/(R.avg)^2)*(1-z.alpha)
    return (dg3.dW[W.optim])
  }
  
  #Derivative of Tail Constraint w.r.t R
  kumTail.cnst.dR <- function(params) {
    W <- params$W
    R <- params$R
    
    #weighted average return
    R.avg <- t(W)%*%R
    dg3.dR <- (-sum(W)*W/(R.avg)^2)*(1-z.alpha)
    return (dg3.dR[R.optim])
  }
  
  #Derivative of Tail Constraint w.r.t a
  kumTail.cnst.da <- function(params) {
    a <- params$a
    b <- params$b
    #derivatives of kumaraswamy inverse CDF
    dg3.da <- -((1-(1-k.alpha)^(1/b))^(1/a)*log(1-(1-k.alpha)^(1/b)))/a^2
    return (-dg3.da)
  }
  #Derivative of Tail Constraint w.r.t b
  kumTail.cnst.db <- function(params) {
    a <- params$a
    b <- params$b
    
    #derivatives of kumaraswamy inverse CDF
    dg3.db <- ((1-k.alpha)^(1/b)*log(1-k.alpha)*(1-(1-k.alpha)^(1/b))^(1/a-1))/(a*b^2)
    return (-dg3.db)
  }
  
  #expected profit 
  f.prft <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate lender profit
    prft <- t(W)%*%(P.in*(R-Z)+Z)
    
    #calculate penalty given cobb-douglas utility function for borrowers <-- This is an extra case and does not matter right now
    if(penalty.RZ>0) {
      penalty <- penalty.RZ*sum(W*R^(elastic.RZ)*Z^(1-elastic.RZ))
    } else {
      penalty <-0
    }
    return (-(prft-penalty))
  }
  
  #derivative of profit w.r.t W
  f.prft.dW <- function(params) {
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprft.dW <- P.in*(R-Z)+Z
    
    #calculate derivative of penalty <-- This is an extra case and does not matter right now
    if(penalty.RZ>0) {
      dpenalty.dW <- penalty.RZ*(R^(elastic.RZ)*Z^(1-elastic.RZ))
    } else {
      dpenalty.dW <-0
    }
    return ((dprft.dW-dpenalty.dW)[W.optim])
  }
  
  #derivative of profit w.r.t R
  f.prft.dR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprft.dR <- W*P.in
    
    #calculate derivative of penalty <-- This is an extra case and does not matter right now
    if(penalty.RZ>0) {
      dpenalty.dR <- penalty.RZ*(elastic.RZ*W*R^(elastic.RZ-1)*Z^(1-elastic.RZ))
    } else {
      dpenalty.dR <-0
    }
    return ((dprft.dR-dpenalty.dR)[R.optim])
  }
  
  #derivative of profit w.r.t Z
  f.prft.dZ <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprft.dZ <- W*(1-P.in)
    
    #calculate derivative of penalty
    if(penalty.RZ>0) {
      dpenalty.dZ <- penalty.RZ*((1-elastic.RZ)*W*R^(elastic.RZ)*Z^(-elastic.RZ))
    } else {
      dpenalty.dZ <-0
    }
    return ((dprft.dZ-dpenalty.dZ)[Z.optim])
  }
  
  #expected VaR
  g.VaR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate scalaing factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    
    return (scale.fct*sqrt(Var))
  }
  
  #derivative of VaR w.r.t W
  g.VaR.dW <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate scalaing factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    dVar.dW <- 2*(corr.mtx%*%(W*(R-Z)*Std))*Std*(R-Z)
    
    return(scale.fct/(2*sqrt(Var[1,1]))*dVar.dW[W.optim])
  }
  
  #derivative of VaR w.r.t R
  g.VaR.dR <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate scalaing factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    dVar.dR <- 2*(corr.mtx%*%(W*(R-Z)*Std))*Std*W
    
    return(scale.fct/(2*sqrt(Var[1,1]))*dVar.dR[R.optim])
  }
  
  #derivative of VaR w.r.t Z
  g.VaR.dZ <- function(params) {
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate scalaing factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    dVar.dZ <- -2*(corr.mtx%*%(W*(R-Z)*Std))*Std*W
    
    return(scale.fct/(2*sqrt(Var[1,1]))*dVar.dZ[Z.optim])
  }
  
  #gradient of profit (not used)
  f.prft.grd <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate derivative of lender profit
    dprft.dW <- P.in*(R-Z)+Z
    dprft.dR <- W*P.in
    dprft.dZ <- W*(1-P.in)
    
    #return list
    return(list('dW'=dprft.dW[W.optim],'dR'=dprft.dR[R.optim],'dZ'=dprft.dZ[Z.optim]))
  }
  
  #gradient of VaR (not used)
  g.VaR.grd <- function(params){
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #calculate scaling factor and variance
    scale.fct <- sqrt((1-eps)/eps)
    Var <- t(W*(R-Z)*Std)%*%corr.mtx%*%(W*(R-Z)*Std)
    
    #calculate derivatives of Var
    dVar.dW <- 2*(corr.mtx%*%(W*(R-Z)*Std))*Std*(R-Z)
    dVar.dR <- 2*(corr.mtx%*%(W*(R-Z)*Std))*Std*W
    dVar.dZ <- -2*(corr.mtx%*%(W*(R-Z)*Std))*Std*W
    
    #Input to get derivatives of VaR
    dVaR.dW <- scale.fct/(2*sqrt(Var[1,1]))*dVar.dW
    dVaR.dR <- scale.fct/(2*sqrt(Var[1,1]))*dVar.dR
    dVaR.dZ <- scale.fct/(2*sqrt(Var[1,1]))*dVar.dZ
    
    #return list
    return(list('dW'=dVaR.dW[W.optim],'dR'=dVaR.dR[R.optim],'dZ'=dVaR.dZ[Z.optim]))
  }
  
  #Function to return gradient for objective function
  obj.grad.eval <- function (X)  {
    
    #update parameters
    params <- opt.update.WRZ (X) 
    
    #calculate gradient
    grad <- rep(0, n.opt)
    if(W.TF) {
      grad[W.indx] <- prft.obj.dW(params)
    }
    if(R.TF) {
      grad[R.indx] <- prft.obj.dR(params)
    }
    if(Z.TF) {
      grad[Z.indx] <- prft.obj.dZ(params)
    }
    return (list('objective' = prft.obj(params),
                 'gradient' = grad))
  }
  
  #Function to return Jacobian for equality constraints
  eql.cnst.eval <- function (X)  {
    
    #update parameters
    params <- opt.update.WRZ (X) 
    #calculate jacobian
    jcb.mtx <- matrix(0, nrow = 2, ncol = n.opt)
    
    #for optimization params
    if(W.TF) {
      jcb.mtx[1, W.indx] <- kumMoM.1.cnst.dW(params)
      jcb.mtx[2, W.indx] <- kumMoM.2.cnst.dW(params)
    }
    if(R.TF) {
      jcb.mtx[1, R.indx] <- kumMoM.1.cnst.dR(params)
      jcb.mtx[2, R.indx] <- kumMoM.2.cnst.dR(params)
    }
    if(Z.TF) {
      jcb.mtx[1, Z.indx] <- kumMoM.1.cnst.dZ(params)
      jcb.mtx[2, Z.indx] <- kumMoM.2.cnst.dZ(params)
    }
    
    #for distribution params
    jcb.mtx[1,(n.opt-1)] <- kumMoM.1.cnst.da(params)
    jcb.mtx[2,(n.opt-1)] <- kumMoM.2.cnst.da(params)
    jcb.mtx[1, n.opt] <- kumMoM.1.cnst.db(params)
    jcb.mtx[2, n.opt] <- kumMoM.2.cnst.db(params)
    
    #For constraints
    return (list('constraints' = c(kumMoM.1.cnst(params), kumMoM.2.cnst(params)),
                 'jacobian' = jcb.mtx))
  }
  #Function to return Jacobian for inequality constraint
  ineq.cnst.eval <- function (X)  {
    
    #update parameters
    params <- opt.update.WRZ (X) 
    
    #calculate jacobian
    jcb.mtx <- matrix(0, nrow = 1, ncol = n.opt)
    
    #for optimization params
    if(W.TF) {
      jcb.mtx[1, W.indx] <- kumTail.cnst.dW(params)
    }
    if(R.TF) {
      jcb.mtx[1, R.indx] <- kumTail.cnst.dR(params)
    }
    
    #for distribution params
    jcb.mtx[1,(n.opt-1)] <- kumTail.cnst.da(params)
    jcb.mtx[1, n.opt] <- kumTail.cnst.db(params)
    
    return (list('constraints' = kumTail.cnst(params),
                 'jacobian' = jcb.mtx))
  }
  
  #Function combines equality and inequality constraints in a single objec (required for certain algorithms)
  combo.cnst.eval <- function (X)  {
    #update parameters
    params <- opt.update.WRZ (X) 
    
    #calculate jacobian
    jcb.mtx <- matrix(0, nrow = 3+n.S+n.C, ncol = n.opt)
    
    #for optimization params
    if(W.TF) {
      jcb.mtx[1, W.indx] <- kumTail.cnst.dW(params)
      jcb.mtx[2, W.indx] <- kumMoM.2.cnst.dW(params)
      jcb.mtx[3, W.indx] <- -kumMoM.2.cnst.dW(params)
    }
    if(R.TF) {
      jcb.mtx[1, R.indx] <- kumTail.cnst.dR(params)
      jcb.mtx[2, R.indx] <- kumMoM.2.cnst.dR(params)
      jcb.mtx[3, R.indx] <- -kumMoM.2.cnst.dR(params)
    }
    if(Z.TF) {
      jcb.mtx[2, Z.indx] <- kumMoM.2.cnst.dZ(params)
      jcb.mtx[3, Z.indx] <- -kumMoM.2.cnst.dZ(params)
    }
    
    #for distribution param a
    jcb.mtx[1,(n.opt-1)] <- kumTail.cnst.da(params)
    jcb.mtx[2,(n.opt-1)] <- kumMoM.2.cnst.da(params)
    jcb.mtx[3,(n.opt-1)] <- -kumMoM.2.cnst.da(params)
    
    #for distribution param b
    jcb.mtx[1, n.opt] <- kumTail.cnst.db(params)
    jcb.mtx[2, n.opt] <- kumMoM.2.cnst.db(params)
    jcb.mtx[3, n.opt] <- -kumMoM.2.cnst.db(params)
    
    #accumulate constraints
    cnst <- c(kumTail.cnst(params),
              kumMoM.2.cnst(params), -kumMoM.2.cnst(params))
    
    W <- params$W
    R <- params$R
    Z <- params$Z
    #New constraint: amount purchased+securitized <= trust channel
    if(S.TF) {
      #constraint values
      trust.ineq <- W[W.optim]+W[S.optim]*(-Z[S.optim])-Wlim
      cnst <- c(cnst, trust.ineq)
      
      #constraint jacobian
      jcb.mtx[c(4:(3+n.S)), W.indx] <- 1 
      #jcb.mtx[c(4:(3+n.S)), ZS.indx] <- -W[S.optim]
      jcb.mtx[c(4:(3+n.S)), ZS.indx] <- -(W[S.optim]+Z[S.optim]*S.dZ.intrp(R[S.optim],Z[S.optim])) 
      jcb.mtx[c(4:(3+n.S)), RS.indx] <- -Z[S.optim]*S.dR.intrp(R[S.optim],Z[S.optim]) 
    }
    #New constraint: amount purchased+amountSold == Total Consumed
    if(C.TF){
      #constraint values
      cnsm.ineq <- W[W.optim]+ifelse(S.TF,W[S.optim],0)-Clim
      cnst <- c(cnst, cnsm.ineq)
      
      #constraint jacobian
      jcb.mtx[c((4+n.S):(3+n.S+n.C)), W.indx] <- 1
      if(S.TF){
        jcb.mtx[c((4+n.S):(3+n.S+n.C)), ZS.indx] <- S.dZ.intrp(R[S.optim],Z[S.optim])
        jcb.mtx[c((4+n.S):(3+n.S+n.C)), RS.indx] <- S.dR.intrp(R[S.optim],Z[S.optim])
      }
      #Repeat with negative side
      cnst <- c(cnst, -cnsm.ineq)
      jcb.mtx <- rbind(jcb.mtx,-jcb.mtx[c((4+n.S):(3+n.S+n.C)),])
    }
    
    return (list('constraints' = cnst, 'jacobian' = jcb.mtx))
  }
  
  #Function directly evalues tail inequality without equality constraints on moments
  ineq.drct.eval <- function (X)  {
    
    #update parameters
    params <- opt.update.WRZ (X) 
    W <- params$W
    R <- params$R
    Z <- params$Z
    
    #expected profit normalized against maximum possible profit
    muHat.norm <- sum(W*(P.in*(R-Z)+Z))/sum(W*R)
    
    #variance normalized against amount lent
    sigma.vec <- Std*W/sum(W)*(R-Z)
    varHat.norm <- t(sigma.vec)%*%corr.mtx%*%sigma.vec
    
    #method of moments estimate for distribution
    fit.kumar <- kumar.MoM(muHat.norm, varHat.norm)
    a <- fit.kumar[1]
    b <- fit.kumar[2]
    
    #define k.alpha % probability that losss is >= z.alpha*ValueAtRisk
    tail.losslim <- sum(W)/sum(W*R)*(1-z.alpha)
    tail.invcdf <- (1-(1-k.alpha)^(1/b))^(1/a) 
    tail.ineq <- tail.losslim-tail.invcdf
    
    #in case no other ineuqality
    if(!S.TF) {
      return (tail.ineq)
    } else {
      if(W[S.optim]<0) {browser()}
      
      #amount purchased+securitized <= trust channel
      trust.ineq <- W[W.optim]+W[S.optim]*(-Z[S.optim])-Wlim
      return (c(tail.ineq, trust.ineq))
    }
  }
  
  if(browse) {
    browser()
  }
  
  #run solver - retrieve solution
  if(relax) {
    soln.CBY <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = function (X)  {prft.obj(opt.update.WRZ (X) )},
                               eval_g_ineq = ineq.drct.eval,
                               opts = c(list(algorithm = 'NLOPT_LN_COBYLA'), controls))
    return (list(W = soln.CBY$solution[W.indx],
                 R = soln.CBY$solution[R.indx],
                 Z = soln.CBY$solution[Z.indx],
                 S = ifelse(S.TF,S.intrp(soln.CBY$solution[RS.indx], soln.CBY$solution[ZS.indx]),NA)))
  }
  if(algorithm == 'NLOPT_LN_COBYLA') { #status - runs and solutions are good, but slow
    soln.CBY <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = function (X)  {prft.obj(opt.update.WRZ (X) )},
                               eval_g_ineq = function (X)  {params <- opt.update.WRZ (X) ;
                               c(kumTail.cnst(params),
                                 #kumMoM.1.cnst(params),-kumMoM.1.cnst(params),
                                 kumMoM.2.cnst(params),-kumMoM.2.cnst(params))},
                               opts = c(list(algorithm = 'NLOPT_LN_COBYLA'), controls))
    return (list(W = soln.CBY$solution[W.indx],
                 R = soln.CBY$solution[R.indx],
                 Z = soln.CBY$solution[Z.indx],
                 K = soln.CBY$solution[K.indx],
                 S = ifelse(S.TF,S.intrp(soln.CBY$solution[RS.indx], soln.CBY$solution[ZS.indx]),NA)))
  }
  if(algorithm == 'NLOPT_GN_ISRES') { #status - runs, good solutions but converges slowly
    soln.ISR <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = obj.grad.eval,
                               eval_g_ineq = combo.cnst.eval,
                               opts = c(list(algorithm = 'NLOPT_GN_ISRES'), controls))
    return (list(W = soln.ISR$solution[W.indx], 
                 R = soln.ISR$solution[R.indx],
                 Z = soln.ISR$solution[Z.indx],
                 K = soln.ISR$solution[K.indx],
                 S = ifelse(S.TF,S.intrp(soln.ISR$solution[RS.indx], soln.ISR$solution[ZS.indx]),NA)))
  }
  if(algorithm == 'NLOPT_LD_MMA') { #status - runs but produces nonsensical results
    soln.MMA <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = obj.grad.eval,
                               eval_g_ineq = combo.cnst.eval,
                               opts = c(list(algorithm = 'NLOPT_LD_MMA'), controls))
    return (list(W = soln.MMA$solution[W.indx],
                 R = soln.MMA$solution[R.indx],
                 Z = soln.MMA$solution[Z.indx],
                 K = soln.MMA$solution[K.indx]))
  }
  if(algorithm == 'NLOPT_GN_ORIG_DIRECT_L') { #status - runs but produces non-sensical results
    soln.DCT <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = obj.grad.eval,
                               eval_g_ineq = combo.cnst.eval,
                               opts = c(list(algorithm = 'NLOPT_GN_ORIG_DIRECT_L'), controls))
    return (list(W = soln.DCT$solution[W.indx],
                 R = soln.DCT$solution[R.indx],
                 Z = soln.DCT$solution[Z.indx],
                 K = soln.DCT$solution[K.indx]))
  }
  if(algorithm == 'NLOPT_LD_SLSQP') { #status - runs but results are unsatisfactory
    soln.SSP <- nloptr::nloptr(x0 = X0.opt,
                               lb = LB.opt, ub = UB.opt,
                               eval_f = obj.grad.eval,
                               eval_g_ineq = ineq.cnst.eval,
                               eval_g_eq = eql.cnst.eval,
                               opts = c(list(algorithm = 'NLOPT_LD_SLSQP'), controls))
    return (list(W = soln.SSP$solution[W.indx],
                 R = soln.SSP$solution[R.indx],
                 Z = soln.SSP$solution[Z.indx],
                 K = soln.SSP$solution[K.indx]))
  }
  if(algorithm == 'NLOPT_AUGLAG') { #status - runs but does not do anything :(
    soln.ALG <- nloptr::auglag(x0 = X0.opt, upper = UB.opt, lower = LB.opt,
                               fn = function (X)  {prft.obj(opt.update.WRZ (X) )},
                               gr = function (X)  {obj.grad.eval (X) [[2]]},
                               hin = function (X)  {kumTail.cnst(opt.update.WRZ (X) )},
                               hinjac = function (X)  {ineq.cnst.eval (X) [[2]]},
                               heq = function (X)  {c(kumMoM.1.cnst(opt.update.WRZ (X) ),
                                                      kumMoM.2.cnst(opt.update.WRZ (X) ))},
                               heqjac = function (X)  {eql.cnst.eval (X) [[2]]},
                               localsolver = 'MMA', control = list(maxeval = 50000, xtol_rel = 0.1)) 
  }
  if(algorithm == 'constrOptim.nl') { #status - runs but solutions don't make sense
    soln.ALB <- alabama::constrOptim.nl(X0.opt,
                                        fn = function (X)  {prft.obj(opt.update.WRZ (X) )},
                                        gr = function (X)  {obj.grad.eval (X) [[2]]},
                                        hin = function (X)  {kumTail.cnst(opt.update.WRZ (X) )},
                                        hin.jac = function (X)  {ineq.cnst.eval (X) [[2]]},
                                        heq = function (X)  {c(kumMoM.1.cnst(opt.update.WRZ (X) ),
                                                               kumMoM.2.cnst(opt.update.WRZ (X) ))},
                                        heq.jac = function (X)  {eql.cnst.eval (X) [[2]]},
                                        control.outer = list(eps = 0.0001, NMinit = TRUE),
                                        control.optim = list(eps = 0.0001, NMinit = TRUE))
  }
  if(algorithm == 'nlminb2') { #status - not working
    soln.ROI <- nlminb2(X0.opt, upper = UB.opt, lower = LB.opt,
                        objective = function (X)  {prft.obj(opt.update.WRZ (X) )},
                        gradient = function (X)  {obj.grad.eval (X) [[2]]},
                        eqFun = function (X)  {eql.cnst.eval (X) [[1]]},
                        leqFun = function (X)  {kumTail.cnst(opt.update.WRZ (X) )})
  }
}
