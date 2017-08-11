require(bvarsv)
data(usmacro)

mlag <- function(X,lag)
{
  p <- lag
  X <- as.matrix(X)
  Traw <- nrow(X)
  N <- ncol(X)
  Xlag <- matrix(0,Traw,p*N)
  for (ii in 1:p)
  {
    Xlag[(p+1):Traw,(N*(ii-1)+1):(N*ii)]=X[(p+1-ii):(Traw-ii),(1:N)]
  }
  return(Xlag)
}


p <- 5 #lags

# Data: Inflation; Unemployment; Interest Rate
# Dimensions: 195x3
Y <- as.matrix(usmacro)

# p lags of Y with first p rows = 0
# Dimensions: 195x3*p
X <- mlag(Y,p)
X <- cbind(X,1)
#X <- cbind(as.vector(matrix(1,nrow(X),1)),X)

###### constructing an nx1 vector containing the average of the first p observations for each variable

#y0 <- as.vector(matrix(0,ncol(Y),1))
y0 <- rep(0, ncol(Y))

for(irep in 1:ncol(Y)){
   y0[irep] <- mean(Y[(1:p),irep]) 
    }
        
Y<-Y[(p+1):nrow(Y),]
X<-X[(p+1):nrow(X),]

n <- ncol(Y)
T <- nrow(Y)
k <- n*p+1  #number of regressors=number of endogenous variables multiplied with the number of lags plus 1 (because of constant)
d <- n+2 # see logMLVAR_formcmc.m ### WTF?


############# OLS results ################
library(vars)
ols.mod <- VAR(as.matrix(usmacro), p = p, type = "const")
#summary(ols.mod)

beta.OLS <- solve(crossprod(X))%*%crossprod(X,Y)
#check:
library(compare)
beta.OLS.check<-as.matrix(sapply(coefficients(ols.mod), function(x)x[,1]))
compare(beta.OLS, beta.OLS.check, allowAll =TRUE) 
#v <- T-n
v <- T-k # ??? That's DF right? So Obs-Regressors?
v.check <- sapply(summary(ols.mod)$varresult, function(x) x$df)[2,]
compare(v, v.check, allowAll = TRUE)

residuals.OLS <- Y-X%*%beta.OLS
residuals.OLS.check <- sapply(summary(ols.mod)$varresult, function(x) x$residuals)
compare(residuals.OLS, residuals.OLS.check, allowAll = TRUE)

sigma.OLS <- crossprod(residuals.OLS)/v
sigma.OLS.check <- summary(ols.mod)$covres
compare(sigma.OLS, sigma.OLS.check, allowAll = TRUE)


#beta.var <- sigma.OLS*solve(crossprod(X)) #works only for p=1, don't know why
beta.var <- beta.var.check <- sapply(summary(ols.mod)$varresult, function(x) x$coefficients[,"Std. Error"])
##########################################


#MH algorithm
#starting value

                                        #for the gamma density
gammacoef <- function(mode, sd){
    k.shape <- (2+mode^2/sd^2+sqrt((4+mode^2/sd^2)*mode^2/sd^2))/2
    theta.scale <- sqrt(sd^2/k.shape)
    return(data.frame(shape = k.shape, scale = theta.scale))
}


accept <- 0
scale.psi <- shape.psi <- 0.02^2

nsave <- 200
nburn <- 200
ntot <- nsave+nburn


###############################################################
## NEWCODE                                                   ##
## MN is minnessota                                          ##
## noc is sum of coefficients prior                          ##
## sur is single unit root prior = dummy initial observation ##
###############################################################

##########
## FUNS ##
##########
gammacoef <- function(mode, sd){
    k.shape <- (2+mode^2/sd^2+sqrt((4+mode^2/sd^2)*mode^2/sd^2))/2
    theta.scale <- sqrt(sd^2/k.shape)
    return(data.frame(shape = k.shape, scale = theta.scale))
}


logGammapdf <- function(xInt, kInt, thetaInt){
    lgp <- kInt-1*log(xInt)-xInt/thetaInt-kInt*log(thetaInt)-lgamma(kInt)
    return(lgp)
}

logIG2pdf <- function(xInt, alphaInt, betaInt){
    # Matlab's "./" divides element-wise so this beta/Xint should work 
    ligp <- alpahInt*log(betaInt)-(alphaInt + 1)*log(xInt)-beta/Xint-lgamma(alphaInt)
    return(ligp)
}


make.dummy.sur <- function(theta = theta.prop){
    Ydsur <- (1/theta)*t(y0)
    Xdsur <- as.vector(matrix(1/theta,1,1+n*p))
    for(irep2 in 1:p)
    {
      Xdsur[(1+(irep2-1)*n+1):(1+irep2*n)] <- Ydsur
    }
    
    Yd <- rbind(Y, Ydsur) #stack the dummy vector at the end of the data
    Xd <- rbind(X, Xdsur) 
    Td <- 1 #number of additionally rows due to the dummy 
    return(list(Y = Yd, X = Xd, T = Td))
}

make.dummy.noc <- function(miu = miu.prop, Yint = Y, Xint = X, Tint = T){
    Ydnoc <- (1/miu)*diag(y0)
    Xdnoc <- matrix(0,n,1+n*p)
    for(irep3 in 1:p)
    {
      Xdnoc[(1:n),(1+(irep3-1)*n+1):(1+irep3*n)] <- Ydnoc
    }
    Yd <- rbind(Yint, Ydnoc)  
    Xd <- rbind(Xint, Xdnoc) 
    Td <- Td+n
    return(list(Y = Yd, X =  Xd, T = Td))
}


make.postmod <- function(Yint, Xint, OmegaInt, bInt, Tint, psiInt, doSur, doNoc, thetaInt, lambdaInt, miuInt){
    
    betahat <- solve(crossprod(Xint) + diag(1/OmegaInt))%*%(crossprod(Xint,Yint) + diag(1/OmegaInt)%*%bInt)
    
    #VAR residuals
    epshat <- Yint-Xint%*%betahat
    
    ###### logML ###########
    Tint <- T + Td
    
    aaa <- diag(sqrt(OmegaInt))%*%(crossprod(Xint))%*%diag(sqrt(OmegaInt))
    bbb <- diag(1/sqrt(psiInt))%*%(crossprod(epshat) + t(betahat-bInt)%*%diag(1/OmegaInt)%*%(betahat-bInt))%*%diag(1/sqrt(psiInt))
    
    eigaaa <- Re(eigen(aaa)$values)
    eigaaa[eigaaa<1e-12] <- 0
    eigaaa <- eigaaa+1
    eigbbb <- Re(eigen(bbb)$values)
    eigbbb[eigbbb<1e-12] <- 0
    eigbbb <- eigbbb+1
    
    logML <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psiInt))/2 - n*sum(log(eigaaa))/2 - (T+d)*sum(log(eigbbb))/2

    if (doSur == TRUE | doNoc == TRUE){

    #prior mode of the VAR coefficients (analogously to the paper code)
        Yd <- rbind(sur.dum$Y, noc.dum$Y)
        Xd <- rbind(sur.dum$X, noc.dum$X)

        betahatd <- b

        epshatd <- Yd-Xd%*%betahatd

        aaad <- diag(sqrt(OmegaInt))%*%(crossprod(Xd))%*%diag(sqrt(OmegaInt))  
        bbbd <- diag(1/sqrt(psiInt))%*%(crossprod(epshatd) + t(betahatd-b)%*%diag(1/OmegaInt)%*%(betahatd-b))%*%diag(1/sqrt(psiInt))

        eigaaad <- Re(eigen(aaad)$values)
        eigaaad[eigaaad<1e-12] <- 0
        eigaaad <- eigaaad+1
        eigbbbd <- Re(eigen(bbbd)$values)
        eigbbbd[eigbbbd<1e-12] <- 0
        eigbbbd <- eigbbbd+1
    #normalizing constant
        norm <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psiInt))/2 - n*sum(log(eigaaad))/2 - (T+d)*sum(log(eigbbbd))/2
        
        logML <- logML - norm

        # Assuming we always use hyperpriors
        
        logML <- logML + logGammapdf(lambdaInt, lambda$shape, lambda$scale)

        if (doSur == TRUE){
            logML <- logML + logGammapdf(thetaInt, theta$shape, theta$scale)
        }

        if (doNoc == TRUE){
            logML <- logML + logGammapdf(miuInt, miu$shape, miu$scale)
        }

        if (mn.psi == TRUE){
            logML <- logML + sum(logIG2pdf(psiInt/(d-n-1), 0.02^2, 0.02^2))
        }
    }
  }



##################################
## condition posterior proposal ##
##################################

psi <- rep(0.02^2, n)

#prior scale matrix for the covariance of the shocks
PSI <- diag(psi)


#MN prior mean; each column corresponds to the prior mean of the coeeficients of each equation (see Appendix A)
b <- matrix(0,k,n)
b[2:(n+1),] <- diag(n)

Td <- 0

##############################
## bounds for maximization  ##
##############################
# I don't think we are using this???
##########################
## MIN.lambda <- 0.0001 ##
## MIN.alpha <- 0.1     ##
## MIN.theta <- 0.0001  ##
## MIN.miu <- 0.0001    ##
## MAX.lambda <- 5      ##
## MAX.miu <- 50        ##
## MAX.theta <- 50      ##
## MAX.alpha <- 5       ##
##########################


######################################
## Metropolist-Hastings Interations ##
######################################


# Start fun here
metroPolice.hasThings <- function(use.SUR == TRUE, use.NOC = TRUE, adjustSD = FALSE, burn.in = 500, nsave = 1000, prop.sd = 100, count = 0){
    
    interations <- burn.in + nsave

    # Initial "draws"
    lambda.draw <- 5 
    theta.draw <- 10
    miu.draw <- 10

    # Calculate shape and scale of coefs
    lambda <- gammacoef(mode = 0.2, sd = 0.4)
    theta <- gammacoef(mode = 1, sd = 1)
    miu <- gammacoef(mode = 1, sd = 1)

    # Empty Storage matrices
    lambda_store <- matrix(NA, nsave, 1)
    theta_store <- matrix(NA, nsave, 1)
    miu_store <- matrix(NA, nsave, 1)

    # Initial 
    logMLold==-10e15
    while(logMLold == -10e15){
        logMLold <- make.postmod(Yint = Y, Xint = X, OmegaInt = omega, bInt = b, Tint = T, psiInt = psi, doSur = TRUE, doNoc = TRUE, thetaInt = theta.draw, lambdaInt = lambda.draw, miuInt = miu.draw)  
}
   
    for(irep in 1:iterations){
        # Propose a new value for the hyperpriors
        # Drawing from log-normal to ensure positive values 
        lambda.prop <- rlnorm(1, lambda_draw, prop.sd) 
        theta.prop <- rlnorm(1, theta_draw, prop.sd)
        miu.prop <- rlnorm(1, miu_draw, prop.sd)

        #hyperparameter: variance cov of the minnesota prior 
        Vc <- 10e6 
        omega <- rep(0, k)
        #first element is the prior variance in the MN prior for the coefficients
        omega[1] <- Vc         
        for(lag in 1:p)
        {
                                        #makes all the other lags less important
            omega[(1+(lag-1)*n+1):(1+lag*n)] <- (d-n-1)*(lambda.prop^2)*(1/(lag^2))/psi 
                                        #omega is here still a kx1 vector! it will later become a diag matrix
        }

        # Choose which priors to use
        if (use.SUR == TRUE){
            sur.dum <- make.dummy.sur(theta = theta.prop)
            Y <- sur.dum$Y
            X <- sur.dum$X
            T <- sur.dum$T
        }

        if (use.NOC == TRUE){
            noc.dum <- make.dummy.noc(miu = miu.prop, Yint = Y, Xint = X, Tint = T)
            Y <- noc.dum$Y
            X <- noc.dum$X
            T <- noc.dum$T
        }

        # Calculate new logML
        logMLnew <- make.postmod(Yint = Y, Xint = X, OmegaInt = omega, bInt = b, Tint = T, psiInt = psi, doSur = use.SUR, doNoc = use.NOC, thetaInt = theta.prop, lambdaInt = lambda.prop, miuInt = miu.prop) 

        # Accept draw?
        if ((logMLnew - logMLold) > runif(1)){
            lambda.draw <- lambda.prop
            theta.draw <- theta.prop
            miu.draw <- miu.prop

            logMLold <- logMLnew
            
            count <- count + 1
        }

        # Adjust prop SD [optional]
        if (adjustSD == TRUE){
            if (irep<(nburn/2)){
                if((count/irep)>0.4) prop.sd <- 1.01*prop.sd
                if((count/irep)<0.2) prop.sd <- 0.99*prop.sd
            }
        }

        # Save values
        if (irep>burn.in){
            lambda_store[irep-burn.in,1] <- lambda.draw
            theta_store[irep-burn.in,1] <- theta.draw
            miu_store[irep-burn.in,1] <- miu.draw
        }
        print(count/irep)
    }
    return(list(lambdas = lambda_store, thetas = theta_store, mius = miu_store))
}

result <- metroPolice.hasThings()

lambda.density <- result[1]
theta.density <- result[2]
miu.density <- result[3]



##########################
## #### ROBSICODE ##### ##
##########################

for(ii in 1:ntot){
    lambda_prop <- rnorm(1,lambda_draw,150)
    while(lambda_prop < 0)
      {
        print(lambda_prop)
        lambda_prop <- rnorm(1,lambda_draw,150)
      }
    theta_prop <- rnorm(1,theta_draw,150)
    while(theta_prop < 0)
      {
        print(theta_prop)
        theta_prop <- rnorm(1,theta_draw,150)
      }
    miu_prop <- rnorm(1,miu_draw,150)
    while(miu_prop < 0)
      {
        print(miu_prop)
        miu_prop <- rnorm(1,miu_draw,150)
      }
   #condition posterior proposal ##########################
    psi <- as.vector(matrix(0.02^2,n,1))
    PSI <- diag(psi,n,n) #prior scale matrix for the covariance of the shocks
    b <- matrix(0,k,n) 
    diagb <- as.vector(matrix(1,n,1))
    b[2:(n+1),] <- diag(diagb) #MN prior mean; each column corresponds to the prior mean of the coeeficients of each equation (see Appendix A)

    
    Vc <- 10e6 
    omega <- as.vector(matrix(0,k,1))  #hyperparameter: variacnce cov of the minnesota prior
    omega[1] <- Vc         #first element is the prior variance in the MN prior for the coefficients (very large value)
    for(irep in 1:p)
    {
      #makes all the other lags less important
      omega[(1+(irep-1)*n+1):(1+irep*n)] <- (d-n-1)*(lambda_prop^2)*(1/(irep^2))/psi 
      #omega is here still a kx1 vector! it will later become a diag matrix
    }
    
    
    #Construction of the Prior dummys (x and y underbar)
    ############## SUR dummy ################
    Ydsur <- (1/theta_prop)*t(y0)
    Xdsur <- as.vector(matrix(1/theta_prop,1,1+n*p))
    for(irep2 in 1:p)
    {
      Xdsur[(1+(irep2-1)*n+1):(1+irep2*n)] <- Ydsur
    }
    Yd1 <- rbind(Y,Ydsur) #stack the dummy vector at the end of the data
    Xd1 <- rbind(X,Xdsur)
    Td <-1 #number of additionally rows due to the dummy 
    ###########################################
    ############# NOC dummy #################
    Ydnoc <- (1/miu_prop)*diag(y0)
    Xdnoc <- matrix(0,n,1+n*p)
    for(irep3 in 1:p)
    {
      Xdnoc[(1:n),(1+(irep3-1)*n+1):(1+irep3*n)] <- Ydnoc
    }
    Yd2 <- rbind(Yd1,Ydnoc) #here both prior dummys are stacked at the end of the Y and X data matrices
    Xd2 <- rbind(Xd1,Xdnoc)
    Td <- Td+n
    ############################################
    
    
    ##### output ###########
    #posterior mode of the VAR coeeficients
    #see the Appendix for the formulas
    betahat <- solve(crossprod(Xd2) + diag(1/omega))%*%(crossprod(Xd2,Yd2) + diag(1/omega)%*%b)
    
    #VAR residuals
    epshat <- Y-X%*%betahat
    
    ###### logML ###########
    T <- T + Td
    
    aaa <- diag(sqrt(omega))%*%(crossprod(Xd2))%*%diag(sqrt(omega))
    bbb <- diag(1/sqrt(psi))%*%(crossprod(epshat) + t(betahat-b)%*%diag(1/omega)%*%(betahat-b))%*%diag(1/sqrt(psi))
    
    eigaaa <- Re(eigen(aaa)$values)
    eigaaa[eigaaa<1e-12] <- 0
    eigaaa <- eigaaa+1
    eigbbb <- Re(eigen(bbb)$values)
    eigbbb[eigbbb<1e-12] <- 0
    eigbbb <- eigbbb+1
    
    logML1 <- -n*T*log(pi)/2 + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaa))/2 - (T+d)*sum(log(eigbbb))/2
    
    #prior mode of the VAR coefficients (analogously to the paper code)
    Yd <- rbind(Ydsur,Ydnoc)
    Xd <- rbind(Xdsur,Xdnoc)
    
    betahatd <- b #this is the case for our priors (the line above delivers the same but is numerically not very stable
    epshatd <- Yd-Xd%*%betahatd
    
    aaad <- diag(sqrt(omega))%*%(crossprod(Xd))%*%diag(sqrt(omega))  
    bbbd <- diag(1/sqrt(psi))%*%(crossprod(epshatd) + t(betahatd-b)%*%diag(1/omega)%*%(betahatd-b))%*%diag(1/sqrt(psi))
    
    eigaaad <- Re(eigen(aaad)$values)
    eigaaad[eigaaad<1e-12] <- 0
    eigaaad <- eigaaad+1
    eigbbbd <- Re(eigen(bbbd)$values)
    eigbbbd[eigbbbd<1e-12] <- 0
    eigbbbd <- eigbbbd+1
    
    #normalizing constant
    norm <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaad))/2 - (T+d)*sum(log(eigbbbd))/2
    
    logML <- logML1 - norm #this should be our p(Y) (hopefully)
    
    cond.post.prop <- logML + log(sum(dgamma(lambda_prop,shape=lambda.k,scale=lambda.theta))) + log(sum(dgamma(theta_prop,shape=theta.k,scale=theta.theta))) + log(sum(dgamma(miu_prop,shape=miu.k,scale=miu.theta)))

    ####################################################
    
    #condition posterior current ##########################
    psi <- as.vector(matrix(0.02^2,n,1))
    PSI <- diag(psi,n,n) #prior scale matrix for the covariance of the shocks
    b <- matrix(0,k,n) 
    diagb <- as.vector(matrix(1,n,1))
    b[2:(n+1),] <- diag(diagb) #MN prior mean; each column corresponds to the prior mean of the coeeficients of each equation (see Appendix A)
    
    Vc <- 10e6 
    omega <- as.vector(matrix(0,k,1))  #hyperparameter: variacnce cov of the minnesota prior
    omega[1] <- Vc         #first element is the prior variance in the MN prior for the coefficients (very large value)
    for(irep4 in 1:p)
    {
      #makes all the other lags less important
      omega[(1+(irep4-1)*n+1):(1+irep4*n)] <- (d-n-1)*(lambda_draw^2)*(1/(irep4^2))/psi 
      #omega is here still a kx1 vector! it will later become a diag matrix
    }
    
    
    #Construction of the Prior dummys (x and y underbar)
    ############## SUR dummy ################
    Ydsur <- (1/theta_draw)*t(y0)
    Xdsur <- as.vector(matrix(1/theta_draw,1,1+n*p))
    for(irep5 in 1:p)
    {
      Xdsur[(1+(irep5-1)*n+1):(1+irep5*n)] <- Ydsur
    }
    Yd1 <- rbind(Y,Ydsur) #stack the dummy vector at the end of the data
    Xd1 <- rbind(X,Xdsur)
    Td <-1 #number of additionally rows due to the dummy 
    ###########################################
    ############# NOC dummy #################
    Ydnoc <- (1/miu_draw)*diag(y0)
    Xdnoc <- matrix(0,n,1+n*p)
    for(irep6 in 1:p)
    {
      Xdnoc[(1:n),(1+(irep6-1)*n+1):(1+irep6*n)] <- Ydnoc
    }
    Yd2 <- rbind(Yd1,Ydnoc) #here both prior dummys are stacked at the end of the Y and X data matrices
    Xd2 <- rbind(Xd1,Xdnoc)
    Td <- Td+n
    ############################################
    
    
    ##### output ###########
    #posterior mode of the VAR coeeficients
    #see the Appendix for the formulas
    betahat <- solve(crossprod(Xd2) + diag(1/omega))%*%(crossprod(Xd2,Yd2) + diag(1/omega)%*%b)
    
    #VAR residuals
    epshat <- Y-X%*%betahat
    
    ###### logML ###########
    T <- T +Td
    
    aaa <- diag(sqrt(omega))%*%(crossprod(Xd2))%*%diag(sqrt(omega))
    bbb <- diag(1/sqrt(psi))%*%(crossprod(epshat) + t(betahat-b)%*%diag(1/omega)%*%(betahat-b))%*%diag(1/sqrt(psi))
    
    eigaaa <- Re(eigen(aaa)$values)
    eigaaa[eigaaa<1e-12] <- 0
    eigaaa <- eigaaa+1
    eigbbb <- Re(eigen(bbb)$values)
    eigbbb[eigbbb<1e-12] <- 0
    eigbbb <- eigbbb+1
    
    logML1 <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaa))/2 - (T+d)*sum(log(eigbbb))/2
    
    #prior mode of the VAR coefficients (analogously to the paper code)
    Yd <- rbind(Ydsur,Ydnoc)
    Xd <- rbind(Xdsur,Xdnoc)
    
    betahatd <- b #this is the case for our priors (the line above delivers the same but is numerically not very stable
    epshatd <- Yd-Xd%*%betahatd
    
    aaad <- diag(sqrt(omega))%*%(crossprod(Xd))%*%diag(sqrt(omega))  
    bbbd <- diag(1/sqrt(psi))%*%(crossprod(epshatd) + t(betahatd-b)%*%diag(1/omega)%*%(betahatd-b))%*%diag(1/sqrt(psi))
    
    eigaaad <- Re(eigen(aaad)$values)
    eigaaad[eigaaad<1e-12] <- 0
    eigaaad <- eigaaad+1
    eigbbbd <- Re(eigen(bbbd)$values)
    eigbbbd[eigbbbd<1e-12] <- 0
    eigbbbd <- eigbbbd+1
    
    #normalizing constant
    norm <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaad))/2 - (T+d)*sum(log(eigbbbd))/2
    
    logML <- logML1 - norm #this should be our p(Y) (hopefully)
    
    cond.post.current <- logML + log(sum(dgamma(lambda_draw,shape=lambda.k,scale=lambda.theta))) + log(sum(dgamma(theta_draw,shape=theta.k,scale=theta.theta))) + log(sum(dgamma(miu_draw,shape=miu.k,scale=miu.theta)))
    
    ####################################################
    
    if((cond.post.prop-cond.post.current)>log(runif(1,0,1)))
        {
          lambda_draw <- lambda_prop
          theta_draw <- theta_prop
          miu_draw <- miu_prop
          accept <- accept+1
        }
    if(ii>nburn)
        {
          lambda_store[ii-nburn,1] <- lambda_draw
          theta_store[ii-nburn,1] <- theta_draw
          miu_store[ii-nburn,1] <- miu_draw
        }
    print(ii)
    }


print(accept/ntot)


plot(lambda_store, type = "l")
plot(theta_store, type = "l")
plot(miu_store, type = "l")











##################################################################################################################
##################################################################################################################
##################################################################################################################
##################################################################################################################
##################### this is the pure calculation of the ML p(y), before using it for calculating the posteriors
#Hyperparameter (parameter of the prior distributions)

d <- n+2

psi <- as.vector(matrix(0.02^2,n,1))
PSI <- diag(psi,n,n) #prior scale matrix for the covariance of the shocks
b <- matrix(0,k,n) 
  diagb <- as.vector(matrix(1,n,1))
b[2:(n+1),] <- diag(diagb) #MN prior mean; each column corresponds to the prior mean of the coeeficients of each equation (see Appendix A)

  
Vc <- 10e6 
omega <- as.vector(matrix(0,k,1))  #hyperparameter: variacnce cov of the minnesota prior
omega[1] <- Vc         #first element is the prior variance in the MN prior for the coefficients (very large value)
for(irep in 1:p)
  {
    #makes all the other lags less important
    omega[(1+(irep-1)*n+1):(1+irep*n)] <- (d-n-1)*(lambda^2)*(1/(irep^2))/psi 
    #omega is here still a kx1 vector! it will later become a diag matrix
  }


#Construction of the Prior dummys (x and y underbar)
############## SUR dummy ################
Ydsur <- (1/theta)*t(y0)
Xdsur <- as.vector(matrix(1/theta,1,1+n*p))
for(irep in 1:p)
  {
    Xdsur[(1+(irep-1)*n+1):(1+irep*n)] <- Ydsur
  }
Yd1 <- rbind(Y,Ydsur) #stack the dummy vector at the end of the data
Xd1 <- rbind(X,Xdsur)
Td <-1 #number of additionally rows due to the dummy 
###########################################
############# NOC dummy #################
Ydnoc <- (1/miu)*diag(y0)
Xdnoc <- matrix(0,n,1+n*p)
for(irep in 1:p)
  {
   Xdnoc[(1:n),(1+(irep-1)*n+1):(1+irep*n)] <- Ydnoc
  }
Yd2 <- rbind(Yd1,Ydnoc) #here both prior dummys are stacked at the end of the Y and X data matrices
Xd2 <- rbind(Xd1,Xdnoc)
Td <- Td+n
############################################


##### output ###########
#posterior mode of the VAR coeeficients
#see the Appendix for the formulas
betahat <- solve(crossprod(Xd2) + diag(1/omega))%*%(crossprod(Xd2,Yd2) + diag(1/omega)%*%b)

#VAR residuals
epshat <- Y-X%*%betahat

###### logML ###########
T <- T +Td

aaa <- diag(sqrt(omega))%*%(crossprod(Xd2))%*%diag(sqrt(omega))
bbb <- diag(1/sqrt(psi))%*%(crossprod(epshat) + t(betahat-b)%*%diag(1/omega)%*%(betahat-b))%*%diag(1/sqrt(psi))

eigaaa <- Re(eigen(aaa)$values)
eigaaa[eigaaa<1e-12] <- 0
eigaaa <- eigaaa+1
eigbbb <- Re(eigen(bbb)$values)
eigbbb[eigbbb<1e-12] <- 0
eigbbb <- eigbbb+1

logML1 <- -n*T*log(pi) + sum(lgamma((T+d-c(0:(n-1)))/2) - lgamma(d-c(0:(n-1)/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaa))/2 - (T+d)*sum(log(eigbbb))/2

#prior mode of the VAR coefficients (analogously to the paper code)
Yd <- rbind(Ydsur,Ydnoc)
Xd <- rbind(Xdsur,Xdnoc)

betahatd <- b #this is the case for our priors (the line above delivers the same but is numerically not very stable
epshatd <- Yd-Xd%*%betahatd

aaad <- diag(sqrt(omega))%*%(crossprod(Xd))%*%diag(sqrt(omega))  
bbbd <- diag(1/sqrt(psi))%*%(crossprod(epshatd) + t(betahatd-b)%*%diag(1/omega)%*%(betahatd-b))%*%diag(1/sqrt(psi))

eigaaad <- Re(eigen(aaad)$values)
eigaaad[eigaaad<1e-12] <- 0
eigaaad <- eigaaad+1
eigbbbd <- Re(eigen(bbbd)$values)
eigbbbd[eigbbbd<1e-12] <- 0
eigbbbd <- eigbbbd+1

#normalizing constant
norm <- -n*T*log(pi) + sum(log(gamma((T+d)/2))) - sum(log(gamma(d/2))) - T*sum(log(psi))/2 - n*sum(log(eigaaad))/2 - (T+d)*sum(log(eigbbbd))/2

logML <- logML1 - norm #this should be our p(Y) (hopefully)






############### this is just the example from hubsiflo ##########################
#MH
#Do AR(1) model

rho.true <- 0.95
sigma.true <- 0.01
T <- 1500
y <- matrix(0,T,1)

for (t in 2:T){
  y[t,] <- rho.true*y[t-1,1]+rnorm(1,0,sigma.true)
}

#------------------------Create X and Y --------------------------------#

X <- y[1:(T-1),]
y <- y[2:T,]

#OLS results

rho.OLS <- solve(crossprod(X))%*%crossprod(X,y)
v <- T-1
sig.OLS <- crossprod(y-X%*%rho.OLS)/v
rho.var <- sig.OLS*solve(crossprod(X))

#Prior hyperparameter

#for rho
rho.up <- 0.999
rho.down <- -0.999

#for sigma
S0 <- 0.01
s0 <- 0.01

#Get starting value for sigma2
rho.draw <- 0.5
sigma2.draw <- sig.OLS
scale1 <- 0.01
accept <- 0

#MCMC preliminaries

nsave <- 50
nburn <- 50
ntot <- nsave+nburn
rho_store <- matrix(NA,nsave,1)
sigma2_store <- matrix(NA,nsave,1)

for (irep in 1:ntot){
  rho.prop <- rnorm(1,rho.draw,scale1)
  #Evaluate conditonal posterior at rho.prop and rho.draw
  cond.post.prop <- sum(dnorm(y,X*rho.prop,sqrt(sigma2.draw),log=TRUE))+dunif(rho.prop,rho.down,rho.up,log=TRUE)
  cond.post.current <- sum(dnorm(y,X*rho.draw,sqrt(sigma2.draw),log=TRUE))+dunif(rho.draw,rho.down,rho.up,log=TRUE)
  if ((cond.post.prop-cond.post.current)>log(runif(1,0,1))){
    rho.draw <- rho.prop
    accept <- accept+1
  }
  SSE.post <- crossprod(y-X*rho.draw)/2+S0
  v1 <- T/2+s0
  sigma2.draw <- 1/rgamma(1, v1, SSE.post )
  if (irep>nburn){
    rho_store[irep-nburn,1] <- rho.draw
    sigma2_store[irep-nburn,1] <- sigma2.draw
  }
}

plot(rho_store, type="l")
plot(sigma2_store, type="l")

print(accept/ntot)

