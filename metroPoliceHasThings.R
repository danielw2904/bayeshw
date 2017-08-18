rm(list=ls())
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
Tt <- nrow(Y)
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
    ligp <- alphaInt*log(betaInt)-(alphaInt + 1)*log(xInt)-betaInt/xInt-lgamma(alphaInt)
    return(ligp)
}


make.dummy.sur <- function(theta = theta.prop, Ysur, Xsur){
    Ydsur <- (1/theta)*t(y0)
    Xdsur <- as.vector(matrix(1/theta,1,1+n*p))
    for(irep2 in 1:p)
    {
      Xdsur[(1+(irep2-1)*n+1):(1+irep2*n)] <- Ydsur
    }
    
    Yd <- rbind(Ysur, Ydsur) #stack the dummy vector at the end of the data
    Xd <- rbind(Xsur, Xdsur) 
    Td <- 1 #number of additionally rows due to the dummy 
    return(list(Y = Yd, X = Xd, T = Td, Xdum = Xdsur, Ydum = Ydsur))
}

make.dummy.noc <- function(miu = miu.prop, Yint, Xint, Tint){
    Ydnoc <- (1/miu)*diag(y0)
    Xdnoc <- matrix(0,n,1+n*p)
    for(irep3 in 1:p)
    {
      Xdnoc[(1:n),(1+(irep3-1)*n+1):(1+irep3*n)] <- Ydnoc
    }
    Yd <- rbind(Yint, Ydnoc)  
    Xd <- rbind(Xint, Xdnoc) 
    Td <- Tint + n
    return(list(Y = Yd, X =  Xd, T = Td, Xdum = Xdnoc, Ydum = Ydnoc))
}


make.postmod <- function(Yint, Xint, OmegaInt, bInt, Tint, psiInt, doSur, doNoc, mn.psi, thetaInt, lambdaInt, miuInt, sur.dumInt, noc.dumInt){
  
    betahat <- solve(crossprod(Xint) + diag(1/OmegaInt))%*%(crossprod(Xint,Yint) + diag(1/OmegaInt)%*%bInt)
    
    #VAR residuals
    epshat <- Yint-Xint%*%betahat
    
    ###### logML ###########
    Ttot <- Tt + Tint
    
    aaa <- diag(sqrt(OmegaInt))%*%(crossprod(Xint))%*%diag(sqrt(OmegaInt))
    bbb <- diag(1/sqrt(psiInt))%*%(crossprod(epshat) + t(betahat-bInt)%*%diag(1/OmegaInt)%*%(betahat-bInt))%*%diag(1/sqrt(psiInt))
    
    eigaaa <- Re(eigen(aaa)$values)
    eigaaa[eigaaa<1e-12] <- 0
    eigaaa <- eigaaa+1
    eigbbb <- Re(eigen(bbb)$values)
    eigbbb[eigbbb<1e-12] <- 0
    eigbbb <- eigbbb+1
    
    logML <- -n*Ttot*log(pi)/2 + sum(lgamma((Ttot+d-c(0:(n-1)))/2) - lgamma((d-c(0:(n-1))/2))) - Ttot*sum(log(psiInt))/2 - n*sum(log(eigaaa))/2 - (Ttot+d)*sum(log(eigbbb))/2

    if (doSur == TRUE & doNoc == TRUE){ #Change for eventualities that only one is true

    #prior mode of the VAR coefficients (analogously to the paper code)
        Yd <- rbind(sur.dumInt$Ydum, noc.dumInt$Ydum)
        Xd <- rbind(sur.dumInt$Xdum, noc.dumInt$Xdum)

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
        norm <- -n*Tint*log(pi)/2 + sum(lgamma((Tint+d-c(0:(n-1)))/2) - lgamma((d-c(0:(n-1))/2))) - Tint*sum(log(psiInt))/2 - n*sum(log(eigaaad))/2 - (Tint+d)*sum(log(eigbbbd))/2
        
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
            logML <- logML + sum(logIG2pdf(xInt = (psiInt/(d-n-1)), alphaInt = (0.02^2), betaInt = (0.02^2)))
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

rmvnorm <- function(sigma, mu = 0){
    sigma <- as.matrix(sigma)
    h <- chol(sigma)
    nvars <- nrow(sigma)
    X <- rnorm(nvars, mean = mu)
    Y <- t(h) %*% X
    return(Y)
}

##############################################
## use.NOC <- use.mn.psi <- use.SUR <- TRUE ##
## prop.sd <- 100                           ##
## burn.in <- 500                           ##
## nsave <- 1000                            ##
## Ymetro <- Y                              ##
## Xmetro <- X                              ##
##############################################

                                        # Start fun here
metroPolice.hasThings <- function(use.SUR = TRUE, use.NOC = TRUE, use.mn.psi = TRUE, adjustSD = FALSE, burn.in = 500, nsave = 1000, prop.sd = 100, count = 0, Xmetro = X, Ymetro = Y){
    
    iterations <- burn.in + nsave
    Tmetro <- 0
    # Initial "draws"
    lambda.draw <- 4.5
    theta.draw <- 9.5
    miu.draw <- 9.5

    # Calculate shape and scale of coefs
    lambda <<- gammacoef(mode = 0.2, sd = 0.4)
    theta <<- gammacoef(mode = 1, sd = 1)
    miu <<- gammacoef(mode = 1, sd = 1)

    # Empty Storage matrices
    lambda_store <- matrix(NA, nsave, 1)
    theta_store <- matrix(NA, nsave, 1)
    miu_store <- matrix(NA, nsave, 1)

    # Initial omega
    Vc <- 10e6 
    omega <- rep(0, k)
#first element is the prior variance in the MN prior for the coefficients
    omega[1] <- Vc         
    for(lag in 1:p)
    {
#makes all the other lags less important
        omega[(1+(lag-1)*n+1):(1+lag*n)] <- (d-n-1)*(lambda.draw^2)*(1/(lag^2))/psi}

    if (use.SUR == TRUE){
        sur.dummetro <- make.dummy.sur(theta = theta.draw, Ysur = Ymetro, Xsur = Xmetro)
         Ymetro1 <- sur.dummetro$Y
         Xmetro1 <- sur.dummetro$X
         Tmetro1 <- Tmetro + sur.dummetro$T
    }

     if (use.NOC == TRUE){
         noc.dummetro <- make.dummy.noc(miu = miu.draw, Yint = Ymetro1, Xint = Xmetro1, Tint = Tmetro1)
         Ymetro1 <- noc.dummetro$Y
         Xmetro1 <- noc.dummetro$X
         Tmetro1 <- noc.dummetro$T 
     }


    # Initial 
    logMLold <- -10e15
    while(logMLold == -10e15){
        logMLold <- make.postmod(Yint = Ymetro1, Xint = Xmetro1, OmegaInt = omega, bInt = b, Tint = Tmetro1, psiInt = psi, doSur = use.SUR, doNoc = use.NOC, mn.psi = use.mn.psi, thetaInt = theta.draw, lambdaInt = lambda.draw, miuInt = miu.draw, sur.dumInt = sur.dummetro, noc.dumInt = noc.dummetro)  
}

    for(irep in 1:iterations){
        # Propose a new value for the hyperpriors
        # Drawing from log-normal to ensure positive values 
        lambda.prop <- theta.prop <- miu.prop <- -1
while(lambda.prop < 0 | theta.prop <0 | miu.prop < 0){
    sd <- prop.sd*diag(3)
    vals <- rmvnorm(sigma = sd, mu = c(lambda.draw, theta.draw, miu.draw))
    vals

    lambda.prop <- vals[1, 1]
    theta.prop <-  vals[2, 1]
    miu.prop <- vals[3, 1]
    #######################################################
    ##     lambda.prop <- rnorm(1, lambda.draw, prop.sd) ##
    ##     theta.prop <- rnorm(1, theta.draw, prop.sd)   ##
    ## miu.prop <- rnorm(1, miu.draw, prop.sd)           ##
    #######################################################
}

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

        Yloop <- Ymetro
        Xloop <- Xmetro
        Tloop <- Tmetro
        
        # Choose which priors to use

     if (use.SUR == TRUE){
        sur.dumloop <- make.dummy.sur(theta = theta.prop, Ysur = Yloop, Xsur = Xloop)
         Yloop <- sur.dumloop$Y
         Xloop <- sur.dumloop$X
         Tloop <- Tloop + sur.dumloop$T
    }
    
     if (use.NOC == TRUE){
         noc.dumloop <- make.dummy.noc(miu = miu.prop, Yint = Yloop, Xint = Xloop, Tint = Tloop)
         Yloop <- noc.dumloop$Y
         Xloop <- noc.dumloop$X
         Tloop <- noc.dumloop$T 
     }


        # Calculate new logML
        logMLnew <- make.postmod(Yint = Yloop, Xint = Xloop, OmegaInt = omega, bInt = b, Tint = Tloop, psiInt = psi, doSur = use.SUR, doNoc = use.NOC, thetaInt = theta.prop, lambdaInt = lambda.prop, miuInt = miu.prop, mn.psi = use.mn.psi, sur.dumloop, noc.dumInt = noc.dumloop) 

        if (logMLnew > logMLold){
            
        }
        # Accept draw?
        if (exp(logMLnew - logMLold) > runif(1,0,1)){
            lambda.draw <- lambda.prop
            theta.draw <- theta.prop
            miu.draw <- miu.prop

            logMLold <- logMLnew
            
            count <- count + 1
        }

        # Adjust prop SD [optional]
        ##########################################################
        ## if (adjustSD == TRUE){                               ##
        ##     if (irep<(nburn/2)){                             ##
        ##         if((count/irep)>0.4) prop.sd <- 1.01*prop.sd ##
        ##         if((count/irep)<0.2) prop.sd <- 0.99*prop.sd ##
        ##     }                                                ##
        ## }                                                    ##
        ##########################################################

        # Save values
        if (irep>burn.in){
            lambda_store[irep-burn.in,1] <- lambda.draw
            theta_store[irep-burn.in,1] <- theta.draw
            miu_store[irep-burn.in,1] <- miu.draw
        }
        print(count/irep)
        cat("SD", prop.sd)
        cat("logMLnew", logMLnew)
        cat("logMLold", logMLold)
    }
    return(list(lambdas = lambda_store, thetas = theta_store, mius = miu_store))
}

result <- metroPolice.hasThings(burn.in = 0, nsave = 10000, prop.sd = 1, adjustSD = FALSE)

lambda.density <- result$lambdas
theta.density <- result[2]
miu.density <- result[3]

plot(density(as.matrix(lambda.density)))

plot(lambda.density, type = "l")

hist(lambda.density, 1000)
