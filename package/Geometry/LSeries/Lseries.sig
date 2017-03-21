174,1
T,LSer,-,0
V,LSeries,3
A,LSer,6,conductor,weight,sign,gamma,lpoles,lresidues
A,LSer,1,effwt
A,LSer,2,signfun,lresiduesfun
A,LSer,6,precision,parent,name,ImS,cutoff,cfgrowth
A,LSer,3,expfactor,gammapoles,gammapoleorders
A,LSer,4,lfunprecision,asympprecision,termprecision,taylorprecision
A,LSer,4,LfunReals,LfunComplexes,TermReals,TermComplexes
A,LSer,4,TaylorReals,TaylorComplexes,AsympReals,AsympComplexes
A,LSer,6,cffun,cfvec,cfrequired,cftype,cfprecpar,cfmax
A,LSer,4,cffuncK,degreeK,hodgeK,condK
A,LSer,3,aacoeff,known_ef,EF_SAVE_LIM
A,LSer,1,SAVE
A,LSer,5,asymptotics,maxasympcoeff,phiV,phiVnn,phiVser
A,LSer,6,recF,recG,lastt,PhiCaseBound,GCaseBound,termstep
A,LSer,8,logsum,Gvec,fcf,gcf,gncf,fncf,phiinfterms,Ginfterms
A,LSer,4,expdifff,asympconstf,expdiffg,asympconstg
A,LSer,5,last_fgs_s,last_fgs_terms,last_fgs_val,last_g_logsum,last_g_s
A,LSer,1,prod
A,LSer,1,object
A,LSer,2,vprint_coeffs,vprint_series
A,LSer,1,maxcoeff
A,ModFrmElt,1,ef_warning
S,HackobjPrintNamedLSer,,0,3,0,0,1,0,0,0,0,298,,0,0,298,,0,0,LSer,,-38,-38,-38,-38,-38,-38
S,Print,,0,2,0,0,1,0,0,0,0,298,,0,0,LSer,,-38,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,LSer,,36,-1,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,-1,,0,0,LSer,,36,-38,-38,-38,-38,-38
S,LCfRequired,How many Dirichlet coefficients are needed to compute L(s),0,1,0,0,0,0,0,0,0,LSer,,148,-38,-38,-38,-38,-38
S,LSetCoefficients,"Set coefficients of the L-series. The options are LSetCoefficients(L,[1,1,1,1,1,1]); // pre-computed vector of a_n's LSetCoefficients(L,func<n|1>); // a_n as a function of n LSetCoefficients(L,func<p,d|1-x>); // inv local factor at p [+O(x^(d+1))] in the last two cases the function may have an optional parameter ""Precision"", if your coefficients are real/C numbers rather than integers/rationals, e.g. LSetCoefficients(L,func<n:Precision| Pi(RealField(Precision))^n >);",0,2,0,0,1,0,0,0,0,-1,,0,0,LSer,,-38,-38,-38,-38,-38,-38
S,Coefficient,nth coefficient of the L-series L(s),0,2,0,0,0,0,0,0,0,148,,0,0,LSer,,-1,-38,-38,-38,-38,-38
S,LGetCoefficients,The sequence of first N coefficients of the L-series,0,2,0,0,0,0,0,0,0,148,,0,0,LSer,,168,-38,-38,-38,-38,-38
S,LSeriesData,"Return the tuple of invariants of the L-function <weight, gamma, conductor, cffun, sign, poles, residues> This is the data that can be used to create L with LSeries",0,1,0,0,0,0,0,0,0,LSer,,303,-38,-38,-38,-38,-38
S,LPhi,Testing function,0,2,0,0,0,0,0,0,0,402,,0,0,LSer,,402,-38,-38,-38,-38,-38
S,GTest,Testing function,0,4,0,0,0,0,0,0,0,148,,0,0,172,,0,0,402,,0,0,LSer,,172,-38,-38,-38,-38,-38
S,CFENew,New version of CheckFunctionalEquation,0,1,0,0,0,0,0,0,0,LSer,,402,-38,-38,-38,-38,-38
S,CheckFunctionalEquation,"Verify numerically that L(s) satisfies the assumed functional equation. Ideally, this should return 0, i.e. about 10^(-28) if you did not change the precision with LSetPrecision. If this is far from 0, the functional equation is probably wrong. If the residues of L^*(s) or have not been set, this function will compute them first. If the sign has not been determined yet, the function computes it and returns Abs(sign-1). Again, this should be 0",0,1,0,0,0,0,0,0,0,LSer,,402,-38,-38,-38,-38,-38
S,LSetPrecision,"Change precision that is used to computing values L(s) to a given number of decimal digits and set two other precision-related settings: ""ImS"" specifies the largest Im(s) for which you are planning to compute L(s). Default is 0 and if you will try to ask for L(s) with Im(s) large, precision loss will occur and a warning will be printed. ""asymptotics"" specifies whether to use only Taylor expansions of special functions at 0 or to allow using continued fractions of the asymptotic expansions at infinity. The former (false) is very slow but known to converge, the latter (true, default) is faster but as yet unproved to work in general. ""cfgrowth"" is a name of a function C(x) or C(L,x) that bounds the Dirichlet coefficients, |a_n|<C(n). Must be increasing and defined for all real x. (Default one would normally work fine.)",0,2,0,0,1,0,0,0,0,148,,0,0,LSer,,-38,-38,-38,-38,-38,-38
S,LStar,Value (D:=0) or D-th derivative of the modified L-function L^*(s)=L(s)*gamma factor at s=s0,0,2,0,0,0,0,0,0,0,-1,,0,0,LSer,,-1,-38,-38,-38,-38,-38
S,LTaylor,First n+1 terms of the Taylor expansion of L(s) about s=s0,0,3,0,0,0,0,0,0,0,148,,0,0,-1,,0,0,LSer,,-1,-38,-38,-38,-38,-38
S,Evaluate,Value (Derivative:=0) or D-th derivative of the L-function L(s) at s=s0. Set leading if you know that all lower order derivatives L^(k)(s0) vanish,0,2,0,0,0,0,0,0,0,-1,,0,0,LSer,,-1,-38,-38,-38,-38,-38
S,LSeries,"Construct an L-Series L with given invariants. The arguments are as follows: weight = enters the functional equation L(s)<->L(weight-s), gamma = list of Hodge numbers [l_1,..,l_d] that specify the gamma factor = A^s * product over k of Gamma((s+l_k)/2), conductor = with, in the above line, A = Sqrt(conductor/pi^d), cffun = specifies Dirichlet coefficients, either of the following four options: - pre-computed vector, e.g. [1,1,1,1,1,1] - a_n as a function of n, e.g. func<n|1> - function that computes the inverse local factor at p as a polynomial or a series up to O(x^(d+1)), e.g. func<p,d|1-x> - 0, coefficients will be set later with LSetCoefficients in cases 2 and 3, your function may have optional parameter ""precision"", (if your coefficients are real/complex numbers rather than integers/rationals), e.g. func<n:precision| Pi(RealField(precision))>. Sign = complex number of absolute value 1 in the func. equation or a function s(p) (or s(L,p)) which computes it to p digits or 0, meaning solve numerically, Poles = poles of L^*(s), only half of them needs to be specified (they are symmetric about s=weight/2), of type SeqEnum, Residues = list of residues at the poles of L*(s), or a function r(p) (or r(L,p)) which computes them to p digits or 0, meaning solve numerically, Parent = any Magma object, used to compare two L-series. e.g. for LSeries(ell. curve), parent = ell.curve. Name = used for printing (if not specified, print Parent). CoefficientGrowth = name of a function C(x) or C(L,x) that bounds the Dirichlet coefficients, |a_n|<C(n). Must be increasing and defined for all real x. Precision = number of digits to compute the values L(s) to. Can be also changed later with LSetPrecision. ImS (default 0) and asymptotics (default true): see LSetPrecision",0,4,0,0,0,0,0,0,0,-1,,0,0,-1,,0,0,82,,0,0,-1,,LSer,-38,-38,-38,-38,-38
