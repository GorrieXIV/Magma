174,1
S,PrecisionBound,Some integer b such that f + O(q^b) determines any modular form f in M. If the optional paramater Exact is set to true then the smallest such integer is returned,0,1,0,0,0,0,0,0,0,ModFrm,,148,-38,-38,-38,-38,-38
S,CoefficientRing,"A ring that contains the coefficients of f. If IsNewform(f) is true, then this is the ring generated by the Fourier coefficients. The optional paramater Bound can be used to obtain the ring generated by the coefficients a_n with n <= Bound",0,1,0,0,0,0,0,0,0,ModFrmElt,,-44,-38,-38,-38,-38,-38
S,CoefficientField,The field in the which the Fourier coefficients lie,0,1,0,0,0,0,0,0,0,ModFrmElt,,-24,-38,-38,-38,-38,-38
S,Coefficient,The nth Fourier coefficient of f,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,-45,-38,-38,-38,-38,-38
S,!,"The q-expansion of the modular form f, as a power series in the given ring R",0,2,0,0,0,0,0,0,0,ModFrmElt,,0,0,-49,,-48,-38,-38,-38,-38,-38
S,Basis,Same as qExpansionBasis,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrm,,82,-38,-38,-38,-38,-38
S,qExpansionBasis,"A sequence of power series containing q-expansions of the standard basis of M, to absolute precision 'prec'",0,2,0,0,0,0,0,0,0,148,,0,0,ModFrm,,82,-38,-38,-38,-38,-38
S,qExpansion,The q-expansion of the modular form f to absolute precision prec,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,286,-38,-38,-38,-38,-38
S,qExpansion,The q-expansion of the modular form f to absolute precision prec,0,1,0,0,0,0,0,0,0,ModFrmElt,,286,-38,-38,-38,-38,-38
S,PowerSeries,The q-expansion of the modular form f to absolute precision prec,0,1,0,0,0,0,0,0,0,ModFrmElt,,286,-38,-38,-38,-38,-38
S,PowerSeries,The q-expansion of the modular form f to absolute precision prec,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,286,-38,-38,-38,-38,-38
S,Reductions,"The mod p reductions of the modular form f. Because of denominators, the list of reductions can be empty",0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,168,-38,-38,-38,-38,-38
S,pAdicEmbeddings,The p-adic embeddings of f,0,2,0,0,0,0,0,0,0,148,,0,0,ModFrmElt,,168,-38,-38,-38,-38,-38
S,ComplexEmbeddings,The complex embeddings of f,0,1,0,0,0,0,0,0,0,ModFrmElt,,168,-38,-38,-38,-38,-38
S,Bernoulli,"The kth generalized Bernoulli number B_[k,eps] associated to the Dirichlet character eps. By definition, B_[k,eps]/k! equals the coefficient of t^k in the sum over 1<=a<=N of eps(a)*t*e^(at)/(e^(N*t)-1), where N is Modulus(eps)",0,2,0,0,0,0,0,0,0,GrpDrchElt,,0,0,148,,-45,-38,-38,-38,-38,-38
S,CyclotomicEmbedding,The canonical map from the field Q(eps) generated by the values of eps into the field K_f generated by the Fourier coefficients of f. We assume that f is a newform with Dirichlet character eps,0,1,0,0,0,0,0,0,0,ModFrmElt,,175,-38,-38,-38,-38,-38