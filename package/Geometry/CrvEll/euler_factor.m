
freeze;

intrinsic EulerFactor(E::CrvEll[FldRat],p::RngIntElt) -> RngUPolElt
{The pth Euler of the given elliptic curve over Q}
 require IsPrime(p): "p must be prime";
 M:=MinimalModel(E); // this is not the best, but no easy solution currently
 A:=[1,-FrobeniusTraceDirect(M,p),Conductor(E) mod p ne 0 select p else 0];
 return Polynomial(A); end intrinsic;

intrinsic EulerFactor(E::CrvEll[FldNum],p::RngIntElt) -> RngUPolElt
{The pth Euler factor of the given elliptic curve over a number field}
 require IsPrime(p): "p must be prime";
 return &*[EulerFactor(E,Ideal(P[1])) :
	   P in AbsoluteDecomposition(BaseField(E),p)]; end intrinsic;

intrinsic EulerFactor(E::CrvEll[FldNum],P::RngOrdIdl) -> RngUPolElt
{The Euler factor of an elliptic curve over K at a prime ideal}
 require IsPrime(P): "P must be prime";
 D:=Discriminant(E); D:=AbsoluteNorm(D); D:=Numerator(D)*Denominator(D);
 K:=BaseField(E); F,m:=ResidueClassField(P); q:=#F; _,p,f:=IsPrimePower(q);
 R:=PolynomialRing(Rationals()); x:=R.1;
 if D mod p ne 0 then a1,a2,a3,a4,a6:=Explode(aInvariants(E));
  ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
  return 1-ap*x^f+q*x^(2*f); end if;
 locinf,EM:=LocalInformation(E,P);
 a1,a2,a3,a4,a6:=Explode(aInvariants(EM));
 cond:=locinf[3];
 if cond gt 1 then return R!1; end if;    // additive
 if cond eq 1 then                        // multiplicative  
 return 1-((#Roots(PolynomialRing(F)![1,m(a1),m(-a2)]) ne 0)
	   select 1 else -1)*x^f; end if;// split/nonsplit
 ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
 return 1-ap*x^f+q*x^(2*f); end intrinsic; // good red, orig model bad
