freeze;

// This might not have been tested in all situations

PREC:=Precision; 

intrinsic HodgeStructure(f::ModFrmHilElt) -> HodgeStruc
{The Hodge structure of a Hilbert modular form}
 Mf:=Parent(f); K:=BaseRing(Mf); N:=Level(Mf); W:=Sort(Weight(Mf)); w:=W[#W];
 require &and[IsEven(w) : w in W]: "All weights must be even";
 gamma:=&cat[[0-e,1-e] where e:=(w-W[i]) div 2 : i in [1..Degree(K)]];
 return HodgeStructure(w,gamma); end intrinsic;

intrinsic LSeries(f::ModFrmHilElt : Precision:=0) -> LSer
{The L-series of the Hilbert modular newform f.}
 Mf:=Parent(f); K:=BaseRing(Mf); N:=Level(Mf); WT:=Weight(Mf);
 require not ISA(Type(Mf),ModFrmBianchi):
  "Bianchi case not implemented (no Hecke eigenvalues at bad primes)";
 require assigned Mf`HeckeIrreducible and Mf`HeckeIrreducible:
  "The argument must be a Hilbert modular newform (obtained from 'Eigenform')";
 // TO DO: won't work for indefinite? because bad Heckes not availabe
 require Type(DirichletCharacter(Mf)) eq RngIntElt:
 "Only trivial character is currently implemented";
 if Type(WT) eq RngIntElt then W:=[WT,WT]; else W:=Sort(Weight(Mf)); end if;
 w:=W[#W]; require &and[IsEven(w) : w in W]: "All weights must be even";

 E:=HeckeEigenvalueField(Mf);  A:=AbsoluteField(E);
 prec:=(Precision eq 0) select PREC(RealField()) else Precision;
 R1 := PowerSeriesRing(RealField(prec),1+2*Degree(K)); T := R1.1;
 R2 := PolynomialRing(RealField(prec)); U := R2.1; // hack: are T,U compatible?
 ip:=InfinitePlaces(A)[1]; // only first place...

 function cfK(p,d : Precision:=prec)   fp:=Degree(p); P:=Norm(p); // prec?
  if fp gt d then return 1+O(T^(d+1)); end if; // think here?
  if Degree(A) eq 1 then ap:=HeckeEigenvalue(f,p);
  else ap:=Evaluate(A!HeckeEigenvalue(f,p),ip : Precision:=prec); end if;
  eps:=Valuation(N,p) gt 0 select 0 else 1; //need character generally
  return 1-ap*(U^fp)+eps*P^(w-1)*U^(2*fp);  end function;

 function cf(p,d : Precision:=prec) // need prec compatible
  F:=Factorization(p*Integers(K)); B:=[* cfK(f[1],d) : f in F *];
  if &and[Type(Parent(b)) eq Type(R2) and Parent(b) eq R2 : b in B]
   then B:=[b : b in B]; else B:=[R1!b :  b in B]; end if; return &*B;
  end function;

 name:=<"L-series of ",f>;
 gamma:=&cat[[0-e,1-e] where e:=(w-W[i]) div 2 : i in [1..Degree(K)]];
 L:=LSeries(w,gamma,Norm(N)*Discriminant(Integers(K))^2,cf :
	    Name:=name, Precision:=prec);
 L`cffuncK:=cfK; L`degreeK:=<2,K>; L`condK:=N;
 IP:=InfinitePlaces(K);
 L`hodgeK:=
   &cat[[<[w-W[i],W[i]-1,2],IP[i]>,<[W[i]-1,w-W[i],2],IP[i]>] : i in [1..#IP]];
 return L; end intrinsic;
