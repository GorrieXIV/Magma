freeze;
/****************************************************************
2nd3isog.m
Brendan Creutz
Started: April 2011

Contains functions for performing a second 3-isogeny descent on a plane	cubic.

****************************************************************/

declare verbose Selmer, 3;

//import "../NineDesc/Getell.m": FlexPoints;

QQ := Rationals();
ZZ := Integers();


QQ := Rationals();
ZZ := Integers();

FlexPoints := function(C);
  X := Flexes(C);
  Rp := RepresentativePoints(X);
  PsoverQ := < P : P in Rp | Degree(Ring(Parent(P))) eq 1 >;
  error if #PsoverQ gt 0, "C has a rational flex; not implemented in this case.\n";
  Ks := [ AbsoluteField(Ring(Parent(P))) : P in Rp ];
  Knews := [];
  Rpnews := <>;
  for u in [1..#Ks] do
    //get better representations;
    Knew,toKnew := OptimisedRepresentation(Ks[u]);
    Knews cat:= [ Knew ];
    Append(~Rpnews,C(Knew) ! [ toKnew(Rp[u][i]) : i in [1..3] ]);
  end for;
  return Rpnews,Knews;
end function; //FlexPoints


FindQpPoint := function(C,p,prec)
// Calls IsLocallySolvable - may result in error...
// Finds a 'random' Q_p-point on C (not deterministic)

eqs := DefiningEquations(C);
BP := AmbientSpace(C);
q := Dimension(BP)+1;
Zp2 := Integers(p^2);
LocPoint := false;

while not LocPoint do

Hyperplane := &+[ (ZZ!Random(Zp2))*BP.i : i in [1..q] ];
HypSlice := Scheme(BP, [ Evaluate(f,[BP.i : i in [1..q]]) : f in eqs] cat [Hyperplane]);

  if Dimension(HypSlice) eq 0 then
    LocPoint, Pt := IsLocallySolvable(HypSlice,p);
  end if;

end while; //LocPoint

Qp := pAdicField(p,2*prec);
Pt := C(Qp)!Pt;
Pt := LiftPoint(Pt,prec);

Pt := [QQ!c : c in Eltseq(Pt)];
d := LCM([Denominator(co) : co in Pt]);
Pt := [ZZ!d*co : co in Pt];

return Pt;
end function;


DescentMap := function(C,P)
  // Returns a linear form defining the tangent line to the plane cubic C, at the point P
  // together with any 'bad primes' for the linear form.
  f := DefiningEquation(C);
  R := Parent(f);
  K := Ring(Parent(P));
  PR := PolynomialRing(K,3);
  T := [Evaluate(Derivative(f,i),Eltseq(P)) : i in [1..3]];
  O := MaximalOrder(K);
  n := Degree(K);
  M := KMatrixSpace(K,n,n)!BasisMatrix(O);
  Fvsp, map := KSpace(K,QQ);
  // Write out coefficients in terms of the Power basis for F
  Tv:= [map(T[i]) : i in [1..3]];
  // Write out coefficients in terms of the integral basis
  ITv := [Tv[i]*M^(-1) : i in [1..3]];
  // Determine scaling factor
  d := LeastCommonMultiple([Denominator(ITv[i][j]) : j in [1..n], i in [1..3]]);
  T := &+[ d*T[i]*PR.i : i in [1..3]];
  Opol := PolynomialRing(O,3);
  TO := Opol!T;
  d := GCD([ GCD([ ZZ ! a : a in Eltseq(cc)  ]) : cc in Coefficients(TO) ]);
  T := T/d;
  S_T := {};
  Ncfs := [ ZZ! Norm(c) : c in Coefficients(T) ];
  for p in Factorization(GCD(Ncfs)) do
    for pid in Decomposition(K,p[1]) do
      if Min({ Valuation(c,pid[1]) : c in Coefficients(T) }) gt 0 then
        // pid divides all coefficients...
        S_T := S_T join {p[1]};
        break;
      end if;
    end for;
  end for;
  
  GetEll2 := function(P);
  // The 3 flexes lie on a rational linear
  K := Ring(Parent(P));
  
  if not IsSquare(Discriminant(K)) then
    // K is not Galois over Q
    dg2 := { pol[1] : pol in Factorization(DefiningPolynomial(K),K) | Degree(pol[1]) gt 1 };
    ps := Random(dg2);
    L := AbsoluteField(ext<K|ps>);
  else
    L := K;
  end if;
  //Normal Closure of K.
  rts := [rts[1] : rts in Roots(DefiningPolynomial(K),L)];
  
  ConjugatePoint := function(i);
    Q := [];
    for coord in Eltseq(P) do
      Q cat:= [&+[ coord[j]*rts[i]^(j-1) : j in [1..#Eltseq(coord)] ]];
    end for;
    return Q;
  end function;
  
  P1 := ConjugatePoint(1);
  P2 := ConjugatePoint(2);
  // Now we want the line between P1 and P2
  
  R := PolynomialRing(QQ,3);
  ind := {@ i : i in [1..3] | P1[i] eq 0 and P2[i] eq 0 @};
  if #ind gt 0 then
    return R.ind[1];
  else
    ind := {@ i : i in [1..3] | P1[i] eq 0 or P2[i] eq 0 @};
    if #ind eq 0 then
      ind := {@ 3 @};
    end if;
  end if;
  ind := Random(ind);
  xy := {@ 1,2,3 @} diff {ind};
  rise := P1[xy[2]] - P2[xy[2]];
  run := P1[xy[1]] - P2[xy[1]];
  if run ne 0 then
    m := QQ!(rise/run);
    b := QQ!(P[xy[2]] - m*P[xy[1]]);
    return R.xy[2]-m*R.xy[1]-b*R.ind;
  else
    return R.xy[1] - (QQ!P[xy[1]])*R.ind;
  end if;
  end function;
  
  l2 := GetEll2(P);
  
  //Compute the constant c:
  R := Parent(l2);
  IC := ideal<R|DefiningEquations(C)>;
  _,m := SwapExtension(Parent(T));
  NT := NormalForm(R!Norm(m(T)),IC);
  l2cube := NormalForm(l2^3,IC);
  c := QQ!(NT/l2cube);
  Deltac := Denominator(c)^(-1)*Sign(c);
  c := AbsoluteValue(c*Denominator(c)^3);
  fc := Factorization(ZZ!c);
  
  for factor in fc do
    val := factor[2];
    if val ge 3 then
      Deltac *:= (factor[1]^(Floor(val/3)));
      c := c/(factor[1]^(3*Floor(val/3)));
    end if;
  end for;
  
  
  return T,S_T,c,Deltac*l2,Deltac;
  
end function; //DescentMap


Second3IsogenyDescent := function(C,originalE1,originalE2,phi,Models);

Cm := Reduce(Minimize(GenusOneModel(C)));
C := Curve(Cm);

q := Dimension(AmbientSpace(C))+1;
vprintf Selmer, 2: "Doing phi-descent on %o.\n", C;
if Type(phi) eq MonStgElt then
  _,phi := IsIsogenous(originalE1,originalE2);
else
  originalE1 := Domain(phi);
  originalE2 := Codomain(phi);
end if;

E1, originalE1toE1, E1tooriginalE1 := MinimalModel(originalE1);
E2, originalE2toE2, E2tooriginalE2 := MinimalModel(originalE2);

assert E2 eq MinimalModel(Jacobian(C));

phi := E1tooriginalE1*phi*originalE2toE2;
phihat := DualIsogeny(phi);

// determines which isogeny is locally surjective on the kernel of reduction at p = 3.
AforIsog := Coefficients(DefiningEquations(phi)[1])[1];
AforDualIsog := Coefficients(DefiningEquations(phihat)[1])[1];
assert {AforIsog,AforDualIsog} eq {1,1/9};
extraDimAt3 := (AforIsog eq 1) select 0 else 1;

P := PolynomialRing(QQ : Global := false); t := P.1;
ker := Kernel(phi);
assert Degree(DefiningEquations(ker)[1],1) eq 1;
sigma := -QQ!Coefficient(DefiningEquations(ker)[1], 3,1);
a1, a2, a3, a4, a6 := Explode(aInvariants(E1));
polyForIsogKer := t^2+a1*sigma*t+a3*t-sigma^3-a2*sigma^2-a4*sigma-a6;

Disc_E := Discriminant(E1);

Pts, Fields := FlexPoints(C);
RatFlex := [ P : P in Pts | Degree(Ring(Parent(P))) eq 1 ];

if #RatFlex gt 0 then
  printf "Has a rational flex: %o.\n No need for descent!\n", Random(RatFlex);
end if;
// find the best field to work with
fld := [ k : k in Fields | Degree(k) eq 3];
error if #fld eq 0, "There is either no 3-isogeny or no non-rational flex.";
d,n := Min([AbsoluteValue(Discriminant(Integers(k))) : k in fld]);
m := Index(Fields,fld[n]);
K := Fields[m];
P := Pts[m];
d := ZZ!d;
S_K := { p[1] : p in Factorization(d) };
S_E := Set(BadPrimes(E2));

ell,S_l,c,l2,Deltac := DescentMap(C,P);
_,swap := SwapExtension(Parent(ell));
Nell := Norm(swap(ell));
vprintf Selmer, 2: "Constant for norm condition is: c = %o.\n",c;
S_c := { p[1] : p in Factorization(ZZ!c) };
// need to compute the line on which the flex points lie.
vprintf Selmer, 3: "Primes ramifying in flex algebra are %o.\nBad Primes from E are %o.\nBad Primes from l are %o.\nBad Primes from c are %o.\n", S_K,S_E,S_l,S_c;

S := Setseq( S_K join S_E join S_l join {3} join S_c);

vprintf Selmer, 2: "Discriminant of O_K is %o.\n", d;
vprintf Selmer, 1: "Computing K(S,%o)/Q(S,%o) for the %o, with S = %o.\n",q,q, K, S;
Hc,KtoKSqQ,respFlds,respGrps,KpModqQs := LocalGlobalSelmerDiagram(K,QQ!c,S,3);
KSqQtoK := Inverse(KtoKSqQ);

if Type(Hc[1]) eq Type({}) then
  printf "Norm condition is not satisfied.\n";
  if Models then return [],[* *];
  else return -1; end if;
end if;

KernelNorm := Kernel(Hc[1]);
vprintf Selmer, 2: "Subset of K*/Q*K*3 unramified outside S and satisfying the norm condition has dimension %o.\n", #Generators(KernelNorm);
Alpha_c := Random(Hc[2]) @@ Hc[1]; // an element in KS3Q of norm c
vprintf Selmer, 3: "An element of norm c = %o is Alpha_c = %o.\n", c, Alpha_c;
KSqQ := Domain(KSqQtoK);

ComputeLocalImageAtp := function(p);
Method := "LocSol";
N := Index(S,p);
KtoKp := respFlds[N];
mod_q := KpModqQs[N]; // K_p ---> K_p* / Q_p*K_p*3
res_p := respGrps[N]; // K(S,3)/Q(S,3) --> K_p* / Q_p*K_p*3
Gp := Codomain(res_p);

DimensionOfLocalImage := function(p);

  pr := (p in {2,3}) select 1000 else 300;
  // needs fixing!
  
  Qp := pAdicField(p,pr);
  
  if HasRoot(polyForIsogKer, Qp) then
          // the kernel of phi is locally rational
          dimfromtorsion := 1;
  else dimfromtorsion := 0; end if;
  
  tamagawadiff := Valuation(TamagawaNumber(E2,p),3) - Valuation(TamagawaNumber(E1,p),3);
  DD := dimfromtorsion + tamagawadiff;
  if p eq 3 then
    DD +:= extraDimAt3;
    vprintf Selmer,2: "dimfromtorsion = %o.\ntamagawadiff = %o.\nextraDimAt3 = %o.\n", dimfromtorsion,tamagawadiff,extraDimAt3;
  end if;
  
  vprintf Selmer,2: "E'(Q_p)/phi(E(Q_p)) has dimension %o.\n", DD;
  
  injective := false;
  if HasRoot(DefiningPolynomial(K),Qp) then
      injective := true;
  end if;
  if DD eq 0 or not (p mod 3 eq 1) then
      injective := true;
  end if;
  
  if injective then
    vprintf Selmer, 2: "Local descent map is injective.\n";
    return DD;
  end if;
  
  //else: p = 1 mod 3 and DD gt 0.
  
  vprintf Selmer, 2: "Local descent map is not injectve.\n";
  
  if tamagawadiff ne 0 then
    vprintf Selmer, 3: "Kernel of local descent on E' map may be ramified.\n";
    return DD; // not necessarily sharp...
  end if;
  
  //else: p = 1 mod 3 and kernel of local descent map on E' is unramified.
  
  vprintf Selmer, 3: "Kernel of local descent on E' map is unramified.\n";
  
  if not p in S_K then
    vprintf Selmer, 3: "Kernel of local descent map on C is unramified.\n";
    return DD - 1;
  else
    vprintf Selmer, 3: "Kernel of local descent map on C is ramified.\n";
    return DD - 1;
  end if;

end function; //DimensionOfLocalImage

vprintf Selmer, 1: "Computing local data at the prime p = %o.\n", p;
dimLocalImage := DimensionOfLocalImage(p);
vprintf Selmer, 2: "Local image has dimension %o.\n", dimLocalImage;

//if testhyp then
//dimLocalImage +:= 1;
//end if;

pr := (p in {2,3}) select 1000 else 300;

if dimLocalImage lt 0 then
  return <Domain(res_p),Domain(res_p)!0>;
else
  
  vprintf Selmer, 3: "Searching for a Q_%o-point.\n",p;
  found := false;

  while not found do
    if Method eq "LocSol" then
      sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
      error if not sol, "C is not locally solvable at p = %o.\n";
    else
      R := FindQpPoint(C,p,pr);
    end if;
    R := [ QQ! R[i] : i in [1..3] ];
    if Valuation(Norm(Evaluate(ell,R)),p) lt pr/4 then
      found := true;
    end if;
  end while;

  EllofR1 := mod_q(KtoKp(Evaluate(ell,R)));
  vprintf Selmer, 3: "Found a Q_%o-point.\nl_%o(R) = %o.\n", p, p, EllofR1;
  LocalImage := < sub<Gp|0> , EllofR1 >;
  tries := 0;

 while #Generators(LocalImage[1]) lt dimLocalImage or tries lt 5 do
    // tries ge 10 there to catch spurious points.
    found := false;
    
    while not found do
      if Method eq "LocSol" then
        sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
        error if not sol, "C is not locally solvable at p = %o.\n";
      else
        R := FindQpPoint(C,p,pr);
      end if;
      R := [ QQ! R[i] : i in [1..3] ];
      if Valuation(Norm(Evaluate(ell,R)),p) lt pr/4 then
	      found := true;
      end if;
    end while;
    
    EllofR := mod_q(KtoKp(Evaluate(ell,R)));
    nim := sub<Gp| { EllofR - LocalImage[2] + b : b in Generators(LocalImage[1]) join {LocalImage[1] ! 0} } >;
    //vprintf Selmer, 3: "Found new Q_%o-point R = %o mod %o.\nl_%o(R) = %o.\n", p, [ (ZZ!r) mod p : r in R ], p, p, EllofR;
    if #Generators(nim) gt #Generators(LocalImage[1]) then
      vprintf Selmer, 3: "Found a Q_%o-point.\nl_%o(R) = %o.\n", p, p, EllofR;
      LocalImage := <nim,EllofR1>;
      vprintf Selmer, 3: "Dimension of found space is now %o.\n", #Generators(nim);
      tries := 0;
    end if;
    tries +:= 1;
    if tries gt 10 and Method eq "LocSol" then
      // IsLocallySoluble is having trouble finding points, so we try the other method.
      Method := "RHyperplane";
      vprintf Selmer, 3: "    Switching to random hyperplane method...\n";
    end if;
    if tries gt 100 then
      dimLocalImage -:= 1;
      printf "****************\nCould not find enough Q_%o-points!.\n****************\n",p;
      tries := 0;
    end if;
    if #Generators(LocalImage[1]) gt dimLocalImage then
      printf "****************\nFinding spurious Q_%o-points!\n****************\n",p;
    end if;
  end while;
  vprintf Selmer, 2: "Finished computing the local image.\n";
  if #Generators(LocalImage[1]) eq 0 then
    vprintf Selmer, 3: "l(C(Q_%o)) = %o.\n", p,LocalImage[2];
  else
    vprintf Selmer, 3: "l(C(Q_%o)) = Span(%o) + %o.\n", p, Generators(LocalImage[1]), LocalImage[2];
  end if;

  // compute preimage of l(C(Q_p)) in KSqQ.
  GpmodIm,modIm := quo<Gp|LocalImage[1]>;
  comp := hom<Domain(res_p) -> Codomain(modIm) | [ (res_p*modIm)(KSqQ.i) : i in [1..#Generators(KSqQ)] ] >;
  boo,preim := HasPreimage(modIm(LocalImage[2]-res_p(Alpha_c)),comp);
  if boo then
    PI := < Kernel(comp),preim + Alpha_c>;
    vprintf Selmer, 3: "res_%o^(-1)(l(C(Q_%o))) has dimension %o.\n",p,p,#Generators(PI[1]);
  else
    PI := "empty";
    vprintf Selmer, 3: "res_%o^(-1)(l(C(Q_%o))) is empty.\n", p,p;
  end if;
  return PI;
end if;
end function;

PreimsOfLocalIms := <KernelNorm,Alpha_c>;

IntersectCosets := function(V,W);
    V1 := V[1];
    v1 := V[2];
    V2 := W[1];
    v2 := W[2];
    // we want to find  ( V1 + v1 ) meet ( V2 + v2)
    VW,i1,i2 := DirectSum(V1,V2);
    p1 := Inverse(i1); p2 := Inverse(i2);
    dif := hom< VW -> KSqQ | [ -p1(VW.i) : i in [1..#Generators(V1)] ] cat [ p2(VW.i) : i in [#Generators(V1)+1..#Generators(VW)] ] >;
    if HasPreimage(v1-v2, dif) then
      alpha := v1 + p1((v1-v2) @@ dif);
      return <V1 meet V2,alpha>;
    else
      return "empty";
    end if;
  end function;


vprintf Selmer, 2: "\nComputing Local images.\n\n";

for p in S do
  PI := ComputeLocalImageAtp(p);
  if Type(PI) eq MonStgElt then
    if Models then
      return [],[* *];
    else
      return -1;
    end if;
  end if;

  PreimsOfLocalIms := IntersectCosets(PreimsOfLocalIms,PI);
  if Type(PreimsOfLocalIms) eq MonStgElt then
    if Models then
      return [],[* *];
    else
      return -1;
    end if;
  else
    vprintf Selmer, 3: "Dimension is now %o.\n", #Generators(PreimsOfLocalIms[1]);
  end if;
end for;

vprintf Selmer, 1: "\nFake phi-Selmer set has dimension %o.\n", #Generators(PreimsOfLocalIms[1]);

if not Models then
  return #Generators(PreimsOfLocalIms[1]);
end if;

vprintf Selmer, 1: "Computing models and 'unfaking'.\n";
Sel_0 := PreimsOfLocalIms[1];
sel := PreimsOfLocalIms[2];

SelK := [ NiceRepresentativeModuloPowers(KSqQtoK(g + sel),3) : g in Sel_0 ];
//Representatives for the fake Selmer set in K*

PF<z1,z2,z3> := PolynomialRing(K,3);
ell := PF ! ell;
OK := LLL(Integers(K));
// a generic element of K
z := OK.1*z1 + OK.2*z2 + OK.3*z3;
_,PFswap := SwapExtension(PF);
Nz := Norm(PFswap(z));
zcube := z^3;
Q1 := PolynomialRing(QQ);
F6<u1,u2,u3,z1,z2,z3> := PolynomialRing(K,6);
Q6<x,y,z,X,Y,Z> := PolynomialRing(QQ,6);

P2 := AmbientSpace(C);
Cubics := [];
Coverings := [* *];

for d in SelK do
  // defining equations for the cubic are:
  // ell(u1,u2,u3) = d*z^3 and u_n = e*Nz, where e is a cube root of N(d)/c and d in Sel_fake.

  e := Roots(Q1.1^3 - Norm(d)/(c));
  if #e eq 0 then
    vprintf Selmer, 1: "norm condition failed for %o", d;

  else
    e := e[1,1];
    eq1 := Evaluate(ell,[u1,u2,u3]) - d*Evaluate(zcube,[z1,z2,z3]);
    eq2 := Evaluate(l2,[u1,u2,u3]) - e*Evaluate(Nz,[z1,z2,z3]);
    EqsF6 := Reduce({eq1,eq2});
    //Now write them in a basis over Q
    _,Swapper := SwapExtension(F6);
    EqsQ := {};
    for equa in EqsF6 do
	    EqsQ := EqsQ join { Evaluate(P,[x,y,z,X,Y,Z]) : P in Eltseq(Swapper(equa)) };
    end for;
    rEqsQ := Reduce(EqsQ);
    D := Curve(P2,Evaluate(rEqsQ[4],[0,0,0,P2.1,P2.2,P2.3]));
    pi := [ -Evaluate(rEqsQ[j],[0,0,0,P2.1,P2.2,P2.3]) : j in [1..3] ];
    pi1 := map<D -> C | pi>;

    Dmin,TM := Minimize(GenusOneModel(D));
    Dmin,TM2 := Reduce(Dmin);
    if IsLocallySoluble(Dmin) then
      TM := TM2 * TM;
      rm := map<Curve(Dmin) -> D | [ &+[TM`Matrix[i,j]*P2.i : i in [1..3] ] : j in [1..3] ] >;
      pi := rm * pi1;
      D := Curve(Dmin);
      pi := map< D -> C | DefiningEquations(pi) >;
      Cubics cat:= [D];
      Append(~Coverings,pi);
    end if; //else Dmin not everywhere locally solvable...

  end if;
end for;

vprintf Selmer, 1: "Dimension of phi-Selmer Set is %o.\n",
(#Cubics gt 0) select Ilog(3,#Cubics) else -1;

return Cubics,Coverings;

end function;



