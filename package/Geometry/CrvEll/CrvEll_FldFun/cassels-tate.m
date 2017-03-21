freeze;

 /**************************************************************************
 *                                                                         *
 *            CASSELS-TATE PAIRING ON THE 2-SELMER GROUP                   *
 *              FOR E/K OVER A RATIONAL FUNCTION FIELD                     *
 *                                                                         *
 *                  Steve Donnelly, December 2007.                         *
 *                                                                         *
 *   The algorithm is given in detail in notes available from me.          *
 *   The only nontrivial computation involved is solving a conic over K.   *
 *                                                                         *
 *   This is a virtual a copy of my *old* code over Q                      *
 *   (the first algorithm I came up with, not the fast one)                *
 *                                                                         *
 *   It's done explicitly over FldFunRat (no linear extension),            *
 *   I don't plan on extending it to general FldFun any time soon.         *
 *                                                                         *
 **************************************************************************/

debug := true; // switched on for the moment (until more tesing is done)

/************** BUGS ***********************************

// Consistently returns 1 ... need more smallprimes? or error in HilbertSymbol?
SetSeed(3576757106, 15); // Randomness in TwoDescent
SetVerbose("CasselsTate",1);
F := FunctionField(GF(5)); t := F.1;
E := EllipticCurve([1,t-3,t-1,1,t^2]);
td := TwoDescent(E); td;
CasselsTatePairing(td[3],td[3]);

// Inconsistently gives 1 ... (t+2) vacillates between 0 and 1
SetSeed(6,15); SetVerbose("CasselsTate",1);
F := FunctionField(GF(5)); t := F.1;
E := EllipticCurve([t,t^3-2,t-1,1,t^2]);
td := TwoDescent(E); td;
CasselsTatePairing(td[1],td[1]);

*******************************************************/

/**********************************
*  Basic stuff for FldFunRatElts  *
**********************************/

// This is needed in order to run code in ellmodel.m for E over a FldFunRat

intrinsic '*'(r::FldRatElt, f::FldFunElt) -> FldFunElt
{Product of r and f, as an element of Parent(f)}
  F := Parent(f);
  n := F! Numerator(r);
  d := F! Denominator(r);
  require not IsZero(d) : "Denominator is not prime to the characteristic";
  return n/d*f;
end intrinsic;

// These are used in this file.
// Galois action on a residue ring element 

intrinsic '^'(f::RngMPolResElt, rho::Map) -> RngMPolResElt
{The element obtained by applying rho to the coefficients of f}
  coeffs := Coefficients(f);
  mons := Monomials(f);
  if debug then assert f eq &+[ coeffs[i]*mons[i] : i in [1..#coeffs] ]; end if;
  coeffs_rho := [ rho(c) : c in coeffs ];
  return &+[ coeffs_rho[i]*mons[i] : i in [1..#coeffs_rho] ];
end intrinsic;

// Galois action on a function field element

intrinsic '^'(f::FldFunFracSchElt, rho::Map) -> FldFunFracSchElt
{The function field element obtained by applying rho to the coefficients of f}
  FF := Parent(f);
  X := Scheme(FF);
  R_X := CoordinateRing(X);
  num := Numerator(f);
  den := Denominator(f);
  num_rho := num^rho;
  den_rho := den^rho;
  return FF!num_rho/FF!den_rho;
end intrinsic;

function DenominatorFldFunElt(x) // FldFunElt -> RngUPolElt
  while not ISA( Type(Parent(x)), FldFunRat) do 
    error if Type(Parent(x)) ne FldFun, 
         "We're assuming we have a tower of FldFuns over a FldFunRat";
    x := Norm(x);
  end while;
  return Denominator(x);
end function;

// For a poly or FldFunRatElt f, returns the set of irred monic polys dividing f

function prime_divisors(f) 
  assert not IsZero(f);
  if ISA(Type(f), FldFunRatElt) then
    assert f eq Parent(f)! Numerator(f);
    f := Numerator(f); 
  end if;
  ans := { tup[1] : tup in Factorization(f) };
  assert &and[ IsMonic(pol) and not IsZero(pol) : pol in ans ];
  return ans;
end function;

// Given a sequence of RngMPolElts, return the corresponding sequence
// of elements in the 'target' RngMPol, obtained by applying 'coeff_map' 
// to the coefficients

function coerce_pols(seq, coeff_map, target) 
  ans := [target| ];
  for pol in seq do 
    mons := Monomials(pol);  coeffs := Coefficients(pol);
    pol1 := &+[target| coeffs[i]@coeff_map * target!mons[i] : i in [1..#mons]]; 
    Append( ~ans, pol1);
  end for;
  return ans;
end function;

intrinsic Valuation(f::FldFunRatUElt, p::RngUPol) -> RngIntElt
{Valuation of f at the prime ideal p}
  pi := Generator(p);
  return Valuation(f, pi);
end intrinsic;

/********************************
*  Finding a quadratic point    *
*********************************/

// Given a CrvHyp C : y^2 = quartic(x), return a point
// with x coordinate in BaseField(C), and return the field F of the point.
// If avoid2tors is true, then do not return a point whose image 
// under the (2-covering) map CcovE lies in E[2] (unless it's a rat'l point!).

function quadratic_point(C, CcovE : avoid:={}, avoid2tors:=true) 
//    -> Pt, FldFun
 
  const_pts := Points(C : Bound:=0); // Points is quick for degree 0 only 
  if not debug and not IsEmpty(const_pts) then 
    return const_pts[1], BaseField(C); end if;
 
  K := BaseField(C); t := K.1;  assert ISA(Type(K), FldFunRat);
  k := BaseField(K);  assert IsFinite(k) and IsOdd(Characteristic(k));
  kT := PolynomialRing(k); T :=kT.1;  assert Integers(K) eq kT; 
  quartic,h := HyperellipticPolynomials(C); assert IsZero(h) and Degree(quartic) eq 4;
  quartic_coeffs := ChangeUniverse(Coefficients(quartic), kT);
  _<X,Z> := PolynomialRing(kT,2);
  homquartic := &+[ c[i+1]*X^i*Z^(4-i) : i in [0..4]] where c is quartic_coeffs;
  A := LeadingCoefficient(quartic);
  N := 100;  // Number of points to collect (and then choose smallest discriminant)

  // Choose a set of pairs [X,Z] of elements of kT to plug in for X and Z
  if #k gt N then
    XZs := {}; 
    while #XZs lt N do 
      XZs join:= {[Random(k)*T+Random(k), T+Random(k)]}; end while;
  elif #k^5 le 2*N then
    XZs := {[k2*T^2+k1*T+k0, T^2+l1*T+l0] : k2,k1,k0,l1,l0 in k};
  elif #k^4 le 2*N then
    XZs := {[k2*T^2+k1*T+k0, T+l0] : k2,k1,k0,l0 in k};
  elif #k^3 le 2*N then
    XZs := {[k1*T+k0, T+l0] : k1,k0,l0 in k};
  elif #k^2 le 2*N then
    XZs := {[k1*T+k0, 1] : k1,k0 in k};
  elif #k le 2*N then
    XZs := {[T+k0, 1] : k0 in k};
  end if;
  
  discs := [];
  for XZ in XZs do 
    Ysquared := Evaluate(homquartic, XZ);
    sqfact := SquarefreeFactorization(Ysquared);
    squarefreepart := &*[kT| tup[1] : tup in sqfact | IsOdd(tup[2]) ];  assert IsMonic(squarefreepart);
    lc := LeadingCoefficient(Ysquared);  if IsSquare(lc) then lc := 1; end if;
    D := lc*squarefreepart; 
    if D eq 1 then
      Yissqr, YY := IsSquare(Ysquared);  assert Yissqr;
      return C(K)! [XZ[1], YY, XZ[2]], K; end if;
    Append( ~discs, [*XZ, Ysquared, D*]);
  end for;
  vprintf CasselsTate,2: 
         "Some quadratic fields where this curve has a point are:\n %o\n", [seq[3] : seq in discs];
  if debug then  // don't allow disc = 1 (that's too easy, we want to test the code!)
    ones := Reverse([i : i in [1..#discs] | discs[i][3] eq 1]);
    for i in ones do Remove(~discs, i); end for; end if;
  
  // now find the smallest disc that does not give a point mapping to E[2]
  Sort( ~discs, func<seq1,seq2| Degree(seq1[3])-Degree(seq2[3]) >);
  vprintf CasselsTate: 
         "Discriminants of possible quadratic fields have degrees %o\n", {Degree(seq[3]) : seq in discs};
  for i := 1 to #discs do  
    XZ, Ysquared, D := Explode(discs[i]);  
    bool, S := IsSquare(Ysquared div D);  assert bool;
assert D*S^2 eq Ysquared;
    L := ext< K | Polynomial([K| -D, 0, 1]) >;  
    pt := C(L)! [XZ[1], L.1*S, XZ[2]];
    if D in avoid or avoid2tors and 2*CcovE(pt) eq Codomain(CcovE)!0 then 
      continue; end if;
    return pt, L;
  end for;
end function;

// Find an approximation to a random local solution at the place pl.

// To create completions we have to use a stupid linear extension, 
// and to avoid creating that multiple times, we create everything in
// the calling function.  Here 'pl' is a place of the linear extension.
/* [ this fragment was for testing?? ]
  FF := ext< F | Polynomial([F|-1,1]) >;
  OFF := MaximalOrderFinite(FF);
  pl := Place(ideal<OFF|t+2>);
  coeffnegval := Max([0] cat [-Valuation(c,pl) : c in Coefficients(DefiningEquation(C))]);
  FFpl, completion_map := Completion(FF,pl : Precision:=20+coeffnegval);
*/
function local_point(C, pl, completion_map)  
  K := Domain(completion_map);
  Kpl := Codomain(completion_map);
  if BaseRing(C) cmpne K then C := ChangeRing(C,K); end if;
  Cpl := DefiningEquation(BaseChange(C, completion_map));
  k := BaseRing(Kpl);  assert IsFinite(k);
  pi := UniformizingElement(Kpl);
  
  bool, pt := IsLocallySolvable(C, pl : completion_map:=completion_map);
  error if not bool, "The given curve is not locally solvable"; 

  // try nearby x-values (because we need more precision, 
  //                      and we need randomness to avoid bad points)
  X0 := ChangePrecision(pt[1], Infinity());  valX0 := Valuation(pt[1]);   
  Z0 := ChangePrecision(pt[3], Infinity());  valZ0 := Valuation(pt[3]);
  v0 := Min(valX0,valZ0);  
  while Random(1) eq 1 do v0 +:= 1; end while; // add a random integer to v0
  for v := v0 to 1000 do 
   if v gt v0+30 then 
vprint CasselsTate: "some problem in local_point, trying again";
                      return local_point(C, pl, completion_map); end if;
   for i := 1 to 100 do 
    repeat kk := Random(k); until kk ne 0;
    delta := kk * pi^v; 
    if valZ0 le valX0 then 
      Z1 := Z0;  X1 := X0 + delta;
    else
      X1 := X0;  Z1 := Z0 + delta;
    end if;
    issqr, Y1 := IsSquare( - Evaluate( Cpl, [X1,0,Z1]) );
    if issqr then 
      assert Valuation(Evaluate( Cpl, [X1,Y1,Z1])) gt 15;
      return [X1,Y1,Z1]; end if;
  end for; end for;
end function;

// "evaluate" a function field element at a "point" that is not (quite) on the curve!

function plug_in(f, pt) 
  assert FFPatchIndex(Scheme(Parent(f))) eq 1;
  num := Numerator(f);
  den := Denominator(f);
  PAA := OriginalRing(Parent(num));
  return Evaluate( PAA!num, pt)/Evaluate( PAA!den, pt);
end function; 

// Return an isomorphism C_F -> E_F, sending pt to O,
// between the base-changed curves, where F is the field of definition of pt.

function trivialization(C, pt, E)  //  -> MapSch
  F := Ring(Parent(pt));
  if F ne BaseField(C) then C := BaseChange(C,F); end if;
  if F ne BaseField(E) then E := BaseChange(E,F); end if;
  assert BaseField(C) eq BaseField(E);
  EE, CtoEE := EllipticCurve(C, pt);
  bool, EEtoE := IsIsomorphic(EE,E);
  error if not bool, "The given curves do not seem to be isomorphic as curves";
  return CtoEE*EEtoE;
end function;

/*********************************************************************************/

function cassels_tate_pairing_FldFunRat(C,D : avoid:={})
 time0 := Cputime();
  K := BaseField(C);
  k := BaseField(K);  kT := PolynomialRing(k);  T := kT.1;
  C := SimplifiedModel(C);
  D := SimplifiedModel(D);
  E, CcovE := AssociatedEllipticCurve(C);
  _, DcovE := AssociatedEllipticCurve(D : E:=E );
  
  KK := ext< K | Polynomial([K| -1,1]) >; // always use this linear extension (to avoid creating too many maps)
  OKK := MaximalOrderFinite(KK);
  CKK := BaseChange(C,KK);

  // TO DO: is this bit appropriate for the function field case?
  // (think about the assumption on automorphisms we need in the trick for getting P)
  j := jInvariant(E);
  if j eq 1728 then avoid join:= {-1};
  elif j eq 0 then avoid join:= {-3}; end if;
  // because we want the only auts of E over the quad fields to be +-1
  PC, FC := quadratic_point(C, CcovE : avoid:=avoid);
  PD, FD := quadratic_point(D, DcovE : avoid:=avoid join {K!(FC.1^2)});

  if FC eq K or FD eq K then return 0; 
  elif IsSquare(K!(FC.1^2)/K!(FD.1^2)) then 
    if IsIsomorphic(C,D) then return 0; end if;
    error "Same fields, can't deal with it!";
  end if;

  // TO DO: make D the one with the smaller discriminant ???
  //   if Discriminant(FC) lt Discriminant(FD) then 
  //     C,D, PC,PD, FC,FD := Explode([* D,C, PD,PC, FD,FC *]); end if;
  vprint CasselsTate : "The quadratic fields are: \n", FC, "", FD;
  vprintf CasselsTate: "Time to find quadratic points: %o \n", Cputime(time0);

 time0 := Cputime();
  CtoE_FC := trivialization(C, PC, E);  // defined over FC
  if debug then DtoE_FD := trivialization(D, PD, E); end if;
  vprintf CasselsTate: "Trivialization: %o \n", Cputime(time0);

 time0 := Cputime();
  // Set up biquadratic field L := FC*FD
  L := ext< FD | ChangeRing(DefiningPolynomial(FC),FD) >;
  if debug then assert K!(L.1^2) eq K!(FC.1^2); end if;
  FCtoL := hom< FC -> L | L.1 >;
  
  // Let Gal(L/K) = <sigma, tau>, where sigma fixes FC and tau fixes FD.
  tau := hom< L->L | -L.1 >;
  sigmaFD := hom< FD->FD | -FD.1 >;
  sigma := hom< L->L | l:-> L! [sigmaFD(cc) : cc in Eltseq(l)] >;
  vprintf CasselsTate: "Setting up fields and Galois groups: %o \n", Cputime(time0);
  
 time0 := Cputime();
  // tricky way of quickly getting P := PD - PD^sigma (or -P)
  // (we can't just get it by evaluating DtoE_FD at PD^sigma because
  // it is not defined there, and extending the map takes too long)
  // Claim: PD - PD^sigma = phi(DcovE(PD)) for some automorphism phi of E defined over FD.
  // We have arranged that the only such automorphisms are +-1.  Likewise for FC.
  P := DcovE(PD);
  // same for R := PC^sigma - PC
  R := CcovE(PC);
  // need to get the sign of R right:
  imR := [ Evaluate(eqn, Eltseq(R)) : eqn in DefiningEquations(Inverse(CtoE_FC)) ];
  if imR eq [0,0,0] then 
    R := -R;
    imR := [ Evaluate(eqn, Eltseq(R)) : eqn in DefiningEquations(Inverse(CtoE_FC)) ];
  end if;
  assert FCtoL([imR[1]/imR[3], imR[2]/imR[3]^2, 1]) eq [ (coord@FCtoL@tau) : coord in Eltseq(PC)];

  if debug then   // do it the old way too, and compare
    plc2 := Pullback(Inverse(CtoE_FC), Place( Domain(CtoE_FC)! [PC[1],-PC[2],1] ));
    R_old := E(FC)! RepresentativePoint(Support(plc2)[1]);  // this = PC^sigma - PC
    plc1 := Pullback(Inverse(DtoE_FD), Place( Domain(DtoE_FD)! [PD[1],-PD[2],1] ));
    P_old := - E(FD)! RepresentativePoint(Support(plc1)[1]);  // this = PD - PD^sigma 
    assert R_old eq R;
    assert P_old in {P, -P};
  end if;
  vprintf CasselsTate: "Mapping tricky points to E: %o \n", Cputime(time0);

 time0 := Cputime();
  E_L := BaseChange(E, L);  PolE_L := CoordinateRing(Ambient(E_L));
  C_L := BaseChange(C, L);  PolC_L := CoordinateRing(Ambient(C_L));

  vprint CasselsTate: "fC: "; 
  CtoE_Lmap := map< C_L -> E_L | coerce_pols( DefiningEquations(CtoE_FC), FCtoL, PolC_L), 
                                 coerce_pols( DefiningEquations(Inverse(CtoE_FC)), FCtoL, PolE_L)
                               : Check:=false >;
  FFE_L<Ex,Ey> := FunctionField(E_L);      // Note: want to recode everything without using
  FFC_L<Cx,Cy> := FunctionField(C_L);      // function fields at all (just use nums and denoms)
  fE_num := E_L.1 - P[1]/P[3]*E_L.3;
  fE_denom := E_L.3;
  fE := Ex - P[1]/P[3];  // = x_E - x_E(P) 
  CtoE_L := [Evaluate(DefiningEquations(CtoE_Lmap)[i],[C_L.1,C_L.2,C_L.3]) : i in [1..3]];
  fC_num := CtoE_L[1] - P[1]/P[3]*CtoE_L[3];
  fC_denom := CtoE_L[3];
  fC := Evaluate(CtoE_L[1],[Cx,Cy,1]) / Evaluate(CtoE_L[3],[Cx,Cy,1]) - P[1]/P[3];              
   // = Pullback(CtoE_L,fE) and is really defined over F_C

  vprint CasselsTate: "gC: "; 
  // Construct gE directly, to have divisor [P+R]+[O]+[-P-R] over [P]+[R]+[-P-R]
  P := E(L)! P;
  R := E(L)! [c@FCtoL : c in Eltseq(R)];
  Px,Py,Pz := Explode(Eltseq(P));
  Rx,Ry,Rz := Explode(Eltseq(R));
  PplusRx,_,PplusRz := Explode(Eltseq(P+R));
  assert Pz eq 1 and Rz eq 1 and PplusRz eq 1;
  gE_num := E_L.1 - PplusRx*E_L.3;  // vertical line through P+R
  gE_denom := (Px-Rx)*E_L.2 - (Py-Ry)*E_L.1 + (Py*Rx-Px*Ry)*E_L.3;  // line through P and R
  if debug then assert Evaluate(gE_denom, Eltseq(-P-R)) eq 0; end if; 
  gE := Evaluate(gE_num, [Ex,Ey,1]) / Evaluate(gE_denom, [Ex,Ey,1]);
  //gC := Pullback(CtoE_L, gE);
  gC_num := Evaluate(gE_num,CtoE_L);
  gC_denom := Evaluate(gE_denom,CtoE_L);
  gC := Evaluate(gC_num, [Cx,Cy,1]) / Evaluate(gC_denom, [Cx,Cy,1]);  
  if debug then
    assert fE eq FFE_L! (E_L.1/E_L.3) - P[1]/P[3];  
    assert gE eq FFE_L! (gE_num/gE_denom);
    assert fC eq FFC_L! (CtoE_L[1]/CtoE_L[3]) - P[1]/P[3]; 
    assert gC eq FFC_L! (gC_num/gC_denom);  // this is the really awful one
  end if;
  vprintf CasselsTate: "Total time spent messing around: %o \n", Cputime(time0);

 time0 := Cputime();
  // Now arrange that gC^(sigma*tau)/gC = fC/fC^tau ...
  // We know that LHS/RHS is a constant, and will rescale gC 
  // by an element of L to make the constant 1.
  // We determine the constant by evaluating the functions at pt:=P-R+PC,
  // or equivalently, evaluating their translations to E at P-R,
  // which after some manipulation are given as follows:
  const := Evaluate(fE_num, Eltseq(P-2*R)) / Evaluate(fE_denom, Eltseq(P-2*R))  // = fC^tau(pt)
         * Evaluate(fE_denom, Eltseq(P-R)) / Evaluate(fE_num, Eltseq(P-R))      // = fC(pt)
        * (Evaluate(gE_num, Eltseq(-P+2*R)) / Evaluate(gE_denom, Eltseq(-P+2*R))) @sigma@tau 
                                                                                // = gC^(sigma*tau)(pt)
        * Evaluate(gE_denom, Eltseq(P-R)) / Evaluate(gE_num, Eltseq(P-R));      // = gC(pt) 
if debug then
 const0 := Evaluate(fE, E_L!(P-2*R))                // = fC^tau(pt)
         / Evaluate(fE, E_L!(P-R))                  // = fC(pt)
         *(Evaluate(gE, E_L!(-P+2*R)) @sigma@tau)   // = gC^(sigma*tau)(pt)
         / Evaluate(gE, E_L!(P-R));                 // = gC(pt) 
 assert const eq const0;
end if;
  // solve sigmatau(cc) = const*cc for cc in L, by linear algebra:
  const_sigmatau := const @sigma @tau;
  assert const*const_sigmatau eq 1;
  c1 := (const + const_sigmatau)/2;
  c2 := (const - const_sigmatau)/2;
  dd := FC.1@FCtoL * L!FD.1;
assert const eq c1 + c2*dd;
assert c1^2 - dd^2*c2^2 eq 1;
  b := 1+c1 - c2*dd;
  if c2 eq 0 then   // special case
    assert const^2 eq 1; 
    if const eq 1 then b := 1; else b := FD.1; end if;
  end if;
if debug then assert b@sigma@tau eq const*b; end if;
  gC /:= b; 
  gE /:= b; 
  gC_denom *:= b;
  gE_denom *:= b;
  // Should now have (gC^sigma)^tau/gC eq fC/fC^tau;

  // We know that gC*gC^tau is a constant, and we will make the constant 1.
  // In fact the constant belongs to K, because the previous step implies that
  // gC*gC^tau is fixed by sigma
  // To get the constant, evaluate at -P+PC, hoping it's not a zero or pole
  // ... after some manipulation, this value equals:
  const := Evaluate(gE_num, Eltseq(-P)) / Evaluate(gE_denom, Eltseq(-P))
        * (Evaluate(gE_num, Eltseq(-P+R)) / Evaluate(gE_denom, Eltseq(-P+R))) @tau;
  const := K! const;
  assert const ne 0;
  vprintf CasselsTate: "   ...      More messing around: %o \n", Cputime(time0);

  vprintf CasselsTate: "Solving NormEquation:   Norm x = %o \n", const;
  // first try solving it in Fst := K(dd) = fixed field of sigma*tau
//Fst := ext< K | Polynomial([K| -dd^2, 0, 1]) >;
//bool1, sols := NormEquation(Fst, const);
  conic := Conic([K| 1, -dd^2, -const]);  
  bool1, sol := HasPoint(conic);
  if bool1 then 
    error if sol[3] eq 0, "Oops ... HasPoint came up with a pt at infinity";
    cc := (c1 + dd*c2)/c3  where c1,c2,c3 := Explode(Eltseq(sol));
    vprintf CasselsTate: "Found solution in quadratic subfield: \n  %o\n", cc;
  else 
    vprint CasselsTate: "\n\nInteresting example!!!!",
         "\nThe norm equation is not solvable over the middle quadratic field.\n";
error "Please send this example to magma-bugs@maths.usyd.edu.au";
    bool2, sols := NormEquation(L, const);
    error if not bool2, "The norm equation that we need to solve is not solvable";
    cc := sols[1];
    vprintf CasselsTate,2: "  Solution is: %o\n", cc;
  end if;
  gE /:= cc;
  gC /:= cc;
  gE_denom *:= cc;
  gC_denom *:= cc;
  // Should now have gC*gC^tau eq 1;
  
  if not bool1 then 
    vprintf CasselsTate: "Fixing things so bool1 is true: ";
    // Now we need to arrange that gC*gC^sigma = fC^tau/fC 
    // We know that LHS/RHS is a constant, and will rescale fC 
    // by an element of FC to make the constant 1.
    // Evaluate the functions by evaluating their translations to E at pt = -P-R 
    PL := E_L!P;
    RL := E_L!R;
    const_L := Evaluate(gE, -P-R)         // = 0/0 unfortunately
            * (Evaluate(gE_num, Eltseq(P-R)) / Evaluate(gE_denom, Eltseq(P-R))) @sigma 
            *  Evaluate(fE_num, Eltseq(-P-R)) / Evaluate(fE_denom, Eltseq(-P-R))
            *  Evaluate(fE_denom, Eltseq(-P-2*R)) / Evaluate(fE_num, Eltseq(-P-2*R));
    const := const_L @@ FCtoL;
    assert FCtoL(const) eq const_L;
    assert Norm(const) eq 1;
    // solve tau(b) = const*b for b in FC, by linear algebra:
    c1, c2 := Explode(Eltseq(const));
    b := 1+c1 - c2*FC.1;
    if c2 eq 0 then   // special case
      assert const^2 eq 1; 
      if const eq 1 then b := 1; else b := FC.1; end if;  
    end if;
    fE *:= b;
    fC *:= b;
    fE_num *:= b;
    fC_num *:= b;
    assert const_L eq b@tau/b; 
  end if;

  if debug then 
    vprintf CasselsTate: "Checking we have a cocycle ... ";
    vtime CasselsTate: 
    assert gC*gC^tau eq 1 and fC eq fC^sigma and gC*gC^sigma eq fC^tau/fC; 
  end if;
/* alternative, but not quicker
time assert fC_num*fC_denom^sigma - fC_denom*fC_num^sigma in Ideal(C_L);
time assert gC_num*gC_num^tau - gC_denom*gC_denom^tau in Ideal(C_L);
*/

 time0 := Cputime();
  // Now we have a 2-cocycle in L(C)* with values 
  // (on 1, sigma, tau, sigma*tau):
  // cocyc := [ [ 1,  1,        1,  1       ], 
  //            [ 1, fC,        1, fC       ],
  //            [ 1, gC,        1, gC       ],
  //            [ 1, fC^tau/gC, 1, fC^tau/gC] ] 

  // Finally we adjust by a 2-coboundary in L(C)* so that
  // the cocycle depends only on sigma 
  // (ie is in the image of inflation from <1,sigma>):
  // Solve gg^tau/gg = gC, for gg in L(C), which is possible since gC*gC^tau = 1, 
  // and divide by the coboundary of the cochain:
  // ( c_1 = c_tau = 1, c_sigma = c_sigmatau = gg ).
  // Then the values of the resulting 2-cocycle (on 1, sigma) are:
  //   1   1 
  //   1   fC/(gg*gg^sigma)
/* Efficient version:
  gC_denom_tau := gC_denom^tau;  // first rationalize the denominator
  gC_num *:= gC_denom_tau;
  gC_denom *:= gC_denom_tau;
assert gC_denom^tau eq gC_denom;
assert FFC_L! (gC_num/gC_denom) eq gC;
  gC_num_tau := gC_num^tau;
  g0 := (gC_num + gC_num_tau)/2;
  g1 := (gC_num - gC_num_tau)/(2*FC.1);
  gg := gC_denom+g0 - g1*FC.1;
time  assert gg^tau*gC_denom - gg*gC_num in Ideal(C_L);
  num := fC_num*gC_denom*gC_denom^sigma;
  den := fC_denom*gg*gg^sigma;
  cocyc := num/den;
//cocyc := fC_num/fC_denom/(gg*gg^sigma)*gC_denom*gC_denom^sigma;
  lcm_coeff_denoms := LCM([ Denominator(coeff) : coeff in Coefficients(num) cat Coefficients(den) ]);
  gcd_num_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(lcm_coeff_denoms*num) ]);
  gcd_den_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(lcm_coeff_denoms*den) ]);
*/
  if true or debug then  // Old version:
    gC_tau := gC^tau;
    g0 := (gC + gC_tau)/2;
    g1 := (gC - gC_tau)/(2*FC.1@FCtoL);
  //assert g0^tau eq g0 and g1^tau eq g1 and gC eq g0 + g1*L.1;
  //assert g0^2-L.1^2*g1^2 eq 1;
    gg := 1+g0 - g1*FC.1@FCtoL;
    assert gg^tau/gg eq gC;
    gg_sigma := gg^sigma;
    cocyc0 := fC/(gg*gg_sigma);  // the value at (sigma,sigma) ... all other values are 1
    assert cocyc0^tau eq cocyc0 and cocyc0^sigma eq cocyc0;
    num := Numerator(cocyc0);  
    den := Denominator(cocyc0);
    PR<x_L,y_L> := OriginalRing(Parent(num));
    lcm_coeff_denoms := LCM([ DenominatorFldFunElt(coeff) : coeff in Coefficients(PR!num) cat Coefficients(PR!den) ]);
    num := lcm_coeff_denoms*PR!num;
    den := lcm_coeff_denoms*PR!den;
    gcd_num_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(num) ]);
    gcd_den_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(den) ]);
cocyc := cocyc0;
 //   assert FFC_L! cocyc eq cocyc0;
  end if;

  vprintf CasselsTate: "Step 4 (deflating): %o \n", Cputime(time0);

 time0 := Cputime();
  // Which primes do we need to look at???
  ramprimesD := prime_divisors(K!(FD.1^2));
  ramprimesC := prime_divisors(K!(FC.1^2));
  badrednprimesC := prime_divisors(Discriminant(GenusOneModel(C)));
  badrednprimesD := prime_divisors(Discriminant(GenusOneModel(D)));
  bad_cocyc_primes := prime_divisors(gcd_num_coeffs) join prime_divisors(gcd_den_coeffs);
  vprint CasselsTate : "Ramified primes for FD are", ramprimesD, "Ramified primes for FC are", ramprimesC;
  vprint CasselsTate : "Bad reduction primes for C and D are", badrednprimesC, badrednprimesD;
  vprint CasselsTate : "Bad primes for the 2-cocycle are", bad_cocyc_primes;
//TO DO: which smallprimes do we need? (anyway throw in low degree pols for debug)
smallprimes := true and #k lt 20 select {T+c0 : c0 in k} else {};
/*
smallprimes join:= {pol : pol in pols | IsIrreducible(pol)} where pols is {T^2+c1*T+c0 : c0,c1 in k};
smallprimes join:= {pol : pol in pols | IsIrreducible(pol)} where pols is {T^3+c2*T^2+c1*T+c0 : c0,c1,c2 in k};
smallprimes join:= {pol : pol in pols | IsIrreducible(pol)} where pols is {T^4+c3*T^3+c2*T^2+c1*T+c0 : c0,c1,c2,c3 in k};
smallprimes join:= {pol : pol in pols | IsIrreducible(pol)} where pols is 
                                        {T^5+&+[(eval("c"*IntegerToString(i)))*T^i : i in [0..4]] : c0,c1,c2,c3,c4 in k};
*/
  reallybadprimes := ramprimesD join badrednprimesC join bad_cocyc_primes join smallprimes;
  badprimes := reallybadprimes join badrednprimesD join ramprimesC;
  badprimes := Sort( SetToSequence(badprimes), func<p1,p2| Degree(p1)-Degree(p2) >);
  badprimes := [ ideal<kT|p> : p in badprimes ]; 
  vprintf CasselsTate: "Getting bad primes: %o \n", Cputime(time0);
  
 time0 := Cputime();
  quarticC := HyperellipticPolynomials(C);
  ans := 0;
  vprint CasselsTate : "Calculating local invariants";
  num_fails := 0;
  for p in badprimes do
    pp := Generator(p);
    pl := Place(ideal< OKK | OKK!pp >);
    _,toKKpl := Completion(KK,pl);
    // TO DO: if p splits in FD, then apparently the invariant is trivial
    if false then
      //invt := 1;
    else
      invts := [];  // do it for several different local points, as a check
      while #invts lt (debug and Degree(pp) le 13 select 6 else 1) do 
        // evaluate cocyc at a local point, check value is not too close to 0
        pt := local_point(CKK, pl, toKKpl);  
        assert not IsWeaklyZero(pt[3]);
        pt := [pt[1]/pt[3], pt[2]/pt[3]];
        pt := [K| cc@@toKKpl : cc in pt];
        cocyc_val := K! plug_in(cocyc, pt);
        if Valuation(cocyc_val, p) gt 6 then  // TO DO: This sometimes happens for all pt's
           num_fails +:= 1;
           if num_fails ge 10 then 
             printf "Cocycle value has valuation %o (too large), trying again...\n", Valuation(cocyc_val, p);     
             return cassels_tate_pairing_FldFunRat(D,C : avoid:=avoid join {K!(FC.1^2),K!(FD.1^2)}); end if; 
           continue; end if;
        // local invariant:
      //if e eq 1 then   // unramified local extension (TO DO!!)
        if false then 
          invt := Valuation(cocyc_val, p) mod 2;
        else             // ramified local extension
          hilb := HilbertSymbol(cocyc_val, K!(FD.1^2), p);
          invt := (1-hilb) div 2;  // convert from {1,-1} to {0,1}
        end if;
        Append(~invts, invt);
      end while;
      if debug then 
        assert &and[invt eq invts[1] : invt in invts];  // check that we got the same every time
        if pp notin reallybadprimes then assert invt eq 0; end if;  // this prime should be irrelevant
      end if;
    end if;
    vprintf CasselsTate: "%o : invariant = %o\n", pp, invt;
    ans := (ans + invt) mod 2;
  end for;
  vprintf CasselsTate: "Local invariants: %o \n", Cputime(time0);
  return ans;
end function;
