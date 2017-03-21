freeze;

 /************************************************************************
 *                                                                       *
 *     CASSELS-TATE PAIRINGS ON COVERINGS OF ELLIPTIC CURVES OVER Q      *
 *                                                                       *
 *                      Steve Donnelly, 2008                             *
 *                                                                       *
 *      The algorithms are explained in notes available from me.         *
 *                                                                       *
 ************************************************************************/

import "CrvEll_FldFun/cassels-tate.m": cassels_tate_pairing_FldFunRat;

import "cassels-tate_help.m": quadratic_point, 
			      quadratic_point_FldNum, 
                              real_point, 
                              local_point, 
                              local_point_FldNum, 
                              plug_in; 

import "8descent.m": proj_to_P2, HasRealPoint;  

debug := false;
paranoid := false;

declare verbose CasselsTate, 3;

//////////////////////  TEMPORARY INTRINSICS  //////////////////////////// 

intrinsic '^'(D::DivCrvElt, rho::Map) -> DivCrvElt
{The image of D under rho, where rho is a map on the base field 
(such as a Galois automorphism)}
  I := Ideal(D);
  Irho := ideal< Generic(I) | [pol^rho : pol in Basis(I)] >;
  return Divisor( Curve(Parent(D)), Irho);
end intrinsic;

intrinsic '!'(DG::DivCrv, D::DivCrvElt : base_change_map:=0 ) -> DivCrvElt
{Given a divisor D on a curve C, coerces D into DG where DG is 
 the divisor group of some base change of C.  This assumes the 
 base change was by standard coercion of the coefficient rings, 
 unless the 'base_change_map' (between the coefficient rings)
 is specified.}

  require base_change_map cmpeq 0: "The base_change_map option is not yet implemented";
  C := Curve(Parent(D));
  CL := Curve(DG);
  K := BaseField(C);
  L := BaseField(CL);
  require IsCoercible(L, K.1) : "The first argument should be the divisor group" 
         * " of some base change of the curve on which the second argument lives";
  PolL := CoordinateRing(Ambient(CL));  
  IL := ideal< PolL | ChangeUniverse( Basis(Ideal(D)), PolL) >;
  DL := Divisor(CL, IL);  assert Parent(DL) eq DG;
  return DL;
end intrinsic;

function Translation_Map(E,P) // (E::CrvEll, P::PtEll) -> MapSch
// {The map from E to itself which adds the point P, as a map of schemes}
  error if not Scheme(P) eq E and Ring(Parent(P)) cmpeq BaseRing(E),
    "The second argument should be a point on the first argument, defined over the base field";
  F<X,Y> := FunctionField(E);
  EE := EllipticCurve(ChangeUniverse(Coefficients(E),F));
  PP := EE! P;
  XY := EE! [X,Y,1];
  addP := Eltseq(XY + PP)[1..2];
  subP := Eltseq(XY - PP)[1..2];
  tP := Normalization(map< E -> E | addP cat [1] >);
  tmP := Normalization(map< E -> E | subP cat [1] >);
  if #BasePoints(tP) gt 0 then tP := Extend(tP); end if;
  if #BasePoints(tmP) gt 0 then tmP := Extend(tmP); end if;
  return iso< E -> E | AllDefiningPolynomials(tP), AllDefiningPolynomials(tmP) >;
end function;

// Create the divisor corresponding to the point P by writing down the ideal
// (Assume the coordinates of P generate the field they live in)

function myPlace(P : DivisorOnly:=false)  // Pt -> PlcCrvElt 

IndentPush();

  C := Curve(P);
  K := BaseField(C);  assert K eq Rationals();  // for the moment
  L := Ring(Parent(P));
  d := Degree(L,K);
  m := #Eltseq(P);
  if P[m] ne 1 then 
//"WARNING from myPlace: the point isn't on the first affine patch ... reverting to Place";
    return Place(P); end if;

  // Create ideal in the finite order
  vprintf CasselsTate,2: "writing down the ideal ... "; 
  F := FunctionField(C);
  FF, FtoFF := AlgorithmicFunctionField(F);
  OFF := MaximalOrderFinite(FF);
  V := [ FtoFF(C.i/C.m) : i in [1..m-1] ];  

  // Only handle special case of a QI for now
  assert IsQuadricIntersection(C);  
  RR,SS,TT := Explode(V); // names for debugging
  okay := SS eq FF.1 and TT eq BaseField(FF).1 and TT in OFF;
  if not okay then 
//"WARNING from myPlace: assumptions are not satisfied ... reverting to Place";
IndentPop();
    return Place(P); end if;

  if L cmpeq K then 
    error "still need to get this case right";
    I := ideal< OFF | [ V[i]-P[i] : i in [1..m-1] ] >;  assert IsPrime(I);
  else // L is an extension of K
    k := 3; // this should be the index of the base coordinate
    f := MinimalPolynomial(P[k], K);
    // get full algebraic relations between the coords
    // TO DO: this is the most naive way to do it, and assumes one coord generates the whole field
    if Degree(f) ne d then 
//"WARNING from myPlace: 1st coordinate of the point doesn't generate the field ... reverting to Place";
IndentPop();
      return Place(P); end if;
    Labs := AbsoluteField(L); // in case L was relative (currently we're assuming K = Q)
    LL := ext< K | f >;
    LLtoLabs := iso< LL -> Labs | Labs! P[3] >;  
    LtoLL := map< L -> LL | l :-> (Labs!l) @@ LLtoLabs >;
    coords := [Eltseq(a @ LtoLL) : a in Eltseq(P)];  
    assert coords[3] eq [0,1] cat [0 : i in [3..d]] and coords[m] eq [1] cat [0 : i in [2..d]];
    eqns := [OFF| Evaluate(f,V[3]) ] 
        cat [OFF| num - den * &+[coords[i][j+1]*V[3]^j : j in [0..d-1]] 
                  where num, den := IntegralSplit(V[i],OFF) 
            : i in [2..2]];
    vprintf CasselsTate,2: "creating ideal ... "; vtime CasselsTate,2:
    I := ideal< OFF | eqns >;  
    if debug then 
      IC := ideal<Parent(C.1)| [Numerator(Evaluate( Numerator(b@@FtoFF), [C.i/C.4:i in [1..3]])): b in Basis(I)]>;
      assert &and[ Evaluate(b,Eltseq(P)) eq 0  : b in Basis(IC) ]; 
      assert IsPrime(I); 
    end if;
  end if;

  vprint CasselsTate,2: "Making places:"; 
  vtime CasselsTate,2:
  pl := DivisorOnly select Divisor(I)
                     else  Place(I);
  vtime CasselsTate,2:
  plC := DivisorOnly select CurveDivisor(C, pl)
                      else  CurvePlace(C, pl);

IndentPop();
  return plC;

  // OLD VERSION: create ideal in the coordinate ring 
  // (not sure why it was better to use the function field order)
  if L cmpeq K then 
    I := ideal< Parent(C.1) | [C.i - P[i]*C.m : i in [1..m-1]] >;
    assert IsPrime(I);
  else // L is an extension of K
    f := MinimalPolynomial(P[1], K);
error if Degree(f) ne d, "the 1st coordinate of the point doesn't generate field";
    Labs := AbsoluteField(L);
    LL := ext< K | f >;
    LLtoLabs := iso< LL -> Labs | Labs! P[1] >;  
    LtoLL := map< L -> LL | l :-> (Labs!l) @@ LLtoLabs >;
    coords := [Eltseq(a @ LtoLL) : a in Eltseq(P)];  assert coords[1][1..2] eq [0,1];
    eqns := [ C.m^d * Evaluate(f,C.1/C.m) ] cat 
            [ C.m^Degree(ff) * Evaluate(ff,C.i/C.m) where ff is MinimalPolynomial(P[i],K)
             : i in [2..m-1] ] cat
            [ C.i*C.m^(ee-1) - &+[c[j]*C.1^(j-1)*C.m^(ee-j+1) : j in [1..e]] 
              where ee is (e eq 1) select 1 else e-1
              where e is Max([j : j in [1..d] | c[j] ne 0])
              where c is coords[i]
             : i in [2..m]];
assert eqns[#eqns] eq 0; // could omit it            
    assert &and [Evaluate(eqn, Eltseq(P)) eq 0 : eqn in eqns];
    I := ideal< Parent(C.1) | eqns >;  
vprintf CasselsTate,2: "Taking radical ... "; vtime CasselsTate,2: 
    I := Radical(I);
vprintf CasselsTate,2: "Make sure its prime ... "; vtime CasselsTate,2: assert IsPrime(I);
/*if not IsPrime(I) then printf "Not prime!!!!!!!! "; time
 // _, primes := PrimaryDecomposition(Radical(I));
 primes := RadicalDecomposition(I);
 degs := [Degree(Scheme(C,PI)) : PI in primes];
 primes := [primes[i] : i in [1..#primes] | degs[i] gt 1];
 assert #primes eq 1; // otherwise need to decide which one to take
 I := primes[1];
end if;*/
  end if;
vprintf CasselsTate,2: "Place of ideal ... "; vtime CasselsTate,2:
  pl := Place(C,I);  assert Degree(pl) eq d;
IndentPop();
  return pl;
end function;


/////////////////////////////  RIEMANN-ROCH BY HAND  ////////////////////////////

// C is a QI over a number field, D is effective consisting of 4 conjugate points
// (Currently not used)

function RiemannRochBasisQI(D)
  C := Curve(D);
  Pol := CoordinateRing(Ambient(C));
  assert IsQuadricIntersection(C);
  assert Degree(D) eq 4 and IsEffective(D);
  K := BaseField(C);  assert ISA(Type(K),FldAlg) and IsAbsoluteField(K);
  /* This seems to be wrong (comes up with 3 sections??) ... also extremely slow
  quads := LinearSystem(Ambient(C),2);  assert Dimension(quads) eq 9;
  quadsD := LinearSystem(quads, Scheme(C,Ideal(D)) );  assert Dimension(quadsD) eq 5;
  */
  supp, mults := Support(D);  assert mults eq [1];
  P := Eltseq(RepresentativePoint(supp[1]));
  quads := MonomialsOfDegree(Pol, 2);
  conditions := Matrix(K,10,4, [Eltseq(Evaluate(q,P)) : q in quads]);
  f := &+ [b[i]*quads[i] : i in [1..10]] where b is Basis(Kernel(conditions))[1];
assert Evaluate(f,P) eq 0;  
  I := ideal< Pol | f, DefiningPolynomials(C) >;  Groebner(I);
time  DI := Divisor(C,I);
time  DD := DI - D;
  supp, mults := Support(DD);  assert mults eq [1];
error "in RiemannRochBasisQI";
  return 0;
end function;
 
////////////////  TRIVIALIZING OBSTRUCTIONS ON 2-COVERINGS  ////////////////

// Given a 2-covering map CtoE over K (not necessarily in normal form), 
// and a point P in E(K), find an isomorphism over K from C to the 2-covering 
// (given as a QI) that corresponds to the sum of CtoE and P as elements of
// the 2-Selmer group. 

function add_point_to_two_covering(CtoE, P : compute_composition:=true)
  C := Domain(CtoE);  
  E := Codomain(CtoE);  
  K := BaseField(C);
  assert Scheme(P) eq E and Ring(Parent(P)) eq K; 

  D := Divisor(C, P @@ CtoE); // consists of the 4 preimages of P on C 
  if Degree(D) ne 4 then 
    vprintf CasselsTate, 2: "Extending 2-covering map ... "; vtime CasselsTate, 2:
    CtoE := Extend(CtoE);
    D := Divisor(C, P @@ CtoE);
    assert Degree(D) eq 4;
  end if;
  
  Pr3<R,S,T,U> := ProjectiveSpace(K,3);
  L, Lmap := RiemannRochSpace(D);  
  RRbas := [b @ Lmap : b in Basis(L)];
  CtoPr3 := map< C -> Pr3 | RRbas >;
//CPeqns := DefiningEquations(Image(CtoPr3, C, 2)); // this seems to come up with bulkier equations
  CPeqns := [eqn : eqn in DefiningEquations(Image(CtoPr3)) | TotalDegree(eqn) eq 2];
  assert #CPeqns eq 2 and &and [TotalDegree(eqn) eq 2 : eqn in CPeqns]; // check it's a QI
  CP := Curve(Pr3, CPeqns);

  // Identify which hyperplane section of CP will be the preimage of O_E (= pushforward of D under CtoCP).
  // It corresponds to a constant function in L, which should be the last entry (since L gets echelonized).
  idx := 4; assert IsZero(Divisor(RRbas[idx])); 
  kernel_hyperplane := CP.idx;

  CtoCP := map< C -> CP | DefiningEquations(CtoPr3) : Check:=false >;
  if not IsEmpty(BaseScheme(CtoCP)) then 
    vprintf CasselsTate, 2: "Extending map CtoCP ... "; vtime CasselsTate, 2:
    CtoCP := Extend(CtoCP); end if;
  vprintf CasselsTate, 2: "Getting inverse map CPtoC ... "; vtime CasselsTate, 2:
  bool, CPtoC := IsInvertible(CtoCP);  assert bool;
  CtoCP := iso< C -> CP | AllDefiningPolynomials(CtoCP), 
                          AllDefiningPolynomials(CPtoC) : Check:=false >;

  if not compute_composition then
    return CP, CtoCP, kernel_hyperplane;
  else
    vprintf CasselsTate, 2: "Getting translation by P map ... "; vtime CasselsTate, 2:
    tP := Translation_Map(E,P);
    CPtoE := Inverse(CtoCP) * CtoE * tP;
    return CP, CtoCP, CPtoE, kernel_hyperplane;
  end if;
end function;


// Trivialise the obstruction for the 2-covering CtoE, specified by C (must be a QI),
// and a hyperplane H (the preimage of O_E) given as a linear form in C.1,...,C.4
// 
// Returns an iso from C to C1, where C1 has the form y^2 = quartic(x).
// I've copied from Nils' function Quartic (same thing, except no quadratic_field).
// (When E[2] is nontrivial, he chooses one of the singular quadrics at random;
// here, we take the one that matches the kernel_hyperplane)
//
// This function is used only for the 4x2 pairing, which calls it in both steps.

function remove_obstruction(C, H : quadratic_field:=0)
  K := BaseField(C);
  eqns := DefiningEquations(C);
  error if &or [TotalDegree(eqn) ne 2 : eqn in eqns], "in remove_obstruction, C is not a QI";
  assert IsHomogeneous(H) and TotalDegree(H) eq 1; // linear form
  H := [MonomialCoefficient(H, C.i) : i in [1..4]]; // coefficients

  // Find the K-rational singular quadrics in the pencil
  M1,M2 := Explode([ SymmetricMatrix(eqn) : eqn in eqns ]);
  det:=Determinant( M1*PolynomialRing(K).1 + M2 );
  disc:=Discriminant(det);
  error if Degree(det) lt 3 or disc eq 0, "Oops, broken pencil in remove_obstruction";

  // Singular quadrics <==> roots of det <==> E[2]
  // Iterate through the roots until we find a singular quadric matching H
  rts := Roots(det);  assert #rts gt 0 or Degree(det) eq 3;  
  assert &and [tup[2] eq 1 : tup in rts];
  rts := [* tup[1] : tup in rts *];  
  if Degree(det) eq 3 then rts := [* Infinity() *] cat rts; end if;
  for idx := 1 to #rts do  
    r := rts[idx];
    if r cmpeq Infinity() then
      S:=M1;  Q:=M2; 
    else
      S:=r*M1+M2;  Q:=M1;
    end if;
    if IsZero( Vector([K|0,0,0,1])*S ) then
      T:=Parent(S)!1;
    else
      T:=Basis(Kernel(S));
      assert #T eq 1;
      T:=Matrix(Reverse(ExtendBasis(T,Generic(Universe(T)))));
      S:=T*S*Transpose(T);
      Q:=T*Q*Transpose(T);
      assert IsZero( Vector([K|0,0,0,1])*S );
    end if;

    // if more then 1 root, check which is the right one
    // TO DO: if only 1 root, only do this as a debug check
    if true or #rts gt 1 then  
      // Complete the square wrt the 4th variable in Q, so Q takes the form const*X4^2 + F(X1,X2,X3)
      assert Q[4,4] ne 0; // otherwise the QI would be linear in the 4th variable
      X4vec := [-Q[4,i]/Q[4,4] : i in [1..3]] cat [1];
      TT := Matrix([[1,0,0,0], [0,1,0,0], [0,0,1,0], X4vec]);
      if debug then assert &and [QQ[4,i] eq 0 : i in [1..3]] where QQ is Transpose(TT)*Q*TT; end if;
      if Eltseq(Vector(H)*Transpose(T)*TT)[1..3] eq [0,0,0] then
        break idx;
      elif idx le #rts then
        vprintf CasselsTate,2: "Root # %o is the wrong singular quadric!\n", idx; 
      else
        error "None of the singular quadrics match the specified hyperplane";
      end if;
    end if;
    error if idx eq #rts, "None of the singular quadrics match the specified hyperplane";
  end for; // idx

  con := Conic(Submatrix(S,1,1,3,3));
  vprint CasselsTate,2: "Solving", con;
  // Parametrize, over K whenever possible, otherwise over quadratic_field if specified.  
  // TO DO: use internal parametrization in Parametrization where relevant
  if quadratic_field cmpeq 0 or IsLocallySolvable(con) then 
    w:=DefiningPolynomials(Parametrization(con));
    KK:=K;
  else 
    error if quadratic_field cmpeq 0, "in remove_obstruction: the covering does not have " *
         "trivial obstruction over the base field, and \'quadratic_field\' was not specified";
    KK:=quadratic_field; 
    error if BaseField(KK) cmpne K or Degree(KK) ne 2, "in remove_obstruction: the given " *
         "quadratic_field must be a degree 2 extension of the base field of C";
    con:=BaseChange(con,KK);
    bool, PKK := HasPoint(con : Check:=debug);
    error if not bool, "in remove_obstruction: the covering does not have " *
                       "trivial obstruction over the given quadratic_field";
    w:=DefiningPolynomials(Parametrization(con,PKK));
    error "Example where the conic is not soluble over K, please report it to magma-bugs@maths.usyd.edu.au";
  end if;

  KKx := PolynomialRing(KK); x := KKx.1;
  R:=PolynomialRing(KKx);
  v:=Vector(Append([Evaluate(f,[R!x,1]):f in w],R.1));
  f:=InnerProduct(v*Matrix(BaseRing(v),Q),v);
  assert Degree(f) eq 2;
  assert Coefficient(f,2) in KK;
  f:=f/KK!Coefficient(f,2);
  H:=HyperellipticCurve(-Coefficient(f,0),Coefficient(f,1));
  mp:=Vector(Append([Evaluate(f,[H.1,H.3]):f in w],H.2));
  mp:=Eltseq(mp*Matrix(BaseRing(mp),T));
  HtoC:=map< H->C | mp : Check:=debug >;  
  if Type(KK) eq FldRat then
    H,mpm:=ReducedMinimalWeierstrassModel(H);
    H,mps:=SimplifiedModel(H);
    HtoC:=Expand(Inverse(mpm*mps)*HtoC);
  end if;
  return HtoC;
end function;


// Let CtoE be a 2-covering defined over K (not necessarily in normal form), 
// and let P be a point in E(K) or in E(L) for some quadratic extension L/K 
// with x(P) in K.  This finds a divisor D_P of degree 2 on C (over K or L resp.) 
// whose "sum" is P, where the sum of Q+Q' of points on C can be defined as 
// CtoE(Q')+(Q-Q') on E.  In particular if C is y^2 = quartic(x) and CtoE sends
// the ramification points to 0, then for any a fibre D_0 = (x-c), the class of 
// D_P - D_0 in Pic^0(C_L) == E(L) is P.

// This function is called only by the 4x2 pairing

function rational_divisor_in_class( CtoE, P : avoid:={})
  C := Domain(CtoE);
  E := Codomain(CtoE);
  K := BaseField(C);
  L := Ring(Parent(P));
  assert Scheme(P) eq E;

/* This case is not called
  if L eq K then 
    CP, CtoCP, CPtoE := add_point_to_two_covering( CtoE, P);
    _, CPtrivtoCP := remove_obstruction(CPtoE);  CPtriv := Domain(CPtrivtoCP);
    Delta := Divisor(CPtriv, Scheme(CPtriv, CPtriv.1));
    Delta := Pullback( CtoCP, Pushforward( CPtrivtoCP, Delta));
    assert Degree(Delta) eq 2;
    return Delta; end if; 
*/
  assert BaseField(L) eq K and Degree(L) eq 2;
  assert P[3] ne 0;
  xP := P[1]/P[3];
  error if not IsCoercible(K,xP), "P must have K-rational x-coordinate";
  error if Type(C) ne CrvHyp or Degree(C) ne 4, 
       "When P is defined over a quadratic extension, C must be y^2 = quartic(x)";
  fC,hC := HyperellipticPolynomials(C);  
  error if hC ne 0, 
       "When P is defined over a quadratic extension, C must be y^2 = quartic(x)"; 

  // Reduce to the untwisted situation (assuming CtoE sends the ram. points to 0)
  d := Discriminant(L)/4;
  bool, sqrtd := IsSquare(L!d); assert bool; // fix a sqrt of d
  // replace E by E1 : y^2 = cubic(x)
  E1, EtoE1 := WeierstrassModel(E); 
  CtoE1 := Expand(CtoE*EtoE1);
  P1 := P @ EtoE1;  assert P1[3] eq 1;
  Ed := EllipticCurve([0,d*a2,0,d^2*a4,d^3*a5]) 
                where _,a2,_,a4,a5 is Explode(Coefficients(E1));
  Cd := HyperellipticCurve(1/d*fC); // Cd : d*y^2 = fC(x)
  // Get the relevant point on Ed  
  // (xx,sqrtd*yy) on E1  <==>  (xx,yy) on d*y^2=f(x)  <==>  (d*xx,d^2*yy) on Ed
  xx := K! P1[1];  yy := K!( P1[2]/sqrtd );
  Pd := Ed! [d*xx,d^2*yy];
  // Twist the covering map, so Cd -> Ed is the composition of the above maps
  // with C -> Cd : (x,sqrtd*y) :-> (x,y) 
  eqns := DefiningEquations(CtoE1);  assert &and [WeightedDegree(ee) eq 6 : ee in eqns];
  even_parts := [C.2*eqns[1], eqns[2], C.2*eqns[3]]; 
  // The even_parts should be functions of x_C, so eliminate C.2 from them
  PC := CoordinateRing(Ambient(C));
  PCelim := ChangeOrder(PC, "elim", [2]);
  eqnC := ideal< PCelim | PCelim! DefiningEquation(C) >;
  even_parts := [PC| NormalForm( PCelim! eqn, eqnC) : eqn in even_parts];
  assert &and [ee eq Evaluate(ee,[C.1,0,C.3]) : ee in even_parts]; // no C.2's
  evenCd := [Evaluate(eqn, [Cd.1,0,Cd.3]) : eqn in even_parts];
  twisted_eqns := [d*evenCd[1], d^2*Cd.2*evenCd[2], evenCd[3]];
  CdtoEd := map< Cd -> Ed | twisted_eqns : Check:=debug >; 

  // Get the divisor and pull it back (over L)
  // We know this twisted thing has trivial obstruction over K, since C is locally soluble
  CPd, CdtoCPd, kern := add_point_to_two_covering(CdtoEd, Pd : compute_composition:=false);  
  CPdtrivtoCPd := remove_obstruction(CPd, kern);
  CPdtriv := Domain(CPdtrivtoCPd);  KK := BaseField(CPdtriv); // = K if possible, otherwise L
  vprint CasselsTate,2: "Looking for a quadratic point on", DefiningEquation(CPdtriv); 
  Delta_pt := quadratic_point(CPdtriv, 0 : num:=500, better_bound:=10^4, avoid:=avoid, avoid2tors:=false);
  Delta := Divisor(Place(Delta_pt));

  CL := ChangeRing(C,L);  CdL := ChangeRing(Cd,L); 
  if KK cmpeq K then 
    Delta := Pullback( CdtoCPd, Pushforward( CPdtrivtoCPd, Delta));
    Delta := DivisorGroup(CdL)! Delta;
  else assert KK eq L; 
    Delta := Pullback( BaseChange(CdtoCPd,KK), Pushforward( CPdtrivtoCPd, Delta));
  end if;
  CLtoCdL := iso< CL -> CdL | [CL.1,1/sqrtd*CL.2,CL.3], [CdL.1,sqrtd*CdL.2,CdL.3] >;
  Delta := Pullback( CLtoCdL, Delta);
  assert Degree(Delta) eq 2;
  return Delta;
end function;

// Input: CtoE is a 2-covering over K of the form C : v^2 = f(u), 
//        and P in E(K) is not of order 2.
// Returns: a quadratic polynomial whose roots are u(Q) and u(Q'), 
// where Q + Q' is a K-rational divisor on C that adds up to P
// (or returns linear poly if Q is at infinity).

// Currently assumes that CcovE sends Weierstrass points to O_E 

function rational_divisor_in_class_x_coords( CcovE, P)

  C := Domain(CcovE);
  E := Codomain(CcovE);
  K := BaseField(C);
  assert Scheme(P) eq E and K eq Ring(Parent(P));

  if IsZero(P) then return PolynomialRing(K).1^2; end if;  // any vertical divisor

  error if debug and IsZero(2*P), "Not implemented when the given point P has order 2";

  // reduce to the case c3 = 0, and plug into the generically-computed formulae
  f,h := HyperellipticPolynomials(C);  assert IsZero(h);
  b := Coefficient(f,3) / (4*Coefficient(f,4));  
  f1 := Evaluate(f, PolynomialRing(K).1 - b);  
  c0,c1,c2,c3,c4 := Explode(Coefficients(f1));  assert c3 eq 0;
  a4 := -5184*c0*c4 + 1296*c1*c3 - 432*c2^2;
  a6 := -124416*c0*c2*c4 + 46656*c0*c3^2 + 46656*c1^2*c4 - 15552*c1*c2*c3 + 3456*c2^3;
  E1 := EllipticCurve([a4,a6]);
  // We need the iso between E and E1 that commutes with the covering maps
  // We only need it correct up to sign, since replacing P by -P doesn't change the answer
  // (because -Q + -Q' adds up to -P and u(Q) = u(-Q), where -Q is the point opposite Q)
  // TO DO: get it right when E has extra automorphisms
  assert K cmpeq Rationals() or #AutomorphismGroup(E) eq 2;
  bool, EtoE1 := IsIsomorphic(E,E1);  assert bool;  
  x,y,z := Explode(Eltseq( P @ EtoE1 ));  assert z eq 1;

  // The following conic is the quotient of C by the involution Q :-> P + (-Q).
  // The quotient map is [u+u_inv, u*u_inv, 1], where u_inv denotes the pullback of u.
  // The field K(u+u_inv, u*u_inv) has subdegree 2 inside K(C), if P has order > 2.
  // To see this, one calculates that u_inv is a function of u iff 2*P = 0; hence 
  // K(u,v) = K(u,u_inv), which clearly has degree 2 over K(u+u_inv, u*u_inv).
  // (We obtained the conic via a generic computation.)
  Pr2<S,T,U> := ProjectiveSpace(K,2);
  conic := Curve(Pr2,
    (c0*c4 - 1/36*c2^2 + 1/216*c2*x - 1/5184*x^2)*S^2 + c1*c4*S*T + (2/3*c2*c4 + 1/36*c4*x)*T^2 +
    (-1/6*c1*c2 + 1/72*c1*x)*S*U + (-2/9*c2^2 + 1/108*c2*x + 1/1296*x^2)*T*U + (2/3*c0*c2 + 1/36*c0*x - 1/4*c1^2)*U^2 );

  if debug then  // check the conic by verifying the map 
    C1 := HyperellipticCurve(f1);  u := C1.1/C1.3;  v := C1.2/C1.3^2;
    u_inv :=  // pullback of u under the involution 
      (1/432*y*v - c0*c4*u + 1/12*c1*c2 - 1/2*c1*c4*u^2 - 1/144*c1*x + 5/36*c2^2*u - 1/108*c2*x*u - 1/5184*x^2*u) 
      / (c0*c4 + c1*c4*u - 1/36*c2^2 + 2/3*c2*c4*u^2 + 1/216*c2*x + 1/36*c4*x*u^2 - 1/5184*x^2);
    C1_to_conic := map< C1 -> conic | [u + u_inv, u * u_inv, 1] >; 
  end if;

  // Solve the conic, obtaining solution [S0,T0,U0] with U0 nonzero
  bool, conic1 := IsConic(conic);
  if bool then 
    bool, soln := HasPoint(conic1 : Check:=debug);  
    assert bool;
  else
    assert IsSingular(conic); 
"\n !!!!!!!!!!!  INTERESTING EXAMPLE -- Singular conic in rational_divisor_in_class_x_coords  !!!!!!!!!!!\n";
    soln := RationalPoints(conic)[1]; // not sure if this happens, but anyway, TO DO: implement HasPoint for genus zero curves
  end if;
  S0,T0,U0 := Explode(Eltseq(soln)); 
  if U0 ne 0 then
    pol := Polynomial([K| T0/U0, -S0/U0, 1 ]);
  else
    // wlog Q' is at infinity and u(Q) is any root of the denominator ... TO DO: check this case!!
    bool, u0 := HasRoot(Polynomial([K| c0*c4 - 1/36*c2^2 + 1/216*c2*x - 1/5184*x^2, c1*c4, 2/3*c2*c4 + 1/36*c4*x ]));
    assert bool;  pol := Polynomial([K| -u0, 1 ]);
  end if;

  if debug then  // check Q and Q' exist (over the field defined by their u-coords)
    rts := [tup[1] : tup in Roots(pol)];  
    if Degree(pol) eq 1 then assert #rts eq 1; rts := [*rts[1], Infinity()*]; end if;
    if #rts eq 0 then L := ext<K|pol>; rts := [L.1, Trace(L.1)-L.1]; else L := K; end if;  
    C1L := BaseChange(C1,L);  EL := BaseChange(E,L);  
    C1toC := map< C1 -> C | [C1.1-b*C1.3, C1.2, C1.3] >;
    C1covEL := map< C1L -> EL | DefiningEquations(C1toC*CcovE) >;
    Qs := [Points(C1L,r) : r in rts];  assert &and [#pts eq 2 : pts in Qs]; 
    if #AutomorphismGroup(BaseChange(E,L)) eq 2 then
      EE, C1LtoEE := EllipticCurve(C1L, Qs[1][1]);  
      bool, EEtoEL := IsIsomorphic(EE,EL);  assert bool;  toE := C1LtoEE*EEtoEL;
      // The sum Q + Q' := CcovE(Q) + Q' - Q = CcovE(Q) + toE(Q') - toE(Q) should be P or -P
      // and we take Q = Qs[1][1], so toE(Q) is zero
      if #rts eq 1 then  // special case Q'=Q (or Q'=-Q, but then P is zero) 
        assert IsZero(P) or Eltseq(C1covEL(Qs[1][1]))[1] eq P[1]; 
      else
        phiQ11 := C1covEL(Qs[1][1]);  Qs2EL := [ Q @C1LtoEE @EEtoEL : Q in Qs[2] ];  
        sums := &cat[ [phiQ11 + Q, phiQ11 - Q] : Q in Qs2EL ]; 
                    // + or - Q because we don't know if the iso C->E matches up with the covering
        assert &or[ Eltseq(sum)[1] eq P[1] : sum in sums ];
      end if;
    end if;
  end if;

  return Evaluate(pol, PolynomialRing(K).1 + b);
end function;


// Input: CtoE is a 2-covering over K of the form C : v^2 = f(u), 
//        and P in E(K(sqrt{d})) is not of order 2.
// Returns: a quadratic polynomial over K whose roots are u(Q) and u(Q'), 
// where Q + Q' is a K(sqrt{d})-rational divisor on C that adds up to P
// (or returns linear poly if Q is at infinity).

// Currently assumes CcovE sends the ramification points to 0_E
// TO DO: revise!  Do we really need the map?

function rational_divisor_in_class_x_coords_twisted( CcovE, P)

  C := Domain(CcovE);
  E := Codomain(CcovE);
  K := BaseField(C);
  L := Ring(Parent(P));

  // Reduce to the untwisted situation
  sqrtd := L.1;
  bool, d := IsCoercible(K, sqrtd^2);
  assert bool;

  // replace E by E1 : y^2 = cubic(x)
  E1, EtoE1 := WeierstrassModel(E); 
  CcovE1 := Expand(CcovE*EtoE1);
  P1 := P @ EtoE1;  assert P1[3] eq 1;
  Ed := EllipticCurve([0,d*a2,0,d^2*a4,d^3*a5]) 
                where _,a2,_,a4,a5 is Explode(Coefficients(E1));
  fC,hC := HyperellipticPolynomials(C);  assert hC eq 0;
  Cd := HyperellipticCurve(1/d*fC); // Cd : d*y^2 = fC(x)
  // Get the relevant point on Ed  
  // (xx,sqrtd*yy) on E1  <==>  (xx,yy) on d*y^2=f(x)  <==>  (d*xx,d^2*yy) on Ed
  xx := K! P1[1];  yy := K!( P1[2]/sqrtd );
  Pd := Ed! [d*xx,d^2*yy];
  // Twist the covering map, so Cd -> Ed is the composition of the above maps
  // with C -> Cd : (x,sqrtd*y) :-> (x,y) 
  eqns := DefiningEquations(CcovE1);  assert &and [WeightedDegree(ee) eq 6 : ee in eqns];
  even_parts := [C.2*eqns[1], eqns[2], C.2*eqns[3]]; 
  // The even_parts should be functions of x_C, so eliminate C.2 from them
  PC := CoordinateRing(Ambient(C));
  PCelim := ChangeOrder(PC, "elim", [2]);
  eqnC := ideal< PCelim | PCelim! DefiningEquation(C) >;
  even_parts := [PC| NormalForm( PCelim! eqn, eqnC) : eqn in even_parts];
  assert &and [ee eq Evaluate(ee,[C.1,0,C.3]) : ee in even_parts]; // no C.2's
  evenCd := [Evaluate(eqn, [Cd.1,0,Cd.3]) : eqn in even_parts];
  twisted_eqns := [d*evenCd[1], d^2*Cd.2*evenCd[2], evenCd[3]];
  CdtoEd := map< Cd -> Ed | twisted_eqns : Check:=debug >; 

  return rational_divisor_in_class_x_coords( CdtoEd, Pd);
end function;

///////////////////////////////   2 x 2 PAIRING   ///////////////////////////////  

function prime_divisors(N) 
  if ISA(Type(N), RngOrdElt) then
    N := N*Parent(N);
  end if;
  l := Ilog(10, Minimum(N));
  if l ge 100 then
    printf "\nWARNING: factoring a %o-digit integer\n", l;
  end if;
  return [tup[1] : tup in Factorization(N)];
end function;

// An integral model y^2 = f(x) over Q
function nice_model(D)
  if not IsZero(h) where _,h := HyperellipticPolynomials(D) then 
    D := SimplifiedModel(D); 
  end if;
  if not CanChangeRing(HyperellipticPolynomials(D), Integers()) then
    D := ReducedMinimalWeierstrassModel(D : Simple);
  end if;
  return D;
end function;

// An integral model y^2 = f(x)
// In this context it's fine to just multiply f by a square integer
function decent_model(C0)
  f, h := HyperellipticPolynomials(C0);
  if IsZero(h) and forall{c : c in Coefficients(f) | IsIntegral(c)} then
    return C0;
  end if;
  F := f + h^2/4;
  coeffs := Coefficients(F);
  if not forall{c : c in coeffs | IsIntegral(c)} then
    denom := LCM([Denominator(c) : c in coeffs]);
    d := &*PrimeDivisors(denom);
    i := 0; repeat i +:= 2; until d^i mod denom eq 0;
    F := d^i*F;
  end if;
  C := HyperellipticCurve(F);
  assert IsIsomorphic(C, C0);
  return C;
end function;

function cassels_tate_pairing_FldNum(C0, D0) // -> RngIntElt
  K := BaseRing(C0);
  OK := Integers(K);

  C := decent_model(C0);
  D := decent_model(D0);

  E, CcovE := AssociatedEllipticCurve(C);
  _, DcovE := AssociatedEllipticCurve(D : E:=E );

  // we need the only automorphisms of E over the quad field to be +-1
  // TO DO: what if E/K has extra autos ?
  avoid := {};
  j := jInvariant(E);
  if j eq 1728 then 
    error if HasRoot(Polynomial([K|1,0,1])), "Not implemented yet for some fields when j(E) = 1728";
    avoid join:= {-1};
  elif j eq 0 then 
    error if HasRoot(Polynomial([K|1,1,1])), "Not implemented yet for some fields when j(E) = 0";
    avoid join:= {-3}; 
  end if;
  PD, FD := quadratic_point_FldNum(D, DcovE : avoid:=avoid); // returns relative field (easier!)
  if FD eq K then 
    return 0; 
  else
    DD := K!(FD.1^2); 
  end if;
  assert exists(sigma){a : a in Automorphisms(FD) | FD.1@a ne FD.1};

  P := DcovE(PD); // = PD - PD^sigma

  _<x,y> := PolynomialRing(K,2); // only used for printing x here
  vprintf CasselsTate: "Computing Cassels-Tate pairing between:\n y^2 = %o\n y^2 = %o\n", 
                        Evaluate(HyperellipticPolynomials(C),x), Evaluate(HyperellipticPolynomials(D),x);
  vprintf CasselsTate: "Using quadratic extension FD : %o\n", DefiningPolynomial(FD);
  vprintf CasselsTate: "Trivializing obstruction (for a related 2-covering) ... "; 
  vtime CasselsTate:
  
  Deltax := rational_divisor_in_class_x_coords_twisted( CcovE, P); 

  KC := FunctionField(C);
  magic_f := Evaluate(Deltax, KC.1);  
  if debug then assert Evaluate(DefiningEquation(C), [KC.1,KC.2,1]) eq 0; end if; // check KC.1 is the x coord 
  vprint CasselsTate: "The function used to define the Azumaya algebra is", magic_f;

  // Figure out the bad primes
  num := Numerator(magic_f);
  den := Denominator(magic_f);
  if debug then
    assert TotalDegree(Pol!num) le 2 and TotalDegree(Pol!den) le 2 where Pol is OriginalRing(Parent(num)); end if;
  PR<x_L,y_L> := OriginalRing(Parent(num));
  lcm_coeff_denoms := LCM([ Denominator(coeff) : coeff in Coefficients(PR!num) cat Coefficients(PR!den) ]);
  num := lcm_coeff_denoms*PR!num;
  den := lcm_coeff_denoms*PR!den;
  gcd_num_coeffs := ideal< OK | [Numerator(K!coeff) : coeff in Coefficients(num)] >;
  gcd_den_coeffs := ideal< OK | [Numerator(K!coeff) : coeff in Coefficients(den)] >;

  // Which primes do we need to look at???
  ramprimesD := Seqset(prime_divisors(ideal<OK|Discriminant(FD)>));
  badrednprimesC := Seqset(prime_divisors(OK!Discriminant(GenusOneModel(C))));
  badrednprimesD := Seqset(prime_divisors(OK!Discriminant(GenusOneModel(D))));
  vprintf CasselsTate, 2: "Factoring content (to get bad primes) ... "; 
  vtime CasselsTate, 2:
  bad_magic_primes := Seqset(prime_divisors(gcd_num_coeffs) cat prime_divisors(gcd_den_coeffs));
  if IsVerbose("CasselsTate", 2) then
    print "Ramified primes for FD are", ramprimesD;
    printf "Bad reduction primes for C and D are %o and %o\n", badrednprimesC, badrednprimesD;
    print "Bad primes for the Azumaya algebra are", bad_magic_primes;
  elif IsVerbose("CasselsTate", 1) then
    print "Ramified primes for FD have norms", {Norm(p) : p in ramprimesD};
    printf "Bad reduction primes for C and D have norms %o and %o\n", 
           {Norm(p) : p in badrednprimesC}, {Norm(p) : p in badrednprimesD};
    print "Bad primes for the Azumaya algebra have norms", {Norm(p) : p in bad_magic_primes};
  end if;

  // TO DO: which primes are small ??
  smallprimes := Seqset(PrimesUpTo(30, K));
  reallybadprimes := ramprimesD join badrednprimesC join bad_magic_primes join smallprimes;
  badprimes := reallybadprimes join badrednprimesD;
  if debug then 
    badprimes join:= Seqset(PrimesUpTo(100,K));
  end if;
  badprimes := Sort(Setseq(badprimes), func<p1,p2|Norm(p1)-Norm(p2)>);

  // Compute local invariants of the quat alg given by 'magic_f'
  // TO DO: special case when quarticC and magic_f are over Q
  vprint CasselsTate : "Local invariants:";
  quarticC := HyperellipticPolynomials(C);
  ans := 0;

  for i := 1 to #RealPlaces(K) do 
    DDi := Conjugate(DD, i);  
    assert IsReal(DDi);
    if Real(DDi) gt 0 then
      invt := 0;
    else
      repeat
        quarticR := Polynomial([Real(Conjugate(c,i)) : c in Coefficients(quarticC)]);
        pt := real_point(quarticR : rand:=true);
        success, magic_f_val := plug_in(magic_f, pt : max_val:=20, conjugate:=i); 
      until success;
      invt := (1-Sign(magic_f_val)) div 2;
    end if;
    vprintf CasselsTate : "  real place : %o\n", invt;
    ans := (ans + invt) mod 2;
  end for;

  for p in badprimes do
    vprintf CasselsTate : "  %o :", Factorization(Norm(p))[1];
    fact := Decomposition(Integers(FD), p);
    P, e := Explode(fact[1]);
    if #fact eq 2 then
      invt := 0;  // trivial local restriction
    else
      // TO DO: Minimise + Reduce at the start, but it will still be important to locally minimise here
      min_model, trans := Minimise(GenusOneModel(Reverse(Coefficients(quarticC))) : UsePrimes:=[p], CrossTerms:=false);
      quartic_min := Evaluate(Equation(min_model), [Parent(quarticC).1, 1]);
      disc_min := Discriminant(quartic_min);
      tt := trans`Scalar;
      aa,bb,cc,dd := Explode(Eltseq(trans`Matrix));
      num_fails := 0; // num of times the local point was too close to a zero or pole
      invts := [];  // do it for several different local points, as a check
      while #invts lt (debug select 10 else 1) do
        if num_fails ge 500 then
          error "Too many failures in attempt to find local points at", p; 
          // start again (alternatively could try a different divisor for the same P)
          return CasselsTatePairing(C, D : avoid := avoid join {DD} ); 
        end if;
        // evaluate magic_f at a local point, check value is not too close to 0
        pt_min := local_point_FldNum(quartic_min, p : prec := 20 + Valuation(disc_min,p) + 5*num_fails);
        xden := bb*pt_min[1] + dd;
        if xden eq 0 then 
          num_fails +:= 1; 
          continue; 
        end if;
        pt := [(aa*pt_min[1] + cc)/xden, pt_min[2]/(tt*xden^2)];
        success, magic_f_val := plug_in(magic_f, pt : p:=p, max_val:=4+num_fails );
        if not success or Valuation(pt[2]^2 - Evaluate(quarticC,pt[1]), p) lt 10 then 
          num_fails +:= 1; 
          continue; 
        end if;
        // local invariant:
        if e eq 1 then   // unramified local extension
          invt := Valuation(K!magic_f_val, p) mod 2;
        else             // ramified local extension
	  hilb := HilbertSymbol(K!magic_f_val, DD, p);
          invt := (1-hilb) div 2;  // convert from {1,-1} to {0,1}
        end if;
        Append(~invts, invt);
        assert invt eq invts[1];   // check we got the same every time
      end while;
    end if;
    if p notin reallybadprimes then // prime should be irrelevant
      assert invt eq 0; 
    end if; 
    vprintf CasselsTate : " %o\n", invt;
    ans := (ans + invt) mod 2;
  end for;
  return ans;
end function;
  

intrinsic CasselsTatePairing(C::CrvHyp, D::CrvHyp) -> RngIntElt
{The Cassels-Tate pairing of C and D, which should be hyperelliptic curves 
 representing elements in the 2-Selmer group of some elliptic curve, 
 returned as an element of Z/2}

  if C cmpeq D then return 0; end if; 
  require BaseRing(C) eq BaseRing(D) : "The curves must be defined over the same field";
  K := BaseRing(C);

  if ISA(Type(K), FldNum) then 
    return cassels_tate_pairing_FldNum(C,D); 
  elif ISA(Type(K), FldFunRat) then
    return cassels_tate_pairing_FldFunRat(C,D); 
  end if;

  C := nice_model(C);
  D := nice_model(D);
  E, CcovE := AssociatedEllipticCurve(C);
  _, DcovE := AssociatedEllipticCurve(D : E:=E );

  // we need the only automorphisms of E over the quad field to be +-1
  avoid := {};
  j := jInvariant(E);
  if j eq 1728 then avoid join:= {-1};
  elif j eq 0 then avoid join:= {-3}; end if;
  PD, FD := quadratic_point(D, DcovE : avoid:=avoid, num:=20);
  if FD eq K then return 0; end if;
  assert exists(sigma){a : a in Automorphisms(FD) | FD.1@a ne FD.1};
 
  // Claim: PD - PD^sigma = DcovE(PD) 
  // Proof: Let T on D be such that phi(T) = O_E, and let ' denote the hyp involution on C.
  // We have PD' - PD = (PD'-T) - (PD-T) = (PD'-T) + (PD-T) - [2](PD-T) = - phi(PD). 
  // This uses that Q :-> Q-T is an isomorphism of 2-coverings and is compatible with the involutions.
  P := DcovE(PD);  
  
  _<x,y> := PolynomialRing(K,2); // only used for printing x here
  vprintf CasselsTate: "Computing Cassels-Tate pairing between:\n y^2 = %o\n y^2 = %o\n", 
                        Evaluate(HyperellipticPolynomials(C),x), Evaluate(HyperellipticPolynomials(D),x);
  vprintf CasselsTate: "Trivializing obstruction (for a related 2-covering) ... "; vtime CasselsTate:
  
  Deltax := rational_divisor_in_class_x_coords_twisted( CcovE, P); 

/* Non-twisted version 
  Delta := rational_divisor_in_class( CcovE, P);  // divisor on C base changed to FD
  CFD := Curve(Parent(Delta));  assert CFD eq BaseChange(C,FD);  // not identical though
  Delta0 := Divisor(C, ideal< Parent(C.1) | C.3 >); 
  Delta0 := DivisorGroup(CFD)! Delta0; // get them on the same curve (easier to coerce divisors up than down)

  magic_divisor := Delta + Delta^sigma - 2*Delta0;  
  bool, magic_f := IsPrincipal(magic_divisor);  assert bool;
  // Get the magic_f over K.  TO DO: This is dodgy! Probably better push the divisor down first.
  PolK := CoordinateRing(Ambient(C));
  PolFD := CoordinateRing(Ambient(CFD));
  KC := FunctionField(C);
  FDC := Parent(magic_f); // = FunctionField(CFD);
  pushdown := hom< FDC -> KC | [KC.1,KC.2] >; // Magma doesn't ask awkward questions about this!
  magic_f := magic_f @ pushdown;
*/
  KC := FunctionField(C);
  magic_f := Evaluate(Deltax, KC.1);  
  if debug then assert Evaluate(DefiningEquation(C), [KC.1,KC.2,1]) eq 0; end if; // check KC.1 is the x coord 
  vprint CasselsTate: "The function used to define the Azumaya algebra is", magic_f;

  // Figure out the bad primes
  num := Numerator(magic_f);
  den := Denominator(magic_f);
  if debug then
    assert TotalDegree(Pol!num) le 2 and TotalDegree(Pol!den) le 2 where Pol is OriginalRing(Parent(num)); end if;
  PR<x_L,y_L> := OriginalRing(Parent(num));
  lcm_coeff_denoms := LCM([ Denominator(coeff) : coeff in Coefficients(PR!num) cat Coefficients(PR!den) ]);
  num := lcm_coeff_denoms*PR!num;
  den := lcm_coeff_denoms*PR!den;
  gcd_num_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(num) ]);
  gcd_den_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(den) ]);

  // Which primes do we need to look at???
  ramprimesD := Seqset(PrimeDivisors(Discriminant(FD)));
  badrednprimesC := Seqset(PrimeDivisors(Integers()!Discriminant(GenusOneModel(C))));
  badrednprimesD := Seqset(PrimeDivisors(Integers()!Discriminant(GenusOneModel(D))));
  bad_magic_primes := Seqset(PrimeDivisors(gcd_num_coeffs) cat PrimeDivisors(gcd_den_coeffs));
  smallprimes := Seqset(PrimesUpTo(30));
  reallybadprimes := ramprimesD join badrednprimesC join bad_magic_primes join smallprimes;
  badprimes := reallybadprimes join badrednprimesD;
  if debug then badprimes join:= Seqset(PrimesUpTo(1000)); end if;
  if K eq Rationals() then badprimes := [ ideal<Integers()|p> : p in Sort(Setseq(badprimes)) ]; end if;

  vprint CasselsTate : "Ramified primes for FD are", ramprimesD;
  vprintf CasselsTate : "Bad reduction primes for C and D are %o and %o\n", badrednprimesC, badrednprimesD;
  vprint CasselsTate : "Bad primes for the Azumaya algebra are", bad_magic_primes;
 
  // Compute local invariants of the quat alg given by 'magic_f'
  quarticC := HyperellipticPolynomials(C);
  ans := 0;

  vprint CasselsTate : "Local invariants:";
  if IsTotallyReal(FD) then 
    invt := 0;
  else
    repeat
      pt := real_point(quarticC : rand:=true);
      success, magic_f_val := plug_in(magic_f, pt : max_val:=20); 
    until success;
    invt := (1-Sign(K!magic_f_val)) div 2;
  end if;
  vprintf CasselsTate : "  real place : %o\n", invt;
  ans := (ans + invt) mod 2;

  for p in badprimes do
    pp := (K eq Rationals()) select Minimum(p) else p;
    fact1 := Decomposition(Integers(FD), pp)[1];
    P, e := Explode(fact1);

    Np := (K eq Rationals()) select Minimum(p) else Norm(p);
    NP := Norm(P);
    if NP eq Np and e eq 1 then 
      invt := 0;  // trivial local restriction
    else
      num_fails := 0; // num of times the local point was too close to a zero or pole
      invts := [];  // do it for several different local points, as a check
      while #invts lt (debug select 10 else 1) do
        if num_fails ge 500 then
          error "Too many failures in attempt to find local points at", pp; 
          // start again (alternatively could try a different divisor for the same P)
          return CasselsTatePairing(C, D : avoid := avoid join {K!(FD.1^2)} ); end if;
        // evaluate magic_f at a local point, check value is not too close to 0
        pt := local_point(quarticC, p : prec:=20+5*num_fails );
        success, magic_f_val := plug_in(magic_f, pt : max_val:=4+num_fails );
        if not success or Valuation(pt[2]^2 - Evaluate(quarticC,pt[1])) lt 10 then 
          num_fails +:= 1; continue; end if;
        // local invariant:
        if e eq 1 then   // unramified local extension
          invt := Valuation(K!magic_f_val, p) mod 2;
        else             // ramified local extension
	  hilb := HilbertSymbol(K!magic_f_val, K!Discriminant(FD), pp);
          invt := (1-hilb) div 2;  // convert from {1,-1} to {0,1}
        end if;
        Append(~invts, invt);
        assert invt eq invts[1];  // check we got the same every time
      end while;
    end if;
    if pp notin reallybadprimes then assert invt eq 0; end if; // prime should be irrelevant
    vprintf CasselsTate : "  %o : %o\n", Minimum(p), invt;
    ans := (ans + invt) mod 2;
  end for;
  return ans;
end intrinsic;

//////////////////////////////   4 x 2 PAIRING   ///////////////////////////////   

// permute a sequence by a permutation 
function spin(seq, perm)
  return [seq[i] : i in Eltseq(Inverse(perm))];
end function;

// find a random point on a QI over Q_p as a sequence (must have last coord = 1)

function local_point_on_QI(C, p : prec:=20);
  model := GenusOneModel(C);
  repeat
    bool, pt := IsLocallySolvable(model, p : Random, Precision:=prec+20); assert bool;
    pt := Eltseq(pt);
    assert IsWeaklyZero(pt[4]-1);
  until forall{eqn: eqn in DefiningPolynomials(C) | Valuation(Evaluate(eqn,pt)) ge prec};
  return pt;
end function;

intrinsic CasselsTatePairing(C::Crv, D::CrvHyp : quadratic_point_on_D:=0 ) -> RngIntElt
{Pairing of a 4-covering (given as a QI) with a 2-covering 
 (given as a hyperelliptic curve), returned as an element of Z/2}

  Q := Rationals();

  require IsQuadricIntersection(C) : "The first argument must be a 4-covering of an elliptic "
                                   * "curve, given as an intersection of quadrics in P^3"; 
  require Type(D) eq CrvHyp and Degree(D) eq 4 : "The second argument must be a 2-covering "
                         * "of an elliptic, curve given as a hyperelliptic curve of degree 4";
  require BaseRing(C) cmpeq Q and BaseRing(D) cmpeq Q : 
         "The given curves must be defined over the rationals";
  
  C2, CtoC2 := AssociatedHyperellipticCurve(C);  
  E, C2toE := AssociatedEllipticCurve(C2);
  assert h eq 0 where _,h := HyperellipticPolynomials(C2);

  if IsIsomorphic(C2,D) and not debug then 
    vprint CasselsTate: "Pairing is trivial (4-cover covers 2-cover)";
    return 0; 
  end if;

  D := nice_model(D);
  EE, DtoEE := AssociatedEllipticCurve(D);
  bool, EEtoE := IsIsomorphic(EE, E);  
  require bool : "The given curves are not coverings of the same elliptic curve";
  DtoE := Expand(DtoEE * EEtoE);

  // Get a point PD on D over some quad extension Q(sqrtd)
  if quadratic_point_on_D cmpne 0 then
    PD := quadratic_point_on_D; 
    FD := Ring(Parent(PD));
  else
    // we need the only automorphisms of E over the quad field to be +-1 
    avoid := {};
    j := jInvariant(E);
    if j eq 1728 then avoid join:= {-1};
    elif j eq 0 then avoid join:= {-3}; end if;
    // TO DO: effort should depend on difficulty
    PD, FD := quadratic_point(D, DtoE : avoid:=avoid, num:=10^3, better_bound:=10^4 );
  end if;
  if FD cmpeq Q then return 0,_; end if;
   
  // tricky way of quickly getting P := PD - PD^sigma (or -P)
  // (we can't just get it by evaluating DtoE_FD at PD^sigma because
  // it is not defined there, and extending the map takes too long)
  // Claim: PD - PD^sigma = phi(DtoE(PD)) for some automorphism phi 
  //  of E defined over FD (and we have arranged these are only +-1).
  P := DtoE(PD);

  // Get a divisor in Div^4(C) over FD that "sums" to P, by a two-step process going via C2
  vprint CasselsTate: "Finding Delta2 ... ";  time_Delta2 := Cputime();
  IndentPush();
  Delta2 := rational_divisor_in_class(C2toE, P : avoid:={Q|1,FD.1^2} ); // divisor on C2 base changed to FD
  IndentPop();
  vprintf CasselsTate: "Took %o sec for Delta2\n", Cputime(time_Delta2);

  vprintf CasselsTate,2: "RepresentativePoint of Delta2 ... "; vtime CasselsTate,2: 
  Q2 := RepresentativePoint(Support(Delta2)[1]);  
  Lrel := Ring(Parent(Q2)); assert Degree(Lrel,FD) eq 2; // we will use that the points are conjugates (TO DO!)
  Labs := AbsoluteField(Lrel);
  L, Labs_to_L := OptimizedRepresentation(Labs);
  Q2 := C2(L)! [Labs_to_L(Labs!c) : c in Eltseq(Q2)];
  vprint CasselsTate: "Biquadratic field L has optimized representation", DefiningPolynomial(L); 

  // The second step is to get a divisor in Div^2(C) over L that "sums" to Q2
  // For this we consider the 2-covering over L given by C -> C2 == E, where this 
  // iso sends Q2 to O_E, and trivialise the obstruction by solving a conic over L.
  // First we embed C as a QI with hyperplane sections adding up to Q2 on C2.

// Extend if there are base points, in case base points make the computations below much worse
// TO DO: include alternative eqns in these covering maps so they are always defined everywhere
assert IsEmpty(BaseScheme(CtoC2));
//if not IsEmpty(BaseScheme(CtoC2)) then 
// printf "extending CtoC2 ... "; time CtoC2 := Extend(CtoC2); end if;

  CL := BaseChange(C,L);  C2L := BaseChange(C2,L);
  CLtoC2L := map< CL -> C2L | AllDefiningPolynomials(CtoC2) : Check:=debug >;
  // TO DO: the next bit is a major problem...
  // Novel idea(!) -- could define H by specifying its points
  
  vprint CasselsTate,2: "Getting H ... ";  
  Q2pullback := (C2L!Q2) @@ CLtoC2L; // = pullback of Q2 to C
//Q2pullback := Pullback(CLtoC2L, Place(C2L!Q2) ); 
  
  // First try just fixing up the ideal defining this

  // TO DO: looks like pullbacks of points could benefit from some careful treatment,
  // at least when we know a lot about the variety, eg the pullback scheme will have 
  // components in one dimension only, will be radical, etc, 
  // In certain situations it makes sense to Groebner (currently this doesn't get done
  // even when we create the divisor, for instance)

  IQ2 := DefiningIdeal(Q2pullback);  
vprintf CasselsTate,2: "Groebner ... "; vtime CasselsTate,2:
  Groebner(IQ2 : ReduceInitial:=false );
vprintf CasselsTate,2: "Radical ... "; vtime CasselsTate,2:
  IQ2 := Radical(IQ2);  // really it should be already, but in fact it has some non-geometric components
  Q2pullback := Scheme( Ambient(CL), IQ2);
vprintf CasselsTate,2: "Divisor ... "; vtime CasselsTate,2: 
  H := Divisor(CL, Q2pullback);  assert Degree(H) eq 4;  
  FCL := FunctionField(CL);
  _,alffmap := AlgorithmicFunctionField(FCL); 
  Pr3<R,S,T,U> := ProjectiveSpace(L,3);
vprintf CasselsTate,2: "Riemann-Roch ... "; vtime CasselsTate,2:
  RRbasis_alff := Basis(FunctionFieldDivisor(H) : Reduction:=true, Simplification:="Full");
vprintf CasselsTate,2: "alff basis --> basis ... "; vtime CasselsTate,2:
  RRbasis := [b @@ alffmap : b in RRbasis_alff];  assert #RRbasis eq 4;
 
  vprintf CasselsTate, 2: "Choosing a nicer basis ... "; time_nicer := Cputime(); 
  basL := Basis(L);

  // Method 1: create vectors by clearing denoms and taking coeffs of the polys
  Pol := OriginalRing(Parent(Numerator(RRbasis[1]))); 
  PolFF := FieldOfFractions(Pol);
  // Multiply through by denoms, obtaining an isomorphic RR space consisting of polynomials
  RRbasis_PolFF := ChangeUniverse(RRbasis, PolFF);
  lcm := LCM([Pol| Denominator(rrb) : rrb in RRbasis_PolFF ]);
  RRbasis_integral := [Pol| ];
  for rrb in RRbasis_PolFF do 
    bool, num := IsCoercible(Pol, lcm*rrb);  assert bool;
    Append(~RRbasis_integral, num);
  end for;
  RRbasis_integral_over_Q := [Pol| b * rrb : b in basL, rrb in RRbasis_integral];
  mons := Setseq(Seqset( &cat [Monomials(pol) : pol in RRbasis_integral] ));
  RRbasis_eltseqs := [&cat [Eltseq(MonomialCoefficient(pol,mon)) : mon in mons] : pol in RRbasis_integral_over_Q]; 
  mat0 := Matrix(RRbasis_eltseqs); 
/*  
  // Method 2: create vectors by taking values at small points on CL
  // This code doesn't work yet, seems hard to get nice points even though CL has nice equations
  RRbasis_over_Q := [b * rrb : b in basL, rrb in RRbasis];
  RRbasis_integral := RRbasis;  lcm := 1;  // no need to clear denoms (just need to define these for below)
  mat0 := ZeroMatrix(Q, 16, 0);
  u := PolynomialRing(L).1;
  ijs := [[i,j] : i,j in [1..4] | i lt j];
vprintf CasselsTate,2: "Get some small points on CL ... "; vtime CasselsTate,2:
"\nCL is", CL;
  for ij in ijs, a in [1..2] do
    i,j := Explode(ij);
    k := Min([k : k in [1..4] | k notin {1,i,j}]);
    CLsection := Scheme(CL, CL.i - a*CL.j);
    polM := Basis(EliminationIdeal( DefiningIdeal(CLsection), {1,k}))[1];
    pol := Evaluate(polM, [u,1,1,1]); assert Degree(pol) eq 4;
    field := NumberField(Factorization(pol)[1][1]);
    pts := Points(CLsection, field); assert #pts gt 0; // TO DO: write down the pt quickly
    // TO DO: toss out poles of the functions
    try 
      // TO DO: only need to evaluate RRbasis, not RRbasis_over_Q
      eltseqs := [ &cat [Eltseq(c) : c in Eltseq(Evaluate(rrb, pts[1]))] : rrb in RRbasis_over_Q ];
      mat0 := HorizontalJoin(mat0, Matrix(eltseqs));
i,j,k, "field is", DefiningPolynomial(field); 
"evaluated at pt =", pts[1];
    catch ERR vprint CasselsTate,2: "Problem evaluating at random point"; end try;
  end for;
*/
  assert assigned mat0 and assigned RRbasis_integral and assigned lcm; 
  assert BaseRing(mat0) eq Q and Ncols(mat0) ge 16;
  mat1 := Saturation(mat0); 
  sat, kern := Solution(mat0, ChangeRing(mat1,Q) ); assert Dimension(kern) eq 0; // sat*mat0 = mat1
  mat2, lll := LLL(mat1);
  cob := ChangeRing(lll,Q) * sat;  
  if paranoid then assert cob * ChangeRing(mat0,Q) eq ChangeRing(mat2,Q); end if;
  cobL := Matrix(L, 16, 4, [[L| &+[ cob[i,4*k+j]*basL[j] : j in [1..4]] : k in [0..3]] : i in [1..16]] );
  // Get indices of first 4 rows that are independent over L
  indices := [1];
  Ech := Submatrix(cobL, 1,1, 1,4);
  r := 1;
  i := 1;
  while r lt 4 or debug and i lt 16 do 
    i +:= 1;
    Ech := EchelonForm(VerticalJoin(Ech, Submatrix(cobL, i,1, 1,4) ));
    if r lt Rank(Ech) then 
      r +:= 1;
      Append(~indices, i);
    end if;
  end while;
  RRbasis := [&+[ cobL[i,j] * RRbasis_integral[j] : j in [1..4] ] : i in indices];
  RRbasis_alff := [&+[cobL[i,j] * RRbasis_alff[j] : j in [1..4] ] : i in indices]; // still with denoms
  if paranoid then assert RRbasis_alff eq [(FCL!b/FCL!lcm) @alffmap : b in RRbasis]; end if;
  vprintf CasselsTate, 2: "%o sec\n", Cputime(time_nicer); 
  
  //RRbasis := RiemannRochBasisQI(H);

  vprintf CasselsTate,2: "Getting the RR image CLQI using alff relations ... ";  time0_rels := Cputime();  
  monsL := MonomialsOfDegree(PolynomialRing(L,4),2);
  RRquads_alff := [Evaluate(mon, RRbasis_alff) : mon in monsL];
  rels_alff := Relations(RRquads_alff, L); assert Dimension(rels_alff) eq 2;  
  vprintf CasselsTate,2: "%o sec\n", Cputime(time0_rels);
  monsPr3 := [Evaluate(mon, [Pr3.i : i in [1..4]]) : mon in monsL];
  CLQI := Curve(Pr3, [&+ [rel[i]*monsPr3[i] : i in [1..#monsPr3]] : rel in Basis(rels_alff) ]);
  CLtoCLQI := map< CL -> CLQI | RRbasis : Check:=debug >;
  vprint CasselsTate, 3: "4-covering embedded differently as QI over L is", CLQI;

  // The preimage of Q2 in CLQI is a hyperplane section; find this hyperplane
  // (Note: much faster to push a representative point rather than the divisor)
  Q2preimages := [* pt @CLtoCLQI : pt in RepresentativePoints(Q2pullback) *];
  Q2preimages := [* Ambient(CLQI)(Ring(Parent(pt)))! pt : pt in Q2preimages *]; // LinearSystem requires points in ambient
  assert &+ [Degree(Ring(Parent(pt)), L) : pt in Q2preimages] eq 4;
/*
// check cluster thing
assert &+ [Degree(Cluster(rpt)) : rpt in Q2preimages] eq 4;
  // LinearSystem was broken; anyway using Relations is a better way
  LS := LinearSystem(Ambient(CLQI), 1);
  for pt in Q2preimages do
    LS := LinearSystem(LS, pt);
  end for;
  assert #Sections(LS) eq 1;
  Q2hyperplane := LS.1;
*/
  // find the hyperplane whose divisor is the image of H by identifying 1 in the Riemann-Roch space
  RR1 := Relations(RRbasis_alff cat [1], L); 
  assert Dimension(RR1) eq 1;
  r := Eltseq(RR1.1);
  assert r[5] eq 1 and exists(l){r[i] : i in [1..4] | r[i] ne 0};
  Q2hyperplane := &+ [r[i]/l * CLQI.i : i in [1..4]];
  if false or debug then
    if IsEmpty(BaseScheme(CLtoCLQI)) then
      // can get away with scheme pullback
printf "Create hyperplane divisor: "; time
      HCLQI := Scheme(CLQI, [Q2hyperplane]);
      assert Degree(HCLQI) eq 4;
printf "Scheme pullback: "; time
      assert H eq Divisor(CL, HCLQI @@ CLtoCLQI);
    else
printf "Create hyperplane divisor: "; time
      HCLQI := Divisor(CLQI, Scheme(CLQI, [Q2hyperplane]));
      assert Degree(HCLQI) eq 4;
printf "Divisor pullback: "; time
      assert H eq Pullback(CLtoCLQI, HCLQI);
    end if;
  end if;

  vprintf CasselsTate: "Trivializing obstruction for QI over %o \n", L; 
  IndentPush(); 
  CLhyptoCLQI := remove_obstruction(CLQI, Q2hyperplane);
  IndentPop();

  CLhyp := Domain(CLhyptoCLQI);
  xx := 0; zz := 1;
  pol := Evaluate(DefiningPolynomial(CLhyp), [xx,u,zz]) where u is PolynomialRing(L).1;
  if IsIrreducible(pol) then
    LQ4 := NumberField(pol); 
    Q4s_on_CLhyp := [CLhyp(LQ4)! [xx, LQ4.1, zz]];
  else
    LQ4 := L;
    rts := Roots(pol);   assert &+[tup[2] : tup in rts] eq 2;
    if #rts eq 1 then rts cat:= rts; end if; // list double root twice
    Q4s_on_CLhyp := [CLhyp! [xx, tup[1], zz] : tup in rts];
  end if;
  NormDelta4 := DivisorGroup(C)!0;
  Q4s := [* *];
  for Q4CLhyp in Q4s_on_CLhyp do
    Q4CLQI := Q4CLhyp @CLhyptoCLQI;
vprintf CasselsTate,2: "Pull back Q4 to CL ... "; vtime CasselsTate,2:
    Q4Sch := Q4CLQI @@CLtoCLQI; // map is one-to-one, but pullback is a scheme containing base points
vprintf CasselsTate,2: "Points (on 0-dimensional scheme over relative field) ... "; vtime CasselsTate,2:
    Q4candidates := Points(Q4Sch, LQ4);
    ok := false;
vprintf CasselsTate,2: "Do the candidates map to Q4CLQI?  "; vtime CasselsTate,2: 
    for Q4c in Q4candidates do 
      if Q4c in BaseScheme(CLtoCLQI) then 
         continue;
      elif Q4c@CLtoCLQI eq Q4CLQI then 
         Q4 := Q4c;
         ok := true;
         break;
      end if;
    end for; 
    assert ok;
vprintf CasselsTate,2: "Getting norm by calling (my)Place ... "; vtime CasselsTate,2:
    Q4pl := myPlace(C(LQ4)! Eltseq(Q4) : DivisorOnly); // the Place is over Q, ie the sum of the conjugate points 
    m := AbsoluteDegree(LQ4) div Degree(Q4pl); // # conjugates = Degree(Q4pl), could be less than the degree of LQ4
    NormDelta4 +:= m*Q4pl;
    Append(~Q4s, <Q4,m>); // for checking addition
  end for;
  assert Degree(NormDelta4) eq 8;
  Delta0 := Divisor(C, Scheme(C, C.1)); 
  Delta := NormDelta4 - 2*Delta0;
  vprintf CasselsTate,2: "Get magic function by Riemann-Roch ... "; vtime CasselsTate,2:
  bool, magic_f := IsPrincipal(Delta);  assert bool;
  // adjust magic_f if it has some common factors 
  magic_f *:= GCD(&cat[ Coefficients(Denominator(cc)) : cc in Coefficients(magic_f) ]);  
  magic_f /:= GCD(&cat[ Coefficients(Numerator(cc)) : cc in Coefficients(magic_f) ]);
  vprint CasselsTate,2: "The function on C that defines the Azumaya algebra is \n", magic_f;
 
  // TO DO: (if paranoid) check that the points of N add to a point on E with rational x coord = x(P) 

  // decide which primes are bad ... TO DO: isn't C integral???
  badprimesC := Seqset(PrimeDivisors(Numerator(disc)) cat PrimeDivisors(Denominator(disc))) 
                                                where disc is Discriminant(GenusOneModel(C));
  badprimesD := Seqset(PrimeDivisors(Integers()! Discriminant(GenusOneModel(D)) ));
  badprimesFD := Seqset(PrimeDivisors(Discriminant(FD)));
  // get primes where magic_f might reduce to 0 or infinity ... TO DO: with more thought!
  univ_polys := &cat[ [Numerator(cc), Denominator(cc)] : cc in Coefficients(magic_f) ]; 
                       // the cc's are rational functions in the base variable of the FunctionField
  badprimesmagicf := Seqset(&cat[ PrimeDivisors(GCD(Coefficients(up))) : up in univ_polys ]);
  smallprimes := Seqset(PrimesUpTo(23)); // the function has degree 8, need 16 < p - 2sqrtp ie p > 23
  if debug then smallprimes := Seqset(PrimesUpTo(100)); end if;
  if paranoid then smallprimes := Seqset(PrimesUpTo(1000)); end if;
  badprimes := Sort(Setseq( badprimesC join badprimesD join badprimesmagicf join badprimesFD join smallprimes ));  
  vprintf CasselsTate : "The bad primes are: \n  %o for the 4-covering, \n  %o for the 2-covering," * 
                                            "\n  %o for the magic function, and \n  %o for the quadratic extension\n", 
                                               badprimesC, badprimesD, badprimesmagicf, badprimesFD;

  vprint CasselsTate: "Local invariants:";
  // How many times shall we compute each invariant? (using different local points)
  CHECKS := debug select 20 else 2;

  if Discriminant(FD) gt 0 then 
    invt := 0;
  else
    size := Max(&cat[ Coefficients(up) : up in univ_polys ]);
    prec := 100 + Ilog(10, Round(size)); // maybe don't really need high prec
    it := 0;
    while it lt CHECKS do
      while true do 
        bool, realpt := HasRealPoint(C : Precision:=prec);  assert bool;
        if Abs(realpt[4]) le 10^-20 then continue; end if;
        realpt := [realpt[i]/realpt[4] : i in [1..4]];
        success, magic_val := plug_in( magic_f, realpt[1..3] : max_val:=20);  
//success, ChangeUniverse(realpt, RealField(10)), RealField(10)! magic_val;
        if success then break; end if;
      end while;
      invt := (1 - Sign(magic_val)) div 2;  // convert from {1,-1} to {0,1}
      if it eq 0 then invt1 := invt; else assert invt eq invt1; end if;
      it +:= 1;
    end while;
  end if;
  vprintf CasselsTate : "  real place : %o\n", invt;
  ans := invt mod 2;

  for p in badprimes do 
    for it := 1 to CHECKS do  
      prec := 20;
      repeat 
        Pp := local_point_on_QI(C, p : prec:=prec);  // over Qp, with Pp[4] = 1
        success, magic_val := plug_in( magic_f, Pp[1..3] : max_val := prec div 4 );
        if success then 
//Pp, magic_val;
           success := Precision(magic_val) ge 10;
        end if;
        prec *:= 2;
      until success;
      hilb := HilbertSymbol( Q! magic_val, Q! Discriminant(FD), p);
      invt := (1-hilb) div 2;  // convert from {1,-1} to {0,1}
      if it eq 1 then invt1 := invt; Pp1 := Pp; else assert invt eq invt1; end if;
    end for; // it
    vprintf CasselsTate : "  %o : %o\n", p, invt;
    ans := (ans + invt) mod 2;
  end for;
  return ans;
end intrinsic;

//////////////////////////////   THE 2-ISOGENY CASE   //////////////////////////////   

// TO DO: Consolidate code that is common to the 2 x 2 case ??

// TO DO: Need to make sure that the coverings respect the involutions 
//    (otherwise it's wrong, and will probably give an error due to getting a non-principal divisor)

// TO DO: test it!!!

function CasselsTatePairing_2isogeny(CcovEE, DcovEE : avoid:={})

  if Domain(CcovEE) eq Domain(DcovEE) then return 0; end if;

  K := Rationals();
  C := Domain(CcovEE);  
  D := Domain(DcovEE);
  EE := Codomain(CcovEE); 
  if not IsZero(h) where _,h := HyperellipticPolynomials(C) then 
    C, oldC_to_C := SimplifiedModel(C);  CcovEE := Inverse(oldC_to_C) * CcovEE; end if;
  if not IsZero(h) where _,h := HyperellipticPolynomials(D) then 
    D, oldD_to_D := SimplifiedModel(D);  DcovEE := Inverse(oldD_to_D) * DcovEE; end if;

  // check that the coverings respect the involutions.  TO DO: make it work in general
  iC := map< C -> C | [C.1,-C.2,C.3] >;
  iD := map< D -> D | [D.1,-D.2,D.3] >;
  iEE := map< EE -> EE | [EE.1,-EE.2,EE.3] >;
  okay := Expand(iC * CcovEE) eq Expand(CcovEE * iEE) 
      and Expand(iD * DcovEE) eq Expand(DcovEE * iEE);
  error if not okay, "Not implemented for these coverings. " * 
                     "Give covering maps that are compatible with the involutions on the curves";

  PD, FD := quadratic_point(D, DcovEE : avoid:=avoid, num:=20); 
  if FD eq K then return 0; end if;
  PEE := DcovEE(PD);
  vprint CasselsTate: "Using the quadratic field", DefiningPolynomial(FD);
 
  // Get the magic function
  DivPEE := Divisor(Place(PEE));  assert Degree(DivPEE) eq 2; // DivPEE = PEE + PEE^sigma
  NormDelta := Pullback(CcovEE, DivPEE);  assert Degree(NormDelta) eq 4;
  Delta0 := Divisor(C, (EE!0) @@ CcovEE );  
  if Degree(Delta0) ne 2 then  // sigh ... the usual crap 
    CcovEE := Extend(CcovEE);
    Delta0 := Divisor(C, (EE!0) @@ CcovEE ); assert Degree(Delta0) eq 2;
  end if;
  bool, magic_f := IsPrincipal(NormDelta - 2*Delta0);  assert bool;

  vprint CasselsTate: "The function used to define the Azumaya algebra is", magic_f;

  // Get invariants (copied everything below from the new version of 2 x 2 case)

  // Figure out the bad primes
  num := Numerator(magic_f);
  den := Denominator(magic_f);
  assert TotalDegree(Pol!num) le 2 and TotalDegree(Pol!den) le 2 where Pol is OriginalRing(Parent(num));
  PR<x_L,y_L> := OriginalRing(Parent(num));
  lcm_coeff_denoms := LCM([ Denominator(coeff) : coeff in Coefficients(PR!num) cat Coefficients(PR!den) ]);
  num := lcm_coeff_denoms*PR!num;
  den := lcm_coeff_denoms*PR!den;
  gcd_num_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(num) ]);
  gcd_den_coeffs := GCD([ Numerator(K!coeff) : coeff in Coefficients(den) ]);
  magic_f := Parent(magic_f)! (num/den * gcd_den_coeffs/gcd_num_coeffs);
  num := Numerator(magic_f);
  den := Denominator(magic_f);
assert GCD([ Numerator(K!coeff) : coeff in Coefficients(num) ]) eq 1 
   and GCD([ Numerator(K!coeff) : coeff in Coefficients(den) ]) eq 1;

  // Which primes do we need to look at???
  ramprimesD := Seqset(PrimeDivisors(Discriminant(FD)));
  badrednprimesC := Seqset(PrimeDivisors(Integers()!Discriminant(GenusOneModel(C))));
  badrednprimesD := Seqset(PrimeDivisors(Integers()!Discriminant(GenusOneModel(D))));
bad_magic_primes := Seqset(PrimeDivisors(gcd_num_coeffs) cat PrimeDivisors(gcd_den_coeffs));
  vprint CasselsTate : "Ramified primes for FD are", ramprimesD;
  vprintf CasselsTate : "Bad reduction primes for C and D are %o and %o\n", badrednprimesC, badrednprimesD;
  vprint CasselsTate : "Bad primes for the Azumaya algebra are", bad_magic_primes;
  smallprimes := { p : p in [2..30] | IsPrime(p) };
  reallybadprimes := ramprimesD join badrednprimesC join bad_magic_primes join smallprimes;
  badprimes := reallybadprimes join badrednprimesD;
  if debug then badprimes join:= { p : p in [2..1000] | IsPrime(p) }; end if;
  if K eq Rationals() then badprimes := [ ideal<Integers()|p> : p in Sort(Setseq(badprimes)) ]; end if;
 
  // Compute local invariants of the quat alg given by 'magic_f'
  quarticC, h := HyperellipticPolynomials(C);  assert IsZero(h);
  ans := 0;

  vprint CasselsTate : "Local invariants:";
  if IsTotallyReal(FD) then invt := 0;
  else
    repeat
      pt := real_point(quarticC : rand:=true);
      success, magic_f_val := plug_in(magic_f, pt : max_val:=20); 
    until success;
    invt := (1-Sign(K!magic_f_val)) div 2;
  end if;
  vprintf CasselsTate : "  real place : %o\n", invt;
  ans := (ans + invt) mod 2;

  for p in badprimes do
    pp := (K eq Rationals()) select Minimum(p) else p;
    fact1 := Decomposition(Integers(FD), pp)[1];
    P, e := Explode(fact1);

    Np := (K eq Rationals()) select Minimum(p) else Norm(p);
    NP := Norm(P);
    if NP eq Np and e eq 1 then invt := 0;  // trivial local restriction
    else
      invts := [];  // do it for several different local points, as a check
      num_invts := debug select 10 else 1;
      num_fails := 0;
      while #invts lt num_invts do
        // evaluate magic_f at a local point, check value is not too close to 0
        pt := local_point(quarticC, p);
        success, magic_f_val := K! plug_in(magic_f, pt : max_val:=6);
        if not success then num_fails +:= 1;
           if num_fails ge 10*num_invts then 
             return CasselsTatePairing_2isogeny(CcovEE, DcovEE : avoid := avoid join {K!(FD.1^2)} ); 
           end if;
           continue;
        end if;
        // local invariant:
        if e eq 1 then   // unramified local extension
          invt := Valuation(magic_f_val, p) mod 2;
        else             // ramified local extension
          hilb := HilbertSymbol(magic_f_val, K!Discriminant(FD), pp);
          invt := (1-hilb) div 2;  // convert from {1,-1} to {0,1}
        end if;
        Append(~invts, invt);
      end while;
      assert &and[invt eq invts[1] : invt in invts];  // check that we got the same every time
      if pp notin reallybadprimes then assert invt eq 0; end if;  // this prime should be irrelevant
    end if;
    vprintf CasselsTate : "  %o : %o\n", Minimum(p), invt;
    ans := (ans + invt) mod 2;
  end for;
  return ans;
end function;

////////////////////////////   THE 3-ISOGENY CASE   ////////////////////////////   

function CasselsTatePairing_3isogeny(cov1, cov2, phi)
  error "Not implemented";
end function;

/////////////////////// Interface for the isogeny cases ///////////////////////

// TO DO: Should we omit phi from the signature ??

intrinsic CasselsTatePairing(cov1::MapSch, cov2::MapSch, phi::MapSch) -> RngIntElt
{Given a 2-isogeny or 3-isogeny phi : E -> E' between elliptic curves over a field K,
and coverings cov1 : C -> E' and cov2 : D -> E' that correspond to elements of H^1(Q,E[phi]),
this returns the Cassels-Tate pairing between cov1 and cov2 as an element of Z/2}

  E := Domain(phi);  EE := Codomain(phi);
  C := Domain(cov1);  D := Domain(cov2);
  degphi := Degree(phi);
  K := Rationals();
  require BaseField(E) eq K and BaseField(EE) eq K and BaseField(C) eq K and BaseField(D) eq K :
         "All the given curves and maps should be defined over the rationals";
  require Type(E) eq CrvEll and Type(EE) eq CrvEll and Codomain(cov1) eq EE and Codomain(cov2) eq EE :
         "The third argument should be an isogeny E -> E' of elliptic curves, and " *
         "the first two arguments should be covering maps C -> E' and D -> E'";
  require degphi in {2,3} : "The isogeny phi should have degree 2 or 3";
  require Degree(cov1) eq degphi and Degree(cov2) eq degphi :
         "The first two arguments should be covering maps with the same degree and codomain " *
         "as the third argument (which should be an isogeny between elliptic curves)";

  if degphi eq 2 then 
    require Type(C) eq CrvHyp and (h eq 0 where _,h := HyperellipticPolynomials(C)) and 
            Type(D) eq CrvHyp and (h eq 0 where _,h := HyperellipticPolynomials(D)) : 
           "In the 2-isogeny case, the first two arguments should be covering maps of degree 2, " *
           "whose domains are hyperelliptic curves of the form y^2 = quartic(x)";
    return CasselsTatePairing_2isogeny(cov1, cov2);
  elif degphi eq 3 then 
    error "Not implemented";
    require Degree(C) eq 3 and Dimension(Ambient(3)) eq 2 and Degree(D) eq 3 and Dimension(Ambient(D)) eq 2 :
           "In the 3-isogeny case, the first two arguments should be covering maps of degree 3, " *
           "whose domains are cubic curves in the projective plane";
    return CasselsTatePairing_3isogeny(cov1, cov2, phi);
  end if;
end intrinsic;
