freeze;

///////////////////////////////////////////////////////////////////
//                                                               // 
// 2-descent for curves over number fields.                      // 
//                                                               // 
// Steve Donnelly, June 2011                                     // 
// (with some remnants of earlier version by Mark Watkins)       // 
//                                                               // 
// Note: code for curves over Q is in CrvEll/two_desc.m          // 
//                                                               // 
///////////////////////////////////////////////////////////////////

// TO DO: TwoCover (for individual Selmer elements), as for FldRat

import "../CrvCon/points.m": reduce_ideal, small_element;
//import "../CrvRat/param.m": ds_param;

declare verbose TwoDescent, 2;

debug := false;

function selmer_quo(E, remove_tors, remove_gens)
 F := BaseRing(E);
 S, m := TwoSelmerGroup(E);
 A<theta> := Domain(m);
 assert F eq BaseRing(A);
 f := Modulus(A);
 if debug then
   assert IsIsomorphic(E, EllipticCurve(f));
 end if;

 // Construct quotient S/<2-torsion, generators> if required
 pts := [];
 if remove_tors or not IsEmpty(remove_gens) then
   E2 := EllipticCurve(f);
 end if;
 if remove_tors then
   T2, mT2 := TorsionSubgroup(E2);
   pts := [E2(F)| mT2(x) : x in Generators(T2)]; 
 end if;
 if not IsEmpty(remove_gens) then
   bool, EtoE2 := IsIsomorphic(E, E2); assert bool;
   pts cat:= [E2(F)| P@EtoE2 : P in remove_gens];
 end if;
 if IsEmpty(pts) then
   return S, m; 
 else
   xcoords := [P[1]/P[3] : P in pts | P[3] ne 0];
   im := [A| ];
   for x0 in xcoords do
     if Evaluate(f, x0) ne 0 then
       v := x0 - theta;
     else
       // write f(x) = (x - theta) * g(x)
       PA := PolynomialRing(A); 
       x := PA.1;
       fA := Evaluate(f, x);
       gA := fA div (x - theta);
       v := (x0 - theta) + Evaluate(gA, x0);
       // A is a sum of fields; in each field, precisely
       // one of (x0 - theta) and g(x0) is zero
     end if;
     Append(~im, v);
   end for;
   Sim, StoSim := quo< S | [m(a) : a in im] >; 
   return Sim, m*StoSim; 
 end if;
end function;

function hereht(x) 
 if x eq 0 then return 0; end if;
 return Ilog(2,Max(Abs(Numerator(x)),Abs(Denominator(x)))); 
end function;

// paramatrisation returned as a sequence of 3 binary quadratic forms
function parametrization(conic)  // CrvCon -> [ RngMPolElt ]
 K:=BaseRing(conic);
 if Type(K) eq FldRat then 
  g:=Max([hereht(x) : x in Eltseq(M) where _,M:=IsDefinedByQuadric(conic)]);
  vprintf TwoDescent: "Size of Conic is %o\n",g; // Should use Parametrization?
  CP:=ParametrizationMatrix(conic); 
  vprintf TwoDescent,2: "Param mat %o\n",CP;
  XX:=ProjectiveSpace(K,1); PX2:=[XX.1^2,XX.1*XX.2,XX.2^2];
  uu:=[ &+[CP[i,j]*PX2[i] : i in [1..3]] : j in [1..3]];
 elif ISA(Type(K),FldAlg) and AbsoluteDegree(K) eq 1 then // TO DO: change calling functions so this case won't occur
  uuQ:=parametrization(ChangeRing(conic,Rationals()));
  uu:=ChangeUniverse(uuQ,PolynomialRing(K,2));
 elif ISA(Type(K),FldAlg) then  
  has_sol, sol := HasRationalPoint(conic:Check:=false); // don't check local solubility
  assert has_sol; // assuming 2-covering was locally soluble
  uu := DefiningEquations(Parametrization(conic,sol));
  // uu := ds_param(conic, sol); // TO DO
 end if;
 return uu; 
end function;


// return s1, s2 in R such that x = x1*s2^2, for x in Q
// TO DO: use easy_factorization instead of TrialDivision

function square_factor(x, R)
  bool, x := IsCoercible(Rationals(), x); assert bool;
  bool, s2 := IsSquare(R!x);
  if not bool then 
    s2 := 1;
    _, hard := TrialDivision(Denominator(x));
    bool, s := IsSquare(R!&*hard);
    if bool then
      s2 /:= s;
    end if;
    _, hard := TrialDivision(Numerator(x));
    bool, s := IsSquare(R!&*hard);
    if bool then
      s2 *:= s;
    end if;
  end if;
  return x/s2^2, s2;
end function;

// RngUPolElt or RngMPolElt -> RngUPolElt

function minimise_and_reduce(quartic)
  q0:=quartic; 
  q:=q0; 
  K:=BaseRing(Parent(q)); 

  // Clear denoms and try to remove square common factors
  if Type(K) eq FldRat then
    L:=LCM([Denominator(t) : t in Coefficients(q)]);
    a,b:=SquarefreeFactorization(L);  
    _,ss:=IsSquare(a*L);  

  elif ISA(Type(K), FldAlg) then
    ZK:=Integers(K);
    C := ideal<ZK|Coefficients(q)>;
    ss:=1;
    if Denominator(C) ne 1 or Minimum(C) ne 1 then
      denoms := [Denominator(c) : c in Coefficients(q)]; 
      // There are sometimes large square common factors.
      g := GCD(denoms);
      _,s := square_factor(g, K);
      ss *:= s;
      C := s^2*C;
      _,s := square_factor(Denominator(C), K);
      ss *:= s;
      C := s^2*C;
      _,s := square_factor(Numerator(Minimum(C)), K);
      ss /:= s;
      C := 1/s^2*C;

      small := {t[1] : t in TrialDivision(Denominator(C), 10^6)} join
               {t[1] : t in TrialDivision(Numerator(Minimum(C)), 10^6)};
      Cfact := [* *];
      for p in small, tup in Decomposition(ZK,p) do 
        P := tup[1];
        vP := Valuation(C, P);
        if vP ne 0 then
          Append(~Cfact, <P, vP>);
          C /:= P^vP;
        end if;
      end for;
      bool, sC := IsSquare(C);
      if bool then 
        Append(~Cfact, <sC,2>);
      else
        Cfact cat:= Factorization(C);
      end if;

      I := &* [t[1]^(t[2] div 2) : t in Cfact];
      _, sI := reduce_ideal(I);
      ss *:= sI;
//"sI =", sI, "extra norm =", Norm(sI*I);
    end if;

  else
    ss := 1;
  end if;

  q := ss^2 * q; 

  PK:=PolynomialRing(K); 
  ZorK:=(K eq Rationals()) select Integers() else K; 
  x:=PolynomialRing(ZorK).1;

  if Type(q) eq RngMPolElt then
     q:=Evaluate(q,[x,1]); 
     q0:=Evaluate(q0,[PK.1,1]);  
  end if;
/* 
  // TO DO: case where 2-covering is a cubic (just use E itself)
  if Degree(q) eq 3 and K eq Rationals() then 
     q0:=q;  E := MinimalModel(EllipticCurve(q));
     a1,a2,a3,a4,a6 := Explode(Coefficients(E));
     b2:=a2+a1^2/4;  b4:=a4+a1*a3/2;  b6:=a6+a3^2/4;
     while not &and[IsIntegral(bb) : bb in [b2,b4,b6]] do
       b2*:=4; b4*:=16; b6*:=64; 
     end while;
     q := x^3 + ZorK!b2*x^2 + ZorK!b4*x + ZorK!b6;   
     bool, transmap:=IsIsomorphic(EllipticCurve(q0), EllipticCurve(q)); assert bool;
     eqs:=DefiningEquations(transmap);  
     bool, y_scaling:=IsSquare(Evaluate(eqs[2],[0,1,0])); assert bool;
     A:=MonomialCoefficient(eqs[1],[1,0,0]);
     B:=MonomialCoefficient(eqs[1],[0,0,0]);
     den:=LCM(Denominator(A),Denominator(B));  
     trans1:=Matrix(2,2,[A,0,B,den]);
     assert q eq y_scaling^2*q0^trans1; 
  end if;
*/
  if K eq Rationals() and Degree(q) eq 4 then 
     q, tr1, s := QuarticMinimise(q);
     s *:= ss; 
     q, tr2 := QuarticReduce(q); 
     t := tr1 * tr2; 
     assert ChangeRing(q,K) eq s^2*q0^t; 
     return q, t, s;
  elif ISA(Type(K), FldAlg) then
     m := GenusOneModel(q);
     mmin, tr1 := Minimise(m);
     mred, tr2 := Reduce(mmin);
     tr := tr2 * tr1;
     q := HyperellipticPolynomials(HyperellipticCurve(mred));
     s := ss * tr`Scalar;
     t := Transpose(tr`Matrix);
     assert q eq s^2*q0^t;
     return q, t, s;
  else 
     return q0, IdentityMatrix(K,2), ss;
  end if;
end function;

// Nice basis of a frac ideal of a relative order

function lll_basis(I)
  Z := Order(I);
  L := FieldOfFractions(Z);
  K := BaseField(L);
  Za := AbsoluteOrder(Z);
  Ia := Za!!I;
  Ba := [L!b : b in LLLBasis(Za!!I)];
  B := [L|];
  V := VectorSpace(K, Degree(L));
  W := sub<V|>;
  for b in Ba do 
    Include(~W, V!Eltseq(b), ~new);
    if new then Append(~B,b); end if;
    if W eq V then break; end if;
  end for;
  return B;
end function;

// TO DO: NiceRepresentativeModuloPowers should do something like this
function nicify(x)
  prev := {@ @}; // keep in order just for debugging
  repeat
    Include(~prev, x); 
    x := NiceRepresentativeModuloPowers(x, 2);
  until x in prev;
  return x;
end function;
  

// TO DO 
//  MinRedEffort ???
//  for fields of degree 1, interface to FldRat case

declare attributes CrvEll: TwoDescent;

intrinsic TwoDescent(E::CrvEll[FldAlg] : RemoveTorsion:=false,
                                         RemoveGens:={},
                                         MinRed:=0,
                                         MinRedEffort:=0,
                                         WithMaps:=true)
       -> SeqEnum[CrvHyp], List, Map

{A sequence of reduced 2-covering curves of the form y^2=quartic(x),
corresponding to the nontrivial elements of the 2-Selmer group of E.
If the option 'WithMaps' is set to true, the second object returned 
is a corresponding list of maps from each 2-covering curve to E.
The third object returned is a map (with inverse) from an abstract 
group to the sequence of 2-coverings: this abstract group is either
TwoSelmerGroup(E), or a quotient if RemoveTorsion or RemoveGens 
were specified.}

  K:=BaseRing(E);

  // Set defaults: MinRed:=true whenever it works, MinRedEffort:=10
  if MinRed cmpeq 0 or MinRedEffort gt 0 then
    MinRed := true;
  end if;
  if MinRed and MinRedEffort eq 0 then
    MinRedEffort := 10;
  end if;

  // Caching:
  // E`TwoDescent is a list of tuples of the form
  //  < RemoveTorsion [Bool], MinRed [Bool], curves [Seq], Selmer elts [SetIndx] >
  // Convention: if E[2] is trivial, we always set RemoveTorsion to be false
  // No caching is done when RemoveGens is given (TO DO)

  if RemoveTorsion and #TwoTorsionSubgroup(E) eq 1 then
    RemoveTorsion := false;
  end if;

  cached := false;
  cached_red := false;
  if assigned E`TwoDescent and IsEmpty(RemoveGens) then
    TD := E`TwoDescent;
    // preferably return reduced quartics, if we have them
    if exists(t){t: t in TD | t[2] and RemoveTorsion eq t[1]} then
      quartics := t[3];
      selmer_elts := t[4];
      cached := true;
      cached_red := true;
    elif exists(t){t: t in TD | RemoveTorsion eq t[1]} then
      quartics := t[3];
      selmer_elts := t[4];
      cached := true;
      if MinRed then
        // remove this record from the cache; the reduced curves will be cached below
        E`TwoDescent := [* tt : tt in E`TwoDescent | not IsIdentical(tt,t) *];
      end if;
    end if;
  elif not assigned E`TwoDescent then
    E`TwoDescent := [* *];
  end if;

  if not cached then
         
    require #RemoveGens eq 0 or Curve(Random(RemoveGens)) eq E:
      "The generators specified in RemoveGens are not on the curve";

    /*
    if #TwoTorsionSubgroup(E) gt 1 then  // TO DO: use descent by 2-isogenies
      Cs,_,CCs:=TwoIsogenyDescent(E:RemoveDualIsogenyKernel,MinRed:=false); 
      Ds:=&cat[TwoDescendantsOverTwoIsogenyDescendant(C):C in Cs];
      // TO DO: Remove Torsion or Gens if desired 
      if RemoveTorsion then 
        print "WARNING: RemoveTorsion option not available in this case"; 
      elif not IsEmpty(RemoveGens) then 
        print "WARNING: RemoveGens option not available in this case"; 
      end if;
      return CCs cat Ds; 
    end if;
    */

    vprintf TwoDescent: "Computing the 2-Selmer group ... "; 
    vtime TwoDescent:
    S, m := selmer_quo(E, RemoveTorsion, RemoveGens); 

    selmer_elts := {@ S | s : s in S | not IsId(s) @};

    quartics := [PowerStructure(CrvHyp)| ];
    A := Domain(m); 
    assert assigned A`AbsoluteMap;
    AAA, mAAA := AbsoluteAlgebra(A);
    // AAA is used to nicify elements
    // TO DO: this should be part of the Selmer map
    // TO DO: how well does it work in the non-irred case?
    f := Modulus(A); 
    irred := IsIrreducible(f);
    if irred then 
      AA := ext<K|f>;
    else 
     //AA := [ext<K|t[1]>: t in Factorization(f)]; 
     //toAA := [hom<A->L|L.1>: L in AA]; // TO DO: just use matrices
    end if;
    
    for s in selmer_elts do 
     e0 := s @@ m;
     e := < nicify(ei) : ei in mAAA(e0) > @@ mAAA;
     vprintf TwoDescent,2: "\nSelmer element = %o\n", e;

     // write down arbitrary square using appropriate basis
     if irred then
       ZA:=Integers(AA); 
       ee:=AA!EltseqPad(e);
       I:=(&*[PowerIdeal(ZA)| t[1]^(t[2] div 2) 
                           : t in Factorization(ee*ZA) | t[2] div 2 ne 0])^-1;
       BI:=Basis(I); 
       CI:=CoefficientIdeals(I); 
       cI:=[small_element(c:class): c in CI]; // TO DO: small elements in inverses instead?
//"Coefficient ideals have norms", [Norm(c): c in CI];
//"extra norm in ideal =", &*[Norm(cI[i]*CI[i]^-1): i in [1..3]];
       /* what was this?
       BI:=lll_basis(I); 
       cI:=[AA!1 : b in BI];
       */
       bas:=[A!Eltseq(AA!(cI[i]*BI[i])) : i in [1..3]];
     else 
       bas:=[A|A.1^2,A.1,1]; // TO DO!!!
     end if;

     P1:=PolynomialRing(A,4); 
     h:=hom<A->P1 | P1.4>;
     u:=P1.1; v:=P1.2; w:=P1.3; 
     h2:=hom<P1->P1 | h,u,v,w,P1.4>;
     sqN:=(u*bas[1]+v*bas[2]+w*bas[3])^2; 
     thQ:=e*sqN; 
     h2thQ:=h2(thQ);
     q1:=Coefficient(h2thQ,P1.4,1); 
     q2:=Coefficient(h2thQ,P1.4,2);
     vprintf TwoDescent,2 : "Quadric intersection is:\n0 = %o,\n-z^2 = %o\n",q2,q1;
     Q3:=PolynomialRing(K,3); 
     PS:=ProjectivePlane(K);
     h3:=hom<P1->Q3 | Q3.1,Q3.2,Q3.3,1>; 
     c:=Conic(PS,h3(q2));
     uu:=parametrization(c); 
     Q:=-Evaluate(h3(q1),uu);
     Append(~quartics, HyperellipticCurve(GenusOneModel(Q))); // convert from RngMPolElt

    end for; // s in S

  end if; // not cached

  if MinRed and not cached_red then
    quartics := [HyperellipticCurve(minimise_and_reduce(
                     HyperellipticPolynomials(Q))) : Q in quartics];
  end if;

  if (not cached or MinRed and not cached_red) and IsEmpty(RemoveGens) then
    Append(~E`TwoDescent,  <RemoveTorsion, MinRed, quartics, selmer_elts>);
  end if;

  // Silly map between S and {quartics and E}
  S := Universe(selmer_elts);
  selmer_map := map< S  -> cop<quartics, [E]> | 
                     s :-> IsId(s) select E 
                                    else quartics[Index(selmer_elts,s)],
                     q :-> Type(Retrieve(q)) eq CrvEll 
                                   select S.0 
                                    else selmer_elts[Index(quartics,q)]
                   >;

  if WithMaps then 
    maps := [* CtoE where _,CtoE := AssociatedEllipticCurve(C:E:=E) : C in quartics *]; 
    return quartics, maps, selmer_map; 
  else 
    return quartics, _, selmer_map; 
  end if;
end intrinsic;

/************************************************************************

                DESCENT BY 2-ISOGENIES 

************************************************************************/

// For E : y^2 = x(x^2+cx+d), get coverings C->E parallel to phi : EE -> E
function TwoIsogenyDescent_internal(c, d, E : RemoveIsogenyKernel:=false, MinRed:=true )  
//    -> SeqEnum[ CrvHyp ], List
  // TO DO: Over Q, don't call SelmerGroup ... get quartics from the internal two descent instead
  Sel, Selmap := SelmerGroup(DualIsogeny(TwoIsogeny(E![0,0])));   
  K := BaseRing(E);   assert Domain(Selmap) cmpeq K;
  d1s := [ s @@ Selmap : s in Sel | s ne Sel!0 ];
  if K eq Rationals() then 
     d1s := [Integers()| SquarefreeFactorization(Numerator(d1)*Denominator(d1)) : d1 in d1s]; 
     d := Integers()!d;  assert &and[ d mod d1 eq 0 : d1 in d1s];  
     if RemoveIsogenyKernel then 
       alld1s := d1s; d1s := [];
       for d1 in alld1s do 
         if SquarefreeFactorization(d1*d) notin d1s cat [1] then Append(~d1s,d1); end if; 
       end for; 
     end if; 
  end if;
  Cs := [];  mapsCtoE := [* *];
  for d1 in d1s do 
     if MinRed then
        quartic,trans,scaling := minimise_and_reduce(Polynomial(Reverse([K| d1,0,c,0, d div d1])));
     else 
        quartic := Polynomial(Reverse([K| d1,0,c,0, d div d1])); 
        trans := IdentityMatrix(K,2);   scaling := 1;   
     end if;
     C := HyperellipticCurve(quartic);    
     t11,t12,t21,t22 := Explode(Eltseq( ChangeRing(trans,K) ));   
     transC := [ t11*C.1+t12*C.3, 1/scaling*C.2, t21*C.1+t22*C.3 ];
     CtoE := map< C -> E | [ d1*transC[1]^2*transC[3], d1*transC[1]*transC[2], transC[3]^3] >;
     Append( ~Cs, C);  Append( ~mapsCtoE, CtoE);  
  end for;
  return Cs, mapsCtoE; 
end function;


intrinsic TwoIsogenyDescent(E::CrvEll : Isogeny:=0, TwoTorsionPoint:=0, RemoveDualIsogenyKernel:=false, MinRed:=true) 
       -> SeqEnum[CrvHyp], List, SeqEnum[CrvHyp], List, MapSch, MapSch
{Given an elliptic curve E admitting a 2-isogeny phi E'->E, computes 2-coverings representing 
the nontrivial elements of the Selmer groups of phi and of the dual isogeny phi' E->E'.
These coverings are given as hyperelliptic curves C: y^2=quartic(x). Six objects
are returned: the sequence of coverings C of E for phi followed by the corresponding list of 
maps C->E, then similarly the coverings and maps C'->E' for phi', and finally phi and phi'. 
It's advisable to give a model for E that is nearly minimal.}
 
  K := BaseField(E);  require K cmpeq Rationals() or ISA(Type(K),FldAlg) :
       "The elliptic curve must be defined over the rationals, a number field or a function field";

  // Find the point T of order 2 in the kernel of the isogeny
  if TwoTorsionPoint cmpne 0 then 
     bool, T := IsCoercible(E(K), TwoTorsionPoint); 
     require bool : "TwoTorsionPoint should be a rational point on the elliptic curve";
     require IsZero(2*T) : "TwoTorsionPoint should have order 2";
  elif Isogeny cmpne 0 then 
     Isog_ok := exists(T){P : P in Points(Kernel(Isogeny)) | P cmpne E!0};  
     require Isog_ok: "Isogeny should be an isogeny of degree 2 from the given curve" 
                     *"to another elliptic curve, defined over the base field"; 
  else // take a random 2-torsion point
     require exists(T){E2toE(P) : P in E2 | P ne E2!0} where E2,E2toE := TwoTorsionSubgroup(E) :
        "The given elliptic curve should have at least one 2-torsion point defined over the base field";
  end if;

  // Put the curve in the form y^2 = x(x^2+cx+d) where (0,0) is the kernel of the isogeny
  Eorig := E;
  if K eq Rationals() then Emin, Eorig_Emin := MinimalModel(E);   T := T @ Eorig_Emin;
  else Emin := E; end if;
  // complete the square and translate T to (0,0) 
  a1,a2,a3,a4,a6 := Explode(aInvariants(Emin));  
  b2 := a2+a1^2/4;  b4 := a4+a1*a3/2;  b6 := a6+a3^2/4;
  xT := T[1]/T[3];   c := 3*xT+b2;  d := 3*xT^2+2*b2*xT+b4;   assert xT^3+b2*xT^2+b4*xT+b6 eq 0;
  while LCM(Denominator(c),Denominator(d)) ne 1 do c*:=4; d*:=16; end while;
  E := EllipticCurve([0,c,0,d,0]);   bool, EtoEorig := IsIsomorphic(E, Eorig);   assert bool;
  cc := -2*c;   dd := c^2-4*d;  EE :=  EllipticCurve([0,cc,0,dd,0]);
 
  Cs, mapsCtoE := TwoIsogenyDescent_internal(c,d,E: MinRed:=false);   
  mapsCtoE := [* Expand(CtoE*EtoEorig) : CtoE in mapsCtoE *];
  CCs, mapsCCtoEE := TwoIsogenyDescent_internal(cc,dd,EE: RemoveIsogenyKernel:=RemoveDualIsogenyKernel);   
  
  phi := TwoIsogeny(EE![0,0]);    phiprime := TwoIsogeny(E![0,0]);   
  bool, toE := IsIsomorphic(Codomain(phi),E);   assert bool;   
  bool, toEE := IsIsomorphic(Codomain(phiprime),EE);   assert bool;   
  phi := Expand(phi*toE*EtoEorig);   phiprime := Expand(Inverse(EtoEorig)*phiprime*toEE);   
  
  return Cs, mapsCtoE, CCs, mapsCCtoEE, phi, phiprime;  
end intrinsic;


/************************************************************************

            EXTENDING 2-ISOGENY DESCENT TO FULL 2-DESCENT

                   Steve Donnelly, November 2006
                    
                  (following John Cremona's notes)

************************************************************************/

intrinsic TwoDescendantsOverTwoIsogenyDescendant(C::CrvHyp) 
       -> SeqEnum[CrvHyp], List, MapSch
{Same as LiftDescendant}
  return LiftDescendant(C);
end intrinsic;

intrinsic LiftDescendant(C::CrvHyp) -> SeqEnum[CrvHyp], List, MapSch
{Given a hyperelliptic curve of the form C : y^2 = d1x^4+cx^2+d2,
let E be the elliptic curve y^2 = x(x^2+cx+d) where d=d1*d2. Then E admits a 2-isogeny and 
C admits a two-to-one map to E, which is a "covering arising in 2-isogeny descent on E".
Return the locally soluble coverings D of C that arise in a full 2-descent on E,
together with a list of the corresponding covering maps D -> C, and thirdly the 
covering map C -> E. (The compositions D -> E are covering maps for full 2-descent on E)}

  K := BaseRing(C);  OK := Integers(K);
  require K cmpeq Rationals() or ISA(Type(K),FldAlg):
     "The given curve must be defined over the rationals, a number field or a function field";
  f,h := HyperellipticPolynomials(C);
  C_is_legal := #Coefficients(f) eq 5;
  if C_is_legal then 
     d2, a3, c, a1, d1 := Explode(Coefficients(f));
     C_is_legal := h eq 0 and a1 eq 0 and a3 eq 0 and d1*d2 ne 0; end if;
  require C_is_legal: "The given curve must be degree 4 hyperelliptic, of the form y^2 = d1*x^4 + c*x^2 + d2";

  // Rescale when the coefficients aren't integers ..
  denom_primes := &join[ {fact[1] : fact in Factorization(Denominator(aa))} : aa in [d1,c,d2]];
  Y_scaling := 1;
  for pp in denom_primes do
    val := Max([ Valuation(Denominator(aa), pp) : aa in [d1,c,d2] ]);
    Y_scaling *:= pp^Ceiling(val/2); end for;
  d2 := OK!(Y_scaling^2*d2);  c := OK!(Y_scaling^2*c);  d1 := OK!(Y_scaling^2*d1);

  // Cremona's notation: 
  d := d1*d2; cc := -2*c; dd := c^2-4*d;
  E := EllipticCurve([0,c,0,d,0]);  // EE := EllipticCurve([0,cc,0,dd,0]);
  CtoE := map< C -> E | [ d1*C.1^2*C.3, d1*C.1*C.2*Y_scaling, C.3^3] >;
  vprintf TwoDescent,1: " C : Y^2 = %o\n  covers\n E : Y^2 = %o\n",DefiningEquation(C),DefiningEquation(E);

  Pr2 := ProjectiveSpace(K,2); X,Y,Z := Explode([Pr2.i : i in [1..3]]); // avoids assigning print names
  
  // Parametrize the conic Y^2 - d1*X^2 - c*X*Z - d2*Z^2
  vprintf TwoDescent,1: "Parametrising conic obtained from C\n";
  if not IsLocallySolvable(Conic(Pr2, Y^2 - d1*X^2 - c*X*Z - d2*Z^2)) then return [],[**],CtoE; end if;
  param := parametrization(Conic(Pr2, Y^2 - d1*X^2 - c*X*Z - d2*Z^2));
  q1,q2,q3 := Explode([ Evaluate(q, [X,Z]) : q in param ]);

  // The coverings are given as quadric intersections by 
  //    d3*s^2 - q1(X,Z),  d3*t^2 - q3(X,Z)  
  // for squarefree d3 dividing 16*d' (but taking only one of d3 and d'/d3)
  // When both the conics are soluble, make the covering a CrvHyp, D : y^2 = quartic
  // TO DO: use the group structure to help find the locally soluble sub-coset
  //      (but over Q, not using the standard SelmerGroup routine, which would be slower)
  Pr2_121 := ProjectiveSpace(K,[1,2,1]); XX,YY,ZZ := Explode([Pr2_121.i : i in [1..3]]);
  Kx := PolynomialRing(K); x := Kx.1;
  d3s := [];
  vprint TwoDescent: "dd =", dd;
  if K eq Rationals() then 
     for d3 in &cat[ [di,-di] : di in Divisors(Abs(2*Integers()!dd)) ] do 
       if IsSquarefree(d3) and SquarefreeFactorization(dd*d3) notin d3s then Append( ~d3s, d3); end if; end for;
  elif ISA(Type(K), FldNum) then 
     error "Not implemented yet for number fields";   // TO DO: Number field case
  else 
     error "Not implemented yet for function fields"; // TO DO: Function field case
  end if;
  vprint TwoDescent: "The d3s are", d3s;
  Ds := [];   maps_DtoC := [* *];   
  for d3 in d3s do 
     if &and[ IsLocallySolvable(Conic(Pr2, d3*Y^2 - q )) : q in [q1,q3] ] then 
       vprintf TwoDescent,1: "Parametrising QI for d3 = %o\n", d3;
       param := parametrization(Conic(Pr2, d3*Y^2 - q1 ));
       Q1,Q2,Q3 := Explode([ Evaluate(q, [XX,ZZ]) : q in param ]);
       assert Evaluate(q1,[Q1,0,Q3]) eq d3*Q2^2;
       f_hyp := Evaluate( d3*Evaluate(q3,[Q1,0,Q3]), [x,0,1]);
       denom := LCM([ Denominator(coeff) : coeff in Coefficients(f_hyp) ]);
       if denom ne 1 then vprintf TwoDescent,2:
          "Scaling by %o to clear denominators after paramatrising\n",denom; end if;
       f_hyp *:= denom^2;  // TO DO: be less lazy!!
       // Now really check local solubility ...  TO DO: Real places for number fields
       if Eltseq(f_hyp)[1] lt 0 and IsEmpty(Roots(f_hyp, RealField())) then 
          continue d3; end if;
       nonredD := HyperellipticCurve(Pr2_121, Kx!f_hyp, Kx!0); 
       known_insoluble := false;
       for pp in [fact[1] : fact in Factorization(Integers()!(2*Discriminant(f_hyp)))] do
          if not InternalIsSoluble(ChangeRing(f_hyp,Integers()), pp : IsSquarefree) then 
             known_insoluble := true; end if; 
       end for;
       if debug then  // check internal routine against Nils routine
          known_insoluble1 := false;
          for pp in [fact[1] : fact in Factorization(Integers()!(2*Discriminant(f_hyp)))] do
            if not IsLocallySolvable(nonredD, pp) then 
               known_insoluble1 := true; end if; 
          end for;
          assert known_insoluble eq known_insoluble1;
       end if;
       if known_insoluble then continue d3; end if;
       f_hyp, trans, minred_scaling := minimise_and_reduce(f_hyp); 
       D := HyperellipticCurve(Pr2_121, Kx!f_hyp, Kx!0);
       transD := [trans[1,1]*XX+trans[1,2]*ZZ, YY/(minred_scaling*denom), trans[2,1]*XX+trans[2,2]*ZZ];
       eqns_nonredDtoC := [ Q2, 1/(d3*Y_scaling)*Evaluate(q2,[Q1,0,Q3]), YY/d3];
       DtoC := map< D -> C | [Evaluate(eqn, transD) : eqn in eqns_nonredDtoC] >;
       Append( ~Ds, D);  Append( ~maps_DtoC, DtoC);  end if;
  end for;
  
  assert #Ds eq 0 or 2^Ilog(2,#Ds) eq #Ds; // check #Ds is a power of 2

  if debug then
    for D in Ds do 
      assert Degree(D) eq 3 or IsIsomorphic(AssociatedEllipticCurve(D), E); 
    end for;
  end if;

  return Ds, maps_DtoC, CtoE; 
end intrinsic;
