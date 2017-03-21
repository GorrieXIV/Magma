freeze;

import "3selmer.m": FindSubspace;

function ThreeIsogenySelmerGroupInternal(Isog) 
  //     -> GrpAb, Map
  
  Q := Rationals();
  vprintf Selmer, 1: "Doing Selmer group for %o\n", Isog;
  originalE := Domain(Isog);
  originalEE := Codomain(Isog);
  // Setting up, as in ThreeSelmerGroup
  E, originalEtoE, EtooriginalE := MinimalModel(originalE);
  EE, originalEEtoEE, EEtooriginalEE := MinimalModel(originalEE);
  Isog := EtooriginalE*Isog*originalEEtoEE;
  DualIsog := DualIsogeny(Isog);
  aInvs := aInvariants(E);
  vprintf Selmer, 1: "Using minimal model %o\n", E;

  // Get a point in the kernel of each isogeny, and the etale algebra.
  // There is an injection H^1(Q, E[Isog]) --> A*/A*3 where 
  // A is the algebra of degree 2 coming from EE[DualIsog] 
  P := PolynomialRing(Rationals() : Global := false); t := P.1;
  Pr2<X,Y,Z> := Ambient(E);
  ker := Kernel(Isog);
  assert Degree(DefiningEquations(ker)[1],1) eq 1;
  sigma := -Rationals()!Coefficient(DefiningEquations(ker)[1], 3,1);
  a1, a2, a3, a4, a6 := Explode(aInvariants(E));
  polyForIsogKer := t^2+a1*sigma*t+a3*t-sigma^3-a2*sigma^2-a4*sigma-a6;
  IsogHasRatlKer := not IsIrreducible(polyForIsogKer);
  kerD := Kernel(DualIsog);
  assert Degree(DefiningEquations(kerD)[1],1) eq 1;
  sigma := -Rationals()!Coefficient(DefiningEquations(kerD)[1], 3,1);
  a1, a2, a3, a4, a6 := Explode(aInvariants(EE));
  poltau := t^2+a1*sigma*t+a3*t-sigma^3-a2*sigma^2-a4*sigma-a6;
  ratl, tau := HasRoot(poltau);
  if not ratl 
     then Kraw<tau> := NumberField(poltau); 
     K, KrawtoK := OptimisedRepresentation(Kraw);
     tau := K!tau;
     OK := Integers(K);
  end if;

  // FIND THE BAD PRIMES
  bad0 := BadPrimes(E);
  bad := [ 3 ];
  for p in bad0 do
     cpE := TamagawaNumber(E,p);
     cpEE := TamagawaNumber(EE,p);
     vprintf Selmer, 2: "  Bad prime %o --> c_%o(E) = %o and  c_%o(EE) = %o\n", 
                                 p, p, cpE, p, cpEE;
     if IsDivisibleBy(cpE*cpEE, 3) and p ne 3 then Append(~bad, p); end if;
  end for;
  vprintf Selmer, 1: "Bad primes for 3-descent: %o\n", bad;
  
  if ratl then
     A := car< Rationals(), Rationals() >;
     S3 := VectorSpace(GF(3), #bad );
     // map S3 <--> A*/A*3
     S3toA := map< S3 -> A | s :-> <a, 1/a> 
                             where a := &*[bad[i]^Integers()!v[i] : i in [1..#v]]
                             where v := Eltseq(s) >;
     AtoS3 := map< A -> S3 | a :-> S3![ Valuation(a[1], bad[i]) : i in [1..#bad]] >;
     S3tofield := map< S3 -> Q |  s :-> S3toA(s)[1] >;
  else
     vprintf Selmer, 2: "Computing splitting of primes in field of discriminant %o\n", 
                        Discriminant(K);
     badK := &join[ { Ideal(place[1]) : place in Decomposition(K, bad[i]) }
                  : i in [1..#bad] ];
     A := K;
     vprint Selmer, 1: "Doing class/unit stuff...";
     S3group, toS, Stoexpvec, factorbase := pSelmerGroup(3, badK : Raw );
     
     // Find the kernel of the norm:
     S3 := VectorSpace(GF(3), Ilog(3,#S3group) );
     S3toA := map< S3 -> A | s :-> (S3group!Eltseq(s)) @@ toS >;
     S3tofield := S3toA;
     AtoS3 := map< A -> S3 | a :-> S3!Eltseq(toS(a)) >;
     S3 := FindSubspace(S3, func< s | IsPower( Norm(S3toA(s)), 3) >);
  end if; 
  vprintf Selmer,2: "Before using local conditions, bound on Selmer dimension is %o\n",
                     Dimension(S3);

  // The "3-isogeny descent map" EE(Q) -> A*/A*3 
  // associated to a 3-isogeny E -> EE,
  // where pt = [sigma,tau] is in the kernel 
  // (where sigma and tau are in the algebra A)
  three_isog_descentmap_poly := function(EtoEE, pt)
    sigma,tau := Explode(pt);
    Pol2<xEE,yEE> := PolynomialRing(Parent(tau/1),2);
    E := Domain(EtoEE); 
    EE := Codomain(EtoEE);
    polEE := DefiningPolynomial(EE);
    polEEnew := Evaluate( DefiningPolynomial(EE), [xEE+sigma, yEE+tau, 1] );
    a3new,a4new,a6new := Explode([ MonomialCoefficient(polEEnew, term) : term in [yEE,xEE,1] ]);
    assert a6new eq 0;
    m := -a4new/a3new; // the slope of the tangent line after moving (sigma,tau) to (0,0)
    return yEE - m*xEE - (tau - m*sigma);
  end function;

  // The "3-isogeny descent map" EE(Q) -> A*/A*3 
  // (defined everwhere, using that it is 0 only at the chosen 3-torsion point) 
  descmap_poly :=  three_isog_descentmap_poly( Isog, [sigma,tau]);
  descmap := func< x, y | Evaluate( descmap_poly, [x,y]) >;
  descmap := func< x, y | descmap(x,y) ne 0 select descmap(x,y)
                                             else  descmap(x,-a1*x-a3-y)^2 >;

  // For the isogeny Isog: E -> EE, the "descent map" EE(Q) -> A*/A*3
  // can be obtained from the 3-descent map on E, by composing it with 
  // the dual isogeny EE -> E.
  // f := func< x, y | f0*(fx*xx + fy*yy + fc) 
  //                  where xx, yy := Explode(Eltseq([x,y] @ DualIsog)) >;

  // LOCAL CONDITIONS.
  // First, to predict the dimension of EE(Qp)/Isog(E(Qp)) at 3,
  // we need to find out which isogeny is non-surjective on the kernel of reduction. 
  // This depends on the valuation of A, where the isogeny is
  // [ AX^4+BXZ^3, ... , X^3Z ]
  AforIsog := Coefficients(DefiningEquations(Isog)[1])[1];
  AforDualIsog := Coefficients(DefiningEquations(DualIsog)[1])[1];
  assert {AforIsog,AforDualIsog} eq {1,1/9};  // 1 iff surjective on E1
  extraDimAt3 := (AforIsog eq 1) select 0 else 1;
  // put 2 last in the list, in hope of avoiding it!
  if 2 in bad then Exclude(~bad, 2); Append(~bad, 2); end if;  
  for p in bad do
     vprintf Selmer,2 : "Doing local condition at %o\n", p;
     Qp := pAdicField(p : Precision:=50 ); 
     Rp := Integers(Qp);
     // Make Wp
     if ratl and p mod 3 eq 1 then 
        Wp := VectorSpace(GF(3), 2);
        e := 0; n := p-1; while IsDivisibleBy(n,3) do n := n div 3; e +:= 1; end while;
        fieldtoWp := map< Q  -> Wp | 
                          a :-> Wp![ v, Log( GF(p)!(a/p^v)^Integers()!((p-1)/3^e) ) mod 3 ]
                                     where v := Valuation(a,p) >;
     elif  ratl and p mod 3 eq 2 then 
        Wp := VectorSpace(GF(3), 1);
        fieldtoWp := map< Q -> Wp | a :-> Wp![Valuation(a,p)] >;
     elif ratl and p eq 3 then
        Wp := VectorSpace(GF(3), 2);
        fieldtoWp := map< Q -> Wp | a :-> Wp![ v, Integers()!(((a/p^v)^2-1)/3) mod 3 ]
                                         where v := Valuation(a,p) >;
     else  // not ratl
        // use one prime above p
        pid := Ideal(Decomposition(K,p)[1][1]);
        Wp, fieldtoWp := MakeModCubes(K,pid);
     end if;
     
     // Expected dimension ...
     if HasRoot(polyForIsogKer, Qp) then
        // the kernel of Isog is locally rational
        dimfromtorsion := 1;
     else dimfromtorsion := 0; end if;
     tamagawadiff := Valuation(TamagawaNumber(EE,p),3) - Valuation(TamagawaNumber(E,p),3);
     expecteddim := dimfromtorsion + tamagawadiff;
     if p eq 3 then expecteddim +:= extraDimAt3; end if;
     if expecteddim eq Dimension(Wp) then continue; end if;
     
     // Find the local image, as a subspace of Wp ... 
     EEQp := sub< Wp | >;
     // if there is local 3 torsion, try that first.
     xx := Qp!sigma;
     polb := a1*xx + a3; polc := -(xx^3 + a2*xx^2 + a4*xx + a6);
     tauIsInQp, sqrt := IsSquare(polb^2 - 4*polc);
     tauIsInQp, tauInQp := HasRoot(poltau, Qp);
     if tauIsInQp then
        // note that descmap(sigma,-a1*sigma-a3-tau) = -a1*sigma-a3-2*tau
        EEQp := sub< Wp | EEQp, fieldtoWp(-a1*sigma-a3-2*Q!tauInQp) >;
     end if;
     vprintf Selmer,2: "Looking for local points at %o\n", p;
     numextrapoints := 0;
     while Dimension(EEQp) lt expecteddim or numextrapoints le 30 do
                                         // (the usual safety check)
        if Dimension(EEQp) ge expecteddim then numextrapoints +:= 1; end if;
        // find a point
        // TO DO: put in y-coordinate search, 
        //        and/or call the point search functions in other files
        while true do
          xx := p^(Random([-6..6]))*Qp!Random(Rp);
          polb := a1*xx + a3; polc := -(xx^3 + a2*xx^2 + a4*xx + a6);
          flag, sqrt := IsSquare(polb^2 - 4*polc);
          if flag then yy := Qp!((-polb + sqrt)/2); break; end if;
        end while;
        assert Valuation(Evaluate(DefiningEquation(EE), [xx,yy,1])) gt 12;
        // put its image into Wp
        img := fieldtoWp(descmap(Q!xx,Q!yy));
        if not img in EEQp then EEQp := sub< Wp | EEQp, img >; end if;
     end while;
     vprintf Selmer,2: "Dimension of EE(Qp)/image for p=%o is %o\n", p, Dimension(EEQp);
     error if Dimension(EEQp) gt expecteddim, "Finding spurious local points";

     // impose the local condition
     WpModEEQp, quomap := quo< Wp | EEQp >;
     imagesofbasis := [quomap(fieldtoWp(S3tofield(Basis(S3)[i]))) : i in [1..Dimension(S3)]];
     homm := hom< S3 -> WpModEEQp | imagesofbasis >;
     S3 := Kernel(homm);
     vprintf Selmer,2: "Local condition at %o ==> bound on Selmer dimension is %o\n",
                              p, Dimension(S3);
     if #S3 eq 1 then break; end if;
   end for;

   S3group := AbelianGroup([ 3 : i in [1..Dimension(S3)] ]);
   S3grouptoA := map< S3group -> A | 
                           s :-> S3toA( &+[Eltseq(s)[i]*Basis(S3)[i] : i in [1..Dimension(S3)]] ),
                          im :-> S3group(Coordinates( S3, AtoS3(im))) >;
   return S3, S3toA;

end function;



function random3isogeny(E)
  Q := Rationals();
  xcoords := Roots(DivisionPolynomial(E, 3));
  error if #xcoords eq 0, "The given curve does not admit any 3-isogenies";
  xcoord := Random(xcoords)[1];
  ker := SubgroupScheme(E, PolynomialRing(Q).1-xcoord);
  _, Isog := IsogenyFromKernel(ker);
  return Isog;
end function;


intrinsic ThreeIsogenySelmerGroups(E::CrvEll : Isog:=0) 
            -> GrpAb, Map, GrpAb, Map, MapSch
{Given an elliptic curve E over Q admitting a 3-isogeny, 
computes the Selmer groups corresponding to some 3-isogenies E' -> E and E -> E', 
each followed by a map to some algebra.}

  require CoefficientRing(E) cmpeq Rationals(): "E must be defined over the rationals.";
  
  if Isog cmpeq 0 then Isog := random3isogeny(E); end if;
  
  DualIsog := DualIsogeny(Isog);
  S3, S3map := ThreeIsogenySelmerGroupInternal(Isog);
  S3dual, S3dualmap := ThreeIsogenySelmerGroupInternal(DualIsog); 
 
 return S3, S3map,  S3dual, S3dualmap, Isog;
end intrinsic;



intrinsic ThreeIsogenyDescent(E::CrvEll : Isog:=0) -> SeqEnum[Crv], List, SeqEnum[Crv], List, MapSch
{Given an elliptic curve E over Q admitting a 3-isogeny, computes plane cubic curves and covering maps
representing the elements of the Selmer groups corresponding to 3-isogenies E' -> E and E -> E'.}
  
  S3, S3map, S3dual, S3dualmap, EtoEE := ThreeIsogenySelmerGroups(E : Isog:=Isog);
  EEtoE := DualIsogeny(EtoEE);
  EE := Codomain(EtoEE);

  // choose one element from each inverse pair
  S3reps := []; 
  for s in S3 do
     if s eq S3!0 or s in S3reps or -s in S3reps then continue; end if;
     Append( ~S3reps, s);
  end for;
  S3dualreps := [];
  for s in S3dual do
     if s eq S3dual!0 or s in S3dualreps or -s in S3dualreps then continue; end if;
     Append( ~S3dualreps, s);
  end for;

  cubicsEtoEE := [ ];
  mapstoEE := [* *];
  for s in S3reps do
     cubic, maptoEE := ThreeIsogenyDescentCubic(EtoEE, s @ S3map : CheckNontrivial:=false );
     Append( ~cubicsEtoEE, cubic);
     Append( ~mapstoEE, maptoEE);
  end for;

  cubicsEEtoE := [ ];
  mapstoE := [* *];
  for s in S3dualreps do
     cubic, maptoE := ThreeIsogenyDescentCubic(EEtoE, s @ S3dualmap : CheckNontrivial:=false );
     Append( ~cubicsEEtoE, cubic);
     Append( ~mapstoE, maptoE);
  end for;

  return cubicsEtoEE, mapstoEE, cubicsEEtoE, mapstoE, EtoEE;

end intrinsic;
 

 
intrinsic ThreeIsogenyDescentCubic(Isog::MapSch, alpha::Any : CheckNontrivial:=true )
       -> Crv, MapSch
{For an isogeny E -> E' of elliptic curve over Q, and an element
alpha in (the algebra associated to) the Selmer group of that isogeny,
represents the Selmer element as a plane cubic C, and also returns 
a covering map C ->E.}

  vprintf ThreeDescent, 3: "\nGiven Selmer element alpha = %o\n", alpha;
  Q := Rationals();
  
  if Type(alpha) eq Tup then alpha := alpha[1]; end if;

  if CheckNontrivial then 
     vprint ThreeDescent, 1: "Checking if alpha is trivial ...";
     if IsPower(alpha,3) then return Domain(Isog), Isog; end if;
  end if;

  if Type(alpha) ne FldRatElt then
     bool, cbrtNalpha := IsPower( Norm(alpha), 3);
     require bool : "The given element alpha is invalid (its norm should be a cube).";
  end if;

  vprint ThreeDescent,1 : "Setting up the fields and matrices ...";
  // Get the kernel, and the corresponding two torsion matrices, in sequences
  E := Domain(Isog);
  EE := Codomain(Isog);
  EtoEE := Isog;
  ker := Kernel(EtoEE);
  // TO DO: Can we conveniently avoid calling ThreeTorsionPoints?
  // At least we have turned off the OptimisedRepresentation of the points we don't need ...
  tors3 := [* pt : pt in ThreeTorsionPoints(E : OptimisedRep:=false ) *];
  indices := [ i : i in [1..#tors3] | tors3[i] in ker ];
  torspts := [ tors3[i] : i in indices ];
  torsmats := [ ThreeTorsionMatrices(E, Equation(E))[i] : i in indices ];
  torsmat := Transpose(torsmats[1]);  // this acts on coeff vecs (rel. to [X,Y,Z]) 
                                      // on the left
  c := (torsmat^3)[1,1];
  cIsaCube, cubertc := IsPower(c,3);
  assert cIsaCube;
  torsmat /:= cubertc;
  assert torsmat^3 eq 1;
  // We will set K = Q(sqrt(d)) and K1 = Q(sqrt(-3d)), with basis [1,sqrt(-3d)] 
  K1_0 := CoefficientRing(torsmat);
  if Type(K1_0) ne FldRat then
     d := SquarefreeFactorization(-3*Discriminant(K1_0));
     K1<s> := NumberField(Polynomial([3*d,0,1]));
     
     // set up an isomorphism toK1 as a func 
     // (don't call IsIsomorphic, to avoid having a reference pile-up)
     l := K1_0.1;
     nl, tl := Explode(Eltseq(MinimalPolynomial(l)));
     dl := tl^2-4*nl;
     _, cl := IsSquare( dl/(-3*d) );
     l_K1 := -tl/2 + cl*K1.1/2;
     assert Evaluate( MinimalPolynomial(l), l_K1) eq 0;
     toK1 := func< ll | Eltseq(ll)[1] + Eltseq(ll)[2]*l_K1 >;

     torsmat_1 := Matrix(Q, 3,3, [Eltseq(toK1(c))[1] : c in Eltseq(torsmat)]);
     torsmat_s := Matrix(Q, 3,3, [Eltseq(toK1(c))[2] : c in Eltseq(torsmat)]);
     assert torsmat_1+s*torsmat_s eq Matrix(K1, 3,3, [toK1(c) : c in Eltseq(torsmat)]);
  else
     d := -3;
     torsmat_1 := torsmat;
     torsmat_s := Parent(torsmat)!0;
  end if;

  // The fields ...
  // Let K = Q(sqrt(d)) be the field of def of points in ker(EEtoE).
  // Over K, we have ker(EtoEE) iso mu_3, and the restriction to K
  // of the cocycle is given by alpha in K*/K*3.
  // The Galois closure of everything is the degree 12 field 
  // N = K(zeta_3, b) where b^3 = alpha.
  // There is also a cubic subfield L = Q(b+C/b) (where Norm(alpha) = C^3) 
  // with Galois closure K(b). 
  // In fact, the Galois closure of L is the composite of L with K1=Q(sqrt(-3d)), 
  // so N is the composite of two normal extensions: this S3 extension and Q(zeta_3).
  // Basis for N/Q: view the vector space N as the tensor product of
  //   * K1 = Q(sqrt(-3d)) with basis  1, s = sqrt(-3d),
  //   *   Q(zeta_3)       with basis  z = zeta_3, z^2, and
  //   * the vector space  < 1+b+C/b, 1+zb+z^2*C/b, 1+z^2b+z*C/b >
  //                      (this is a normal basis of L over K1)
  // 
  // The special cases are d = 1, where K = Q, and d = -3, where K1 = Q.

  if d eq 1 then         
     N<b,z> := ext< Rationals() | Polynomial([-alpha,0,0,1]), Polynomial([1,1,1]) : Check:=false >;
     z := N!z;
     s := z-z^2;
     sqrtd := 1;
  elif d eq -3 then
     K<z> := NumberField(Polynomial([1,1,1]));
     _, alpha := HasRoot(MinimalPolynomial(alpha), K);
     sqrtd := z-z^2; 
     s := sqrtd;
     N<b> := ext< K | Polynomial([-alpha,0,0,1]) : Check:=false >;
  else 
     KK := Parent(alpha);
     K := QuadraticField(d); sqrtd := K.1;
     vprint ThreeDescent,3: "Doing (unnecessary) call to IsIsomorphic ...";
     _, _ := IsIsomorphic(K, KK);
     vprint ThreeDescent,3: "    ... done";
     alpha := K! alpha;
     N<b,z> := ext< K | Polynomial([-alpha,0,0,1]), Polynomial([1,1,1]) : Check:=false >;
     z := N!z;  
     s := (z-z^2)*sqrtd;   // s^2 = -3d
  end if;

  C := (d eq 1) select 1 
                 else  cbrtNalpha;
  B := 1+b+C/b; BB := 1+z*b+z^2*C/b; BBB := 1+z^2*b+z*C/b;
  if d in {1,-3} then
     BasisN := [  z*B,   z*BB,   z*BBB,   z^2*B,   z^2*BB,   z^2*BBB];
  else
     BasisN := [  z*B,   z*BB,   z*BBB,   z^2*B,   z^2*BB,   z^2*BBB,
                s*z*B, s*z*BB, s*z*BBB, s*z^2*B, s*z^2*BB, s*z^2*BBB ];
  end if;

  // The Galois group is G := < sigma, tau > + < rho > = S_3 + Z/2
  //                          (the fixed fields are K and L*K1).  
  //                       = < sigma, rho*tau > + < rho > = S_3 + Z/2
  //                          (fixed field Q(zeta_3))
  // where 
  //    sigma fixes K(z), and sends b :-> zb,
  //     tau  fixes K(b), and sends z :-> z^2, (hence s :-> -s)
  //     rho  fixes L, K1=Q(sqrt(-3d)), and sends b :-> 1/b, z :-> z^2 
  //
  // In the special cases, s does not appear ...
  //   when d=1, K=Q, sigma and tau are as stated, rho not required and set to I,
  //   when d=-3, K=K(z), sigma and rho are as stated, tau is not required.


  // Matrices for the Galois action on the basis ...
  // Our matrices will be elements of MatK tensor Matz tensor MatL,
  // acting on column vectors that represent elements of N with respect to BasisN.
  MatK1:= MatrixAlgebra(Q,2);
  Matz := MatrixAlgebra(Q,2);
  MatL := MatrixAlgebra(Q,3);
  Matxyz := MatrixAlgebra(Q,3);
  if d notin {1,-3} then
     Sigma := TensorProduct(TensorProduct(MatK1!1, Matz!1), MatL!PermutationMatrix(Q,[3,1,2]));
     Tau :=  TensorProduct(TensorProduct(MatK1![1,0,0,-1], Matz![0,1,1,0]), 
                                         MatL![1,0,0, 0,0,1, 0,1,0]);
     Rho :=  TensorProduct(TensorProduct(MatK1!1, Matz![0,1,1,0]), MatL!1);
  elif d eq 1 then
     Sigma := TensorProduct( Matz!1, MatL!PermutationMatrix(Q,[3,1,2]));
     Tau :=  TensorProduct( Matz![0,1,1,0], MatL![1,0,0, 0,0,1, 0,1,0]);
     Rho := IdentityMatrix(Q,6);
  elif d eq -3 then   
     Sigma := TensorProduct( Matz!1, MatL!PermutationMatrix(Q,[3,1,2]));
     Tau := IdentityMatrix(Q,6);
     Rho :=  TensorProduct( Matz![0,1,1,0], MatL!1);
  end if;

  // Matrix for multiplication by s = sqrt(-3d) ...
  if d notin {1,-3} then
     Mult_s := TensorProduct(TensorProduct(MatK1![0,-3*d, 1,0], Matz!1), MatL!1);
     assert Mult_s^2 eq -3*d;
     assert Eltseq( Matrix(1,12,BasisN)*ChangeRing(Mult_s,N) ) eq [ s*nn : nn in BasisN ];
  elif d eq -3 then  
     // not needed
     Mult_s := 0;
  elif d eq 1 then
     // s = z-z^2, so mult on basis [z,z^2] is: 
     Mult_s_on_Qz := Matrix(Q, [[ 1, -2 ], 
                                [ 2, -1 ]]);
     Mult_s := TensorProduct( Mult_s_on_Qz, MatL!1 );
     assert Eltseq( Matrix(1,6,BasisN)*ChangeRing(Mult_s,N) ) eq [ s*nn : nn in BasisN ];
  end if;   

  // The cocycle ...
  // Its kernel restricted to K is < tau >, 
  // and hence the full kernel is < tau, rho >
  // since that is the only subgroup of order 4 in G containing tau.
  // Therefore tau and rho act trivially on [X,Y,Z], and sigma acts by torsmat.

  // Now make matrices for the new twisted Galois action on the Q-vector space
  // of dimension 18 or 36 spanned by <X,Y,Z> tensor BasisN.
  SigmaFull := TensorProduct(torsmat_1, Sigma) + TensorProduct(torsmat_s, Mult_s*Sigma);
  TauFull := TensorProduct(Matxyz!1, Tau);
  RhoFull := TensorProduct(Matxyz!1, Rho);
  assert  SigmaFull^3 eq 1;
  if d ne -3 then assert TauFull*SigmaFull eq SigmaFull^2*TauFull; end if;

  // The subspace (of dimension 3) invariant under the new Gal-action is:
  vprint ThreeDescent, 2: "Computing invariants under the new Galois action ...";
  W := Nullspace(Transpose(SigmaFull-1)) meet 
       Nullspace(Transpose(RhoFull-1)) meet 
       Nullspace(Transpose(TauFull-1));
  assert Dimension(W) eq 3;
  invcoeffs := [];
  nN := #BasisN;
  for w in Basis(W) do
     w_X := &+[           Eltseq(w)[i]*BasisN[i] : i in [1..#BasisN] ];
     w_Y := &+[   Eltseq(w)[i+#BasisN]*BasisN[i] : i in [1..#BasisN] ];
     w_Z := &+[ Eltseq(w)[i+2*#BasisN]*BasisN[i] : i in [1..#BasisN] ];
     Append( ~invcoeffs, [w_X,w_Y,w_Z] );
  end for;
  coeffmat := Matrix(invcoeffs);   // new Gal-invariants [R,S,T] = coeffmat*[X,Y,Z]

  // recover the equation and the map
  XYZmat := (coeffmat)^-1;
  _<R,S,T> := PolynomialRing(N,3);
  P3Q<X,Y,Z> := PolynomialRing(Q,3);
  XYZ := [ XYZmat[i,1]*R+XYZmat[i,2]*S+XYZmat[i,3]*T : i in [1,2,3] ];
  cubic0 := Evaluate(DefiningEquation(E), XYZ);

  // scale the cubic so it has rational coeffs, then simplify ...
  cubic0 /:= Coefficients(cubic0)[1];
  vprint ThreeDescent, 1: "Minimising ...";
  cubicmin, tup := Minimise(P3Q!cubic0);
  scaling, trans1 := Explode(tup);
  vprint ThreeDescent, 1: "Reducing ... \n";
  cubic, trans2 := Reduce(cubicmin : steps:=3 );
  tmat := Transpose(trans1) * Parent(trans1)!Transpose(trans2[2]);
  chvars := [ tmat[i,1]*X + tmat[i,2]*Y + tmat[i,3]*Z : i in [1,2,3] ];
  assert scaling*Evaluate(cubic0, chvars) eq cubic;

  
  vprint ThreeDescent, 1: "Checking cInvariants ...";
  require cInvariants(GenusOneModel(cubic)) eq 
          cInvariants(GenusOneModel(Minimise(DefiningEquation(E)))):
          "The cubic obtained does not have the same invariants as E";

  // get the covering map: obtain equations for EtoEE given by cubic forms, then substitute ...

  // Magma gives the equations for EtoEE as quartics (it puts a high weight on Y).
  // Our new weighting forces a common factor of Z, which we then divide out:
  PP<XX,YY,ZZ> := PolynomialRing(Rationals(),3,"weight",[1,1,1, 1,1,0, 1,0,0]);
  IE := ideal< PP | Evaluate(DefiningEquation(E), [XX,YY,ZZ]) >;
  newEtoEEeqns := [ NormalForm(Evaluate(ff,[XX,YY,ZZ]), IE) : ff in DefiningEquations(EtoEE) ];
  newEtoEEeqns := [ Evaluate( eqn div ZZ, [X,Y,Z]) : eqn in newEtoEEeqns ];
  assert Evaluate(DefiningEquation(EE), newEtoEEeqns) in ideal< P3Q | DefiningEquation(E)>;

  C := Curve(GenusOneModel(cubic));
  CtoEEeqns := [ Evaluate( Evaluate(eqn, XYZ), chvars) : eqn in newEtoEEeqns ];
  CtoEE := map< C -> EE | ChangeUniverse(CtoEEeqns, P3Q) >;

  return C, CtoEE;

end intrinsic;



