freeze;

// ----------------------------------------------------
//
// Imports
//
// ----------------------------------------------------

import "Repn.m": isPara, inverseops, 
    leftinverseops, leftActionOps, 
    rightActionOpsfunc, rightActionOps,
    rSpace;
//    GraphAutomorphisms;
    
import "../GrpLie/GrpLie.m" : Torus_RatMxAction, Weyl_NonsimpleReflections;
import "../GrpCox/GrpCox.m" : additiveOrder;
import "Weights.m" : weightBase;

// ----------------------------------------------------
//
// Verbosity
//
// ----------------------------------------------------
declare verbose RowRed, 10;

// ----------------------------------------------------
//
// Some utility functions:
//
// * nthRoots
// * ratintMult
// * dependence
// * reduceToBasis
//
// ----------------------------------------------------

nthRoots := function( a, n )
  if n eq 1 then
    return [<a,1>];
  else 
     x  := PolynomialRing( Parent(a) ).1;
    return Roots( x^n - a );
  end if;
end function;

ratIntMult := function(x,A)
  if Category(BaseRing(x)) eq FldRat then
    A := ChangeRing( A, Rationals() );
  elif Category(BaseRing(A)) eq FldRat then
    x := ChangeRing( x, Rationals() );
  end if;
  return x*A;
end function;

dependence := function( vects )
  A := Matrix( vects );
  N := Nullspace( A );
  return N.1;
end function;

reduceToBasis := function( vects )
  B := [1..#vects];
  while not IsIndependent( vects[B] ) do
    d := dependence( vects[B] );
    _ := exists(i){ i : i in [1..#vects] | d[i] ne 0 };
    Remove( ~B, i );
  end while;
  return B;
end function; 


// ----------------------------------------------------
//
// WeightBase: A utility function, returning:
//
// * B is the weight base; 
// * vectB is the corresponding vectors
// * Orbits is the basic orbits; 
// * vectOrbits is the corresponding vectors
// * J is the corresponding simple root subsets
// * Actions is the basic actions
// * M is the bilinear form that is orthonormal on 
//   hwvects and trivial elsewhere
// 
// ----------------------------------------------------

WeightBase := function( rho )
  if (assigned rho`WeightBase_B) then
    return rho`WeightBase_B, 
        rho`WeightBase_vectB, 
        rho`WeightBase_Orbits, 
        rho`WeightBase_vectOrbit, 
        rho`WeightBase_J, 
        rho`WeightBase_Ws, 
        rho`WeightBase_Actions, 
        rho`WeightBase_M, 
        rho`WeightBase_WeylMxs;
  end if;
  
  G := Domain( rho );  M := Codomain( rho );
  k := BaseRing( G );  K := BaseRing( M );
  l := SemisimpleRank( G );  n := ReductiveRank( G );
  d := Degree( Codomain( rho ) );  V := VectorSpace( K, d );
  wtV := VectorSpace( Rationals(), n );
  R := RootDatum( G );

  WeylMxs := [ rho( elt<G|r> ) : r in [1..SemisimpleRank(G)] ];
  WActionOnVect := function( v, w )
    for r in w do
      v := v * WeylMxs[r];
    end for;
    return v;
  end function;

  wts, wvs := Weights( rho );
  wts := &cat[ [ wts[i] : j in [1..Dimension(wvs[i])] ] : 
    i in [1..#wts] ];
  wvs := &cat[ ChangeUniverse( Basis(v), V ) : v in wvs ];
  xs := [ rho( elt<G|<r,1>> ) : r in [1..l] ];
  
  // the highest weight and its orbit
  hws := [ i : i in [1..#wts] | forall{ x : x in xs | isPara(wvs[i]*x,wvs[i]) } ];
  if #hws gt 1 then  
    //hws := [hws[2]]; //this tricks it into working for G2(3)
    error "The representation is reducible";  
  end if;
  mu := wts[hws[1]];  v := wvs[hws[1]];
  Orbit, Actions := WeightOrbit( R, mu );
  vectOrbit := [ WActionOnVect( v, Eltseq(Actions[i]) ) : i in [1..#Orbit] ];

  // the bilinear form
  OrbitSpace := sub< V | vectOrbit >;
  B := Matrix( vectOrbit cat [ v : v in wvs | v notin OrbitSpace ] )^-1;
  M := DiagonalMatrix( Parent(B), [1:i in [1..#vectOrbit]] cat [0:i in [1..(#wvs-#vectOrbit)]] );
  M := B * M * Transpose( B );

  // the weight basis
  WeylOnWeights := ReflectionMatrices( RootDatum(G) );
  WeylOnWeights := [ ChangeRing(A,Rationals()) : A in WeylOnWeights ];
  F := FundamentalWeights( G );
  F := [ RowSpace(F) | F[i] : i in [1..l] ];
  if l ne n then
    F cat:= ChangeUniverse(Basis(RootSpace(Radical(R))), VectorSpace(Rationals(),n));
  end if;  
  F := VectorSpaceWithBasis(F);

  B := [ Orbit[1] ];  vectB := [ vectOrbit[1] ];
  J := [];  J[1] := [1..n];  
  J[2] := [ r : r in [1..n] | v[r] eq 0 ] where v is Coordinates(F,F!Orbit[1]);
  i := 2;  j := 1;
  repeat
    if exists(r){ r : r in J[j] | r notin J[i] and
                  exists(s){ s : s in J[i] | ( wtV!(B[j]*WeylOnWeights[r]), wtV!Coroot(G,s) ) ne 0 } } then
      B[i] := B[j]*WeylOnWeights[r];   vectB[i] := vectB[j]*WeylMxs[r];
      J[i+1] := [ s : s in J[i] | ( Root(G,r), Coroot(G,s) ) eq 0 ];
      i +:= 1;  j := i-1;
    else
    end if;//i;
  until #J[i] eq 0;

  // we project the elements of J to [1..l] (only the semisimple part "counts")
  J := [ [r : r in j | r in [1..l]] : j in J ];

  // the reflection subgroups
  Ws := [ WeylGroup( G ) ];
  for i in [1..#B] do
    Append( ~Ws, ReflectionSubgroup( Ws[i], J[i+1]) );
  end for;

  // the basic orbits
  Orbits := [ Orbit ];
  Actions := [ [Eltseq(a) : a in Actions] ];
  for i in [2..#B] do
    Orbit, Action := WeightOrbit( RootDatum(G), B[i] : J := J[i], dom := false);
    Append( ~Orbits, Orbit );  Append( ~Actions, [Eltseq(a) : a in Action] );
  end for;
  
  //Store result, for future reference
  rho`WeightBase_B          := B;
  rho`WeightBase_vectB      := vectB;
  rho`WeightBase_Orbits     := Orbits;
  rho`WeightBase_vectOrbit  := vectOrbit;
  rho`WeightBase_J          := J;
  rho`WeightBase_Ws         := Ws;
  rho`WeightBase_Actions    := Actions;
  rho`WeightBase_M          := M;
  rho`WeightBase_WeylMxs    := WeylMxs;

  return B, vectB, Orbits, vectOrbit, J, Ws, Actions, M, WeylMxs;
end function;


// ----------------------------------------------------
//
// Printmxs: A function that's used in the "Stepper" 
//   case
//
// ----------------------------------------------------
Printmxs := procedure( list )
  strings := [];  ws := [];  hs := [];
  for j in [1..#list] do
    h := Nrows(list[j]);
    jstrings := [ Sprint( list[j][i] ) : i in [1..h] ];
    w := Maximum( [ #s : s in jstrings ] );
    jstrings := [ s cat " "^(w-#s) : s in jstrings ];
    hs[j] := h;  ws[j] := w;  strings[j] := jstrings;
  end for;
  for i in [1..Maximum( hs ) ] do
    for j in [1..#list] do
      printf "%o\t", (i le hs[j]) select strings[j][i] else " "^ws[j];
    end for;
    printf "\n";
  end for;
end procedure;


// ----------------------------------------------------
//
// Some functions to be used in rowReduction, taken out
//   to simplify.
//
// * extensionDegree
// * right and left actions
// * torusInverseFor(Non)Vectors
// * validateRowReductionInputFor(Non)Vectors
// * actionsOfWeylReflections
// ----------------------------------------------------
extensionDegree := function(rho)
    G := Domain(rho); k := BaseRing(G); K := BaseRing(Codomain(rho));
    return IsFinite(k) select Degree(BaseRing(Codomain(rho)),k) else 
        Lcm( [Integers()| i : i in Invariants(CoisogenyGroup(G)) | i ne 0 ] );
end function;
    
rightActionfunc := func< rho, x, y | (assigned rho`UnderlyingFunction)
    select rightActionOpsfunc( x, (rho`UnderlyingFunction)(y, true) )
      else x*rho(y) 
>;
rightActionInvfunc := func< rho, x, y | (assigned rho`UnderlyingFunction)
    select rightActionOpsfunc( x, inverseops((rho`UnderlyingFunction)(y,true)) )
      else x*rho(y)^-1
>;
rightAction := procedure(rho, ~x, y, ops) 
    if (assigned rho`UnderlyingFunction) then
        rightActionOps( ~x, (rho`UnderlyingFunction)(y, true), 1, ops );
    else 
        x *:= rho(y);
    end if;
end procedure;
rightActionInv := procedure(rho, ~x, y, ops)
    if (assigned rho`UnderlyingFunction) then
        rightActionOps( ~x, inverseops((rho`UnderlyingFunction)(y, true)), 1, ops );
    else 
        x *:= rho(y)^-1;
    end if;
end procedure;
leftActionInv := procedure(rho, ~x, y) 
    if (assigned rho`UnderlyingFunction) then
        leftActionOps( ~x, inverseops((rho`UnderlyingFunction)(y, true)), 1 );
    else 
        x := rho(y)^-1*x;
    end if;
end procedure;


actionsOfWeylReflections := function(rho)
    if (assigned rho`WeylRefl_hs) then
        return rho`WeylRefl_hs,
            rho`WeylRefl_wds,
            rho`WeylRefl_reflmxs,
            rho`WeylRefl_imWeightVect,
            rho`WeylRefl_weightact;
    end if;
    
    G := Domain(rho); R := RootDatum(G); W := WeylGroup(G);
    k := BaseRing(G); K := BaseRing(Codomain(rho));
    d := Degree(Codomain(rho)); N := NumPosRoots(R);

    hs, wds := Weyl_NonsimpleReflections( R, k );
    reflmxs := [];  id := MatrixAlgebra(K,d)!1;  
    for r in [1..N] do
        h := hs[r];  w := wds[r];
        refl := elt<G|h>;  for s in w do  refl *:= elt<G|s>;  end for;
        Append( ~reflmxs, rightActionfunc( rho, id, refl ) );
    end for;
    imWeightVect := function( weight, r )
        imweight := weight * ChangeRing(ReflectionMatrix(W,r),Rationals());
        if r gt N then  r -:= N;  end if;
        imvect := (rho`WeightBase_vectOrbit)[ Position((rho`WeightBase_Orbits)[1],weight) ];
        return imweight, imvect*reflmxs[r];
    end function;
    weightact := func< x,w | ratIntMult(x,PermToMatrix(W,w)) >;
    
    //Store
    rho`WeylRefl_hs := hs;
    rho`WeylRefl_wds := wds;
    rho`WeylRefl_reflmxs := reflmxs;
    rho`WeylRefl_imWeightVect := imWeightVect;
    rho`WeylRefl_weightact := weightact;
    
    return hs, wds, reflmxs, imWeightVect, weightact;
end function;

// find the inverse image of the toral matrix X
// separate functions for vectors and non vectors
torusInverseForVectors := function( rho, X )
    V := RSpace(Codomain(rho)); deg := extensionDegree(rho);
    wts := rho`WeightBase_B; wvs := rho`WeightBase_vectB;
    ims := [ X[i] : i in [1..Nrows(X)] ];
    wts := ExtendBasis( VectorSpaceWithBasis( wts ), Universe( wts ) );
    v := [ ( ims[i], wvs[i] )^deg : i in [1..#ims] ] cat 
            [ 1 : i in [1..#wts-#ims] ];
    A := Transpose( Matrix(wts) )^-1 / deg;
    return Torus_RatMxAction( Vector(v), A );
end function;

/* Try to find an inverse for the diagonal part of the matrix X,
   using the data in rho`extensionDegree.
   
   On success returns a set of possible vectors h (over base ring
   of the codomain) such that X = rho(elt<G | h>) (but the latter 
   statement only makes sense if h is defined over the domain).
   On failure returns false.
 */
torusInverseForMatrices_DR := function( rho, X )
    G := Domain(rho);
    F := CoefficientRing(G);
	
    deg := extensionDegree(rho);
    rnkG := Rank(G);
    FCodom := CoefficientRing(Codomain(rho));
    rnkCodom := Degree(Codomain(rho));
    assert Ncols(X) eq rnkCodom;
    ET := rho`ExtendedTorus;
    assert CoefficientRing(ET) cmpeq Integers();
    VFCodom := VectorSpace(FCodom, rnkG);
    VF := VectorSpace(F, rnkG);

    if IsOne(X) then return {VF|Vector([F|1 : i in [1..rnkG] ])}; end if;
	
    the_hs := []; //will be a sequence of sequences of vectors: each of 
                  //the elements of the_hs correspond to "clearing" one
                  //entry; each of the elemetns of the_hs[i] corresponds
                  //to a possibility of doing that. At the end, we'll
                  //multiply them out to see which ones are in F (rather
                  //than its algebraic closure)
    for i in [1..rnkCodom] do
	t := X[i][i];
	if IsOne(t) then continue; end if;

	//We prefer integral solutions
	subET := Submatrix(ET, 1, 1, rnkG, i);
	cons := false;
	eiv := Vector([Integers()|0 : j in [1..i-1]] cat [deg]);
	cons, vz := IsConsistent(subET, eiv);
	if cons then 
	    v := ChangeRing(vz, Rationals()); 
	else
	    cons, v := IsConsistent(ChangeRing(subET, Rationals()), 
                ChangeRing(eiv, Rationals()));
	end if;
	if (not cons) then return false; end if;
        v := Vector(v);
			
	// Good, try and patch that entry. Using v above we construct 
        // vectors h such that rho(elt<G | h>) has 1's on diag. entries 
        // before i, and t on the entry i.
	hs := [[]];
	for j in [1..rnkG] do
	    if IsOne(Denominator(v[j])) then
		entries := [FCodom|t^(Integers()!v[j])];
	    else
		x := PolynomialRing(FCodom).1;
		entries := [FCodom|r[1] : 
                    r in Roots((x^Denominator(v[j]))-(t^Numerator(v[j])))];
	    end if;
	    hs := [Append(h, e) : h in hs, e in entries];
	end for;
	hs := [VFCodom | Vector(h) : h in hs];
	if #hs eq 0 then return false; end if;
	    Append(~the_hs, hs);

	//Now apply h^-1 to X (but we can't do that using rho, since the 
	//vector may not be in F).
	diagact_h_inv_pow := v*ChangeRing(ET, Rationals())/deg;
	pow_to_entry := func<t, p | (Denominator(p) eq 1) 
            select t^Numerator(p) else Root(t^Numerator(p), Denominator(p))>;
	fake_rho_h := DiagonalMatrix([FCodom | pow_to_entry(t, diagact_h_inv_pow[j]) : j in [1..rnkCodom]]);
	X := X*(fake_rho_h)^-1;
	assert2 IsOne(X[i][i]^deg);
	if (not IsOne(X[i][i]^deg)) then return false; end if;
    end for;
	
    //Combine the data in the_hs and hope to find a vector with entries in F.
    one_h := func< which | Vector([ &*[ the_hs[j][which[j]][i] : 
        j in [1..#the_hs] ] : i in [1..rnkG]])>;
    cands := { one_h(p) : p in CartesianProduct([[1..#t] : t in the_hs]) };
	
    //Done!
    return (#cands eq 0) select false else cands;
end function;


torusInverseForMatrices := function( rho, X )
//    print "X",X;
    //Try the new code first.
    if assigned rho`ExtendedTorus then
        h := torusInverseForMatrices_DR(rho, X);
        if (h cmpne false) and (#h gt 0) then return h; end if;
        //OK, failed; try the old stuff.
        G := Domain(rho);
        V := RSpace(Codomain(rho)); 
        deg := extensionDegree(rho);
        wts, wvs := Weights( rho );
        wts := &cat[[ wts[i] : j in [1..Dimension(wvs[i])] ] : i in [1..#wts]];
        wvs := &cat[ ChangeUniverse( Basis(v), V ) : v in wvs ];

        indxs := reduceToBasis( wts );  
        wts := wts[indxs];  
        wts := ExtendBasis( VectorSpaceWithBasis( wts ), Universe( wts ) );
        A := Transpose( Matrix(wts) )^-1/deg;

        if forall{i : i in [1..#wvs] | InnerProduct(wvs[i],wvs[i]) eq 1}
          and forall{<i,j> : j in [1..i-1], i in [2..#wvs] | 
              InnerProduct(wvs[i],wvs[j]) eq 0} then

            wvs := wvs[indxs];
            ims := [ wv*X : wv in wvs ];
            v := [ ( ims[i], wvs[i] )^deg : i in [1..#ims] ] cat 
                [ 1 : i in [1..#wts-#ims] ];
        else
    /*
       The above code attempts to find the eigenvalues of X using
       the inner product of the weight vectors. But this assumes that
       the weight vectors are orthonormal. When this is not the case
       the following version is used -- at the moment it is only 
       expected to work for simply connected root data.
           DET 2013-08-12.
    */
            W := Matrix(wvs);
            Q := W*X*W^-1;
            v := [ Q[i,i]^deg : i in indxs ];
        end if;
    else
        // Use the weight basis attached to rho

        deg := extensionDegree(rho);
        wts := SetToSequence(rho`WeightBase_Orbits[1]);
        wvs := rho`WeightBase_vectOrbit;
        indxs := reduceToBasis( wts );  
        wts := wts[indxs];  
        wts := ExtendBasis( VectorSpaceWithBasis( wts ), Universe( wts ) );
        wvs := wvs[indxs];
        A := Transpose( Matrix(wts) )^-1/deg;
//        print "A",A;
        v := [];
        for gamma in wvs do
            d := Depth(gamma);
            t := (gamma*X)[d]*gamma[d]^-1;
            Append(~v,t^deg);
        end for;
//        print v;
    end if;
    return Torus_RatMxAction( Vector(v), A );
end function;


validateRowReductionInputForVectors := function(rho, X)
    ok, X := CanChangeUniverse( X, rSpace( Codomain( rho ) ) );
    if not ok then
        error "Cannot coerce images into the appropriate vector space";
    end if;
    return Matrix( X );
end function;

validateRowReductionInputForNonVectors := function(rho, X)
    ok, X := IsCoercible( Codomain( rho ), X );
    if not ok then
        error "Cannot coerce matrix into the codomain of the representation";
    end if;
    return X;
end function;

// ----------------------------------------------------
//
// Two very important functions that rowReduction uses
//
// * clearRow
// * clearCol
// ----------------------------------------------------
//


// working in row im:  use the pivot at column j to eliminate
//   the column with weight  lambda_j s_r
// (returns the transforming element only)
// 
elimEntryInRow := function(variant, rho, im, i, j, r : Vectors := false)
    G := Domain(rho);
    deg := extensionDegree(rho);
    wtV := VectorSpace( Rationals(), Dimension(RootDatum(G)) );   
    lambda_j := (rho`WeightBase_Orbits)[1][j];
    
    imweight, imvect := (rho`WeylRefl_imWeightVect)( lambda_j, r );
    imM := im*(rho`WeightBase_M);
    vprintf RowRed, 5 : "elimEntryInRow: j = %o, r = %o, l_j = %o, l_j s_r = %o\n", j, r, lambda_j, lambda_j*ReflectionMatrix(RootDatum(G), r);
    IndentPush();
    vprintf RowRed, 5 : "imM = %o\n", imM;
    vprintf RowRed, 5 : "imweight = %o\n", imweight;
    vprintf RowRed, 5 : "imvect = %o\n", imvect;
    vprintf RowRed, 5 : "( imM, imvect ) = %o\n", (imM, imvect);
    if ( imM, imvect ) eq 0 then 
        //We can't do anything with this root
        IndentPop();
        return G!1;
    end if;
    if ( imM, (rho`WeightBase_vectOrbit)[j] ) eq 0 then
        //What happens here?!
        vprintf RowRed, 2 : "(rho`WeightBase_vectOrbit)[j] = %o\n", (rho`WeightBase_vectOrbit)[j];
        IndentPop();
        error "hoi4";
    end if;        
    mm := Integers()!Abs(( wtV!lambda_j, wtV!Coroot(G,r) ));        
    if ( mm eq 0) then 
        vprintf RowRed, 2 : "==> =====mm = 0======";
        IndentPop();
        return G!1;
    end if;
    vprintf RowRed, 5 : "mm = %o\n", mm;
    pow := ( imM, imvect ) / ( imM, (rho`WeightBase_vectOrbit)[j] );
    bs := nthRoots( BaseRing(G)!(pow^deg), mm*deg );
    bs := [ rt[1] : rt in bs ];
    bs := bs cat [ -b : b in bs ];// needed?
    vprintf RowRed, 5 : "bs = \n%o\n", [ rightActionInvfunc(rho, im, elt<G|<r,b>>) *  (rho`WeightBase_M) : b in bs ]; 
    if exists(b){ b : b in bs | 
        (rightActionInvfunc(rho, im, elt<G|<r,b>>) * (rho`WeightBase_M),
        imvect ) eq 0 } then
        g := elt<G | <r,b> >;
    else
        vprintf RowRed, 1 : "!!hi!!\n";
        IndentPop();
        if (variant eq 1) then
            return false;
        elif (variant eq 2) then
            return G!1;
        end if;
    end if;
    
    IndentPop();
    return g;
end function;

findPivotInRowVariant1 := function( rho, X, i, remaining
    : Vectors := false, Sides := false) //-> j (index), g (required group action)

    G := Domain(rho);
    g := G!1;

    im := Vectors select X[i] else (rho`WeightBase_vectB)[i]*X;
    exsts := exists(j){ j : j in remaining | ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) ne 0 }; 
    if not exsts then 
        return false, _;  
    end if;
    
    return j, g;
end function;
findPivotInRowVariant2 := function( rho, X, i, remaining
    : Vectors := false, Sides := false) //-> j (index), g (required group action)

    G := Domain(rho);

    IndentPush();
    g := G!1;

    im := Vectors select X[i] else (rho`WeightBase_vectB)[i]*X;
    j := Position(rho`WeightBase_vectOrbit, rho`WeightBase_vectB[i]);
    if (j eq 0) or (j notin remaining) then
        vprintf RowRed, 4 :  "(taking \"random\" elt!)";
        exsts := exists(j){ j : j in remaining | ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) ne 0 }; 
        if not exsts then 
            IndentPop(); 
            return false, _;  
        end if;
    elif ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) eq 0 then
        vprintf RowRed, 4 : " scalar product ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) = 0\n";
        IndentPush();
        vprintf RowRed, 4 : "orders of coxeter gps: %o\n", [ #WW : WW in rho`WeightBase_Ws ] ;
        vprintf RowRed, 4 : "im = %o\n", im;
        vprintf RowRed, 4 : "(rho`WeightBase_vectOrbit)[j] = %o\n", (rho`WeightBase_vectOrbit)[j];
        vprintf RowRed, 4 : "X=\n%o\n", X;
        vprintf RowRed, 4 : "im*(rho`WeightBase_M) = %o\n", im*(rho`WeightBase_M);
        ej2 := { j2 : j2 in remaining | ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j2] ) ne 0 };
        if #ej2 eq 0 then 
            vprintf RowRed, 1 : "hoi4\n";
            IndentPop(); IndentPop();
            return false, _;
        end if;
        //Try all possibilities for new pivots
        vprintf RowRed, 4 : "ej2 = %o\n", ej2;
        for j2 in ej2 do 
            IndentPush();
            //Construct new X, hence new im, hence new scalar product
            vprintf RowRed, 4 : "j = %o, j2 = %o\n", j, j2;
            worg := Reverse(rho`WeightBase_Actions[1][j]) cat rho`WeightBase_Actions[1][j2];
            w := elt< G | [* r : r in worg *] >;
            Xnew := rightActionInvfunc(rho, X, w);
            
            //Check if we won't mess everything up we did so far
            W := WeylGroup(G);
            ok := &*[ W | W.r : r in worg ] in rho`WeightBase_Ws[i];
            if (not ok) then 
                vprintf RowRed, 4 : "--> Xnew = \n%o\n", Xnew;
                vprintf RowRed, 4 : "--> w not in W[i]\n";
                IndentPop();
                newip := 0;
                continue;
            end if;
            vprintf RowRed, 4 : "w is in W[i]\n";

            //Check if we actually got somewhere
            vprintf RowRed, 4 : "w= %o\n", w;
            imnw := Vectors select Xnew[i] else (rho`WeightBase_vectB)[i]*Xnew;
            newip := ( imnw*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] );
            vprintf RowRed, 4 : "--> Xnew = \n%o\n", Xnew;
            vprintf RowRed, 4 : "--> ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) = %o\n", newip;
            if newip eq 0 then IndentPop(); continue; end if;

            //It worked!
            vprintf RowRed, 4 : "OK!\n";
            IndentPop(); break;
        end for;
        
        if newip eq 0 then
            vprintf RowRed, 1 : "hoi5\n";
            IndentPop(); IndentPop();
            return false, _;
        end if;
        g := w*g;
        vprintf RowRed, 4 : "X = \n%o\n-->\n%o\n", X, rightActionInvfunc(rho, X, w);
        IndentPop();
    end if;
    
    IndentPop();
    return j, g;
end function;

clearRow := procedure( rho, 
    ~X, u, ~v, ~ws, ~j, i, ~remaining, ~excp
    : Vectors := false, Sides := false, UseVariant := "default")

    var := (UseVariant cmpeq "default") select (Vectors select 2 else 1) else UseVariant;

    vprintf RowRed, 4 : "\nclearRow; i = %o, remaining = %o\n", i,remaining;
    IndentPush();
    
    G := Domain(rho); W := WeylGroup(G); R := RootDatum(G);
    N := NumPosRoots(R);
    k := BaseRing(G); 

    /* Find a suitable pivot */
    findPivotInRow := (var eq 1) select findPivotInRowVariant1 else findPivotInRowVariant2;
    j, g := findPivotInRow( rho, X, i, remaining : Vectors := Vectors, Sides := Sides);
    if j cmpeq false then
        j := 0;
        excp := "findPivotInRow failed";
        IndentPop();
        return;
    end if;
    vprintf RowRed, 4 : "Result of findPivotInRow: j = %o, g = %o\n", j, g;
    rightActionInv(rho, ~X, g, false);
    v := g*v;
    im := Vectors select X[i] else (rho`WeightBase_vectB)[i]*X;
    vprintf RowRed, 4 : "now ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ) = %o\n", ( im*(rho`WeightBase_M), (rho`WeightBase_vectOrbit)[j] ); 

    /* Compute some data needed for Phi_{w_i} */
    imweight := (rho`WeightBase_Orbits)[1][j];
    vprintf RowRed, 4 : "j = %o\n", j;
    vprintf RowRed, 4 : "(rho`WeightBase_vectOrbit)[j] = %o\n", (rho`WeightBase_vectOrbit)[j];
    vprintf RowRed, 4 : "imweight = %o\n", imweight;
    vprintf RowRed, 4 : "ws = %o\n", ws;
    for wj in ws do
        imweight := (rho`WeylRefl_weightact)( imweight, wj^-1 );
    end for;
    vprintf RowRed, 4 : "imweight = %o\n", imweight;
    pos := Position((rho`WeightBase_Orbits)[i],imweight);
    vprintf RowRed, 4 : "pos = %o\n", pos;
    if pos eq 0 then
        excp := "hi3"; j := 0; IndentPop(); return;
    end if;
    w0 := LongestElement(W);
    wi := &*[ (rho`WeightBase_Ws)[i] | W.r : r in (rho`WeightBase_Actions)[i][pos] ];
    vprintf RowRed, 4 : "wi = %o\n", wi;
    wi := TransversalElt( (rho`WeightBase_Ws)[i], (rho`WeightBase_Ws)[i+1], wi );

    /* Now really construct Phi_{w_i} */
    if (var eq 1) then
        Phiwi := additiveOrder(W, PermToWord(W, wi));
        for wj in Reverse( ws ) do 
            Phiwi := [ r^wj : r in Phiwi ];
        end for;
        Append(~ws, wi);
    elif (var eq 2) then
        //Phi_w is, by definition, the set of positive roots that w^-1 sends to a negative root
        Phiwi := [ r : r in [1..N] | r^wi gt N ];
        for wj in Reverse( ws ) do 
            Phiwi := [ r^wj : r in Phiwi ];
        end for;
        Append( ~ws, wi );
        vprintf RowRed, 4 : "Phiwi = %o\n", Phiwi;
        //Change Phiwi into its complement, and negative roots
        Phiwi := [ r+N : r in [1..N] | r notin Phiwi and (rho`WeylRefl_imWeightVect)( imweight, r ) ne imweight ];
    end if;
    vprintf RowRed, 4 : "--> Phiwi = %o\n", Phiwi;
    
    /* Traverse elements in Phiwi, eliminate entries in rows */
    for r in Phiwi do
        /* Try to eliminate entry */
        im := Vectors select X[i] else (rho`WeightBase_vectB)[i]*X;
        g := elimEntryInRow(var, rho, im, i, j, r : Vectors := Vectors);
        if (g cmpeq false) then 
            j := 0; //excp := g; 
            IndentPop();
            return;
        end if;
        
        v := g*v;
        rightActionInv(rho, ~X, g, false);
        
        /* Print some info if we're verbose */
        if GetVerbose("RowRed") ge 7 then
            printf "row, i = %o, j = %o, r = %o\n", i, j, r;
            Printmxs( Sides select [* rho(u), X, rho(v) *] else [*X*] );
            if (GetVerbose("RowRed") ge 9) then read s; IndentPush(); end if;
        end if;
    end for;
    im := Vectors select X[i] else (rho`WeightBase_vectB)[i]*X;
    
    /* OK, we're done */
    vprintf RowRed, 4 : "\nclearRow done (i=%o); X = \n%o\n", i, X;
    IndentPop();
end procedure;

elimEntryInCol := function(rho, r, i, j, u, X);
    G := Domain(rho);
    deg := extensionDegree(rho);
    wtV := VectorSpace( Rationals(), Dimension(RootDatum(G)) );
    
    imweight, imvect := (rho`WeylRefl_imWeightVect)( (rho`WeightBase_B)[i], r );
    XM := X*(rho`WeightBase_M);
    imXM := imvect*XM;

    if ( imXM, (rho`WeightBase_vectOrbit)[j] ) eq 0 then 
        //Nothing to do
        return G!1;
    end if;

    mm := Integers()!Abs(( (wtV!imweight), wtV!Coroot(G,r) ));  // try B[i]
    pow := ( imXM, (rho`WeightBase_vectOrbit)[j] ) / ( (rho`WeightBase_vectB)[i]*XM, (rho`WeightBase_vectOrbit)[j] );

    bs := nthRoots( BaseRing(G)!(pow^deg), mm*deg );// cat nthRoots( -pow, m );
    bs := [ rt[1] : rt in bs ];
    bs := bs cat [ -b : b in bs ];
    if not exists(b){ b : b in bs | 
        (rightActionInvfunc(rho, imvect, elt<G|<r,b>>)*XM, 
        (rho`WeightBase_vectOrbit)[j] ) eq 0 } then
        return false;
    end if;
    g := elt<G | <r,b> >;
    return g;
end function;
clearCol := procedure( rho, w0s, 
    ~X, ~u, v, j, i, ~excp
    : Vectors := false, Sides := false )
    
    G := Domain(rho); W := WeylGroup(G);
    
    Phiw0i := additiveOrder( W, PermToWord(W,w0s[i]^-1) );
    for r in Phiw0i do
        g := elimEntryInCol(rho, r, i, j, u, X);
        if (g cmpeq false) then 
            j := 0; excp := "error in elimEntryInCol"; 
            return;
        end if;

        u := u*g;
        leftActionInv( rho, ~X, g );

        if GetVerbose("RowRed") ge 7 then
            printf "col, j = %o\n", i, j;
            Printmxs( Sides select [* rho(u), X, rho(v) *] else [*X*] );  
            if (GetVerbose("RowRed") ge 9) then read s; end if;
        end if;
    end for;
end procedure;

// ----------------------------------------------------
//
// Functions from the core of rowReduction
//
// * unipotentParts
// * weylPart
// * torusPart
// * oppositeUnipotentPart
// ----------------------------------------------------
unipotentParts := procedure( rho, clearrow, clearcol, ~X, ~u, ~v, ~ws, ~excp
        : Vectors := false, Sides := false)
    remaining := Reverse([1..#((rho`WeightBase_Orbits)[1])]);
    G := Domain(rho); W := WeylGroup(G); m := #(rho`WeightBase_B);  
    
    if GetVerbose("RowRed") ge 7 then
        print "unipotent part";
        Printmxs( Sides select [* rho(u), X, rho(v) *] else [*X*] );
        if (GetVerbose("RowRed") ge 9) then read s; end if;
    end if;
    for i in [1..m] do
        clearrow( ~X, u, ~v, ~ws, ~j, i, ~remaining );
        if j eq 0 then
            excp := [* i, X, v *];
            return;
        else
            Exclude( ~remaining, j );
            if not Vectors then
                clearcol( ~X, ~u, v, j, i );
            end if;
        end if;
    end for;
end procedure;

weylPart := procedure(rho, ws, ~X, ~w, u, ~wdot, v, h : Vectors := false, Sides := false)
    G := Domain(rho);
    w := &*[ WeylGroup(G) | wi : wi in Reverse(ws) ];
    wdot := elt< G | w >;
    rightActionInv( rho, ~X, wdot, false );
    if (GetVerbose("RowRed") ge 7) then
        print "weyl part"; 
        if Vectors then
            Printmxs( Sides select [*X,rho(h),rho(wdot),rho(v)*] else [*X*] );
        else
            Printmxs( Sides select [*rho(u),rho(h),rho(wdot),rho(v)*] else [*X*] );
        end if;
        if (GetVerbose("RowRed") ge 9) then read s; end if;
    end if;
end procedure;

torusPart := procedure( rho, 
    ~X, u, wdot, v, ~h, ~excp : 
    Vectors := false, Sides := false)

    G := Domain(rho); R := RootDatum(G);
    k := BaseRing(G); m := (SemisimpleRank(G) eq 0) select 0 else #(rho`WeightBase_B); 
    wtV := VectorSpace( Rationals(), Dimension(R) );   
    deg := extensionDegree(rho);
    torusInverse := func< X | Vectors select torusInverseForVectors(rho, X) else torusInverseForMatrices(rho, X) >;

    hs := [ elt<G| wtVk!h > : h in torusInverse(X) | IsCoercible( wtVk, h ) ]
        where wtVk is VectorSpace( k, Rank(G) );

    if Vectors then
        ok := exists(h){ h : h in hs |
        forall{<i,j> : j in [i..m], i in [1..m] | (A[i],(rho`WeightBase_vectB)[j]) eq 
            ((i eq j) select 1 else 0) }
        where A is rightActionInvfunc(rho, X, h) };
    else
        ok := exists(h){ h : h in hs | IsScalar(A) and A^deg eq Parent(A)!1 
            where A is rightActionInvfunc(rho, X, h) };
    end if;
    if not ok then 
        excp := [* "not ok" *];
        return;
    end if;
    
    rightActionInv(rho, ~X, h, false);
    if GetVerbose("RowRed") ge 7 then
        print "torus"; 
        if Vectors then
            Printmxs( Sides select [*X,rho(h),rho(wdot),rho(v)*] else [*X*] );
        else
            Printmxs( Sides select [*rho(u),rho(h),rho(wdot),rho(v)*] else [*X*] );
        end if;
        if (GetVerbose("RowRed") ge 9) then read s; end if;
    end if;
end procedure;

oppositeUnipotentPart := procedure(rho, ~X, u, v
        : Sides := false)
	print "hi";
    G := Domain(rho); m := #(rho`WeightBase_B);
    for i in [1..m] do
        for j in [1..i-1] do
            b := ( X[i], (rho`WeightBase_vectB)[j] );
            if b ne 0 then
                r := RootPosition( G, (rho`WeightBase_B)[j]-(rho`WeightBase_B)[i] );
                u := elt<G|<r,-b>>*u;
                rightActionInv(rho, ~X, elt<G|<r,-b>>, false);
            end if;
            if GetVerbose("RowRed") ge 7 then
                print "row2 ",j;
                Printmxs( Sides select [* rho(u), X, rho(v) *] else [*X*] );
                if (GetVerbose("RowRed") ge 9) then read s; end if;
            end if;
        end for;
    end for;
end procedure;


// ----------------------------------------------------
//
// The actual rowReduction function, as described
//   in CohenMurrayTaylor03
//
// ----------------------------------------------------
///
/// We have two variants for the row reduction:
///     -> 1: The `old' variant: quicker, but may mess up "lower-diagonal" stuff
///     -> 2: The `new' variant: slower, but keeps the "lower-diagonal" stuff intact
///     Use 1, 2, or "default" as optional UseVariant parameter,
///     for matrices the default is 1, for vectors the default is 2.
rowReduction := function( rho : Sides:=false, Vectors:=false,
  NoTorus:=false, UseVariant:="default" )

  // Input validation
  if Type(Sides) ne BoolElt then error "RowReduction: Sides must be a boolean."; end if;
  if Type(Vectors) ne BoolElt then error "RowReduction: Vectors must be a boolean."; end if;
  if Type(NoTorus) ne BoolElt then error "RowReduction: NoTorus must be a boolean."; end if;
  if not (UseVariant cmpeq "default" or (Type(UseVariant) eq RngIntElt and UseVariant in {1,2})) then 
      error "RowReduction: UseVariant must be either \"default\", 1 or 2."; 
  end if;

  // Some basic invariants  
  G := Domain( rho );   M := Codomain( rho );  
  W := WeylGroup( G );  R := RootDatum( G );  N := NumPosRoots( R );
  k := BaseRing( G );   K := BaseRing( M );
  l := SemisimpleRank( G );  n := ReductiveRank( G );
  d := Degree( Codomain( rho ) );  V := VectorSpace( K, d );
  //  K is (or contains) a degree deg Kummer extension of k
  deg := extensionDegree(rho);

  //
  // If the group is purely toral, we (have to) take a shortcut
  //
  if l eq 0 then
	  if NoTorus then return func<X | One(G)>; end if;
		
	  return function( X )
	    H := G;

	    // check input element && initialize
	    if Vectors then
	      X := validateRowReductionInputForVectors(rho, X);
	    else
	      X := validateRowReductionInputForNonVectors(rho, X);
	    end if;
	    Xorg := X; 

	      excp := false;
	      torusPart(rho, ~X, G!1, G!1, G!1, ~h, ~excp : Vectors := Vectors, Sides := Sides);
	      if (excp cmpne false) then 
	        return false, excp; 
	      end if;
	    return h;
	  end function;	
  end if;

  // Weight base and associated variables
  // The result of this call is stored as attributes of rho, so we don't need
  // to pass its result around.
  //
  // If there is no ExtendedTorus, change the call from the old WeightBase
  // to the new weightBase.  DET 2013-09-17
  if assigned rho`ExtendedTorus then
    B, vectB, Orbits, vectOrbit, J, Ws, Actions, M, WeylMxs := WeightBase(rho);
  else
    B, vectB, Orbits, vectOrbit, J, Ws, Actions, M, WeylMxs := weightBase(rho);
  end if;
  m := #B;
  wtV := VectorSpace( Rationals(), Dimension(R) );   

  // Decompose the longest element according to the weight base
  w0 := LongestElement( W );
  w0s := [ TransversalElt( Ws[i], Ws[i+1], LongestElement(Ws[i]) ) : i in [1..m-1] ] cat
         [ LongestElement(Ws[m]) ];

  // The action of Weyl reflections on the weights
  // The result of this call is stored as attributes of rho, so we don't need
  // to pass its result around.
  _ := actionsOfWeylReflections(rho);

  //// assign clearrow and clearcol functions using the generics above ////
  clearrow := procedure( ~X, u, ~v, ~ws, ~j, i, ~remaining )
    excp := false;
    clearRow( rho, 
      ~X, u, ~v, ~ws, ~j, i, ~remaining, ~excp
      : Vectors := Vectors, Sides := Sides, UseVariant := UseVariant);
    if (excp cmpne false) then
      vprintf RowRed, 1 : "clearRow failed: %o\n", excp;
      return;
    end if;
  end procedure;
  clearcol := procedure( ~X, ~u, v, j, i )
    excp := false;
    clearCol( rho, w0s, 
      ~X, ~u, v, j, i, ~excp
      : Vectors := Vectors, Sides := Sides );

    if (excp cmpne false) then
      vprintf RowRed, 1 : "clearCol failed: %o\n", excp;
      return;
    end if;
  end procedure;
  
  //// the actual function ////
  return function( X )
    H := G;  // this is necessary because G is considered a global variable

    // check input element && initialize
    if Vectors then
      X := validateRowReductionInputForVectors(rho, X);
    else
      X := validateRowReductionInputForNonVectors(rho, X);
    end if;
    Xorg := X; u := G!1; h := G!1; wdot := G!1; v := G!1; 
    
    ////Unipotent parts////
    ws := [W|]; excp := false;
    unipotentParts( rho, clearrow, clearcol, ~X, ~u, ~v, ~ws, ~excp
        : Vectors := Vectors, Sides := Sides);
    if (excp cmpne false) then
        return false, excp;
    end if;
    
    ////Weyl part////
    weylPart(rho, ws, ~X, ~w, u, ~wdot, v, h : Vectors := Vectors, Sides := Sides);

    if not NoTorus then
      excp := false;
      torusPart(rho, ~X, u, wdot, v, ~h, ~excp :
        Vectors := Vectors, Sides := Sides);
      if (excp cmpne false) then 
        return false, excp; 
      end if;
      
      if (Vectors) then
        ////Opposite unipotent part////
        oppositeUnipotentPart(rho, ~X, u, v 
          : Sides := false);
      end if;
    else
      u := G!1;
    end if;
    
    ////Done////
    return u * h * wdot * v;
  end function;
end function;

// ----------------------------------------------------
//
// Intrinsics to access rowReduction
//
// These should be replaced by Inverse
//
// ----------------------------------------------------

intrinsic GeneralisedRowReduction( rho : Sides:=false, UseVariant := "default" ) -> .
{The inverse of rho}
  return rowReduction( rho : Sides:=Sides, UseVariant := UseVariant );
end intrinsic;

intrinsic RowReductionHomomorphism( rho : Sides:=false, UseVariant := "default" )
-> .
{The inverse of rho}
  return rowReduction( rho : Sides:=Sides, UseVariant := UseVariant );
end intrinsic;

RowReduceVectorImages := function( rho : Sides:=false, UseVariant := "default" )
  return rowReduction( rho : Vectors, Sides:=Sides, UseVariant := UseVariant );
end function;




