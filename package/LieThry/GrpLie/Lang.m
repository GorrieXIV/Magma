freeze;

/*
  $Id: Lang.m 36207 2011-11-29 03:59:35Z danr $

  Arjeh Cohen, Scott H Murray and Sergei Haller
*/

import "../Repn/Repn.m" : 
  reduceToBasis, WeightBase, rSpace;
import "../GrpCox/GrpCox.m" :
  transformation;
import "../Repn/RowRed.m" :
  RowReduceVectorImages;


// ---------------------------------------------------------------
//
//  Matrix norms
//
//  These function work for matrices and GrpLie elements

// c^(F^(r-1)) ... c^F c
FPower := function( c, r, q )
  F := func< a, i | Parent(a)![ x^(q^i) : x in Eltseq(a) ] >;
  if r eq 0 then
    return Parent(c)!1;
  elif r gt 0 then
    power := c;  i := 1;
  end if;

  ret := Parent(c)!1;
  repeat
    if r mod 2 eq 1 then
      r := r-1;
      ret := F(ret,i)*power;
    end if;
    power := F(power,i)*power;
    r div:= 2;  i *:= 2;
  until r eq 0;
  return ret;
end function;

FOrder := function( c, r, q )
  return Order( FPower( c, r, q ) );
end function;


// ---------------------------------------------------------------
//
//  F-eigenspaces
//


// the k-matrix of the automorphism K -> K, x :-> x^q
MatAut := function( q, K, k )
  d := Degree( K, k );
  B := Basis( K, k );
  return Matrix( [ Eltseq( b^q, k ) : b in B ] );
end function;

// rewrite v, an nd dimensional vector over k,
// as an n dimensional vector over K
VectIncreaseField := function( v, K, k )
  d := Degree( K, k );  
  v := Eltseq( v );  n := #v;
  ret := [K|];  i := 0;
  repeat
    Append( ~ret, v[[d*i+1..d*(i+1)]] );
    i +:= 1;
  until d*i eq n;
  return Vector( ret );
end function;

minimalField := function( S )
  K := Universe( S ); 
  k := sub< K | K!1 >;
  for a in S do
    k := CommonOverfield( k, sub< K | a > );
  end for;
  return k;
end function;

// a k-basis for the elements v of V(k_{rs}) st v^Fc=v
FEigenspace := function( c, q : Deterministic := false )
  c := Matrix( c );
  k := GF( q );  n := Nrows( c );
  F := func< x | Parent(x)![ a^q : a in Eltseq(x) ] >;
  r := Lcm( Degree( minimalField(Seqset(Eltseq(c))) ), Degree(k) ) div Degree(k);
  s := Order( FPower(c,r,q) );
  K := ext< k | r*s >;
  if Deterministic then
    A := MatAut( q, K, k );
    C := DiagonalJoin( [A:i in [1..n]] ) * WriteOverSmallerField( c, K, k );
    V := Eigenspace( C , k!1 );
    return [ VectIncreaseField( v, K, k ) : v in Basis(V) ];
  else
    M := MatrixAlgebra( K, n );
    coeffs := [M|c];
    for i in [2..r*s-1] do  coeffs[i] := F(coeffs[i-1])*c;  end for;
    repeat
      x := Random( M );
      a := x;  xFi := x;
      for i in [1..r*s-1] do
        xFi := F(xFi);
        a +:= xFi*coeffs[i];
      end for;
    until Determinant( a ) ne 0;
    return [ A[i] : i in [1..n] ] where A is a^-1;
  end if;
end function;  


// ---------------------------------------------------------------
//
//  Lang
//

intrinsic Lang( c::GrpMatElt, q::RngIntElt ) -> AlgMatElt
{a such that c = a^-F * a}
  c := Matrix( c );
  require Determinant( c ) ne 0 : "The matrix must be invertible";
  require Category( BaseRing(c) ) eq FldFin :
    "The matrix must be over a finite field"; 
  ok, p := IsPrimePower( q );
  require ok : "The integer must be a prime power";
  require Characteristic( BaseRing(c) ) eq p :
    "The matrix has the wrong characteristic";
  
  return Matrix( FEigenspace( c, q ) )^-1;
end intrinsic;

intrinsic Lang( c::GrpLieElt, q::RngIntElt ) -> GrpLieElt
{a such that c = a^-F * a}
  G := Parent( c );
  k := GF(q);  kr := BaseRing( G );
  require Category( kr ) eq FldFin :
    "The base ring must be a finite field"; 
  ok1, p1, a1 := IsPrimePower( q );
  ok2, p2, a2 := IsPrimePower( #kr );
  require ok1 and ok2 and p1 eq p2 and IsDivisibleBy( a2, a1 ) :
    "Invalid prime power";
  
  // The Lie algebra E(k)
  rho, L := AdjointRepresentation( G : NoWarning );
  d := Dimension( L );
  C := Matrix( rho( c ) );
  B := Matrix( FEigenspace( C, q ) )^-1;
  B := [ B[i] : i in [1..d] ];
  V := VectorSpaceWithBasis( B );
  K := BaseRing( V );
  G := BaseExtend( G, K );
  rho, L := AdjointRepresentation( G : NoWarning );
  E := LieAlgebra< k, d | 
    [ [ Coordinates(V, V!(L!x * L!y) ) : y in B ] : x in B ] >;
  inj := map< E -> L | m :-> &+[ m[i]*B[i] : i in [1..d] ] >;

  // Chevalley bases
  pos, neg, cart := StandardBasis( L );
  chevL := pos cat neg cat cart;  
  
  E`RootDatum := RootDatum( G );
  pos, neg, cart := StandardBasis( E );
  chevE := pos cat neg cat cart;
  
  /*V := VectorSpace( K, d );
  VL := VectorSpaceWithBasis( ChangeUniverse(chevL,V) );
  VE := VectorSpaceWithBasis( ChangeUniverse(chevE,V) );
  forall(s){<i,j>:i in [1..d],j in [1..d]|
    Coordinates( VL, VL!(chevL[i]*chevL[j]) ) eq 
    Coordinates( VE, VE!(chevE[i]*chevE[j]) )};*/

  // Compute a
  A := transformation( chevL, 
    [ &+[ (K!ch[i])*B[i] : i in [1..d] ] : ch in chevE ] );
  /*forall(s){<i,j>:i in [1..d],j in [1..d]|(L.i*L.j)*A eq (L.i*A)*(L.j*A)};*/
  inv := RowReductionHomomorphism( rho );
  a := inv( A );
  
  // Correct for nonstandard automorphisms
  // ????


  // Correct for outer automorphisms
  // ????

  // Correct for the centre
  // ????

  return a;
end intrinsic;



// --------------------- eof -----------------------------------





// ===============================================================
//
//  The Graveyard
//
// ===============================================================




// ===============================================================
//
//  Lang's theorem for Borel subgroups
//
// ===============================================================

// a st F(a) * g * a^-1 = 1
/*BorelLang := function( g, q );
  G := Parent( g );  k := BaseRing( G );
  u, t := Bruhat( g );
  
  // torus
  if t ne 1 then
    t := Eltseq( Eltlist( t )[1] );
    a := [ Hilbert90( a, q )^-1 : a in t ];
    K := Universe( a );  G := BaseExtend( G, K );
    a := elt< G | VectorSpace( K, Rank(G) )!a >;
  else
    K := k;  a := G!1;
  end if;
  
  // unipotent
  sigma := iso< K -> K | x :-> x^q, x :-> x^q >;
  F := FieldAutomorphism( G, sigma );
// F(a)*CoerceGrpLie(G,t)*a^-1 eq 1;
  u := F(a) * CoerceGrpLie(G,u) * F(a)^-1;
  while u ne 1 do
    b := Eltlist(u)[1][1];
    r := b[1];  b := b[2];
    c := AdditiveHilbert90( b, q );
    if c notin K then
      K := CommonOverfield( K, Parent(c) );
      G := BaseExtend( G, K );
      sigma := iso< K -> K | x :-> x^q, x :-> x^q >;
      F := FieldAutomorphism( G, sigma );
      u := CoerceGrpLie(G,u);
      a := CoerceGrpLie(G,a);
    end if;
    b := elt< G | <r,-c> >;
    u :=  F(b) * u * b^-1;  a := b*a;
  end while;
  
  return a;
end function;  
*/
  

// ===============================================================
//
//  Lang's theorem for classical groups
//
// ===============================================================
/*
reverseCols := function( B )
  B := Transpose( B );
  B := Matrix( [ B[i] : i in [Nrows(B)..1 by -1 ] ] );
  return Transpose( B );
end function;

reverseEchelon := function( B )
  B := Matrix( B );
  B := reverseCols( B );
  B := EchelonForm( B );
  B := reverseCols( B );
  return [ B[i] : i in [1..Nrows(B)] ];
end function;

Eigenbasis := function( A )
  evals := Setseq( Eigenvalues( A ) );
  return &cat[ reverseEchelon( Basis( Eigenspace(A,e[1]) ) ) : e in evals ], 
         &cat[ [ e[1] : i in [1..e[2]] ] : e in evals ];
end function;


WeightEigenbasis := function( a, G, rho, inv )
  wts, wvs := Weights( rho );
  base := reduceToBasis( wts );
  A := rho( a );
  p := MinimalPolynomial( A );
  K := SplittingField( p );
  A := ChangeRing( A, K );
  evects, evals := Eigenbasis( A );
  wtims := [];  wvims := [];  evalims := [];
  V := Universe(wts);  Vim1 := sub< V | >;
  for wt in wts do
    if wt in Vim1 then
      _ := exists(l){ l : l in [1..#evals] | evals[l] eq 1 };
      Remove( ~evects, l );  Remove( ~evals, l );
    end if;
  end for;
  for i in [1..#base] do
    wvims[i] := evects[1];  evalims[i] := evals[1];
    Remove( ~evects, 1 );  Remove( ~evals, 1 );
    Vi := VectorSpaceWithBasis( wts[base[[1..i]]] );
    for wt in [ wts[j] : j in [1..#wts] | j ne base[i] ] do
      if wt in Vi and wt notin Vim1 then
        coeffs := Coordinates( Vi, wt );
        eval := &*[ evalims[l]^(Integers()!coeffs[l]) : l in [1..i] ];
        _ := exists(l){ l : l in [1..#evals] | evals[l] eq eval };
        Remove( ~evects, l );  Remove( ~evals, l );
      end if;
    end for;
    Vim1 := Vi;
  end for;
  return wvims, evalims;
end function;
*/

// only works for semisimple elements, so far
/* standard representation version 
intrinsic ConjugateIntoBorel( a::GrpLieElt ) -> GrpLieElt
{Element b and c such that c*a*c^-1 = b is in the Borel}
  G := Parent( a );
  rho := StandardRepresentation( G );
  A := rho(a);
  p := CharacteristicPolynomial( A );
  K := SplittingField( p );
  A := ChangeRing( A, K );
  G := BaseExtend( G, K );
  S,U := MultiplicativeJordanDecomposition( A );
  rho := StandardRepresentation( G );
  V := rSpace( Codomain( rho ) );
  _,_,_,_, wB, wvB := weightOrbitBase(rho);
  inv := RowReduceVectorImages( rho );
  WeightEigenbaseRec := function( ims, evals, evects )
    if #ims eq #wB then  return ims;  end if;
    for j in [1..#evals] do
      if Category( inv(ims cat [evects[j]]) ) ne BoolElt then
        ret := $$( ims cat [evects[j]], Remove( evals, j ), Remove( evects, j ) );
        if Category( ret ) ne BoolElt then
//          print ret, "\n";
          return ret;
        end if;
      end if;
    end for;
    return false;
  end function;
  evects, evals := Eigenbasis( S );
  ims := WeightEigenbaseRec( [], evals, evects );
  if Category(ims) eq BoolElt then  error "not found";  end if;
  c := inv( ims );
  return C*S*C^-1, C*U*C^-1 where C is rho(c);//a^(c^-1), c;
end intrinsic;*/

/*
FEigenvectors := function( C, q )
  d := Nrows( C );  k := GF( q );
  F := func< x, q | Parent(x)![ a^q : a in Eltseq(x) ] >;
  NF := func< x, i | (i eq 0) select Parent(x)!1 else F($$(x,i-1),q)*x >;
  kr := CommonOverfield( k, minimalField(Seqset(Eltseq(C))) );  
  r := Degree( kr, k );
  
  B := NF( C, r );
  krs := CommonOverfield( kr, SplittingField(MinimalPolynomial(B)) );
  B := ChangeRing( B, krs );
  evects, evals := Eigenbasis( B );
  assert forall{ i : i in [1..#evects] | evects[i]*B eq evects[i]*evals[i] };
  
  fvects := [];  K := krs;
  for i in [1..#evals] do
    if evals[i] eq 0 then
      Append( ~fvects, evects[i] );
    else
    beta := evals[i];  u := evects[i];
    s := Degree( CommonOverfield(sub<K|beta>,kr), kr );
    alpha := Hilbert90( beta^(-s), q^(r*s) );
    st := Degree( CommonOverfield(Parent(alpha),kr), kr );
    K := CommonOverfield( K, Parent(alpha) );  alpha := K!alpha;
    V := VectorSpace( K, d );  fvects := ChangeUniverse( fvects, V );
    u := V!u;   C := ChangeRing( C, K );
    fvects[i] := &+[ F(u*alpha,q^i) * NF(C,i) : i in [0..r*s-1] ];
    end if;
  end for;
  assert forall{ i : i in [1..#fvects] | F(fvects[i],q)*C in {fvects[i],V!0} };
//  assert Dimension( sub< V | fvects > ) eq Dimension(V);
  return fvects, evects, evals, K;
end function;

AdjointEigenvectors := function( a )
  G := Parent( a );  k := BaseRing( G );
  L, rho := LieAlgebra( G );
  inv := RowReduceVectorImages( rho );
  A := Matrix( rho(a) );
  if not IsSemisimple( A ) then
    error "Only implemented for semisimple matrices";
  end if;
  C := Nullspace( A-1 );  // extend field??
  C := sub< L | ChangeUniverse( Basis( C ), L ) >;
  T := CartanSubalgebra( C );
  ads := [ AdjointMatrix( L, t ) : t in Generators( T ) ];
  _, P := Diagonalise( ads );
  evects := { P[i] : i in [1..Nrows(P)] };
  K := BaseRing( Universe(evects) );
  GK :=  BaseExtend( G, K );  a := CoerceGrpLie( GK, a );
  rhoK := AdjointRepresentation( GK );
  invK := RowReduceVectorImages( rhoK );
  VK := rSpace( Codomain( rhoK ) );
  return ChangeUniverse( evects, VK );
end function; 

AdjointFEigenvectors := function( c, q )
  G := Parent( c );  rho := AdjointRepresentation( G );
  C := rho( c );
  d := Nrows( C );  k := GF( q );
  F := func< x, q | Parent(x)![ a^q : a in Eltseq(x) ] >;
  FG := StandardFrobenius( q );
  NF := func< x, i | (i eq 0) select Parent(x)!1 else F($$(x,i-1),q)*x >;
  kr := CommonOverfield( k, minimalField(Seqset(Eltseq(C))) );  
  r := Degree( kr, k );

  b := G!1;  c := CoerceGrpLie( G, c );
  for i in [1..r] do
    b := FG(b)*c;
  end for;
  
  B := rho( b );
  evects := Setseq( AdjointEigenvectors( b ) );
  krs := BaseRing( Universe( evects ) );
  B := ChangeRing( B, krs );
  evals := [];
  for i in [1..#evects] do
    v := evects[i];  _ := exists(j){j : j in [1..OverDimension(v)] | v[j] ne 0};
    evals[i] := (v*B)[j]/v[j];
  end for;  
  assert forall{ i : i in [1..#evects] | evects[i]*B eq evects[i]*evals[i] };
  
  fvects := [];  K := krs;
  for i in [1..#evals] do
    beta := evals[i];  u := evects[i];
    krs := CommonOverfield( minimalField(Seqset(Eltseq(u))), kr );
    s := Degree( krs, kr );
    alpha := Hilbert90( beta^(-s), q^(r*s) );
    K := CommonOverfield( K, Parent(alpha) );  alpha := K!alpha;
    V := VectorSpace( K, d );  fvects := ChangeUniverse( fvects, V );
    u := V!u;   C := ChangeRing( C, K );
    for a in krs do//Basis( krs, kr ) do
      Append( ~fvects, &+[ F(a*u*alpha,q^i) * NF(C,i) : i in [0..r*s-1] ] );
    end for;
  end for;
  assert forall{ v : v in fvects | F(v,q)*C eq v };
  fvects := fvects[reduceToBasis(fvects)];
  assert Dimension( sub< V | fvects > ) eq Dimension(V);
  return fvects, evects, evals, K;
end function;
*/


// not working
/*AdjointEigenvectorsWeightBase( a )
  B := WeightBase( rho );  // IS THIS NECESSARY
  _ := exists(E){ E : E in Subsequences(evects,#B) | Category(invK(E)) ne BoolElt };
  return E;
end function;*/


/*intrinsic ConjugateIntoBorel( a::GrpLieElt ) -> GrpLieElt
{Element b and c such that c*a*c^-1 = b is in the Borel}
  E := AdjointEigenvectorWeightBase( a );
  G := BaseExtend( Parent(a), BaseRing(Universe(E)) );
  rho := AdjointRepresentation( G );
  inv := RowReduceVectorImages( rho );
  x := inv(E);
  return a^(x^-1), x;
end intrinsic;*/



/*
intrinsic Conj2( c ) -> GrpLieElt
{b and wdot such that c = wdot^b}
  G := Parent( c );
  u, t, wdot, up := Bruhat( c );
  k := BaseRing( G );
  F<[h]> := RationalFunctionField( k, Rank(G) );
  F<[a]> := RationalFunctionField( F, NumPosRoots(G) );
  a := [ c`filter[r] select a[r] else 0 : r in [1..NumPosRoots(G)] ];
  ChangeUniverse( ~h, F );
  G := BaseExtend( G, F );
  b := elt< G | a, VectorSpace(F,Rank(G))!h >;
  lhs := (b*u*t)^wdot;  rhs := (b * up^-1);
  return lhs, rhs;
end intrinsic;
  


WEigenvectors := function( w, G, rho, wts, wvs )
  cyclesigns := function( W, cycle, wvs, K )
    ret := [ K | ];
    for j in cycle do
      _:=exists(eta){ (wvs[i]*W,wvs[j]) : i in cycle | (wvs[i]*W,wvs[j]) ne 0 };
      Append( ~ret, eta );
    end for;
    return ret;
  end function;
  
  k := BaseRing( G );
  refls := [ ChangeRing( refl, Rationals() ) : refl in ReflectionMatrices( RootDatum(G) ) ];
  Wim := rho(w);
  wonwts := [];
  for r in [1..Nrows(Wim)] do
    _ := exists(s){ s : s in [1..Nrows(Wim)] | Wim[r][s] ne 0 };
    Append( ~wonwts, s );
  end for;
  wonwts := Sym(#wts)!wonwts;
  cycles := CycleDecomposition( wonwts );

  r := Lcm( [ ((&*cyclesigns( Wim, cycle, wvs, k ) eq 1) select 1 else 2) * #cycle : cycle in cycles ] );;
  K := Parent( RootOfUnity( r, k ) );
  Wim := ChangeRing( Wim, K );  wvs := [ ChangeRing(wv,K) : wv in wvs ];
  
  evals := [];  evects := [];
  for cycle in cycles do
    m := #cycle;  signs := cyclesigns( Wim, cycle, wvs, K );
    if &*signs eq 1 then
      xi := RootOfUnity( m, k );
      xis := [ xi^j : j in [1..m] ];
    else
      xi := RootOfUnity( 2*m, k );
      xis := [ xi^(2*j-1) : j in [1..m] ];
    end if;
    Append( ~evals, xis );
    Append( ~evects, [ &+[ ( xis[j]^(-i+1) * &*signs[[1..i]]) * wvs[cycle[i]] : i in [1..m] ] : j in [1..m] ] );
  end for;

  return cycles, evects, evals, wonwts;
end function;

weylToG := function( w, G )
  ret := G!1;
  for r in PermToWord(Parent(w),w) do
    ret *:= elt<G|r>;
  end for;
  return ret;
end function;





// returns some representation of L, and its inverse
repn := function( L )
  rho := (assigned L`RootDatum and
    Gcd(#CoisogenyGroup(RootDatum(L)),Characteristic(BaseRing(L))) eq 1) 
    select StandardRepresentation( L ) else AdjointRepresentation( L );
  ims := [ rho(b) : b in Basis( L ) ];  
  M := Universe( ims );
  n := Degree( Universe( ims ) );  k := BaseRing( M );
  V := KMatrixSpace( k, n, n );
  ims := ChangeUniverse( ims, V );
  idxs := reduceToBasis( [ Vector(Eltseq(im)) : im in ims ] );
  ims := ims[idxs];
  U := RMatrixSpaceWithBasis( ims );
  inv := function( a )
    coords := Coordinates( U, U!a );
    ret := L!0;
    for i in [1..#idxs] do  ret[idxs[i]] := coords[i];  end for;
    return ret;
  end function;
  return rho, inv, U, V;
end function;
  
comm := func< a, b | a*b - b*a >;

intrinsic JacobsonMorozov( x::AlgLieElt ) -> AlgLieElt, AlgLieElt
{Given a nilpotent element x of a Lie algebra returns elements y, h that
span a subalgebra isomorphic to sl_2}
  L := Parent( x );  k := BaseRing( L );
  require x ne L!0 : "Zero element not allowed";
  ad := AdjointRepresentation( L );
  require IsNilpotent( ad(x) ) : "Not a nilpotent element";

  X := ad( x );
  J, T, part := JordanForm(X);
  part := [ t[2] : t in part ];
  require forall{ m : m in part | m-1 lt Characteristic(k) } : 
    "Nilpotency index too large";

  H0 := - T^-1*DiagonalMatrix( k, &cat[ [1-m..m-1 by 2] : m in part ] )*T;
  super := function( m )
    Y0 := ZeroMatrix( k, m, m );
    for i in [1..m-1] do
      Y0[i+1,i] := i*(m-i);
    end for;
    return Y0;
  end function;
  Y0 := T^-1*DiagonalJoin( < super(m) : m in part > )*T;

  M := Codomain( ad );
  d := Degree( M );  Mvs := KMatrixSpace( k,d,d );
  matToVect := func< A | Vector( Eltseq( A ) ) >;
  vectToMat := func< v | Matrix( k,d,d, Eltseq(v) ) >;
  tracemat := Matrix( k, d^2, d^2,
    [ (i eq l and j eq k) select 1 else 0 :
    i in [1..d], j in [1..d], k in [1..d], l in [1..d] ] );

  im := sub< Mvs | [ Mvs | ad(b) : b in Basis(L) ] >;
  perp := &meet[ Nullspace( tracemat*Transpose(Matrix(matToVect(A))) ) : 
    A in Basis(im) ];
  perp := sub< Mvs | [ vectToMat(b) : b in Basis(perp) ] >;
  Mvsb := KMatrixSpaceWithBasis( Basis(im) cat Basis(perp) );
  proj := function( A )
    coords := Coordinates( Mvsb, Mvsb!A );  B := Basis(im);
    return M!&+[ coords[i]*B[i] : i in [1..Dimension(im)] ];
  end function;
  H := proj(H0);  Z := proj(Y0);
//  comm(H,X) eq 2*X;
//  comm(X,Z) eq H;

  t := Nullspace(X);  dim := Dimension(t);
  tmat := sub< Mvs | [ ad(b) : b in Basis(t) ] >;
  inv := Matrix( k, dim,dim,
    [ Coordinates( tmat, tmat!(comm(H,b)+2*b) ) : b in Basis(tmat) ] )^-1;
  U := comm(H,Z)+2*Z;
//  U in tmat;
  V := Vector( Coordinates( tmat, tmat!U ) );
  V := V*inv;  B := Basis( tmat );
  V := &+[ V[i]*B[i] : i in [1..#B] ];
  Y := Z-V;
//  comm(H,Y) eq -2*Y;
//  comm(X,Y) eq H;

  imb := KMatrixSpaceWithBasis( [ Mvs | ad(b) : b in Basis(L) ] );
  inv := func< A | L!Coordinates( imb, imb!A ) >;
  y := inv(Y);  h := inv(H);
//  Y eq ad(y);  H eq ad(h);
//  h*x eq 2*x;  h*y eq -2*y;  x*y eq h;
  return y,h;
end intrinsic;
*/    

//  NB: does not work for some reductive algebras

/*
  
//  Note: experimental;  not proved correct
intrinsic NilpotentElement( L::AlgLie ) -> AlgLieElt
{Returns a nonzero nilpotent element of L}
  require Dimension( L ) ne 0 : "The Lie algebra must be nontrivial";
  M := SolubleRadical( L );
  if Dimension( M ) ne 0 then
    return L!M.1;
  end if;
  
  // L is now semisimple
  // This involves a factor of q -- should be more efficient
  repeat
    repeat x := Random( L ); until x ne L!0;
    s, n := JordanDecomposition( x );
    if n ne L!0 then
      return n;
    end if;
    X := AdjointMatrix( L, x );
    evals := Setseq( Eigenvalues( X ) );
    if exists(i){ i : i in [1..#evals] | evals[i][1] eq 0 } then
      Remove( ~evals, i );
    end if;
  until #evals gt 0;
  _, i := Minimum( [ t[2] : t in evals ] );
  return L!( Rep( Eigenspace( X, evals[i][1] ) ) );
end intrinsic;

// NB: need diffrent definition for characteristic 2
intrinsic IsExtremal( L::AlgLie, x::AlgLieElt ) -> BoolElt
{True iff x is an extremal element of L}
  require x ne L!0 : "Zero element not allowed";
  S := sub< Module(L) | x >;
  return forall{ b : b in Basis(L) | Vector( (b*x)*x ) in S };
end intrinsic;

// reduce the degree of nilpotence of x to 3
reduceNilpotence := function( x )
  ok, n := IsNilpotent( x );
  if not ok then
    error "x not nilpotent";
  elif n eq 2 then  // ???
    error "x too nilpotent";
  elif n eq 3 then
    return x;
  else
    return $$( x^n );
  end if;
end function;

  


*/



