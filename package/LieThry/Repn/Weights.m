freeze;

/* 
  An alternative implementation of the internal function WeightBase
  (defined in RowRed.m).

  September 2013 Don Taylor

  $Id: Weights.m 48803 2014-10-30 06:24:06Z don $

*/

// ------------------------------------------------------------
// The common eigenspaces of a sequence of matrices Q.
//
// (A variant implementation of the function commonEigenspaces 
// defined in Algebra/AlgMat/General/diag.m)
//
// returns:  eigvals, spaces, where
// eigvals[i][j] is the eigenvalue of Q[j] on spaces[i]
// ------------------------------------------------------------
theEigenvalues := function( Q : U:=BaseModule(Universe(Q)) )
    A := Universe( Q );
    k := BaseRing( A );
    V := BaseModule( A );

    K := (k cmpeq Rationals() or ISA(Type(k),FldAlg))
      select SplittingField( [ CharacteristicPolynomial(M) : M in Q ] )
        else SplittingField( { CharacteristicPolynomial(M) : M in Q } );
 
    if k ne K then
        Q := [ ChangeRing(M,K) : M in Q ];
        U := ChangeRing(U,K); 
        V := ChangeRing(V,K);
    end if;

    restriction := function( M, S )
        d := Dimension( S );  
        return Matrix(K,d,d, [ Coordinates(S,v*M) : v in Basis(S) ]),
          func< v | &+[ v[i]*V!(S.i) : i in [1..d] ] >;
    end function;

    spaces := [* U *];
    eigvals := [ [] ];
    for M in Q do
        spaces_ := [* *];
        eigvals_ := [];
        for i := 1 to #spaces do
            ev := eigvals[i];
            X, h := restriction(M,spaces[i]);
            for e in Eigenvalues(X) do
                Append(~spaces_,
                    sub<V| [h(b) : b in Basis(Eigenspace(X,e[1]))]>);
                Append(~eigvals_, ev cat [e[1]]);
            end for;
        end for;
        spaces := spaces_;
        eigvals := eigvals_;
    end for;
    return eigvals, spaces;
end function;

// ------------------------------------------------------------
// Given rho : L -> GL(V), where V is a highest weight module,
// return the fixed space of the "standard" Borel subgroup of L.
// ------------------------------------------------------------
highestWeightSpace := function(rho)
    L := Domain(rho);
    d := SemisimpleRank(L);
// If B is a Borel subgroup of L, by the Lie-Kolchin theorem there is a
// one-dimensional subspace of V stabilised by rho(B).  Such a vector is
// fixed by the unipotent radical of B.
    F := BaseRing(L);
    E := [];
    // Constructing the intersection in a single step doesn't seem to work
    for b in Basis(F) do
        U := &meet [ Eigenspace(rho(elt<L|<i,b>>),1) : i in [1..d] ];
        Append( ~E, U );
    end for;
    return &meet E;
end function;

// ------------------------------------------------------------
// Given a common eigenvector v for a sequence M of matrices,
// return the sequence of eigenvalues.  Note that there is no
// test to ensure that v is non-zero.
// ------------------------------------------------------------
eigenvals := func< v, M | [(v*M[i])[d]*v[d]^-1 : i in [1..#M]] 
    where d is Depth(v) >;

// ------------------------------------------------------------
// Given rho : L -> GL(V), where V is irreducible and a highest 
// weight module, return the weight lambda and the space spanned 
// by a maximal vector.
// ------------------------------------------------------------
highestWeight := function(rho)
    hws := highestWeightSpace(rho);
    assert Dimension(hws) eq 1;
    L := Domain(rho);
    d := SemisimpleRank(L);
    n := ReductiveRank(L);
    k := BaseRing(L);
    assert IsFinite(k);
    K := BaseRing(Codomain(rho));
    deg := Degree(K,k);
    xi := PrimitiveElement(k);
    w := hws.1;
    H := [ rho(elt<L|Vector([k| (i eq r) select xi else 1 : i in [1..n]])>) :
        r in [1..d] ];
    // The following line requires x^deg to belong to the base field of L
    // -- this is a consequence of the way "standard" projective 
    // representations are constructed.  Projective representations
    // constructed by other means may not have this property.
    lambda := [Log(xi,k!(x^deg))/deg : x in eigenvals(w,H)];
    zndx := [i : i in [1..d] | lambda[i] eq 0 ];
    if not IsEmpty(zndx) then
        B := Basis(k);
        N := NumPosRoots(L);
        for i in zndx do
            for b in B do
                g := rho(elt<L|<N+i,b>>);
                if w^g notin hws then
                    lambda[i] := #k-1;
                    break;
                end if;
            end for;
        end for;
    end if;
    V := RSpace(Rationals(),d);
    return V!lambda, hws;
end function;

// ----------------------------------------------------
// A frame is a Weyl group orbit of the subspace spanned
// by a maximal vector.  The following function returns
// a 'Weyl group base' for a frame.
//
// rho : G -> GL(V)
// lambda is a dominant weight with eigenvector v
// ----------------------------------------------------
frameBase := function( rho, lambda, v )
  G := Domain(rho);
  R := RootDatum(G);
  l := Rank(R);
  n := Dimension(R);
  // When (if ever) is this change of ring necessary?
  // RefMats := [ChangeRing(A,Rationals()) : A in ReflectionMatrices(R)];
  RefMats := ReflectionMatrices(R);
  WeylMats := [ rho( elt<G|r> ) : r in [1..l] ];

  B := [ lambda ];
  vectB := [ v ];
  K := [1..n];
  J := [s : s in K | InnerProduct(lambda,Coroot(R,s)) eq 0];
  Q := [K,J];
  T := { s : s in K | s notin J };
  j := 0;
 
  while not IsEmpty(J) do
      j +:= 1;
      if exists(r,mu){ <r,mu> : r in T | exists{ s : s in J | 
              InnerProduct(mu,Coroot(R,s)) ne 0 } 
              where mu is B[j]*RefMats[r]} then 
          Append(~B,mu);
          Append(~vectB,vectB[j]*WeylMats[r]);
          K := J;
          Exclude(~T,r);
          J := [s : s in J | InnerProduct(Root(R,r),Coroot(R,s)) eq 0];
          Append(~Q,J);
          j -:= 1;
      else
          T := { s : s in K | s notin J };
      end if;
  end while;
  if l ne n then
    Q := [ [r : r in J | r in [1..l]] : J in Q ];
  end if;

  return B, vectB, Q, WeylMats;
end function;

// ----------------------------------------------------
// The following function is a version of WeightBase which
// has been rewritten to avoid calling the intrinsic Weights().
//
// Restriction: the highest weight calculation depends on the 
// base ring of the group being a finite field.
//
// This function stores its return values as attributes of Map:
//
// B          weight base; 
// vectB      corresponding vectors
// Orbits     basic orbits; 
// vectOrbits corresponding vectors
// J          corresponding simple root subsets
// Actions    basic actions
// M          bilinear form which is orthonormal on the
//              orbit of a maximal vector and such that the
//              other weight spaces are in its radical
// ----------------------------------------------------
weightBase := function( rho )
  if (assigned rho`WeightBase_B) then
    return rho`WeightBase_B, 
        rho`WeightBase_vectB, 
        rho`WeightBase_Orbits, 
        rho`WeightBase_vectOrbit, 
        rho`WeightBase_J,            // NOT USED
        rho`WeightBase_Ws, 
        rho`WeightBase_Actions, 
        rho`WeightBase_M, 
        rho`WeightBase_WeylMxs;      // NOT USED
  end if;
  
  G := Domain(rho);  
  I := Codomain(rho);
  R := RootDatum(G);
  k := BaseRing(G);
  K := BaseRing(I);
  l := Rank(R); // := SemisimpleRank(G);
  n := Dimension(R); // := ReductiveRank(G)
  d := Degree(I);

  // The orbits of the highest weight and maximal vector
  // under the action of the Weyl group.
  hwt, hws := highestWeight(rho);
  orbit, action := WeightOrbit(R,hwt);
  maxv := hws.1;
  vectOrbit := [ maxv^rho(elt<G|a>) : a in action ];

  // partial weight space decomposition
  orbitSpace := sub< VectorSpace(K,d) | vectOrbit >;
  xi := PrimitiveElement(k);
  torus := [ Matrix(rho(TorusTerm(G,i,xi))) : i in [1..l] ];
  _, wtsp := theEigenvalues(torus);

  // find a basis of toral eigenvectors for a complement to orbitSpace
  Q := [];
  for U in wtsp do
      basis := Basis(U meet orbitSpace);
      Q cat:= [ e : e in ExtendBasis(basis,U) | e notin basis ];
  end for;

  // the bilinear form
  wtMat := Matrix(vectOrbit cat Q)^-1;
  M := wtMat*DiagonalJoin(IdentityMatrix(K,d-#Q),ZeroMatrix(K,#Q,#Q))*Transpose(wtMat);

  // the weight basis
  B, vectB, J, WeylMxs := frameBase(rho,orbit[1],vectOrbit[1]);

  // the reflection subgroups
  Ws := [ WeylGroup(G) ];
  for i in [1..#B] do
    Append( ~Ws, ReflectionSubgroup( Ws[i], J[i+1]) );
  end for;

  // the basic orbits
  orbits := [ orbit ];
  actions := [ [Eltseq(a) : a in action] ];
  for i in [2..#B] do
    orbit, action := WeightOrbit(R, B[i] : J := J[i], dom := false);
    Append( ~orbits, orbit );  
    Append( ~actions, [Eltseq(a) : a in action] );
  end for;
  
  //Store result, for future reference
  rho`WeightBase_B          := B;
  rho`WeightBase_vectB      := vectB;
  rho`WeightBase_Orbits     := orbits;
  rho`WeightBase_vectOrbit  := vectOrbit;
  rho`WeightBase_J          := J;
  rho`WeightBase_Ws         := Ws;
  rho`WeightBase_Actions    := actions;
  rho`WeightBase_M          := M;
  rho`WeightBase_WeylMxs    := WeylMxs;

  return B, vectB, orbits, vectOrbit, J, Ws, actions, M, WeylMxs;
end function;


