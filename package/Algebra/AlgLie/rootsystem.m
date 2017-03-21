freeze;

//
//  RootSystem( L )
//
// Calculates the root system of a Lie algebra with nondegenerate
// Killing form and split Cartan subalgebra.
//

import "../../LieThry/Root/RootDtm.m" : rootOrder;
import "../../LieThry/Repn/Repn.m" : isPara;

// convert a matrix or vector to integers
integerConvert := function( A );
  p := Characteristic( BaseRing( Parent(A) ) );
  if p eq 0 then
    return Vector( Integers(), [ Integers()!a : a in Eltseq(A) ] );
  else
    A := ChangeRing( A, Integers() );
    P := Parent( A );
    return P![ (2*a le p) select a else a-p : a in Eltseq(A) ];
  end if;
end function;

// the action of ad(h) on B
AdOnSubbasis := function( L, h, B )
    F := CoefficientField( L );
    V:= VectorSpace( F, Dimension( L ) );
    W:= VectorSpaceWithBasis([ V |  V!Eltseq(b) :  b in B ]);
    M:= [];
    for j in [1..#B] do
      M cat:= Coordinates( W, V!Eltseq( L!(h*B[j]) ) );
    end for;
    return MatrixAlgebra( F, #B ) ! M;
end function;


//
//  My definition of a rational root decomposition is not quite right,
//  so this function is not documented.
//
intrinsic RationalRootDecomposition( L::AlgLie, H::AlgLie : NoCheck:=false ) 
  -> SeqEnum, SeqEnum
{The rational root decomposition of L with respect to the Cartan subalgebra H}

    // require IsCartanSubalgebra( L, H ) : "Not a Cartan subalgebra";
    if not NoCheck then
      ad := AdjointRepresentation( L );
      require IsAbelian( sub< Codomain(ad) | [ ad(L!h) : h in Basis(H) ] > ) :
        "Cannot compute a root decomposition with respect to this subalgebra";
    end if;

    // First we compute the common eigenvectors of the adjoint action of a
    // Cartan subalgebra H. Here B will be a list of bases of subspaces
    // of L such that H maps each element of B into itself.
    // Furthermore, B has maximal length w.r.t. this property.

    F := CoefficientField( L );
    V := VectorSpace( F, Dimension( L ) );

    rvs := [ [ L.i : i in [1..Dimension( L )] ] ];  
    rts := [ [] ];

    for i in [1..Dimension(H)] do

      newrvs:= [ ];  newrts := [ ];
      for j in [1..#rvs] do
        M := AdOnSubbasis( L, H.i, rvs[j] );
        fs := Factorization( MinimalPolynomial( M ) );
        for f in fs do
          B := Basis( NullSpace( Evaluate( f[1], M ) ) );
          Append( ~newrvs, [ &+[ b[l]*rvs[j][l] : l in [1..#rvs[j]] ] : b in B ]);
          Append( ~newrts, rts[j] cat [f[1]] );
        end for;

      end for;
      rvs:= newrvs;  rts := newrts;

    end for;

    // Now we throw away the subspace H.
    _ := exists(i){ i : i in [1..#rvs] | rvs[i][1] in H };
    Remove( ~rvs, i );  Remove( ~rts, i );

    return rvs, rts;
end intrinsic;


intrinsic RationalRootDecomposition( L::AlgLie ) -> SeqEnum, SeqEnum
{The rational root decomposition of L}
    if not assigned L`RationalRootDecomposition then
      rvs, rts :=
        RationalRootDecomposition( L, CartanSubalgebra( L ) );
      L`RationalRootDecomposition := [* rvs, rts *];
    end if;
    ret := L`RationalRootDecomposition;
    return ret[1], ret[2];
end intrinsic;


intrinsic RootDecomposition( L::AlgLie, H::AlgLie : MultipleFields:=false ) 
  -> SeqEnum, SeqEnum, AlgLie
{The root decomposition of L with respect to the Cartan subalgebra H}

    k := CoefficientField( L );
    ratrvs, ratrts := RationalRootDecomposition( L, H );
    if #ratrvs eq 0 then  return ratrvs, [ VectorSpace(k,0)!0 ], L;  end if;
    n := Dimension( H );
    
    if not MultipleFields then
      // Construct the splitting field
      pols := &join{ Seqset( rt ) : rt in ratrts };
      pols := { Universe(pols) | p : p in pols | Degree(p) gt 1 };
      if not IsEmpty( pols ) then
        K := SplittingField( pols );
        LK := ChangeRing( L, K );  
      else
        K := k;  LK := L;
      end if;
      HK := sub< LK | [ LK | Vector( L!h ) : h in Basis( H ) ] >;
      V := VectorSpace( K, Dimension(L) );
      rtV := VectorSpace( K, n );
    end if;
    
    allrvs := MultipleFields select [**] else [];  
    allrts := MultipleFields select [**] else [rtV|];
    for idx in [1..#ratrvs] do
    
      if MultipleFields then
        K := SplittingField( { Universe(ratrts[idx]) | p : 
          p in Seqset(ratrts[idx]) | Degree(p) gt 1 } );
        LK := ChangeRing( L, K );
        HK := sub< LK | [ LK | Vector( L!h ) : h in Basis( H ) ] >;
        V := VectorSpace( K, Dimension(L) );
        rtV := VectorSpace( K, n );
      end if;

      rvs := [[ LK | Vector( x ) : x in ratrvs[idx] ]];  rts := [[]];
      for i in [1..Dimension(H)] do
        newrvs := [];  newrts := [];
        for j in [1..#rvs] do
          M := AdOnSubbasis( LK, HK.i, rvs[j] );
          as := Roots( MinimalPolynomial( M ) );
          for a in as do
            B := Basis( Eigenspace( M, a[1] ) );
            Append( ~newrvs, [ &+[ b[l]*rvs[j][l] : l in [1..#rvs[j]] ] : b in B ]);
            Append( ~newrts, rts[j] cat [a[1]] );
          end for;
        end for;
        rvs := newrvs;  rts := newrts;
      end for;
      
      for i in [1..#rvs] do
        Append( ~allrvs, rvs[i] );  Append( ~allrts, rtV!rts[i] );
      end for;
    end for;

    return allrvs, allrts, LK;
end intrinsic;


intrinsic RootDecomposition( L::AlgLie ) -> SeqEnum, SeqEnum
{The root decomposition of L}

    if not assigned L`RootDecomposition then
      L`RootDecomposition := RootDecomposition( L, CartanSubalgebra( L ) );
    end if;

    return L`RootDecomposition;
end intrinsic;


intrinsic IsClassicalType( L::AlgLie ) -> BoolElt
{True iff L a Lie algebra of classical type}

    k := BaseRing( L );
    require ISA( Category( k ), Fld ) :
      "The Lie algebra must be defined over a field";
    p := Characteristic( k );
    require p notin {2,3} : 
      "Not implemented for fields of characteristic 2 or 3";

    if not assigned L`IsClassicalType then

      if p eq 0 then
        L`IsClassicalType := IsReductive( L );
      else
        M := L / Centre( L );
        H := CartanSubalgebra( M );
        if Dimension( H ) eq 0 then
          L`IsClassicalType := (Dimension(M) eq 0);
        else
          rvs, rts := RootDecomposition( M, H );
          L`IsClassicalType := forall{ i : i in [1..#rvs] | #rvs[i] eq 1 };
        end if;
      end if;

    end if;

    return L`IsClassicalType;
end intrinsic;

function fund_rts_from_pos_rts(posR)
    // A positive root is called fundamental if it is not the sum of two
    // OTHER positive roots. We calculate the set of fundamental roots.
    // removed OTHER from the code to allow nonreduced systems
    
    fundR:= [ ];
    for a in posR do
      issum:= false;
      for i in [1..#posR] do
        for j in [i..#posR] do
          if a eq posR[i]+posR[j] then
            issum:=true; break;
          end if;
        end for;
        if issum then break; end if;
      end for;
      if not issum then
        Append( ~fundR, a );
      end if;
    end for;
    return fundR;
end function;

// Let a and b be two roots of the rootsystem R.
// Let s and t be the largest integers such that a-s*b and a+t*b
// are roots.
// Then the Cartan integer of a and b is s-t.
CartInt := function( R, a, b )
  s:=0; t:=0;
  rt:=a-b;
  while (rt in R) or (rt eq 0*R[1]) do
    rt:=rt-b;
    s:=s+1;
  end while;
  rt:=a+b;
  while (rt in R) or (rt eq 0*R[1]) do
    rt:=rt+b;
    t:=t+1;
  end while;
  return s-t; //a eq b select s+t else s-t;
end function;

intrinsic RootSystem( L::AlgLie, H::AlgLie ) 
  -> SeqEnum, SeqEnum, SeqEnum, SeqEnum
{The root system of L with respect to Cartan subalgebra H}

    k := BaseRing( L );
    require ISA( Category( k ), Fld ) :
      "The Lie algebra must be defined over a field";
    p := Characteristic( k );
    require p notin {2,3} : 
      "Not implemented for fields of characteristic 2 or 3";
    require IsSplittingCartanSubalgebra( L, H ) : 
      "Not a splitting Cartan subalgebra";
      // NB: since L has a splitting Cartan subalgebra, it mst be classical


    B, S, L := RootDecomposition( L, H );
    if BaseRing( L ) ne k then
      H := sub< L | [ L!h : h in Basis( H ) ] >;
    end if;  
      
    rootSp := VectorSpace( k, Dimension(H) );

    Rvecs := [L| B[i][1] : i in [1..#B] ];

    // A set of roots basR is calculated such that the set
    // { [ x_r, x_{-r} ] + Z | r in basR } is a basis of H/Z.
    basH := [  ];
    basR := [  ];
    K := Centre( L );
    i := 1;
    while K ne H and i le #S do
      a:= S[i];
      j:= Position( S, -a );
      h:= B[i][1]*B[j][1];
      if h notin K then
        Append( ~basR, a );  Append( ~basH, h );
        K := sub< H | K, h >;
      end if;
      i:=i+1;
    end while;

    // A root a is said to be positive if the first nonzero element of
    // [ CartInt( S, a, basR[j] ) : j in [1..#basR] ] is positive.
    // We calculate the set of positive roots.

    posR:= [ ];
    i:=1;
    while #posR  lt #S div 2 do
      a:= S[i];
      if (not a in posR) and (not -a in posR) then
        cf:= k!0;
        j:= 0;
        while cf eq 0 do
          j:= j+1;
          cf:= CartInt( S, a, basR[j] );
        end while;
        if 0 lt cf then
          Append( ~posR, a );
        else
          Append( ~posR, -a );
        end if;
      end if;
      i:=i+1;
    end while;

    // compute fundamental roots
    fundR:= fund_rts_from_pos_rts(posR);

    // Now we calculate the Cartan matrix
    n := #fundR;
    C := Matrix( Integers(), n,n, [ [ CartInt( S, fundR[i], fundR[j] ) : 
      j in [1..n] ] : i in [1..n] ]);
    require IsCartanMatrix( C ) : 
      "This should not happen. Please email magma-bugs@maths.usyd.edu.au";

    // We sort the roots in the same order as used in RootDtm.m
    // to prevent inconsistencies between the root datum and the
    // root system

    fundR := [ rootSp | Eltseq( v ) : v in fundR ];
    N := #posR;
    perm := (N ne 0) select Sym(N)!1 else Sym(1)!1;
        
    if IsIndependent( fundR ) then

      //first we apply a permutation to fundR to get them in the correct
      //order. Then we order the roots in the same way as in a standard
      //root datum

      R:= RootDatum( C );
      St:= RootDatum( CartanName(C) );
      _,p:= IsIsomorphic( St, R );
      fundR:= [ fundR[p[i]] : i in [1..#fundR] ];
      C:= CartanMatrix( St );
      pR:= PositiveRoots( St : Basis:= "Root" );
      sorR:= [ &+[ pR[i][j]*fundR[j] : j in [1..#fundR] ] : 
                                                  i in [1..#pR] ];


/*      W := VectorSpaceWithBasis( fundR );
      posRint := [ integerConvert( Vector( Coordinates( W, v ) ) ) : v in posR ];
      Sort( ~posRint, rootOrder, ~perm ); */
      
    else  // this alternative method is needed over certain characteristics
    
      R := RootDatum( C );
      idxs := [ Position( posR, v ) : v in fundR ];
      posRvecs := Rvecs[[ Position(S,v) : v in posR ]];
      VL := VectorSpace( k, Dimension(L) );
      for r in [n+1..N] do
        e1,e2 := ExtraspecialPair( R, r );
        v := posRvecs[idxs[e1]] * posRvecs[idxs[e2]];
        ok := exists(s){ s : s in [1..N] | isPara(VL!v,VL!posRvecs[s]) };
        if not ok then
          error "Error: This should not happen. Please email magma-bugs@maths.usyd.edu.au";
        end if;
        idxs[r] := s;
      end for;
      perm := Parent(perm)!idxs;
      // apply the permutation to the roots
      sorR := [ posR[ i^perm ] : i in [1..N] ];
      
    end if;
 
    sorR cat:= [ -sorR[i] : i in [1..#sorR] ];
 
    // We also sort the root vectors.
    Rvecs:= [ Rvecs[ Position( S, sorR[i] ) ] : i in [1..#sorR] ];

    // And the fundamental roots
    fundR := sorR[[1..#fundR]];
    
    return sorR, Rvecs, fundR, C, L;
end intrinsic;


intrinsic RootSystem( L::AlgLie ) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum
{The root system of L}

    if not assigned L`RootSystem then
      sorR, Rvecs, fundR, C := RootSystem( L, 
        SplittingCartanSubalgebra( L ) );
      L`RootSystem := [* sorR, Rvecs, fundR, C *];
    end if;
    
    lst := L`RootSystem;
    return lst[1], lst[2], lst[3], lst[4];
end intrinsic;
