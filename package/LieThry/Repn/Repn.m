freeze;

// ====================================================
//
// $Id: Repn.m 50035 2015-03-26 03:12:31Z don $
//
//      Scott H Murray
//
//      17 April 1999
//
// ====================================================
import "../Root/Cartan.m" : typeToCartan;
import "../Root/Const.m" : maxMultiplicity;
import "../Root/RootDtm.m" : toType;
import "../GrpLie/GrpLie.m" : copyelt;
import "RowRed.m" : WeightBase, rowReduction, actionsOfWeylReflections;
import "../../Algebra/AlgMat/General/diag.m" : commonEigenspaces;

forward grpRepn, inverseops, rightActionOps, rightActionOpsfunc, 
  leftActionOps, leftinverseops;

// We save the Basis intrinsic because Basis is used as a parameter
basis := Basis;

// ====================================================
//
// Basic functionality for maps
//
// ====================================================

// NB: remove finite field condition for repns once algebraic 
// mx grps are defined.
intrinsic Image( f::Map[GrpLie,Grp] ) -> Grp
{The image of f}
  require ISA( Category( BaseRing( Domain(f) ) ), FldFin ) :
    "Image is not representable";
  require (assigned f`IsHomomorphism and f`IsHomomorphism) or
    (assigned f`IsProjectiveRepresentation and f`IsProjectiveRepresentation) :
    "Image is not computable";
  gl := Codomain(f);
  gens := [ f(g) : g in Generators(Domain(f)) ];
  if assigned f`IsProjectiveRepresentation and f`IsProjectiveRepresentation then 
    Append( ~gens, 
      gl!ScalarMatrix( Degree(gl), 
        PrimitiveElement(BaseRing(gl))^(f`ProjectiveKernelPower) ) );
  end if;
  return sub< gl | gens >;
end intrinsic;

// ====================================================
//
// Utility functions
//
// ====================================================

rSpace := function( G )
  if Category(G) eq GrpMat then  return RSpace(G);
  elif Category(G) in {AlgMat,AlgMatLie} then  return BaseModule(G);
  end if;
end function;

// The exponential of a nilpotent element
// Note: if a is not nilpotent, this is an infinite loop
exp := function( a )
  a := Matrix(a);
  ret := a^0+a;
  pow := a^2;
  i := 2;
  while pow ne 0 do
    pow /:= i;
    ret +:= pow;
    i +:= 1;
    pow *:= a;
  end while;
  return ret;
end function;

// The logarithm of a unipotent element
// Note: if u is not unipotent, this is an infinite loop
log := function( u )
  a := Matrix(u)-1;
  ret := a;
  pow := a^2;
  i := 2;
  while pow ne 0 do
    if IsOdd(i) then  ret +:= pow/i;
    else  ret -:= pow/i;
    end if;
    i +:= 1;
    pow *:= a;
  end while;
  return ret;
end function;

// The matrix commutator
comm := func< a, b | a*b - b*a >;


// ====================================================
//
// Root images in various representations
//
// ====================================================

// ----------------------------------------------------
//
// Highest weight representation root matrices
// Uses de Graaf code.
//
hwRtMxs := function( R, wt : Basis:="Weight" )
  L := LieAlgebra( R, Rationals() );
  pos, neg, carelts := StandardBasis( L );
  repn := HighestWeightRepresentation( L, wt : Basis:=Basis );
  T := func< x | Transpose( Matrix( x ) ) >;
  return [ -T( repn(x) ) : x in pos ],
         [ -T( repn(x) ) : x in neg ];
end function;

// ----------------------------------------------------
//
// Weight orbit root matrices
//
// X is an indexed set of positive roots or an indexed
// set of negative roots for R
//
// The matrix of ad(e_alpha) acting on the left is the
// negative of the transpose of the matrix returned here.
//// In the case of a fundamental root element acting on
// the standard module with basis arranged in the reverse
// of the standard order, the matrix is lower triangular.
//

orbitRtMx := function( R, r, X ) // was orbitRtOp
// 'ade' is a list of triples giving the position and value of the 
// non-zero entries of the matrix of ad(e_r) acting on X (on the right)}
  n := #X;
  root := Root( R, r : Basis:="Root" );
  roots := [ Root( R, s : Basis:="Root" ) : s in X ];
  ade:= [];
  for i := 1 to n do
    c := LieConstant_N( R, X[i], r );
    if c ne 0 then
      j := Position( roots, root + roots[i] );  // use Sum(R,r,s)??
      Append( ~ade, <i,j,c> );
    end if;
  end for;
//  return ade;
  return Matrix( Rationals(), n, n, ade );
end function;

/*
orbitRtMx := function( R, r, X )
  n := #X;
  return Matrix( Rationals(), n, n, orbitRtOp( R, r, X ) );
end function;
*/

// The inclusion of the given root system into one of higher rank.
// This is needed as part of the construction of the standard 
// representation.  The root used to define the representation is
// placed at the extreme left or extreme right.  This is essential
// for the code in standardRootSystemInj().

standardInjectionOfType := function( type )
  // the position to add new roots
  n := &+[ #t[2] : t in type ] + 1;
  // the correspondence of roots in the old system to those in the new one
  inc := [ [i] : i in [1..n-1] ];
  for i in [1..#type] do
    X := type[i][1];  
    rows := type[i][2];
    case X:
    when "A", "B", "C", "D":
      if X eq "D" and #rows eq 1 then
        type[i][1] := "A";
      end if;
      type[i][2] := [n] cat rows;
      n +:= 1;  
    when "E":
      if #rows ne 8 then
        type[i][2] := rows cat [n];
        n +:= 1;
      end if;
    when "F":
      type[i][1] := "E";
      type[i][2] := rows[[4,1,3,2]] cat [n+2,n+1,n];
      inc[rows[3]] cat:= [n+2]; inc[rows[4]] cat:= [n+1];
      n +:= 3;  
    when "G":
      type[i][1] := "D";
      type[i][2] := [n] cat rows cat [n+1,n+2];
      inc[rows[1]] cat:= [n+1,n+2];
      n +:= 3;  
    when "H":
      if #rows eq 3 then
        type[i][2] := rows cat [n];
        n +:= 1;
      end if;
    when "I":
      if type[i][3] eq 5 then
        type[i] := < "H", rows cat [n] >;
        n +:= 1;
      end if;
    end case;
  end for;
  return type, inc;
end function;


// ----------------------------------------------------
//
// Standard representation root matrices
//

standardRootSystemInj := function( R )

  // Construct a root datum containing R with rank one larger
  type := toType( R );
  rank := Rank( R );
  N := NumPosRoots( R );
  overType, inc := standardInjectionOfType( type );
  overRank := &+[ #t[2] : t in overType ];
  A := MatrixAlgebra( BaseRing(R), overRank)!1;
  B := Transpose( typeToCartan( overType ) );
  over := RootDatum( A, B );
  overN := NumPosRoots( over );

  // extend the inclusion inc to all roots
  pairs := ExtraspecialPairs( R );
  for r in [1..N-rank] do
    pair := pairs[r];
    inc[r+rank] := 
      IndexedSetToSequence({@ s : i in inc[pair[1]], j in inc[pair[2]] |
        s ne 0 where s is Sum(over, i,j) @});
  end for;
  for r in [N+1..2*N] do
    inc[r] := [ x + overN : x in inc[r-N] ];
  end for;

  // Make sure the extraspecial signs match
  overPairs := ExtraspecialPairs( over );
  overSigns := [];
  for i in [1..#overPairs] do
    pair := overPairs[i];
    if exists(r){ r : r in [1..N] | pair[1] in inc[r] } and 
       exists(s){ s : s in [1..N] | pair[2] in inc[s] } then
      //print pair, inc[r],inc[s];
      if LieConstant_epsilon( R, r, s ) notin {1,-1} then
        if IsExport() then 
            error "Runtime error in standardRootSystemInj: Wrong signs computed. Please report to magma-bugs@magma.maths.usyd.edu.au"; 
        else
            print R, pair, r, s;
            error "Runtime error in standardRootSystemInj: Wrong signs. FIXME";
        end if;
      end if;
      Append( ~overSigns, LieConstant_epsilon( R, r, s ) );
    else 
      Append( ~overSigns, 1 );
    end if;
  end for;
  if overSigns ne ExtraspecialSigns( over ) then
    over := RootDatum( A, B : Signs:=overSigns );
  end if;

  X := [];
  roots := PositiveRoots( over );  
  for i in [1..#type] do
    if #overType[i][2] eq #type[i][2] then // the E8, H4 or I2 case
      pos := [ s : s in [1..overN] |
          exists(r){ r : r in overType[i][2] | roots[s][r] ne 0 } ];
      X cat:= pos cat [ s+overN : s in pos ];
    else
      // take the new root
      r := Rep( Seqset(overType[i][2]) diff 
        &join{ Seqset(inc[r]) : r in type[i][2] } );
      X cat:= [ s : s in [1..overN] | roots[s][r] eq 1 ];
    end if;
  end for;
  return over, inc, X;
end function;


classicalStdRtMxs := function( X, l )
  Q := Rationals();  B := Basis( VectorSpace( Q, l ) );
  case X :
  when "A" :
    n := l+1;  V := VectorSpace( Q, n );
    M := MatrixAlgebra( Q, n );  Z := Zero(M);
    pos := [];  neg := [];
    for i in [1..l] do
      A := Z;  A[i+1,i] := 1;
      Append( ~pos, A );
      Append( ~neg, Transpose(A) );
    end for;
    wts := [ B[1] ] cat [ B[i+1]-B[i] : i in [1..l-1] ] cat [ -B[l] ];
    wvs := Basis( V );  wvs0 := [V|];
  when "B" :
    n := 2*l+1;  V := VectorSpace( Q, n );
    M := MatrixAlgebra( Q, n );  Z := Zero(M);
    pos := [];  neg := [];
    for i in [1..l-1] do
      A := Z;  A[i+1,i] := 1;  A[n-i+1,n-i] := -1;
      Append( ~pos, A );
      Append( ~neg, Transpose(A) );
    end for;
    A := Zero( M );
    A[l+1,l] := 2;  A[l+2,l+1] := -1;
    Append( ~pos, A );
    A := Zero( M );
    A[l,l+1] := 1;  A[l+1,l+2] := -2;
    Append( ~neg, A );
    wts := [ B[1] ] cat [ B[i+1]-B[i] : i in [1..l-2] ] cat 
      ((l gt 1) select [ 2*B[l]-B[l-1] ] else []);
    wts cat:= [ -wts[i] : i in [l..1 by -1] ];
    wvs := Basis( V )[ [1..l] cat [l+2..n] ];
    wvs0 := [ V.(l+1) ];
    
  when "C" :
    n := 2*l;  V := VectorSpace( Q, n );
    M := MatrixAlgebra( Rationals(), n );
    pos := [];  neg := [];
    for i in [1..l] do
      A := Zero( M );
      A[n-i+1,n-i] := -1;  A[i+1,i] := 1;  
      Append( ~pos, A );
      Append( ~neg, Transpose(A) );
    end for;
    wts := [ B[1] ] cat [ B[i+1]-B[i] : i in [1..l-1] ];
    wts cat:= [ -wts[i] : i in [l..1 by -1] ];
    wvs := Basis( V );  wvs0 := [V|];
    
  when "D" :
    n := 2*l;  V := VectorSpace( Q, n );
    M := MatrixAlgebra( Rationals(), n );
    pos := [];  neg := [];
    for i in [1..l-1] do
      A := Zero( M );
      A[i+1,i] := 1;  A[n-i+1,n-i] := -1;
      Append( ~pos, A );
      Append( ~neg, Transpose(A) );
    end for;
    A := Zero( M );
    if l gt 1 then
      A[l+1,l-1] := 1;  
      A[l+2,l] := -1;
    else
      A[l+1,l] := 1;
    end if;
    Append( ~pos, A );
    Append( ~neg, Transpose(A) );
    wts := [ B[1] ];
    if l gt 1 then
      wts cat:= [ B[i+1]-B[i] : i in [1..l-1] ];  
      wts[l-1][l] := 1;
    end if;
    wts cat:= [ -wts[i] : i in [l..1 by -1] ];
    wvs := Basis( V );  wvs0 := [V|];
    
  end case;
  return pos, neg, wts, wvs, wvs0;
end function;

stdRtMxs := function( R )
  Q := Rationals();
  sumR := R;
  sumM := MatrixAlgebra( Rationals(), 0 );
  sumWtsV := VectorSpace( Rationals(), 0 );  sumWvsV := sumWtsV;
  sumE := [ sumM| ];  sumF := [ sumM|  ];  sumWts := [ sumWtsV |  ];
  sumWvs := [ sumWvsV |  ];  sumWvs0 := [ sumWvsV | ];
  for type in toType(sumR) do
    R, suminc := sub< sumR | type[2] >;
    N := NumPosRoots(R);  rank := Rank(R);
    
    if type[1] eq "E" and #type[2] eq 8 then
      L := LieAlgebra( R, Rationals() );
      pos, neg, cart := StandardBasis( L );
      E := [ Matrix(RightAdjointMatrix( L, x )) : x in pos ];
      F := [ Matrix(RightAdjointMatrix( L, x )) : x in neg ];
      wts := Roots( R : Basis:="Weight" )[ [N..1 by -1] cat [N+1..2*N] ];
      wvsV := Module(L);
      wvs := ChangeUniverse( Reverse( pos ) cat neg, wvsV );
      wvs0 := ChangeUniverse( cart, wvsV );

    elif type[1] in "ABCD" then
      pos, neg, wts, wvs, wvs0 := classicalStdRtMxs( type[1], #type[2] );
      E := [];  F := [];
      for i in [1..rank] do
        E[i] := pos[i];  F[i] := neg[i];
      end for;
      for t in [rank+1..N] do
        r, s := ExtraspecialPair( R, t );
        c := LieConstant_N( R, r, s );
        E[t] :=  (1/c)*comm(E[r],E[s]);
        F[t] := -(1/c)*comm(F[r],F[s]);
      end for;
      wvsV := Universe( wvs );
    elif type[1] eq "E" then
      overR, inc, X := standardRootSystemInj( R );
      overN := NumPosRoots( overR );
      E := [ -Transpose(orbitRtMx( overR, t[1], X )) : t in inc[[1..N]] ];
      F := [ -Transpose(orbitRtMx( overR, t[1]+overN, X )) : t in inc[[1..N]] ];
      wtsV := VectorSpace( Q, #type[2] );
      wts := (#type[2] eq 6) select 
        [ wtsV |
 	  [ 0, 0, 0, 0, 0, 1 ],	  [ 0, 0, 0, 0, 1, -1 ],  [ 0, 0, 0, 1, -1, 0 ],  
	  [ 0, 1, 1, -1, 0, 0 ],  [ 0, -1, 1, 0, 0, 0 ],  [ 1, 1, -1, 0, 0, 0 ],
 	  [ -1, 1, 0, 0, 0, 0 ],  [ 1, -1, -1, 1, 0, 0 ], [ -1, -1, 0, 1, 0, 0 ], 
	  [ 1, 0, 0, -1, 1, 0 ],  [ -1, 0, 1, -1, 1, 0 ], [ 1, 0, 0, 0, -1, 1 ],
 	  [ 0, 0, -1, 0, 1, 0 ],  [ -1, 0, 1, 0, -1, 1 ], [ 1, 0, 0, 0, 0, -1 ],
 	  [ 0, 0, -1, 1, -1, 1 ], [ -1, 0, 1, 0, 0, -1 ], [ 0, 1, 0, -1, 0, 1 ],
 	  [ 0, 0, -1, 1, 0, -1 ], [ 0, -1, 0, 0, 0, 1 ],  [ 0, 1, 0, -1, 1, -1 ],
 	  [ 0, -1, 0, 0, 1, -1 ], [ 0, 1, 0, 0, -1, 0 ],  [ 0, -1, 0, 1, -1, 0 ],
 	  [ 0, 0, 1, -1, 0, 0 ],  [ 1, 0, -1, 0, 0, 0 ],  [ -1, 0, 0, 0, 0, 0 ] ] else 
	[ wtsV |
 	  [ 0, 0, 0, 0, 0, 0, 1 ],    [ 0, 0, 0, 0, 0, 1, -1 ],
 	  [ 0, 0, 0, 0, 1, -1, 0 ],   [ 0, 0, 0, 1, -1, 0, 0 ],
 	  [ 0, 1, 1, -1, 0, 0, 0 ],   [ 0, -1, 1, 0, 0, 0, 0 ],
 	  [ 1, 1, -1, 0, 0, 0, 0 ],   [ -1, 1, 0, 0, 0, 0, 0 ],
 	  [ 1, -1, -1, 1, 0, 0, 0 ],  [ -1, -1, 0, 1, 0, 0, 0 ],
 	  [ 1, 0, 0, -1, 1, 0, 0 ],   [ -1, 0, 1, -1, 1, 0, 0 ],
 	  [ 1, 0, 0, 0, -1, 1, 0 ],   [ 0, 0, -1, 0, 1, 0, 0 ],
 	  [ -1, 0, 1, 0, -1, 1, 0 ],  [ 1, 0, 0, 0, 0, -1, 1 ],
 	  [ 0, 0, -1, 1, -1, 1, 0 ],  [ -1, 0, 1, 0, 0, -1, 1 ],
 	  [ 1, 0, 0, 0, 0, 0, -1 ],   [ 0, 1, 0, -1, 0, 1, 0 ],
 	  [ 0, 0, -1, 1, 0, -1, 1 ],  [ -1, 0, 1, 0, 0, 0, -1 ],
 	  [ 0, -1, 0, 0, 0, 1, 0 ],   [ 0, 1, 0, -1, 1, -1, 1 ],
 	  [ 0, 0, -1, 1, 0, 0, -1 ],  [ 0, -1, 0, 0, 1, -1, 1 ],
 	  [ 0, 1, 0, 0, -1, 0, 1 ],   [ 0, 1, 0, -1, 1, 0, -1 ],
 	  [ 0, -1, 0, 1, -1, 0, 1 ],  [ 0, -1, 0, 0, 1, 0, -1 ],
 	  [ 0, 1, 0, 0, -1, 1, -1 ],  [ 0, 0, 1, -1, 0, 0, 1 ],
 	  [ 0, -1, 0, 1, -1, 1, -1 ], [ 0, 1, 0, 0, 0, -1, 0 ],
 	  [ 1, 0, -1, 0, 0, 0, 1 ],   [ 0, 0, 1, -1, 0, 1, -1 ],
 	  [ 0, -1, 0, 1, 0, -1, 0 ],  [ -1, 0, 0, 0, 0, 0, 1 ],
 	  [ 1, 0, -1, 0, 0, 1, -1 ],  [ 0, 0, 1, -1, 1, -1, 0 ],
 	  [ -1, 0, 0, 0, 0, 1, -1 ],  [ 1, 0, -1, 0, 1, -1, 0 ],
 	  [ 0, 0, 1, 0, -1, 0, 0 ],   [ -1, 0, 0, 0, 1, -1, 0 ],
 	  [ 1, 0, -1, 1, -1, 0, 0 ],  [ -1, 0, 0, 1, -1, 0, 0 ],
 	  [ 1, 1, 0, -1, 0, 0, 0 ],   [ -1, 1, 1, -1, 0, 0, 0 ],
 	  [ 1, -1, 0, 0, 0, 0, 0 ],   [ -1, -1, 1, 0, 0, 0, 0 ],
 	  [ 0, 1, -1, 0, 0, 0, 0 ],   [ 0, -1, -1, 1, 0, 0, 0 ],
 	  [ 0, 0, 0, -1, 1, 0, 0 ],   [ 0, 0, 0, 0, -1, 1, 0 ],
 	  [ 0, 0, 0, 0, 0, -1, 1 ],   [ 0, 0, 0, 0, 0, 0, -1 ] ];
      wvsV := BaseModule( Universe( E ) );
      wvs := Basis( wvsV );  wvs0 := [wvsV|];

    elif type[1] eq "F" then
      overR, inc, X := standardRootSystemInj( R );
      // This returns a root system of type E7
      LRM := [ -Transpose(orbitRtMx(overR,i,X)) : i in [1..7] ];
      EE := [ &+[ LRM[r] : r in inc[s] ] : s in [1..4] ];
      // change the basis
      P := Universe(EE)!1;
      P[13,14] := 1;
      P[14,13] := 1;  P[14,14] := -1;  P[14,15] := 1;
      P[15,14] := 1;
      Pi := P^-1;
      // remove row and column 14
      res := func< A | 
        MatrixRing(Rationals(),26)! &cat[[A[i,j] : j in I ] : i in I ] >
        where I is [1..13] cat [15..27];
      E := [ res(P*e*Pi) : e in EE ];
      F := [ res(P*Transpose(e)*Pi) : e in EE ];
      for sum in [ 5..NumPosRoots(R) ] do
        r,s := ExtraspecialPair( R, sum );
        c := LieConstant_N(R,r,s);
        E[sum] := comm(E[r],E[s]) / c;
        F[sum] := -comm(F[r],F[s]) / c;
      end for;
      wts := [ VectorSpace( Q, 4 ) | [ 0, 0, 0, 1 ], [ 0, 0, 1, -1 ],
        [ 0, 1, -1, 0 ], [ 1, -1, 1, 0 ], [ -1, 0, 1, 0 ], [ 1, 0, -1, 1 ],
        [ 1, 0, 0, -1 ], [ -1, 1, -1, 1 ],[ -1, 1, 0, -1 ],[ 0, -1, 1, 1 ],
        [ 0, -1, 2, -1 ],[ 0, 0, -1, 2 ], [ 0, 1, -2, 1 ], [ 0, 0, 1, -2 ],
        [ 1, -1, 0, 1 ], [ 0, 1, -1, -1 ],[ -1, 0, 0, 1 ], [ 1, -1, 1, -1 ],
        [ -1, 0, 1, -1 ],[ 1, 0, -1, 0 ], [ -1, 1, -1, 0 ],[ 0, -1, 1, 0 ],
        [ 0, 0, -1, 1 ], [ 0, 0, 0, -1 ] ];
      wvsV := BaseModule( Universe( E ) );
      wvs := Basis( wvsV )[ [1..12] cat [15..26] ];
      wvs0 := [ wvsV.13, wvsV.14 ];
   
    elif type[1] eq "G" then
      overR, inc, X := standardRootSystemInj( R );
      // This returns a root system of type D5.
      Reverse( ~X );
      LRM := [ -orbitRtMx(overR,i,X) : i in [1..5] ];
      EE := [ &+[ LRM[r] : r in inc[s] ] : s in [1..2] ];
      // change the basis
      P := Universe(EE)!1;
      P[4,5] := 1;
      P[5,4] := -1;
      Pi := P^-1;
      // remove row and column 5
      res := func< A | 
        MatrixRing(Rationals(),7)! &cat[[A[i,j] : j in I ] : i in I ] >
        where I is [1..4] cat [6..8];
      E := [ res(P*e*Pi) : e in EE ];
      F := [ res(P*Transpose(e)*Pi) : e in EE ];
      for sum in [ 3..NumPosRoots(R) ] do
        r,s := ExtraspecialPair( R, sum );
        c := LieConstant_N(R,r,s);
        E[sum] := comm(E[r],E[s]) / c;
        F[sum] := -comm(F[r],F[s]) / c;
      end for;
      wts := [ VectorSpace(Q,2) | [ 1, 0 ], [ -1, 1 ], [ 2, -1 ], [ 0, 0 ],
        [ -2, 1 ], [ 1, -1 ], [ -1, 0 ] ];
      wvsV := BaseModule( Universe( E ) );
      wvs := Basis( wvsV );  wvs0 := [wvsV|];
      
    else
      error "Error: This should not happen. Please email magma-bugs@maths.usyd.edu.au";

    end if;
    
    newM := Universe( E );
    newsumM := MatrixAlgebra( Rationals(), Degree(sumM)+Degree(newM) );
    newsumE := [newsumM|];  newsumF := [newsumM|];  
    newsumWtsV := VectorSpace( Rationals(), Dimension(sumWtsV)+Rank(R) ); 
    newsumWts := [ newsumWtsV | ];
    newsumWvsV := VectorSpace( Rationals(), 
      Dimension(sumWvsV)+Dimension(wvsV) );

    // extend dimension of elements from previous summands
    for i in [1..#sumE] do
      if IsDefined( sumE, i ) then
        newsumE[i] := DiagonalJoin( sumE[i], newM!0 );
        newsumF[i] := DiagonalJoin( sumF[i], newM!0 );
      end if;
    end for;
    zero := [0:i in [1..Rank(R)]];
    newsumWts := [ Vector( Eltseq(sumWts[i]) cat zero ) : i in [1..#sumWts] ];
    zero := [0:i in [1..Dimension(wvsV)]];
    newsumWvs := [ Vector( Eltseq(sumWvs[i]) cat zero ) : i in [1..#sumWts] ];
    newsumWvs0 := [ newsumWvsV | Vector( Eltseq(v) cat zero ) : v in sumWvs0 ];

    // add elements from the new summand
    for i in [1..N] do
      newsumE[suminc[i]] := DiagonalJoin( sumM!0, E[i] ); 
      newsumF[suminc[i]] := DiagonalJoin( sumM!0, F[i] );
    end for;
    zeroWt := [0:i in [1..Dimension(sumWtsV)]];
    zeroWv := [0:i in [1..Dimension(sumWvsV)]];
    for i in [1..#wts] do
      Append( ~newsumWts, Vector( zeroWt cat Eltseq(wts[i]) ) );
      Append( ~newsumWvs, Vector( zeroWv cat Eltseq(wvs[i]) ) );
    end for;
    for i in [1..#wvs0] do
      Append( ~newsumWvs0, Vector( zeroWv cat Eltseq(wvs0[i]) ) );
    end for;
    
    sumE := newsumE;  sumF := newsumF;  
    sumM := newsumM;
    sumWts := newsumWts;   sumWtsV := newsumWtsV;
    sumWvs := newsumWvs;  
    sumWvsV := newsumWvsV; sumWvs0 := newsumWvs0;

  end for;

  wts := [ BasisChange(sumR,v:InBasis:="Weight") : v in sumWts ];
  wvs := [ PowerStructure(ModTupFld) | sub< sumWvsV | v > : v in sumWvs ];

  if #sumWvs0 ne 0 then
    Append( ~wts, Universe(wts)!0 );
    Append( ~wvs, sub<sumWvsV | sumWvs0 > );
  end if;

  return sumE, sumF, wts, wvs;
end function;


// ====================================================
//
// Constructing the Lie algebra homomorphism
// from the root matrices
//
// ====================================================


myChevBasis := function( L )
  R := RootDatum( L );
  pos, neg := StandardBasis( L );
  cart := [ pos[i]*neg[i] : i in [1..Rank(R)] ];
  return pos,neg,cart;
end function;

lieAlgHom := function( L, M, ims : Check:= true )
  dimL := Dimension( L );
  f := func< x | &+[ M!( x[i]*ims[i] ) : i in [1..dimL] ] >;
  if Check then
    if not forall(t){ <i,j> : j in [i+1..dimL], i in [1..dimL] | 
      f(L.i*L.j) eq f(L.i)*f(L.j) } then
      error "Error:  The given matrices do not define a representation", t;
    end if;
  end if;
  return hom< L -> M | x:->f(x) >;
end function;

stdBasisIms := function( L, pos, neg, cart : chev := true )
  k := BaseRing( L );  d := Dimension( L );
  V := VectorSpace( k, d );
  
  if chev then
    posL, negL, cartL := myChevBasis( L );
  else 
    posL, negL, cartL := StandardBasis( L );
  end if;
  B := posL cat negL cat cartL;
  ims := pos cat neg cat cart;
  VB := VectorSpaceWithBasis( [ Vector(b) : b in B ] );
  
  return  [ &+[ u[i]*ims[i] : i in [1..d] | u[i] ne 0 ] 
    where u is Coordinates( VB, VB!V.j ) : j in [1..d] ];
end function;

// images of all roots
nonsimpleRootMxs := procedure( R, ~pos, ~neg )
  n := Rank( R );  N := NumPosRoots( R );

  for t in [Min(#pos,#neg)+1..N] do
    r, s := ExtraspecialPair( R, t );
    c := LieConstant_N( R, r, s );
    pos[t] :=  pos[r]*pos[s]/c;
    neg[t] := -neg[r]*neg[s]/c;
  end for;

end procedure;

lieAlgRepn := function( L, ML, pos, neg : cart:= false, Check:=true )
  R := RootDatum( L );
  d := Dimension( R ); n := Rank( R );  N := NumPosRoots( R );

  nonsimpleRootMxs( R, ~pos, ~neg );
  
  // images of Cartan elements
  if Category( cart ) eq BoolElt then
    cart := [ pos[i]*neg[i] : i in [1..n] ];
    if d gt n then
      cart cat:= [ ML!0 : i in [n+1..d] ];
    end if;
    ims := stdBasisIms( L, pos, neg, cart );
  else
    ims := stdBasisIms( L, pos, neg, cart : chev:=false );
  end if;

  return lieAlgHom( L, ML, ims : Check:=Check );
end function;

intrinsic Representation( L::AlgLie, pos::[AlgMatLieElt], neg::[AlgMatLieElt] :
  cart:=false, Check:=true ) -> Map
{The representation of the reductive L with the given images of the positive 
and negative simple root elements}

  // check inputs
  require IsReductive( L ) : "The Lie algebra is not reductive";
  R := RootDatum( L );
  d := Dimension( R ); n := Rank( R );  N := NumPosRoots( R );
  require #pos ge n and #pos le N and #neg ge n and #neg le N : 
    "Wrong number of matrices";
  dim := Degree( Universe( pos ) );  k := BaseRing( L );
  ML := MatrixLieAlgebra( k, dim );
  ok, pos := CanChangeUniverse( pos, ML );
  require ok : "Positive root matrices of incorrect type";
  ok, neg := CanChangeUniverse( neg, ML );
  require ok : "Negative root matrices of incorrect type";
  if Category( cart ) ne BoolElt then
    require #cart eq d : "Wrong number of Cartan subalgebra matrices";
    ok, cart := CanChangeUniverse( cart, ML );
    require ok : "Cartan subalgebra matrices of incorrect type";
  end if;
  
  return lieAlgRepn( L, ML, pos, neg : cart:=cart, Check:=Check );
end intrinsic;

intrinsic Representation( L::AlgLie, pos::[AlgMatElt], neg::[AlgMatElt] :
  cart:=false, Check:=true ) -> Map
{The representation of the reductive L with the given images of the positive 
and negative simple root elements}

  // check inputs
  require IsReductive( L ) : "The Lie algebra is not reductive";
  R := RootDatum( L );
  d := Dimension( R ); n := Rank( R );  N := NumPosRoots( R );
  require #pos ge n and #pos le N and #neg ge n and #neg le N : 
    "Wrong number of matrices";
  dim := Degree( Universe( pos ) );  k := BaseRing( L );
  ML := MatrixLieAlgebra( k, dim );
  ok, pos := CanChangeUniverse( pos, ML );
  require ok : "Positive root matrices of incorrect type";
  ok, neg := CanChangeUniverse( neg, ML );
  require ok : "Negative root matrices of incorrect type";
  if Category( cart ) ne BoolElt then
    ok, cart := CanChangeUniverse( cart, ML );
    require ok : "Cartan subalgebra matrices of incorrect type";
  end if;
  
  return lieAlgRepn( L, ML, pos, neg : cart:=cart, Check:=Check );
end intrinsic;

intrinsic TrivialRepresentation( L::AlgLie ) -> Map
{The trivial representation of L}
  M := MatrixLieAlgebra( BaseRing(L), 1 );
  return hom< L -> M | x :-> M!0 >;
end intrinsic;

intrinsic StandardRepresentation( L::AlgLie : NoCharacteristicError := false, ComputePreImage := true ) -> 
  Map
{The standard representation of L}
  require IsSemisimple( L ) : "The Lie algebra is not semisimple";
  if assigned L`StandardRepresentation then
	if not HasPreimageFunction(L`StandardRepresentation) and ComputePreImage then 
		ComputePreImageRule(L`StandardRepresentation); 
	end if;
  else
    R := RootDatum( L );  k := BaseRing( L );
    type := toType(R);
    if IsIrreducible(R) and type[1][1] eq "E" and #(type[1][2]) eq 8 then
      L`StandardRepresentation := AdjointRepresentation( L : ComputePreImage := ComputePreImage);
    else
      LQ := LieAlgebra( R, Rationals() );
      pos, neg, wts, wvs := stdRtMxs( R );
      cart := [ comm(pos[i],neg[i]) : i in [1..Rank(R)] ];
      ims := stdBasisIms( LQ, pos, neg, cart );
      ML := MatrixLieAlgebra(k, Degree(Universe(ims)));
      ok, ims := CanChangeUniverse( ims, ML );
      if NoCharacteristicError and not ok then  return false;  end if;
      require ok : 
        "Cannot compute the standard representation in characteristic ",
        Characteristic(k);
      rep := lieAlgHom( L, ML, ims : Check:=false );
      rep`IsInjective := true;
      rep`Weights := wts;  rep`WeightSpaces := [ ChangeRing( wv, BaseRing(L) ) : wv in wvs ];
      if Characteristic(k) eq 0 then
        rep`HighestWeights := [wts[1]];  
	rep`HighestWeightSpaces := [(rep`WeightSpaces)[1]];
      end if;
      if ComputePreImage then ComputePreImageRule(rep); end if;
      L`StandardRepresentation := rep;
    end if;
  end if;
  return L`StandardRepresentation;
end intrinsic;

LieAlgBaseSpace := func< L | VectorSpace( Rationals(), Dimension(L) ) >;
Eltvect := func< x | LieAlgBaseSpace(Parent(x)) ! Eltseq(x) >;
LieAlgBasisMx := function( V, B, x )
  return Matrix( [ Coordinates(V, Eltvect(b*x)) : b in B ] );
end function;

intrinsic Inverse( rho::Map[AlgLie,AlgMatLie] ) -> Map
{The inverse of rho}
  L := Domain( rho );  M := Codomain( rho );
  dL := Dimension( L );  dM := Degree( M );
  k := BaseRing( L );  
  VL := VectorSpace( k, dL );
  VM := RMatrixSpace( k, dM, dM ); 
  phi := hom< VL -> VM | [ rho( b ) : b in Basis(L) ] >;
  require Dimension( phi(VL) ) eq dL : "Not an invertible map";
  inv := Inverse( phi );
  return hom< M -> L | x :-> L!inv(VM!x) >;
end intrinsic;



// ====================================================
//
// Constructing the homomorphism from the root matrices
//
// ====================================================

kummerExtension := function( k, r )
  if Category( k ) eq FldFin then
    m := #k - 1;  primes := PrimeDivisors( m );
    d := &*[ Integers() | c[1]^c[2] : c in Factorisation( r ) | c[1] in primes ];  
    e := (m eq 1) select 1 else Integers()!( (ResidueClassRing(m)!(r div d))^-1 );
    K := ext<k | d>;
    b := PrimitiveElement( k );  
    if d eq 1 then
      f := func< x | x^e >;
    else 
      br := Roots( P.1^d - b )[1][1] where P is PolynomialRing(K);
      f := func< x | (x eq 0) select 0 else br^Log( b, x^e ) >;
    end if;
    return K, f;
  elif Category( k ) in [FldRe,FldCom] then
    if Category(k) eq FldCom or (Category(k) eq FldRe and IsOdd(r)) then
      K := k;
    else
      K := ComplexField(k);
    end if;
    return K, func< x | Root( K!x, r ) >;
  elif Category( k ) eq FldRat then
    K := AlgebraicClosure();
    f := func< x | Root( K!x , r ) >;
    return K, f;  
  elif ISA( Category(k), FldNum ) or Category(k) eq FldAb then
    k := (Category(k) eq FldAb) select NumberField(k) else SimpleExtension( k );
    P := PolynomialRing( Rationals() );
    K := AlgebraicClosure();
    z := Roots( MinimalPolynomial(k.1), K )[1][1];
    f := func< x | Root( Evaluate( P!Eltseq(k!x), z ), r ) >;
    return K, f;
  else
    error "Cannot compute the Kummer extension of the given ring";
  end if;
end function;

/*
This function is used by extendTorus below.

It returns a list of possible vectors (t1, .., tn) such that mapping
the i-th torus element (i.e., elt<G | Vector([1,1,..,1,v,1,...,1])>, 
where the v is at the i-th coordinate) to diag(v^t_1, ... v^t_n)
is a good idea.

That is: the action on the simple root matrices is as it should be.
For example, if (111v11) x_r(1) = x_r(a) (111v11) then mapping 
(111v11) to diag(....) should be consistent with the image of x_r(1)
and x_r(a).

[Only tested and used for i > Rank(R), but I see no reason why it 
wouldn't work for the other cases as well]
*/
possibleTorusImageForCoroot := function(R, d, rtMxs, i)

	SR := Matrix(SimpleRoots(R));
	BB := Matrix(Basis(CorootSpace(R)));
	tmat := -SR*BB;
	
	/* tmat describes the action of the torus vectors on the roots
	   e.g. if the j-th row is (2 -1 0 0) then 
	   (v1 v2 v3 v4) x_j(a) = x_j(a v_1^2/v_2) (v1 v2 v3 v4).
	
	   See also TorusActionOnUnip in GrpLie.m.
	*/
	
	rnkR := Rank(R);
	V := RSpace(Integers(), d);

	actonrt := [ Integers() | tmat[r][i] : r in [1..rnkR] ];;
	
	//(111v11) x_j(a) should equal x_j(a*...) (111v11)
	//  under rho (where the precise form of the factor in x_j() is determined 
	//  by tmat or actonrt).
	//Under the image of the representation rho being formed, we collect the
	//  contributions of rho((111v11)) in lhsmat, and the contributions in
	//  a*... in rhsmat.
	lhsmat := ZeroMatrix(Integers(), 0, d);
	rhsmat := ZeroMatrix(Integers(), 0, 1);
	for r in [1..rnkR] do
		//nz contains the positions of the nonzero off-diagonal entries of root r...
		nz := [<i,j> : i,j in [1..d] | (rtMxs[r][i][j] ne 0) and (i ne j) ];
		for n in nz do
			//(111v11) has a rowwise contribution on the lhs, 
			//and a columnwise contribution on the rhs
			lhsmat := VerticalJoin(lhsmat, V.n[1] - V.n[2]);
			//contribution due to multiplication
			rhsmat := VerticalJoin(rhsmat, Vector([actonrt[r]]));
		end for;
	end for;
	cons, v, ns := IsConsistent(Transpose(lhsmat),Transpose(rhsmat));

	if not cons then
		return [V|];
	elif IsZero(v) then
		return [ n : n in Basis(ns) ];
	else
		return [ Vector(v) ] cat [ Vector(v) + n : n in Basis(ns) ];
	end if;

end function;
      

// Can the abelian group with invariants a be included in the group with
// invariants b?
invInc := function( a, b )
  i := 1;  j := 1;
  while i le #a and j le #b do
    if (a[i] eq 0 and b[j] eq 0) or (a[i] ne 0 and IsDivisibleBy( b[j], a[i] )) then
      i +:= 1; j +:= 1;
    else
      j +:= 1;
    end if;
  end while;
  return i gt #a;
end function;

extendTorus := function( R, carMxs, rtMxs, k : NoWarning:=false )
  Z := Integers();
  d := Dimension( R );  n := Rank( R );
  B := ChangeRing( SimpleCoroots( R ), Z );
  
  if n eq 0 then
    return IdentityMatrix(Z,d), rtMxs, k, func< x | x >, false, 1;
  end if;
  
  e := Degree( Universe( carMxs ) );
  D := Matrix( Z, n, e, [ carMxs[i][j,j] : j in [1..e], i in [1..n] ] );

  m := (Category(k) eq FldFin) select #k-1 else 0;
  modm := func< a | (m eq 0) select a else [ i mod m : i in a ] >;
  Zm := (m eq 0) select Integers() else ResidueClassRing(m);
  a := Invariants( StandardLattice(d)/Lattice(B) );  
  b := Invariants( StandardLattice(e)/Lattice(D) );
  a := modm(a);  b := modm(b);
  if not invInc( a, b ) then
    olde := e;
    repeat
    	e +:= 1;  b cat:= [0];
	error if e - olde gt 1000, "Infinite loop detected in extendTorus?";
    until invInc( a, b );
    zero := ZeroMatrix(CoefficientRing(Universe(carMxs)), e-olde, e-olde);
    carMxs := [ DiagonalJoin( A, zero ) : A in carMxs ];
    rtMxs  := [ DiagonalJoin( A, zero ) : A in rtMxs ];
    D := HorizontalJoin( D, Matrix(Z,n,e-olde,[0:i in [1..n*(e-olde)]]) );
  end if;
  B, E := EchelonForm(B);  D := E*D;
  if n lt d then

	nonpivots := function( A )
		A := EchelonForm( A );
		np := [1..Ncols(A)];
		for i in [1..Nrows(A)] do
			_ := exists(j){ j : j in [1..Ncols(A)] | A[i,j] ne 0 };
			Exclude( ~np, j );
		end for;
		return np;
	end function;
	
	npB := nonpivots(B);
	assert #npB eq d-n;

	for i in npB do
		rwspc := RowSpace(D);
		cands := possibleTorusImageForCoroot(R, e, rtMxs, i);
		cands := [ v : v in cands | v notin rwspc ];
		if #cands eq 0 then
			error Sprintf("extendTorus: Problem finding image of coroot %o", i);
		end if;
		
		//Just take the first candidate
		v := cands[1];
		D := VerticalJoin(D, v);
		B := VerticalJoin(B, Vector([Integers() | i eq j select 1 else 0 : j in [1..d]]));
	end for;

  end if;
  isproj := false;  // default value
  isinv, Binv := IsInvertible( ChangeRing( B, Zm ) );
  if m ne 1 and isinv then   // m eq 1 iff k=GF(2), so PGL=GL
    r := 1;
    Binv := ChangeRing( Binv, Integers() );
    K := k;  rad := func< x | x >;
  else
     r := Determinant( B );
     B := ChangeRing( B, Rationals() );
     Binv := ChangeRing( r * B^-1, Integers() );
     K, rad := kummerExtension( k, r );
     if r ne 1 then  // r eq 1 can only happen when m eq 1
       isproj := true;
       if not NoWarning then print "Warning: Projective representation"; end if;
     end if;
//     ishom := false;
  end if;
  return Binv*D, rtMxs, K, rad, isproj, r;
end function;

/*grpRepn_mult := function( G, pos, neg : NoWarning:=false )
  R := RootDatum( G );  N := NumPosRoots( R );
  k := BaseRing( G );
  
  // convert to associative mxs
  pos := [ Matrix(x) : x in pos ];  neg := [ Matrix(x) : x in neg ];

  rtMxs := pos cat neg;
  F := Universe( rtMxs );
  K := PolynomialRing( F ); x := K.1;
  carMxs := [ comm(neg[i],pos[i]) : i in [1..Rank(R)] ];
  D, rtMxs, K, rad, isproj := extendTorus( R, carMxs, rtMxs, k : NoWarning:=NoWarning );
  //time 
  expMxs := [ exp( x * R ) : R in rtMxs ];
// expMxs; 

  d := Nrows( pos[1] );
  M := MatrixRing( K, d );  I := M!1;
  ChangeUniverse( ~expMxs, PolynomialRing(M) );
  dim := Dimension( R );
  neg := func< r | (r le N) select r+N else r-N >;

  x := func< r, t | Evaluate( expMxs[r], t*I ) >;
  n := func< r, t | x(r,t) * x(neg(r),-t^(-1)) * x(r,t) >;
  sdot := func< r | n(r,1) >;
  h := func< i, t | DiagonalMatrix( M, [ rad(t)^D[i,j] : j in [1..d] ] ) >;
  
  multByUnipTerm := procedure( ~el, term )
// el; "\n";
// expMxs[term[1]]; "\n";
// x(term[1], term[2]); "\n";
// Parent(term[2]); 
    el := el * x( term[1], term[2] );
// el; "\n"; 
  end procedure;
  multByUnip := procedure( ~el, unip )
    if ISA( Category( Universe(unip) ), Rng ) then
      for r in [1..#unip] do
        el := el * x(r, unip[r]);
      end for;
    else
      for term in unip do
        multByUnipTerm( ~el, term );
      end for;
    end if;
  end procedure;
  multByTorus := procedure( ~el, t )
    for i in [1..dim] do
      el := el * h(i,t[i]);
    end for;
  end procedure;
  multByWeyl := procedure( ~el, w )
    for r in w do
      el := el * n(r);
    end for;
  end procedure;

  f := function( el )
    el := copyelt( el );
    Unnormalise( ~el );
    list := el`List;
    ret := MatrixRing( k, d )!1;
    for term in list do
      if Category(term) eq ModTupFldElt then
        multByTorus( ~ret, term );
      elif Category(term) eq Tup and #term eq 2 then
        multByUnipTerm( ~ret, term );
      elif Category(term) eq SeqEnum then
        multByUnip( ~ret, term );
      elif Category(term) eq RngIntElt then
        ret := ret * sdot(term);
      elif Category(term) eq GrpLieElt then
        multByUnip( ~ret, term`u );
        multByTorus( ~ret, term`h );
        multByWeyl( ~ret, term`w );
        multByUnip( ~ret, term`up );
      else
        error "Error: Entry in list not allowed";
      end if;
    end for;
    return ret;
  end function;

  return (isproj) select hom< G -> GL(d,K) | x :-> f(x) >  
                    else map< G -> GL(d,K) | x :-> f(x) >;
end function;
*/

checkRepnInput := function( G, pos, neg, Check )
  R := RootDatum( G );
  d := Dimension( R ); n := Rank( R );  N := NumPosRoots( R );
  if not ( #pos ge n and #pos le N and #neg ge n and #neg le N ) then 
    return false, "Wrong number of matrices", _;
  end if;
  dim := Degree( Universe( pos ) );  k := BaseRing( G );
  Q := Rationals();  ML := MatrixLieAlgebra( Q, dim );
  ok1, pos := CanChangeUniverse( pos, ML );
  ok2, neg := CanChangeUniverse( neg, ML );
  if not ok1 then
    return false, "Positive root matrices of incorrect type",_;
  elif not ok2 then
    return false, "Negative root matrices of incorrect type",_;
  end if;
  // We actually check the Lie algebra repn
  if Check then
    _ := lieAlgRepn( LieAlgebra(G), MatrixLieAlgebra( k, dim ), 
      pos, neg : cart:=false, Check:=Check );
  end if;
  return true, pos, neg;
end function;


intrinsic Representation( G::GrpLie, pos::[AlgMatLieElt], neg::[AlgMatLieElt] :
  Check:=true, NoWarning:=false ) -> Map
{The representation of G with the given images of the positive and negative
simple root elements in the Lie algebra}
  ok, pos, neg := checkRepnInput( G, pos, neg, Check );
  require ok : pos;
  nonsimpleRootMxs( RootDatum(G), ~pos, ~neg );
  return grpRepn( G, pos, neg : NoWarning:=NoWarning );
end intrinsic;

intrinsic Representation( G::GrpLie, pos::[AlgMatElt], neg::[AlgMatElt] :
  Check:=true, NoWarning:=false ) -> Map
{The representation of G with the given images of the positive and negative
simple root elements in the Lie algebra}
  ok, pos, neg := checkRepnInput( G, pos, neg, Check );
  require ok : pos;
  nonsimpleRootMxs( RootDatum(G), ~pos, ~neg );
  return grpRepn( G, pos, neg : NoWarning:=NoWarning );
end intrinsic;

intrinsic TrivialRepresentation( G::GrpLie ) -> Map
{The standard representation of G}
  H := GL(1,BaseRing(G));
  return hom< G -> H | x :-> H!1 >;
end intrinsic;


intrinsic StandardRepresentation( G::GrpLie : NoWarning:=false ) -> Map
{The standard representation of G}
  if not assigned G`StandardRepresentation then
    pos, neg, wts, wvs := stdRtMxs( RootDatum( G ) );
    rep := grpRepn( G, pos, neg : NoWarning:=NoWarning );
    rep`IsInjective := true;
    rep`Weights := wts;  
    rep`WeightSpaces := [ ChangeRing( wv, BaseRing(G) ) : wv in wvs ];
    if Characteristic( BaseRing( G ) ) eq 0 then
      rep`HighestWeights := [wts[1]];  
      rep`HighestWeightSpaces := [(rep`WeightSpaces)[1]];
    end if;
    G`StandardRepresentation := rep;
  end if;
  return G`StandardRepresentation;
end intrinsic;



myChangeRing := function( L, k )  // SHOULD NOT BE NECESSARY
  newL := ChangeRing( L, k );
  if assigned L`RootDatum then
    newL`RootDatum := L`RootDatum;
  end if;
  if assigned L`ChevalleyBasis then
    C := L`ChevalleyBasis;
    newL`ChevalleyBasis := [* [ newL | Vector(x) : x in c ] : c in C *];
  end if;
  return newL;
end function;


intrinsic AdjointRepresentation( G::GrpLie : NoWarning:=false ) -> Map, AlgLie
{The adjoint representation of G}
  if not assigned G`AdjointRepresentation then
    L := LieAlgebra( RootDatum(G), Rationals() );
    pos, neg := ChevalleyBasis( L );
    pos := [ RightAdjointMatrix( L, x ) : x in pos ];
    neg := [ RightAdjointMatrix( L, x ) : x in neg ];
    G`LieAlgebra := L;
    ad := grpRepn( G, pos, neg : NoWarning:=NoWarning );
    ad`IsInjective := true;
    V := Module( L );  R := RootDatum( G );  N := NumPosRoots( R );
    ad`Weights := [ Root( R, r ) : r in [N..1 by -1] ] cat 
      [ RootSpace( R )!0 ] cat 
      [ Root( R, r ) : r in [N+1..2*N] ];
    pos, neg, cart := StandardBasis( L );
    ad`WeightSpaces := [ sub< V | pos[r] > : r in [N..1 by -1] ] cat
      [ sub< V | [ V!c : c in cart ] > ] cat 
      [ sub< V | neg[r] > : r in [1..N] ];
    if Characteristic( BaseRing(G) ) eq 0 then
      ad`HighestWeights := [ (ad`Weights)[1] ];
      ad`HighestWeightSpaces := [ (ad`WeightSpaces)[1] ];
    end if;
    G`AdjointRepresentation := ad;
  end if;
  return G`AdjointRepresentation, myChangeRing( G`LieAlgebra, BaseRing(G) );
end intrinsic;

intrinsic HighestWeightRepresentation( G::GrpLie, wt :
  Basis:= "Weight", NoWarning:=false ) -> Map
{The highest weight representation of G with highest weight wt}
  if forall{ a : a in Eltseq(wt) | a eq 0 } then
    Gl := GL( 1, BaseRing(G) );
    return hom< G -> Gl | x :-> 1 >;
  end if;
  pos, neg := hwRtMxs( RootDatum( G ), wt );
  return grpRepn( G, pos, neg : NoWarning:=NoWarning );
end intrinsic;


// ====================================================
//
// Weights and weight vectors
//
// ====================================================

// These functions only work for algebraic representations.
// There is no way to check this, so it is assumed.

// ----------------------------------------------------
//
// Utility functions
//

// Are the vectors u and v parallel?
// Note that every vector is parallel to 0.
isPara := function( u, v )
  if exists(i){ i : i in [1..OverDimension(u)] | u[i] ne 0 } then
    return v[i]*u eq u[i]*v;
  else  // u eq 0
    return true;
  end if;
end function;

// A nonzero element b of k.
// If possible, we return an element of maximal multiplicative order.
// The second return value computes base b logarithms, the third
// return value indicates if the order of b is infinite.
nonzeroElt := function( k : deg:=1 )
  if Category(k) eq FldFin then
    b := PrimitiveElement( k );  q := #k;
    inf := false;
  elif Characteristic(k) eq 0 then
    b := 2;  inf := true;
  elif Category(k) eq FldFunRat then
    b := k.1;  inf := true;
  else
    error "Error: Unable to compute weights over this field";
  end if;

  log := function( c )
    if Category(k) eq FldFin then
      return Log( b, k!c );
    elif Characteristic(k) eq 0 then
      return Floor(Log(2, Rationals()!c));
    elif Category(k) eq FldFunRat then
      if Rank(k) eq 1 then
        return Degree(Numerator(c)) - Degree(Denominator(c));
      else
        return Degree(Numerator(c),1) - Degree(Denominator(c),1);
      end if;
    end if;    
  end function;

  return b, log, inf;
end function;


// ----------------------------------------------------
//
// Highest weight space
//
//
// The subspace fixed by the standard nilpotent 
// subalgebra (standard unipotent subgroup) of a
// reductive Lie algebra (algebraic group).
//

intrinsic HighestWeightSpace( rho::Map[AlgLie,AlgMatLie] ) -> ModTupRng
{The space of highest weight vectors of rho}
  if not assigned rho`HighestWeightSpaces then
    L := Domain( rho );  M := Codomain( rho );
    k := BaseRing( L );  K := BaseRing( M );
    d := Degree( M );
    require ISA( Category(k), Fld ) : "The base ring must be a field";
    require IsReductive( L ) : "The Lie algebra must be reductive";
    l := SemisimpleRank( L );

    pos := StandardBasis(L);
    xs := [ M | rho( u ) : u in pos ];
    U := VectorSpace( K, d );
    i := 1;
    while i le #xs and Dimension(U) gt 1 do
       U meet:= Nullspace( xs[i] );  i +:= 1;
    end while;
    rho`HighestWeightSpaces := [ U ];
  end if;
  wvs := rho`HighestWeightSpaces;  V := BaseModule( Codomain(rho) );
  U := wvs[1];  for i in [2..#wvs] do  U := sub<V|U,wvs[i]>;  end for;
  return U;
end intrinsic;

intrinsic HighestWeightVectors( rho::Map[AlgLie,AlgMatLie] ) -> ModTupRng
{The basis of highest weight vectors of rho}
  M := Codomain( rho );
  return ChangeUniverse( Basis( HighestWeightSpace( rho ) ),
    VectorSpace(BaseRing(M), Degree(M)) );
end intrinsic;

intrinsic HighestWeightSpace( rho::Map[GrpLie,GrpMat] ) -> ModTupRng
{The space of highest weight vectors of rho}
  if not assigned rho`HighestWeightSpaces then
    G := Domain( rho );  M := Codomain( rho );
    k := BaseRing( G );  K := BaseRing( M );
    d := Degree( Codomain( rho ) );
    l := SemisimpleRank( G );
    require ISA( Category(k), Fld ) : "The base ring must be a field";

    xs := [ M | rho( elt<G|<r,b>> ) : r in [1..l], b in Basis(k) ];
    U := VectorSpace( K, d );
    i := 1;
    while i le #xs and Dimension(U) gt 1 do
       U meet:= Eigenspace( xs[i], K!1 );  i +:= 1;
    end while;
    rho`HighestWeightSpaces := [ U ];
  end if;

  wvs := rho`HighestWeightSpaces;  V := rSpace( Codomain(rho) );
  U := wvs[1];  for i in [2..#wvs] do  U := sub<V|U,wvs[i]>;  end for;
  return U;
end intrinsic;

intrinsic HighestWeightVectors( rho::Map[GrpLie,GrpMat] ) -> ModTupRng
{The basis of highest weight vectors of rho}
  M := Codomain( rho );
  return ChangeUniverse( Basis( HighestWeightSpace( rho ) ),
    VectorSpace(BaseRing(M), Degree(M)) );
end intrinsic;

// ----------------------------------------------------
//
// Highest weights
//
//
// First we decompose the hw space by eigenvalues wrt
// the Cartan subalgebra (maxl torus).
// If the field has an element of infinite order or 
// none of the weight coefficients are 0, then we are done.
// Otherwise we use the meataxe to complete the 
// decomposition, then compute the correct weight 
// coefficients from module dimensions.
//

intrinsic HighestWeights( rho::Map[AlgLie,AlgMatLie] : Basis:="Standard") -> 
  [], []
{The highest weights of rho}
  L := Domain( rho );  A := Codomain( rho );
  R := RootDatum( L );  
  if not assigned rho`HighestWeights then
    A := Codomain( rho );    
    V := BaseModule( A );  k := BaseRing( L );
    d := Dimension( V );
    l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );

    // compute eigenspaces
    hws := HighestWeightSpace( rho );
    if Characteristic(k) eq 0 then
      b, log, inf := nonzeroElt( k );
      pos,neg,cart := StandardBasis( L );
      M := Codomain( rho );
      M := MatrixAlgebra( BaseRing(M), Degree(M) );  
      wvs, wts := commonEigenspaces( 
        [ M | rho( cart[i] ) : i in [1..#cart] ] : U := hws );
    else
      M := Module( rho );
      summ := IndecomposableSummands( M );
      wvs := [ hws meet sub< V | [V!M!b:b in basis(N)] > : N in summ ];
      require forall{ i : i in [1..#summ] | 
        Dimension(wvs[i]) eq 1 and sub<M|M!(wvs[i].1)> eq summ[i] } :
	"Not a highest weight module";
      _,neg := StandardBasis( L );
      wts := [ [] : wv in wvs ];
      for r in [1..l] do
        Mr := SubalgebraModule( sub< L | neg[r] >, M ); 
	for i in [1..#wvs] do
	  wts[i][r] := Dimension( sub< Mr | Mr!(wvs[i].1) > ) - 1;
	end for;
      end for;
      wts :=  [ BasisChange( R, wt : InBasis:="Weight" ) : wt in wts ];
    end if;

    rho`HighestWeights := wts;  rho`HighestWeightSpaces := wvs;
  end if;
  
  wts := rho`HighestWeights;
  return [ BasisChange( R, wt : OutBasis:=Basis ) : wt in wts ], 
    rho`HighestWeightSpaces;
end intrinsic;


// This only works for simply connected spaces -- in other cases we must
// work wrt the standard basis
intrinsic HighestWeights( rho::Map[GrpLie,GrpMat] : Basis:="Standard" ) ->
  [], []
{The highest weights of rho}
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );
  R := RootDatum( G );  
  if not assigned rho`HighestWeights then
    k := BaseRing( G );  K := BaseRing( Gl );
    deg := Degree( K, k );
    d := Dimension( V );
    l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );

    // compute eigenspaces
    hws := HighestWeightSpace( rho );
    b, log, inf := nonzeroElt( k );
    M := MatrixAlgebra( K, d );  
    wvs, wts := commonEigenspaces( 
      [ M | rho( elt<G|Vector([k| (i eq r) select b else 1 : i in [1..n]])> ) : 
        r in [1..l] ] : U := hws );
    wts := [ [ log(c^deg)/deg : c in wt ] : wt in wts ];     

    // correct weights with coefficient 0
    if not inf then
      q := #k;
      for r in [1..l] do
        wtinds := [ i : i in [1..#wts] | wts[i][r] eq 0 ];
        if not IsEmpty( wtinds ) then
          xs := [rho(elt<G|<r,b>>) : b in basis(k)]
                cat [rho(elt<G|<N+r,b>>) : b in basis(k)];
          M := GModule( sub< Gl | xs > );
          splitinds := [];  newwvs := [**];  newwts := [];
          for i in wtinds do
            U, h := sub< M | basis( wvs[i] ) >;
            Us := IndecomposableSummands( U );
            if exists{ T : T in Us | Dimension(T) eq q } then
              Uq := &+[ U : U in Us | Dimension(U) eq q ];
              Append( ~splitinds, i );
              wt := wts[i];  wt[r] := q-1;
              Append( ~newwvs, hws meet sub< V | [ V | h(b) : b in basis(Uq) ] > );
              Append( ~newwts, wt );
              if exists{ T : T in Us | Dimension(T) eq 1 } then
                U1 := &+[ U : U in Us | Dimension(U) eq 1 ];
                Append( ~newwvs, hws meet sub< V | [ V | h(b) : b in basis(U1) ] > );
                Append( ~newwts, wts[i] );
              end if;
            end if;
          end for;
          wvs := [* wvs[i] : i in [1..#wvs] | i notin splitinds *];
          for i in [1..#newwvs] do  Append( ~wvs, newwvs[i] );  end for;
          wts := [ wts[i] : i in [1..#wts] | i notin splitinds ] cat newwts;
        end if;
      end for;
    end if;
    rho`HighestWeights := wts;  rho`HighestWeightSpaces := wvs;
  end if;
  
  wts := rho`HighestWeights;
  return [ BasisChange( R, wt : InBasis:="Standard", OutBasis:=Basis ) : wt in wts ],
    rho`HighestWeightSpaces;
end intrinsic;

// ----------------------------------------------------
// 
// Decomposing via the highest weights
//

intrinsic DirectSum( rho1::Map[GrpLie,GrpMat], rho2::Map[GrpLie,GrpMat] ) 
  -> Map[GrpLie,GrpMat]
{The direct sum of rho1 and rho2}
  G := CoveringStructure( Domain(rho1), Domain(rho2) );
  k := CoveringStructure( BaseRing(Codomain(rho1)), BaseRing(Codomain(rho2)) );
  d := Degree( Codomain(rho1)) + Degree( Codomain(rho2) );
  return hom< G -> GL(d,k) | g :-> DiagonalJoin( rho1(g), rho2(g) ) >;
end intrinsic;

intrinsic DirectSumDecomposition( rho::Map[GrpLie,GrpMat] ) -> [], []
{The decomposition of rho into indecomposable summands}
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );
  k := BaseRing( G );  K := BaseRing( Gl );
  d := Dimension( V );
  R := RootDatum( G );  
  l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );
  
  _, hws := HighestWeights( rho );
  hws := &cat[ ChangeUniverse( Basis(U), V ) : U in hws ];
  M := GModule( sub< Gl | [ rho(g) : g in AlgebraicGenerators( G ) ] > );
  Us := [ sub< M | hw > : hw in hws ];
  Us := [ sub< V | [ V!(M!u) : u in Basis(U) ] > : U in Us ];
  
  require &+Us eq V and 
    forall{ <U,W> : U in Us, W in Us | U eq W or U meet W eq sub<V|> } :
    "This should not happen.  Please email magma-bugs@maths.usyd.edu.au";
    
  restrict := function( rho, U )
    d := Dimension( U );
    return hom< G -> GL(d,K) | g :->
      [ Coordinates( U, u*rho(g) ) : u in Basis(U) ] >;
  end function;

  return [ restrict(rho,U) : U in Us ], Us;
end intrinsic;

intrinsic IndecomposableSummands( rho::Map[GrpLie,GrpMat] ) -> [], []
{The decomposition of rho into indecomposable summands}
  return DirectSumDecomposition(rho);
end intrinsic;


// ----------------------------------------------------
//
// Weights and weight vectors
//
// If we have a Lie algebra repn or our field has an 
// element of infinite order, the weights can be 
// computed using eigenvectors.
//

/*
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );  
  Vmod := GModule( sub< Gl | [ rho(g) : g in Generators(G) ] );
  k := BaseRing( G );  K := BaseRing( Gl );
  d := Dimension( V );
  R := RootDatum( G );  
  l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );
*/


// Basis of weight vectors
weights_Evect_Alg := function( rho )
  if not assigned rho`Weights then
    L := Domain( rho );
    R := RootDatum( L );  
    l := Rank( R );

    // compute eigenspaces
    pos, neg := StandardBasis( L );
    M := Codomain( rho );
    M := MatrixAlgebra( BaseRing(M), Degree(M) );  
    rho`WeightSpaces, rho`Weights := CommonEigenspaces( 
      [ M | rho( pos[r]*neg[r] ) : r in [1..l] ] );
  end if;
  return rho`Weights, rho`WeightSpaces;
end function;

weights_Evect_Grp := function( rho )
  if not assigned rho`Weights then
    G := Domain( rho );
    k := BaseRing( G );
    R := RootDatum( G );  
    l := Rank( R );  n := Dimension( R );
    deg := Degree( BaseRing(Codomain(rho)), k );
    
    // compute eigenspaces
    b, log, inf := nonzeroElt( k );
    M := Codomain( rho );
    M := MatrixAlgebra( BaseRing(M), Degree(M) );  
    rho`WeightSpaces, wts := CommonEigenspaces(
      [ M | rho( elt<G|Vector([k| (i eq r) select b else 1 : i in [1..n]])> ) : r in [1..l] ] );
    rho`Weights := [ [ log(c^deg)/deg : c in wt ] : wt in wts ];
  end if;
  return rho`Weights, rho`WeightSpaces;
end function;

weightSpace_Evect_Grp := function( rho, mu )
  G := Domain( rho );  M := Codomain( rho );
  V := Parent( mu );
  m := Lcm( [ Denominator(a) : a in Eltseq(mu) ] );
  mu *:= m;  mu := ChangeRing( mu, Integers() );
  k := BaseRing( G );  t := nonzeroElt( k );
  n := Rank( G );  H := RSpace( k, n );
  B := Basis( CorootSpace( G ) );
  BH := [ H | [t^(b[i]*m):i in [1..n]] : b in B ];
  return &meet{ Eigenspace( rho( elt<G|BH[i]> ), t^(mu,Vector(B[i])) ) : 
    i in [1..#B] };
end function;

isWeightVector_Evect_Grp := function( rho, v )
  return 0;
end function;

//
// Otherwise we can compute the weights from the highest 
// weights, PROVIDED none of the weight strings are too
// long.
//

// merges weight vectors with the same weight
mergeWvs := function( wts, wvs, W, V )
  // merge with vectors with same weight
  allwts := {@ W | @};  allwvs := [ PowerStructure(ModTupFld) | ];
  for i in [1..#wts] do
    seqpos := Position( allwts, wts[i] );
    if seqpos eq 0 then
      Include( ~allwts, wts[i] );
      allwvs[#allwts] := sub< V | wvs[i] >;
    else
      allwvs[seqpos] := sub< V | allwvs[seqpos], wvs[i] >;
    end if;
  end for;
  return Setseq( allwts ), allwvs;
end function;
  
  
weights_High_Alg := function( rho )
  L := Domain( rho );  A := Codomain( rho );
  V := BaseModule( A );  k := BaseRing( L );  dim := Dimension( V );
  d := Dimension( V );
  R := RootDatum( L );  
  l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );
  rts := [ Root( R, r ) : r in [1..N] ];
  _,neg := StandardBasis( L );
  rtelts := [ rho( a ) : a in neg[1..N] ];

  W := RootSpace( R );
  hwts, hwvs := HighestWeights( rho );
  
  // start with the highest weights
  wts := &cat[ [ hwts[i] : j in [1..Dimension(hwvs[i])] ] : i in [1..#hwts] ];
  wvs := &cat[ ChangeUniverse( Basis(hwvs[i]), V ) : i in [1..#hwts] ];
  
  // how many wts/wvs do we know so far
  knownwvs := sub< V | wvs >;
  
  // this is essentially the orbit algorithm
  i := 1;
  repeat
    wt := wts[i];  wv := wvs[i];
    for r in {1..N} do
      newwt := wt - rts[r];
      newwv := wv * rtelts[r];
      if newwv ne 0 and newwv notin knownwvs then
	Append( ~wts, newwt );  Append( ~wvs, newwv );
	knownwvs := sub< V | knownwvs, newwv >;
      end if;
    end for;
    //print i,wts; wvs;
    i +:= 1;    
  until Dimension( knownwvs ) eq dim or i gt #wts;
  if Dimension( knownwvs ) eq dim then
    error "Error:  Unable to compute weights for this module";
  end if;
    
  return mergeWvs( wts, wvs, W, V );
end function;



/*SL2weights := function( X, Y, wv )
  k := BaseRing( X );  n := Nrows( X );
  G := MatrixGroup< n, k | X, Y >;
  M := GModule( G );
  m := Dimension( M ) - 1;
  wts := [ -m to m by 2 ];
*/
weights_High_Grp := function( rho )
  G := Domain( rho );  Gl := Codomain( rho );
  V := RSpace( Gl );  
  k := BaseRing( G );  K := BaseRing( Gl );  
  xi := PrimitiveElement(k);
  deg := Degree( K, k );
  d := Dimension( V );
  R := RootDatum( G );  
  l := Rank( R );  n := Dimension( R );  N := NumPosRoots( R );
  W := RootSpace( R );
  negrtmods := [ GModule( sub< Gl | rho( elt<G|<r+N,1>> ) > ) : r in [1..N] ];

  Weyl := CoxeterGroup( GrpFPCox, R );
  weylMxs := [ rho( elt<G|r> ) : r in [1..l] ];
  _, weylPermHom := CoxeterGroup( Weyl );
  
  // start with the highest weights
  hwts, hwvs := HighestWeights( rho );
  wts := &cat[ [ hwts[i] : j in [1..Dimension(hwvs[i])] ] : i in [1..#hwts] ];
  wvs := &cat[ ChangeUniverse( Basis(hwvs[i]), V ) : i in [1..#hwts] ];
  
  // we compute all the wtorbits as we go -- we will need them frequently
  wtset := {@ wt : wt in wts @};
  wtorbs := [];  wtwds := [];
  for wt in wtset do
    orb, wds := WeightOrbit( R, wt );
    Append( ~wtorbs, orb );
    Append( ~wtwds, [ Weyl | Eltseq(w) : w in wds ] );
  end for;

  // compute images of weight vectors under the Weyl group
  wvaction := function( wv, w )
    for r in Eltseq( w ) do  wv *:= weylMxs[r];  end for;
    return wv;
  end function;
  oldwts := wts;
  wts := &cat[ Setseq( wtorbs[Position(wtset,wt)] ) : wt in wts ];
  wvs := &cat[ [ V | wvaction( wvs[i], w ) : w in wtwds[Position(wtset,oldwts[i])] ] : 
    i in [1..#oldwts] ];
  // the last simple root used to compute our weight, so we don't use it again
  lastrt := [ 0 : i in [1..#wts] ];

  // how many wts/wvs do we know so far
  knownwvs := sub< V | wvs >;
  
  // this is a modified orbit algorithm
  i := 1;
//  repeat
  while #wts lt d do
    wt := wts[i];  wv := wvs[i];
    wtwrtwt := BasisChange( R, wt : OutBasis:="Weight" );
    for r in Exclude( {1..N}, lastrt[i] ) do
      rt := Root( R, r );
      // check that wt-m*alpha_r can be dominant for some m
      rtwrtwt := BasisChange( R, rt : OutBasis:="Weight" );
      if forall{ i : i in [1..l] | wtwrtwt[i] ge 0 or rtwrtwt[i] lt 0 } then
      
 	// the space of wvs the new wt string
 	newwvs := sub< negrtmods[r] | wv >;
 	newwvs := sub< V | [ V!negrtmods[r]!b : b in Basis(newwvs) ] >;
 
 	// we can now separate using eigenvalues of the torus element
 	vects, coeffs := commonEigenspaces(
 	  [ Matrix(rho(TorusTerm(G,r,xi))) ] : U := newwvs );
 	coeffs := [ c[1] : c in coeffs ];
	
	// find the coeff of wv
 	if not exists(wtcoeff){ coeffs[idx] : idx in [1..#vects] | wv in vects[idx] } then
 	  error "Error2:  Unable to compute weights for this module";
 	end if;
	
	for m in [1..#vects-1] do
	  newwt := wt - m*rt;
	  if IsDominant( R, newwt ) then
 	    // find newwv in vects
 	    coeff := wtcoeff / xi^(2*m);
	    if not exists(newwv){ vects[idx] : idx in [1..#vects] | coeffs[idx] eq coeff } or
	    Dimension( newwv ) gt 1 then
 	      error "Error3:  Unable to compute weights for this module";
	    end if;
            newwv := newwv.1;
	    if newwv notin knownwvs then
	      setpos := Position( wtset, newwt );
	      if setpos eq 0 then
	    	orb, wds := WeightOrbit( R, newwt );
	    	Include( ~wtset, newwt );
	    	//print wtwds, wds, Universe(wtwds[1]) eq Universe(wds);
	    	Append( ~wtorbs, orb );
	    	Append( ~wtwds, [ Weyl | Eltseq(w) : w in wds ] );
	    	setpos := #wtset;
 	      end if;
 	
	      wts cat:= Setseq( wtorbs[setpos] );
	      newwvs := [ V | wvaction( newwv, w ) : w in wtwds[setpos] ];
	      oldwvs := wvs;
              wvs cat:= newwvs;
	      lastrt cat:= [ r^weylPermHom( w ) : w in wtwds[setpos] ];
 	      knownwvs := sub< V | knownwvs, newwvs >;
              if Dimension( sub< V | wvs> ) ne #wvs then
                error oldwvs, newwvs;
              end if;
	      //knownwvs eq sub< V | wvs >;
 	    end if;
	  end if;
	end for;
	
      end if;
      
    end for;
    i +:= 1;
    if i gt #wts then break; end if;
  end while;
//  until #wts gt d or i gt #wts;
  if #wts ne d then
    error "Error4:  Unable to compute weights for this module", #wts, d;
  end if;
  
  
  return mergeWvs( wts, wvs, W, V );
  
/*  return [ allwts[i] : i in [1..#allwts] | modallwts[i] in modwts ], 
    [ wvs[ Position(modwts, Eltseq(modallwts[i])) ] : i in [1..#allwts] | 
      modallwts[i] in modwts ];*/

end function;



// ----------------------------------------------------
//
// Weights and weight vectors intrinsics
//


intrinsic IsWeightVector( rho::Map[GrpLie,GrpMat], v::ModTupFldElt ) -> BoolElt
{True iff v is a weight vector of rho}
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );  
  k := BaseRing( G );  K := BaseRing( Gl );

  ok, v := IsCoercible( V, v );
  require ok : "Invalid vector";

  if Characteristic( k ) eq 0 and not assigned rho`Weights then
    return isWeightVector_Evect_Grp( rho, v );
  else
    wts, wvs := Weights( rho );
    ok := exists(i){ i : i in [1..#wts] | v in wvs[i] };
    if ok then  return ok, wts[i];
    else  return ok, _;
    end if;
  end if;
end intrinsic;


intrinsic WeightSpace( rho::Map[GrpLie,GrpMat], mu::ModTupRngElt ) -> ModTupFld
{The weight space of mu with respect to rho}
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );  
  k := BaseRing( G );  K := BaseRing( Gl );

  if Characteristic( k ) eq 0 and not assigned rho`Weights then
    return weightSpace_Evect_Grp( rho, mu );
  else
    wts, wvs := Weights( rho );
    i := Position( wts, mu );
    if i ne 0 then  return wvs[i];
    else  return sub< V | >;
    end if;
  end if;
end intrinsic;


//  We shouldn't be computing the weights here
intrinsic WeightSpaces( rho::Map[GrpLie,GrpMat] ) -> ModTupFld
{The weight spaces of rho}
  if not assigned rho`WeightSpaces then
    G := Domain( rho );  k := BaseRing( G );
    if Characteristic( k ) eq 0 then
      rho`Weights, rho`WeightSpaces := Weights( rho );
    else
      rho`Weights, rho`WeightSpaces := Weights( rho );
    end if;
  end if;
  return rho`WeightSpaces;
end intrinsic;

intrinsic WeightSpaces( rho::Map[AlgLie,AlgMatLie] ) -> ModTupFld
{The weight spaces of rho}
  if not assigned rho`WeightSpaces then
    rho`Weights, rho`WeightSpaces := weights_Evect_Alg( rho );
  end if;
  return rho`WeightSpaces;
end intrinsic;


intrinsic WeightVectors( rho::Map[GrpLie,GrpMat] ) -> SeqEnum, .
{A basis of weight vectors of rho}
  G := Domain( rho );  Gl := Codomain( rho );
  V := rSpace( Gl );

  wvs := WeightSpaces( rho );
  return &cat[ ChangeUniverse( Basis(wv), V ) : wv in wvs ];
end intrinsic;

intrinsic WeightVectors( rho::Map[AlgLie,AlgMatLie] ) -> SeqEnum, .
{A basis of weight vectors of rho}
  L := Domain( rho );  M := Codomain( rho );
  V := rSpace( M );  
  wvs := WeightSpaces( rho );
  return &cat[ ChangeUniverse( Basis(wv), V ) : wv in wvs ];
end intrinsic;


intrinsic IsWeight( rho::Map[GrpLie,GrpMat], mu::ModTupRngElt ) -> BoolElt
{True iff mu is a weight of rho}
  return Dimension( WeightSpace(rho,mu) ) ne 0;  
end intrinsic;


intrinsic Weight( rho::Map[GrpLie,GrpMat], v::ModTupRngElt : Basis:="Standard" ) -> ModTupRngElt, ModTupRngElt
{The weight corresponding to the vector v}
  G := Domain( rho );  
  ok, wt := IsWeightVector( rho, v );
  require ok : "Not a weight vector";
  case Basis :
  when "Standard" : 
    return wt;
  when "Root" :
    return ChangeRing(wt,Rationals()) * FundamentalWeights( G ) * ChangeRing(SimpleRoots(G),Rationals())^-1;//WRONG
  when "Weight" :
    return ChangeRing(wt,Rationals());
  else
    error "Error: Invalid Basis parameter";
  end case; 
end intrinsic;


intrinsic Weights( rho::Map[GrpLie,GrpMat] : Basis:="Standard" ) -> SeqEnum, SeqEnum
{The weights of rho}
  G := Domain( rho );  Gl := Codomain( rho );
  if not assigned rho`WeightSpaces then
    if Characteristic( BaseRing(G) ) eq 0 then
      rho`Weights, rho`WeightSpaces := weights_Evect_Grp( rho );
    else
      rho`Weights, rho`WeightSpaces := weights_High_Grp( rho );
    end if;
  end if;

  return [ BasisChange(RootDatum(G),wt:OutBasis:=Basis) : wt in rho`Weights ], 
    rho`WeightSpaces;
end intrinsic;

intrinsic WeightsAndVectors( rho::Map[GrpLie,GrpMat] : Basis:="Standard" ) -> SeqEnum, SeqEnum
{The weights and corresponding vectors of rho}
  return Weights( rho : Basis:=Basis );
end intrinsic;

intrinsic Weights( rho::Map[AlgLie,AlgMatLie] : Basis:="Standard" ) -> SeqEnum, SeqEnum
{The weights of rho}
  L := Domain( rho );  M := Codomain( rho );
  if not assigned rho`WeightSpaces then
    if Characteristic( BaseRing(L) ) eq 0 then
      rho`Weights, rho`WeightSpaces := weights_Evect_Alg( rho );
    else
      rho`Weights, rho`WeightSpaces := weights_High_Alg( rho );
    end if;
  end if;

  if IsReductive( L ) then
    return rho`Weights, rho`WeightSpaces;
    return [ BasisChange( RootDatum(L), Vector(wt) : OutBasis:=Basis ) : 
      wt in rho`Weights ], rho`WeightSpaces;
  else
    return rho`Weights, rho`WeightSpaces;
  end if;
end intrinsic;

intrinsic WeightsAndVectors( rho::Map[AlgLie,AlgMat] : Basis:="Standard" ) -> SeqEnum, SeqEnum
{The weights and corresponding vectors of rho}
  return Weights( rho : Basis:=Basis );
end intrinsic;




// ====================================================
//
// Row reduction
//
// ====================================================

Clear := procedure()  System("clear");  end procedure;

function GraphAutomorphisms( L ) 
    n := Rank(RootDatum(L)); Sn := Sym(n);
    perms := [ Sn!1 ];
    if (not(IsIrreducible(RootDatum(L)))) then
        //We should be able to handle this case, but for now, we can't.
        print "Warning - GraphAutomorphisms not implemented for non-simple Lie algebras";
    else
        tp := CartanName(L)[1];
        chr := Characteristic(BaseRing(L));
        case tp:
        when "A":
            Append(~perms, Sn![n+1-i : i in [1..n] ]);
        when "B", "C": 
            if chr eq 2 then 
                Append(~perms, Sn![n+1-i : i in [1..n] ]);
            end if;
        when "D":
            if (n lt 4) then
                print "Warning - GraphAutomorphisms not implemented for D1,D2,D3";
            elif (n eq 4) then
                perms cat:= [ Sn | (1,3),(1,4),(3,4),(1,3,4),(4,3,1)];
            else
                Append(~perms, Sn!(n-1,n));
            end if;
        when "E":
            if (n eq 6) then
                Append(~perms, Sn!(1,6)(3,5));
            end if;
        when "F":
            if (chr eq 2) then
                Append(~perms, Sn!(1,4)(2,3));
            end if;
        when "G":
            if (chr eq 3) then
                Append(~perms, Sn!(1,2));
            end if;
        end case;
    end if;
    
    eprms := [];
    for s in perms do
        if IsIdentity(s) then
            //This is a slight workaround, to make G2 work over every char except 3
            b := Sym(2*NumberOfPositiveRoots(RootDatum(L)))!1;
        else
            _,_,b := GraphAutomorphism(L, s);
        end if;
        Append(~eprms, b);
    end for;
    return perms, eprms;
end function;

function conjugateIntoBorelOrTorus(md, c : TryTorus := false, RecursionsLeft := 10)
// This only works for semisimple elements, can we extend it to other elements???
    if not md in {"grp","alg"} then error "Invalid mode: " cat md; end if;

    if md eq "grp" then
        G := Parent( c );  k := BaseRing( c );
        R := RootDatum(G); 
        s, u := MultiplicativeJordanDecomposition( c );
        rho, L := AdjointRepresentation( G : NoWarning );
        S := rho( s );  U := rho( u );  C := S*U;
    elif md eq "alg" then
        L := Parent( c ); k := BaseRing( L );
        R := RootDatum(L);
        rhoL := AdjointRepresentation(L);
        C := rhoL(c);
    end if;
    NPR := NumberOfPositiveRoots(R);
    
    // extend field
    if md eq "grp" then   pol := CharacteristicPolynomial( S );
    elif md eq "alg" then pol := CharacteristicPolynomial( C );
    end if;
    K := SplittingField( pol );
    if (K ne k) then
        if md eq "grp" then
            G := BaseExtend( G, K );  
            rho, L := AdjointRepresentation( G : NoWarning );
            C := ChangeRing( C, K );  S := ChangeRing( S, K );  U := ChangeRing( U, K );
        elif md eq "alg" then
            L, h := ChangeRing(L, K);
            rhoL := AdjointRepresentation(L);
            c := h(c);
            C := ChangeRing(C, K);
        end if;
    end if;
    
    // Construct group in the algebra case
    if md eq "alg" then
        //WE NEED TO USE THE ADJOINT GROUP HERE !!!!
        G := GroupOfLieType(RootDatum(L), K);
        rho := AdjointRepresentation(G);
    end if;
    
    // Cent = C_L( S )
    if md eq "grp" then
        N := Nullspace( Matrix(S) - 1 );
        Cent := sub< L | [ L!x : x in Basis(N) ] >;
    elif md eq "alg" then
        Cent := Centraliser( L, L!Eltseq(c) );
    end if;        
    H := SplittingCartanSubalgebra( Cent );
    if not IsCartanSubalgebra( L, H ) then
        error "This shouldn't happen";
    elif not IsSplittingCartanSubalgebra( L, H ) then
        if md eq "alg" then error "SplittingCartanSubalgebra is NOT a SCA"; end if;
        // extend field again
        oldL := L;
        _,_,L := RootDecomposition(L,H);
        H := sub< L | [ L!Eltseq(M[i]) : i in [1..Dimension(H)] ] >
        where M is Morphism(H,oldL);
        K := BaseRing( L );
        G := BaseExtend( G, K );  
        rho := AdjointRepresentation( G : NoWarning );
        C := ChangeRing( C, K );  S := ChangeRing( S, K );  U := ChangeRing( U, K );
    end if;
    
    // Now match up wb and pos/neg to get ims
    wb, B := WeightBase( rho );
    pos, neg, _ := StandardBasis( L, H );
    posneg := pos cat neg;
    rposs := [ RootPosition(R, wt : Basis := "Standard") : wt in wb ];
    if exists{ r : r in rposs | r eq 0 } then 
        error "Could not match up WeightBase and roots.";
    end if;
    
    inv := rowReduction( rho : Vectors, NoTorus, UseVariant := 1 );
    
    perms,eprms := GraphAutomorphisms(L);
    for i in [1..#eprms] do
        ims := [ posneg[r^(eprms[i])] : r in rposs ];
        a := inv( ims );
        if (a cmpne false) then break; end if;
    end for;
    
    if (a cmpeq false) then
        /* It did not work */
        error "Could not find suitable graph automorphism";
    end if;
    
    a := a^-1;
    A := ChangeRing(rho(a), K);
    if (not(TryTorus)) then
        if (md eq "grp") then
            return (G!c)^a, a^-1;
        elif (md eq "alg") then
            return c*A, a^-1, A^-1;
        end if;
    end if;
    
    // Construct delta, mapping borel to opposite borel
    mp := hom<R -> R | [ i+NPR : i in [1..NPR] ]>;
    delta := GroupOfLieTypeHomomorphism(mp, K);
    if (md eq "grp") then
        c2 := delta(c^a);
        C2 := rho(c2);
    elif (md eq "alg") then
        deltaL := LieAlgebraHomomorphism(mp, K);
        u := Domain(deltaL)!Eltseq(c*A); //WHY DO I NEED TO DO THIS ?!
        c2 := deltaL(u);
    end if;
    
    //Create new Cartan Subalgebra and corresponding basis for L
    if (md eq "grp") then
        N := Nullspace( Matrix(C2) - 1 );
        Cent := sub< L | [ L!x : x in Basis(N) ] >;
    elif (md eq "alg") then
        Cent := Centraliser(L, L!Eltseq(c2));
    end if;
    H := SplittingCartanSubalgebra( Cent );
    if not IsSplittingCartanSubalgebra( L, H ) then
        error "Could not get into the torus (H is not a SplittingCartanSubalgebra)";
        //maybe extend field again??
    end if;
    pos, neg, _ := StandardBasis( L, H );
    posneg := pos cat neg;
    
    //(Try to) select entries from posneg in a smart way, i.e. with zeroes
    //  to the right of the pivots-to-be.
    //  ( rmnzp stands for "rightmost nonzero position" )
    rightMostNonZeroPos := function(ln)
        for j in [ NumberOfColumns(ln) .. 1  by -1 ] do
            if (not IsZero(ln[j])) then return j; end if;
        end for;
        return 0;
    end function;
    
    rmnzpPN := [ Integers() | rightMostNonZeroPos(p) : p in posneg ];
    rmnzpB := [ Integers() | rightMostNonZeroPos(p) : p in B ];
    Sort(~rmnzpPN, func<x,y | x - y>, ~prm);
    posneg := PermuteSequence(posneg, prm);
    ims2 := [ Universe(posneg) | ];
    pos := #posneg + 1; for i in [1..#B] do
        repeat
            pos -:= 1;
        until pos eq 0 or
            ( rmnzpB[i] eq rmnzpPN[pos] );
        if (pos eq 0) then
            printf "[Could not construct suitable second image in Conjugate Into Torus.]\n";
            printf "[We try to recursively call this function.                   (%3o) ]\n", RecursionsLeft;
            ims2 := false;
            break;
        end if;
        Append(~ims2, posneg[pos]);
    end for;

    //New ims created, now do row reduction
    inv := rowReduction( rho : Vectors, NoTorus, UseVariant := 2 );
    if (ims2 cmpeq false) then
        //It did not work, that's bad luck - we try again
        if (RecursionsLeft gt 0) then
            _, a2 := conjugateIntoBorelOrTorus(md, c2 : TryTorus := TryTorus, RecursionsLeft := RecursionsLeft - 1);
        else
            error "Could not construct suitable second image in Conjugate Into Torus.";
        end if;
    else
        a2 := inv( ims2 );
        if (a2 cmpeq false) then 
            error "Could not get into the torus (second row reduction failed)"; 
        end if;
        a2 := a2^-1;  
    end if;
    
    //The result (delta is autom)
    //  delta(c^a) ^ a2 is toral
    //  delta(delta(c^a) ^ a2) is toral
    //  c^a^(delta(a2)) is toral
    //  c^(a*delta(a2)) is toral
    a3 := a*delta(a2);
    A3 := rho(a3);
    if (md eq "grp") then
        return (G!c)^a3, a3^-1;    
    elif (md eq "alg") then
        return c*ChangeRing(A3, BaseRing(L)), a3^-1, A3^-1;
    end if;
end function;

intrinsic ConjugateIntoBorel( c::GrpLieElt ) -> GrpLieElt, GrpLieElt
{Borel element b and a such that b = a * c * a^-1}
    return conjugateIntoBorelOrTorus("grp", c);
end intrinsic;

intrinsic ConjugateIntoTorus( c::GrpLieElt ) -> GrpLieElt, GrpLieElt
{Torus element t and a such that t = a * c * a^-1}
    return conjugateIntoBorelOrTorus("grp", c : TryTorus);
end intrinsic;

intrinsic ConjugateIntoBorel( x::AlgLieElt ) -> AlgLieElt, GrpLieElt, Mtrx
{Borel element b, lie group element a, and matrix A such that A = rho(a),
 where rho is the adjoint representation of G, and x*A = b. }
    return conjugateIntoBorelOrTorus("alg", x);
end intrinsic;

intrinsic ConjugateIntoTorus( x::AlgLieElt ) -> AlgLieElt, GrpLieElt, Mtrx
{Torus element t, lie group element a, and matrix A such that A = rho(a),
 where rho is the adjoint representation of G, and x*A = t. }
    return conjugateIntoBorelOrTorus("alg", x : TryTorus);
end intrinsic;

function FindTransfWeylElts(L, C1, C2)
    //Finds the elements in the Weylgroup of L
    //  such that PermuteSequence(C1, w) = C2.
    //Needs to be made to work more efficiently
    W := CoxeterGroup(RootDatum(L));
    return { w : w in W | PermuteSequence(C1, w) eq C2 };
end function;

/* I don't think this is used anywhere
intrinsic ConjugateSemisimpleElements(h1::AlgLieElt, h2::AlgLieElt) -> Mtrx, GrpLieElt, RngIntElt
{ Let G be the Lie group corresponding to the Lie algebra h1 and h2 are in. This function returns 
  a matrix T, g in G and i in \{-1,1\} such that T = i*rho(g) and h1*T = h2.  
  if such an element cannot be found, false is returned.
}
    L := Parent(h1);
    k := BaseRing(L);
    h1p,_,T1 := ConjugateIntoTorus(h1);
    h2p,_,T2 := ConjugateIntoTorus(h2);
    
    pos,neg,_ := StandardBasis(L);
    ev := function(e, h)
        prod := e*h;
        if IsZero(prod) then return k!0; end if;
        _ := exists(i){i : i in [1..NumberOfColumns(e)] | not IsZero(e[i])};
        if IsZero(prod[i]) then return false; end if;
        r := prod[i]/e[i];
        if prod eq r*e then return r; end if;
        return false;
    end function;
    C1 := [ ev(b, h1) : b in pos cat neg ];
    C2 := [ ev(b, h2) : b in pos cat neg ];
    if (exists{i : i in C1 cat C2 | i cmpeq false}) then
        error "Could not determine c such that [e,h] = c.e";
    end if;
    
    G := GroupOfLieType(L);
    rhoG := AdjointRepresentation(G);
    
    _, GA := GraphAutomorphisms(L);
    ts := {WeylGroup(G)|};
    for au1,au2 in GA do
        ts join:= FindTransfWeylElts(L, PermuteSequence(C1, au1), PermuteSequence(C2,au2));
    end for;

    for t in ts do 
        g := elt<G | t>;
        M := ChangeRing(Matrix(rhoG(g)), k);
        for sgn in {1,-1} do 
            if (Vector(h1p)*sgn*M eq h2p) then
                T := Matrix(T1)*sgn*M*(Matrix(T2)^-1);
                return ChangeRing(T,k), elt<G|g>, sgn;
            end if;
        end for;
    end for; 
    return false, _, _;
end intrinsic;
*/


intrinsic Inverse( rho::Map[GrpLie,GrpMat] ) -> Map
{The inverse of rho}
  G := Domain( rho );  H := Codomain( rho );
  f := rowReduction(rho);
  return hom< H -> G | h :-> f(h) >;
end intrinsic;

intrinsic '@@'( x::GrpMatElt, rho::Map[GrpLie,GrpMat] ) -> GrpLieElt
{A preimage of x under f}
  return x@Inverse(rho);
end intrinsic;


// ====================================================
//
// Row and column operations
//

/* 
   This code allows us to compute with sparse nilpotent matrices
   and their exponentials.
   
   We represent sparse nilpotent matrices by a sequence of triples
   <i,j,a> signifying that the <i,j> entry is equal to a.
   
   We represent exponential matrices by a list of triples 
   corresponding to row and column operations as follows:
   
   Triple       Left action       Right action
   <i,0,a>      Ri -> a*Ri        Ci -> a*Ci
   <i,j,0>      Ri <-> Rj         Ci <-> Cj
   <i,j,a>      Ri -> Ri + a*Rj   Ci -> Ci + a*Cj
*/

// Converting between sparse and dense formats for nilpotent matrices
sparseToDense := function( n, k, a )
  A := MatrixAlgebra( k, n )!0;
  for t in a do
    A[t[1],t[2]] := t[3];
  end for;
  return A;
end function;

denseToSparse := function( n, k, A )
  return [ <i,j,k!A[i,j]> : i in [1..n], j in [1..n] | A[i,j] ne 0 ];
end function;

/*
> d2s := function( n, k, A )
>     A := Submatrix(A,1,1,n,n);
>     A := SparseMatrix(A);
>     A := SparseMatrix(k,A);
>     return [ <i,j,k!A[i,j]> : j in Support(A,i), i in [1..n] ];
> end function;
*/

// Operations in the sparse format for nilpotent matrices
addterm := procedure( ~prod, i, j, a )
  if exists( idx ){ idx : idx in [1..#prod] | 
  prod[idx][1] eq i and prod[idx][2] eq j } then
    prod[idx][3] +:= a;
    if prod[idx][3] eq 0 then  Remove( ~prod, idx );  end if;
  else
    Append( ~prod, <i,j,a> );
  end if;
end procedure;

sparseAdd := procedure( ~x, y )
  for op in y do
    addterm( ~x, op[1], op[2], op[3] );
  end for;
end procedure;

sparseProd := function( x, y )
  prod := [];
  for op1 in x do
    for op2 in y do
      if op1[2] eq op2[1] then
        addterm( ~prod, op1[1], op2[2], op1[3]*op2[3] );
      end if;
    end for;
  end for;
  return prod;
end function;

sparseScalarProd := function( c, x )
  if c eq 0 then 
    return [];
  else
    return [ <op[1],op[2],c*op[3]> : op in x ];
  end if;
end function;


// row operations for matrices of the form 1+s, s sparse
addToEntry := procedure( ~s, i,j, a )
  if exists(pos){ pos : pos in [1..#s] | s[pos][1] eq i and s[pos][2] eq j }
  then
    if s[pos][3] eq -a then
      Remove( ~s, pos );
    else
      s[pos][3] +:= a;
    end if;
  else
    Append( ~s, <i,j,a> );
  end if;
end procedure;

addToEntryPos := procedure( ~s, i,j, a, ~pos0 )
  if exists(pos){ pos : pos in [1..#s] | s[pos][1] eq i and s[pos][2] eq j }
  then
    if s[pos][3] eq -a then
      Remove( ~s, pos );
      if   pos lt pos0 then  pos0 -:= 1;
      elif pos eq pos0 then  pos0 := 0;
      end if;
    else
      s[pos][3] +:= a;
    end if;
  else
    Append( ~s, <i,j,a> );
  end if;
end procedure;

addToEntryPos2 := procedure( ~s, i,j, a, ~pos0, ~pos1 )
  if exists(pos){ pos : pos in [1..#s] | s[pos][1] eq i and s[pos][2] eq j }
  then
    if s[pos][3] eq -a then
      Remove( ~s, pos );
      if   pos lt pos0 then  pos0 -:= 1;
      elif pos eq pos0 then  pos0 := 0;
      end if;
      if   pos lt pos1 then  pos1 -:= 1;
      //elif pos eq pos1 then  pos1 := 0;
      end if;
    else
      s[pos][3] +:= a;
    end if;
  else
    Append( ~s, <i,j,a> );
  end if;
end procedure;

opsToDense := function(n,k,ops)
  I := IdentityMatrix(k,n);
  P := PolynomialRing(k);
  for i in [1..#ops] do
    if #ops[i] eq 3 then
      ops[i] := <ops[i][1],ops[i][2],P!ops[i][3]>;
    elif #ops[i] eq 2 and Category(ops[i][2]) ne RngIntElt then
      ops[i] := <ops[i][1],P!ops[i][2]>;
    end if;
  end for;
  rightActionOps( ~I, ops, k!1, false );
  return I;
end function;


// Convert 1+s to operations, where s is sparse
// This is just row reduction
sparseToOp := function(n, k, s)
  ops := [**];
  for i in [1..n] do
    // check the pivot
    if exists(pos){ pos : pos in [1..#s] | 
    s[pos][1] eq i and s[pos][2] eq i } then
      if s[pos][3] eq -1 then
        // swap in a nonzero pivot
        if exists(pos2){ pos2 : pos2 in [1..#s] | 
        s[pos2][1] gt s[pos][1] and s[pos2][2] eq i } then
          j := s[pos2][1];
          pos := pos2;
          // swap rows i and j
          for pos2 in [1..#s] do
            if s[pos2][1] eq i then
              s[pos2][1] := j;
            elif s[pos2][1] eq j then
              s[pos2][1] := i;
            end if;
          end for;
          addToEntryPos( ~s, i,j, 1, ~pos );  addToEntryPos( ~s, j,i, 1, ~pos );
          addToEntryPos( ~s, i,i,-1, ~pos );  addToEntryPos( ~s, j,j,-1, ~pos );
          Append( ~ops, <i,j> );
        else
          error "Non an invertible matrix";
        end if;
      end if;
      if pos ne 0 then
        // make the pivot 1 by a row multiplication
        a := 1/(1+s[pos][3]);
        Remove( ~s, pos );
        for pos in [1..#s] do
          if s[pos][1] eq i then
            s[pos][3] *:= a;
          end if;
        end for;
        Append( ~ops, <i,a^-1> );
      end if;
    end if;
        
    // clear ith column
    pos := 1;
    while pos le #s and pos gt 0 do
      if s[pos][2] eq i then
        j := s[pos][1];
        a := -s[pos][3];
        // clear entry by adding a*R_i to R_j
        Remove( ~s, pos );
        pos2 := 1;
        while pos2 le #s do
          if s[pos2][1] eq i then
            addToEntryPos2( ~s, j,s[pos2][2], a*s[pos2][3], ~pos2, ~pos );
          end if;
          pos2 +:= 1;
        end while;
        Append( ~ops, <i,j,-a> );
      else
        pos +:= 1;
      end if;
    end while;
    
    /*print i, opsToDense(n,k,ops)*(sparseToDense(n,k,s)+1),
    (sparseToDense(n,k,s)+1);*/
  end for;

  return ops;
end function;


// Compute the exponential of a nilpotent matrix given in sparse format
sparseToExpOp := function( n,k,a )
  // minus the identity term
  ret := a;  pow := a;  i := 2;
  while not IsEmpty( pow )  do
    pow := sparseProd( a, pow );
    for j in [1..#pow] do
      pow[j][3] := pow[j][3]/i;
    end for;
    sparseAdd( ~ret, pow );
    i +:= 1;
  end while;
  return sparseToOp(n,k,ret);
end function;



leftActionOp := procedure( ~A, op, sub )
  if #op eq 3 then
    AddRow( ~A, Evaluate(op[3], sub), op[1], op[2] );
  elif #op eq 2 and Category(op[2]) ne RngIntElt then
    MultiplyRow( ~A, Evaluate(op[2], sub), op[1] );
  else
    SwapRows( ~A, op[1], op[2] );
  end if;
end procedure;

rightActionOp := procedure( ~A, op, sub, ops )
  P := Parent(A);
  if #op eq 3 then
    if ops then
        Append(~A, <op[1], op[2], Parent(op[3])!Evaluate(op[3], sub)>);
    else
        AddColumn( ~A, Evaluate(op[3], sub), op[2], op[1] );
    end if;
  elif #op eq 2 and Category(op[2]) ne RngIntElt then
    if ops then
        Append(~A, <op[1], Parent(op[2])!Evaluate(op[2], sub)>);
    else
        MultiplyColumn( ~A, Evaluate(op[2], sub), op[1] );
    end if;
  else
    if ops then
        Append(~A, op);
    else
        SwapColumns( ~A, op[1], op[2] );
    end if;
  end if;
  if not ops then
      A := P!A;
    end if;
end procedure;

rightActionOps := procedure( ~A, ops, sub, as_ops )
  for op in ops do 
    rightActionOp( ~A, op, sub, as_ops );
  end for;
end procedure;

rightActionOpsfunc := function(A, ops)
    rightActionOps(~A, ops, 1, false);
    return A;
end function;

leftActionOps := procedure( ~A, ops, sub )
  for i := #ops to 1 by -1 do 
    leftActionOp( ~A, ops[i], sub );
  end for;
end procedure;


substitute := function( ops, sub )
  newops := [];
  for op in ops do
    Append( ~newops, <op[1],op[2],Evaluate(op[3], sub)> );
  end for;
  return newops;
end function;

leftinverseops := function(ops)
ops;
    newops := [* *];
    for op in ops do
        newop := op;
        if #op gt 2 or Type(op[2]) ne RngIntElt then
            newop[#op] := -newop[#op];
        end if;
        Append(~newops, newop);
    end for;
newops;
    return newops;
end function;

inverseops := function(ops)
    newops := [* *];
    for i in [1 .. #ops] do
        newop := ops[#ops - i + 1];
        if #newop gt 2 then
            newop[#newop] := -newop[3];
        elif Type(newop[2]) ne RngIntElt then
            newop[#newop] := 1/newop[2];
        end if;
        newops[i] := newop;
    end for;
    return newops;
end function;

modularMxToOps := function( A )
/* A; */
  n := Ncols(A);
/*
  perm := [];
  consts := [];
  for i in [1..n] do
    e := exists(j){ j : j in [1..n] | A[i,j] ne 0 };
    if e then
        Append( ~perm, j );
        Append( ~consts, A[i,j] );
    else
        Append(~perm, 0);
        Append(~consts, CoefficientRing(Parent(A))!1);
    end if;
  end for;

    for i in [1 .. n] do
        if perm[i] eq 0 then
            assert exists(j){j : j in [1 .. n] | j notin perm};
            perm[i] := j; 
        end if;
    end for;
perm;
  perm := Sym(n)!perm;

  ops := [* *];
  done := [ false : i in [1..n] ];
  for i in [1..n] do
    j := i;
    while not done[j] do
      Append( ~ops, <j,j^perm> );
      done[j] := true;
      j := j^perm;
    end while;
  end for;

  for i in [1..n] do
    if consts[i] ne 1 then
      Append( ~ops, <i,consts[i]> );
    end if;
  end for;
*/
  ops := [* *];
  reverse := false; // lower triangular
    for i in [1 .. n] do
        for j in [1 .. n] do
            if A[i, j] ne 0 then
                assert i ne j;
                Append(~ops, <j, i, A[i, j]>);
                if not reverse and i lt j then
                    reverse := true;
                elif reverse then
                    assert i lt j;
                end if;
            end if;
        end for;
    end for;
    if reverse then
        for i in [1 .. #ops div 2] do
            tmp := ops[i];
            ops[i] := ops[#ops - i + 1];
            ops[#ops - i + 1] := tmp;
        end for;
    end if;
    I := Identity(Parent(A));
    rightActionOps(~I, ops, CoefficientRing(Parent(A)).1, false);
    assert I - Identity(Parent(A)) eq A;
  return ops;
end function;

// The exponential of a nilpotent element
// minus the identity
// Note: if a is not nilpotent, this is an infinite loop
exp_minus_one := function( a )
  ret := a;
  /*
  n := Nrows(a);
  C := CoefficientRing(Parent(a));
  a := denseToSparse(n, C, a);
  pow := a;
  pow := sparseProd(pow, pow);
  pow := [<t[1], t[2], t[3]/2> : t in pow];
  */
  pow := a^2/2;
  i := 2;
  while pow ne 0 do
    ret +:= pow;
    /*
    for p in pow do
        ret[p[1], p[2]] +:= p[3];
    end for;
    */
    i +:= 1;
    pow *:= a/i;
    /* pow := sparseProd(pow, [<t[1], t[2], t[3]/i> : t in a]); */
    /*
    pow := sparseProd(pow, a);
    for j in [1..#pow] do
      pow[j][3] := pow[j][3]/i;  
    end for;
    */
  end while;
  return ret;
end function;


grpRepn := function(G, pos, neg : NoWarning := false)

  R := RootDatum( G );  N := NumPosRoots( R );
  k := BaseRing( G );
  
  // convert to associative mxs
  Q := BaseRing(Universe(pos));
  d := Degree(Universe(pos));
  M := MatrixAlgebra( Q, d );
  ChangeUniverse( ~pos, M );  ChangeUniverse( ~neg, M );

  rtMxs := pos cat neg;
  carMxs := [ M | comm(neg[i],pos[i]) : i in [1..Rank(R)] ];
  D, rtMxs, K, rad, isproj, r := extendTorus( R, carMxs, rtMxs, k : NoWarning:=NoWarning );
  P := PolynomialRing( Q ); x := P.1;

  // to use polynomials over matrices which is faster in exp but
  // too expensive to convert back
  /* x := PolynomialRing(MatrixRing(K, Degree(F))).1; */

  // sparseToExpOp is fast but converting to a sparse matrix
  // is too expensive for it to be worth it
  rtMxs := [ denseToSparse(d, P, r) : r in rtMxs ];
  rtMxs := [ sparseScalarProd( x, r) : r in rtMxs ];
  expMxs := [ sparseToExpOp(d, P,  R) : R in rtMxs ];

  /*
  Get matrices minus identity so that modularMxToOps can find the non trivial
  entries
  */
  /* time expMxs := [exp_minus_one(x*R) : R in rtMxs]; */
  d := Degree( Universe( pos ) );
  if d eq 0 then
	//Toral!
	d := Dimension(R);
	if d eq 0 then
      return hom< G -> GL(1,k) | x :-> 1 >;
    end if;
  end if;

  // to convert back polynomials over matrices
  // VERY EXPENSIVE
  /* K := PolynomialRing( K ); x := K.1; */
  /* time expMxs := [ MatrixRing(K, Degree(F)) | [K![S[i, j, k] : i in [1 .. #S]] : j, k in [1 .. d]] : S in [Eltseq(e) : e in expMxs]]; */

  /* time expMxs := [modularMxToOps(e) : e in expMxs]; */
  //Universe(expMxs);
  // VERY EXPENSIVE FOR E8 over a finite field
  // Do manually on ops instead
  // time ChangeUniverse(~expMxs, MatrixRing(PolynomialRing(K), Degree(F)));
  P := PolynomialRing(K);
  for i in [1 .. #expMxs] do
    newops := [* *];
    for op in expMxs[i] do
        newop := op;
        if #op eq 3 then
            newop := <op[1], op[2], P!op[3]>;
        elif Type(op[2]) ne RngIntElt then
            newop := <op[1], P!op[2]>;
        end if;
        Append(~newops, newop);
    end for;
    expMxs[i] := newops;
  end for;

  dim := Dimension( R );
  neg := func< r | (r le N) select r+N else r-N >;

  // Old functions
  /* x := func< r, t | Evaluate( expMxs[r], t*I ) >; */
  n := func< r, t | x(r,t) * x(neg(r),-t^(-1)) * x(r,t) >;
  /* sdot := func< r | n(r,1) >; */

  h := func< i, t | [PolynomialRing(K) | rad(t)^(Integers()!D[i,j]) : j in [1..d] ] >;

  multByUnipTerm := procedure( ~el, term, ops )
    rightActionOps(~el, expMxs[term[1]], term[2], ops );
  end procedure;
  multByUnip := procedure( ~el, unip, ops )
    if ISA( Category( Universe(unip) ), Rng ) then
      for r in [1..#unip] do
        rightActionOps(~el, expMxs[r], unip[r], ops);
      end for;
    else
      for term in unip do
        multByUnipTerm( ~el, term, ops );
      end for;
    end if;
  end procedure;
  multByTorus := procedure( ~el, t, ops )
    for i in [1..dim] do
        H := h(i, t[i]);
        for j in [1 .. #H] do
            rightActionOp(~el, <j, H[j]>, 1, ops);
        end for;
    end for;
  end procedure;
  multByWeyl := procedure( ~el, w, ops )
    for r in w do
        rightActionOps(~el, expMxs[r], 1, ops);
        rightActionOps(~el, expMxs[neg(r)], -1, ops);
        rightActionOps(~el, expMxs[r], 1, ops);
    end for;
  end procedure;

  /* K := CoefficientRing(K); */
  f := function( el, ops )
    el := copyelt( el );
    Unnormalise( ~el );
    list := el`List;
    if ops then
        ret := [* *];
    else
        ret := MatrixRing( K, d )!1;
    end if;
    for term in list do
      if Category(term) eq ModTupFldElt then
        multByTorus( ~ret, term, ops );
      elif Category(term) eq Tup and #term eq 2 then
        multByUnipTerm( ~ret, term, ops );
      elif Category(term) eq SeqEnum then
        multByUnip( ~ret, term, ops );
      elif Category(term) eq RngIntElt then
        multByWeyl(~ret, [term], ops);
      elif Category(term) eq GrpLieElt then
        multByUnip( ~ret, term`u, ops );
        multByTorus( ~ret, term`h, ops );
        multByWeyl( ~ret, term`w, ops );
        multByUnip( ~ret, term`up, ops );
      else
        error "Error: Entry in list not allowed";
      end if;
    end for;
    if not ops then
        return GL(d, K)!ret;
    else
        return ret;
    end if;
  end function;
  ret := (isproj) select map< G -> GL(d,K) | x :-> f(x, false) >
                    else hom< G -> GL(d,K) | x :-> f(x, false) >;
  ret`UnderlyingFunction := f;
  ret`ExtendedTorus := D;
  ret`IsProjectiveRepresentation := isproj;
  if isproj then
    ret`ProjectiveKernelPower := r;
  end if;
  
  return ret;
end function;

/*
grpRepnOps := function( G, pos, neg )
  R := RootDatum( G );  N := NumPosRoots( R );
  rtMxs := pos cat neg;
  F := Universe( rtMxs );
  K := PolynomialRing( F ); x := K.1;
  expOps := [ sparseToExpOp( x * R ) : R in rtMxs ];

  d := Nrows( pos[1] );
  k := BaseRing( G );
  M := MatrixRing( k, d );  I := M!1;
  ChangeUniverse( ~expMxs, PolynomialRing(M) );
  dim := Dimension( R );
  neg := func< r | (r le N) select r+N else r-N >;

  x := func< r, t | Evaluate( expMxs[r], t*I ) >;
  n := func< r, t | x(r,t) * x(neg(r),-t^(-1)) * x(r,t) >;
  sdot := func< r | n(r,1) >;
  h := func< i, t | n(i,-1) * n(i,t) >;

  multByUnipTerm := procedure( ~el, term )
    el := el * x( term[1], term[2] );
  end procedure;
  multByUnip := procedure( ~el, unip )
    if ISA( Category( Universe(unip) ), Rng ) then
      for r in [1..#unip] do
        el := el * x(r, unip[r]);
      end for;
    else
      for term in unip do
        multByUnipTerm( ~el, term );
      end for;
    end if;
  end procedure;
  multByTorus := procedure( ~el, t )
    for r in [1..dim] do
      el := el * h(r,t[r]);
    end for;
  end procedure;
  multByWeyl := procedure( ~el, w )
    for r in w do
      el := el * n(r);
    end for;
  end procedure;

  f := function( el )
    Unnormalise( ~el );
    list := el`List;
    ret := MatrixRing( k, d )!1;
    for term in list do
      if Category(term) eq ModTupFldElt then
        multByTorus( ~ret, term );
      elif Category(term) eq Tup and #term eq 2 then
        multByUnipTerm( ~ret, term );
      elif Category(term) eq SeqEnum then
        multByUnip( ~ret, term );
      elif Category(term) eq RngIntElt then
        ret := ret * sdot(term);
      elif Category(term) eq GrpLieElt then
        multByUnip( ~ret, term`u );
        multByTorus( ~ret, term`h );
        multByWeyl( ~ret, term`w );
        multByUnip( ~ret, term`up );
      else
        error "Entry in list not allowed";
      end if;
    end for;
    return ret;
  end function;

  return hom< G -> GL(d,k) | x :-> f(x) >;
end function;




computeElts := function( G )

  R := RootDatum(G);
  N := NumPosRoots(R);
  d := maxMultiplicity(R);
  k := BaseRing(G);
  P<t> := RationalFunctionField( k, 1 );

  // unipotent elements
  lres, d := LieRootElts( R );
  UnipotentElts := [];
  for lre in lres do
    Append( ~UnipotentElts, rowOpExp( [ <op[1], op[2], op[3]*t> : op in lre ] ) );
  end for;
  M := GL( d, P );

  // weyl elements
  WeylElts := [];
  for r in [1..Rank(R)] do
    A := M!1;
    rightActionOps( ~A, UnipotentElts[r],   P!1 );
    rightActionOps( ~A, UnipotentElts[r+N], P!-1 );
    rightActionOps( ~A, UnipotentElts[r],   P!1 );
    Append( ~WeylElts, modularMxToOps(A) );
  end for;

  // torus elements
  TorusElts := [];
  for r in [1..Rank(R)] do
    A := M!1;
    rightActionOps( ~A, UnipotentElts[r],   P!-1 );
    rightActionOps( ~A, UnipotentElts[r+N], P!1 );
    rightActionOps( ~A, UnipotentElts[r],   P!(t-1) );
    rightActionOps( ~A, UnipotentElts[r+N], P!-t^-1 );
    rightActionOps( ~A, UnipotentElts[r],   P!t );
    Append( ~WeylElts, modularMxToOps(A) );
  end for;

  return P, d, UnipotentElts, WeylElts, TorusElts;

end function;

intrinsic StandardRepresentationNew( G::GrpLie ) -> Map
{}
  R := RootDatum( G );  k := BaseRing( G );

  P, d, UnipotentElts, WeylElts, TorusElts := computeElts(G);

  multByUnipTerm := procedure( ~A, term )
    rightActionOps( A, UnipotentElts[term[1]], term[2] );
  end procedure;
  multByUnip := procedure( ~A, unip )
    if ISA( Category( Universe(unip) ), Rng ) then
      for r in [1..#unip] do
        rightActionOps( ~A, UnipotentElts[r], unip[r] );
      end for;
    else
      for term in unip do
        multByUnipTerm( ~A, term );
      end for;
    end if;
  end procedure;
  multByTorus := procedure( ~A, t )
    for r in [1..#t] do
      rightActionOps( ~A, TorusElts[r], t[r] );
    end for;
  end procedure;
  multByWeyl := procedure( ~A, w )
    for r in w do
      rightActionOps( ~A, WeylElts[r], 1 );
    end for;
  end procedure;
  multByLieElt := procedure( ~A, x )
    multByUnip( ~A, x`u );
    multByTorus( ~A, x`h );
    multByWeyl( ~A, x`w );
    multByUnip( ~A, x`up );
  end procedure;

  repn := function( elt )
    A := MatrixRing( k, d )!1;
    if assigned elt`List then
      list := elt`List;
      for term in list do
        if Category(term) eq ModTupFldElt then
          multByTorus( ~A, term );
        elif Category(term) eq Tup and #term eq 2 then
          multByUnipTerm( ~A, term );
        elif Category(term) eq SeqEnum then
          multByUnip( ~A, term );
        elif Category(term) eq RngIntElt then
          multByWeyl( ~A, term );
        elif Category(term) eq GrpLieElt then
          multByLieElt( ~A, term );
        else
          error "Entry in list not allowed";
        end if;
      end for;
    else
      multByLieElt( ~A, elt );
    end if;
    return A;
  end function;

  H := GL( d, k ); //???

  return hom< G -> H | repn >;
end intrinsic;
*/
// -----------------------eof--------------------------

