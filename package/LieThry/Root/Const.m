freeze;

/*
  $Id: Const.m 32949 2011-04-04 04:33:39Z danr $

  Arjeh Cohen, Scott H Murray and D E Taylor

  23 March 2001

  Code to compute and store the constants
  corresponding to given root datum.

  History:
   23 Mar 01
       Split off from RootDtm.m
*/

import "RootDtm.m": computeOrbitReps, toType;
import "Pairs.m":   PairToRoot, RootToPair;
import "../../Algebra/AlgLie/ChevBas/chevbasmain.m":fix_chevbas_scalars;

// ====================================================
//
// The maximum multiplicity of edges in the Dynkin
// diagram.  Several constant computations are easier
// when this constant is 1 or 2.
//
// ====================================================

irredMaxMultiplicity := function( type )
  case type[1]:
  when "I", "i", "I2", "i2":
    return type[3];
  when "H", "h":
    return 5;
  when "G", "g":
    return 3;
  when "B", "b", "C", "c", "F", "f", "BC","bc","Bc","bC":
    return 2;
  else
    return 1;
  end case;
end function;

maxMultiplicity := function( R )
  if not assigned R`MaximumMultiplicity then
    R`MaximumMultiplicity :=
      (#type eq 0 ) select 1 else Max( [ irredMaxMultiplicity(t) : t in type ] )
      where type is toType( R );
  end if;
  return R`MaximumMultiplicity;
end function;




// ====================================================
//
// Coxeter forms
//
// ====================================================

coxeterForms := procedure( ~R )
  coroots := Coroots( R : Basis:="Root" );
  C := CartanMatrix( R );
  n := Rank( R );  d := Dimension(R);  
  K := BaseRing( R );
  V := VectorSpace( K, d );  M := MatrixAlgebra( K, n );

  comps := [ t[2] : t in toType(R) ];

  // Coxeter form
  z := Zero(M);
  for i := 1 to R`NumPosRoots do
    z +:= M![x[j]*x[k] : j,k in [1..n]] where x is coroots[i];
  end for;
  J := C*z*Transpose(C);
  for comp in comps do
    diag := [ J[i,i] : i in comp ];
    if CanChangeUniverse( diag, Integers() ) then
      gcd := Gcd( ChangeUniverse( diag, Integers() ) );
      for i in comp do  for j in comp do
        J[i,j] := J[i,j]/gcd;
      end for;  end for;
    end if;
  end for;
  rootJ := J;
  A := ChangeRing( SimpleRoots(R), K );
  if n ne d then
    A := VerticalJoin( A, BasisMatrix( NullSpace( Transpose(A) ) ) );
    J := DiagonalJoin( J, MatrixAlgebra(K,d-n)!1 );
  end if;
  A := Matrix(A)^-1;
  J := A * J * Transpose(A);
  R`CoxeterForm := J;

  // Dual coxeter form
  dd := DiagonalMatrix(M,[1/rootJ[i,i] : i in [1..n]]);
  J := dd*rootJ*dd;
  diag := [ J[i,i] : i in [1..n] ];
  if CanChangeUniverse( diag, Rationals() ) then
    diag := ChangeUniverse( diag, Rationals() );
    lcm := Lcm( [ Integers() | Denominator( d ) : d in diag ] );
    J := J*lcm;
  end if;
  B := ChangeRing( SimpleCoroots(R), K );
  if n ne d then
    B := VerticalJoin( B, BasisMatrix( NullSpace( Transpose(B) ) ) );
    J := DiagonalJoin( J, MatrixAlgebra(K,d-n)!1 );
  end if;
  B := Matrix(B)^-1;
  J := B * J * Transpose(B);
  R`DualCoxeterForm := J;
end procedure;

formWRTBasis := function( J, B )
  n := Nrows( B );
  B := [ B[i] : i in [1..n] ];
  return Matrix(Rationals(), n,n, [ (v*J,u) : u in B, v in B ] );
end function;

intrinsic CoxeterForm( R::RootSys : Basis := "Standard" ) -> AlgMatElt
{} /* get comment from the next intrinsic */
  if assigned R`CoxeterForm and Basis eq "Standard" then
    return R`CoxeterForm;
  end if;
  coxeterForms( ~R );  J := R`CoxeterForm;
  if Basis eq "Standard" then
    return J;
  elif Basis eq "Root" then
    return formWRTBasis( J, SimpleRoots( R ) );
  elif Basis eq "Weight" then
    error "Weight basis allowed only for root data";
  else
    error "Invalid basis parameter";
  end if;
end intrinsic;

intrinsic CoxeterForm( R::RootDtm : Basis := "Standard" ) -> AlgMatElt
{The Coxeter form of R}
  if assigned R`CoxeterForm and Basis eq "Standard" then
    return R`CoxeterForm;
  end if;
  coxeterForms( ~R );  J := R`CoxeterForm;
  if Basis eq "Standard" then
    return J;
  elif Basis eq "Root" then
    return formWRTBasis( J, ChangeRing( SimpleRoots( R ), BaseRing(R) ) );
  elif Basis eq "Weight" then
    return formWRTBasis( J, FundamentalWeights( R ) );
  else
    error "Invalid basis parameter";
  end if;
end intrinsic;

intrinsic DualCoxeterForm( R::RootSys : Basis := "Standard" ) -> AlgMatElt
{} /* get comment from the next intrinsic */
  if assigned R`DualCoxeterForm and Basis eq "Standard" then
    return R`DualCoxeterForm;
  end if;
  coxeterForms( ~R );  J := R`DualCoxeterForm;
  if Basis eq "Standard" then
    return J;
  elif Basis eq "Root" then
    return formWRTBasis( J, SimpleCoroots( R ) );
  else
    error "Invalid Basis parameter";
  end if;
end intrinsic;

intrinsic DualCoxeterForm( R::RootDtm : Basis := "Standard" ) -> AlgMatElt
{The dual Coxeter form of R}
  if assigned R`DualCoxeterForm and Basis eq "Standard" then
    return R`DualCoxeterForm;
  end if;
  coxeterForms( ~R );  J := R`DualCoxeterForm;
  if Basis eq "Standard" then
    return R`DualCoxeterForm;
  elif Basis eq "Root" then
    return formWRTBasis( J, ChangeRing( SimpleCoroots( R ), BaseRing(R) ) );
  elif Basis eq "Weight" then
    return formWRTBasis( J, FundamentalCoweights( R ) );
  else
    error "Invalid Basis parameter";
  end if;
end intrinsic;



// ====================================================
//
// Root norms
//
// ====================================================

norms := function( R, co )
  if not assigned R`RootNorms then
    F := ISA(Category(R), RootDtm) select BaseRing(R) else BaseField(R);
    n := Rank(R); V := VectorSpace( F, n );
        
    roots := PositiveRoots( R : Basis:="Root" );
    ChangeUniverse( ~roots, V );
    K := CoxeterForm( R : Basis:="Root" );
    norms := [ (v*K,v) : v in roots ];
    R`RootNorms := norms cat norms;  // +ve and -ve

    roots := PositiveCoroots( R : Basis:="Root" );
    ChangeUniverse( ~roots, V );
    K := DualCoxeterForm( R : Basis:="Root" );
    norms := [ (v*K,v) : v in roots ];
    R`CorootNorms := norms cat norms;

  end if;
  return (co) select R`CorootNorms else R`RootNorms;
end function;


intrinsic RootNorms( R::RootStr ) -> []
{The squares of the root lengths of R}
  return norms( R, false );
end intrinsic;
intrinsic CorootNorms( R::RootStr ) -> []
{The squares of the coroot lengths of R}
  return norms( R, true );
end intrinsic;


intrinsic RootNorm( R::RootStr, r::RngIntElt ) -> RngIntElt
{The square of the length of the rth root of R}
  return RootNorms( R )[r];
end intrinsic;
intrinsic CorootNorm( R::RootStr, r::RngIntElt ) -> RngIntElt
{The square of the length of the rth root of R}
  return CorootNorms( R )[r];
end intrinsic;


intrinsic IsLongRoot( R::RootStr, r::RngIntElt ) -> RngIntElt
{True iff the rth root of R is long}
  require IsIrreducible(R) : "For irreducible root data/systems only";
  require IsCrystallographic(R) : "For crystallographic root systems only";
  return RootNorm( R, r ) eq maxMultiplicity( R );
end intrinsic;

intrinsic IsShortRoot( R::RootStr, r::RngIntElt ) -> RngIntElt
{True iff the rth root of R is short}
  require IsIrreducible(R) : "For irreducible root data/systems only";
  require IsCrystallographic(R) : "For crystallographic root systems only";
  return RootNorm( R, r ) eq 1;
end intrinsic;

intrinsic IsIndivisibleRoot( R::RootStr, r::RngIntElt ) -> RngIntElt
{True iff the rth root of R is indivisible}
  require IsIrreducible(R) : "For irreducible root data/systems only";
  require IsCrystallographic(R) : "For crystallographic root systems only";
  return RootNorm( R, r ) le maxMultiplicity( R );
end intrinsic;


// ====================================================
//
// Root strings and sums
//
// ====================================================

// This procedure computes and stores the values of the attributes
// NontrivialPairs, RightStrings, LeftStrings, ExtraspecialPairs
strings := procedure( ~R )
  local i, c;

  N := NumPosRoots( R );  n := Rank( R );
  roots := PositiveRoots( R : Basis := "Root" );
  type  := toType( R );

  // first determine which component each root belongs to
  if #type eq 1 then
    cmps := [ [1..N] ];
  else
    cmps := [ [] : i in [1..#type] ];
    for r in [1..N] do
      _ := exists(i){ i : i in [1..n] | roots[r][i] ne 0 };
      if exists(c){ c : c in [1..#type] | i in type[c][2] } then
        Append( ~cmps[c], r );
      end if;
    end for;
  end if;

  // we store the strings as a short list of long lists, rather
  // than vice versa, because it is more memory efficient.
  l := [Integers()| ];
  pairs := {@@};
  right := [l,l,l,l,l,l,l];  // r+s, 2r+s, r+2s, 3r+s, r+3s, 3r+2s, 2r+3s
  left  := [l,l,l,l,l];      // s-r, s-2r, r-2s, s-3r, r-3s
  paircmps := [];
  esps  := [l,l];
  append := procedure( ~rl, list )
    for i in [1..#rl] do
      t := rl[i];
      rl[i] := l;
      Append( ~t, list[i] );
      rl[i] := t;
    end for;
  end procedure;

  // first we compute sums and differences
  for c in [1..#cmps] do
    cmp := cmps[c];
    for i in [1..#cmp-1] do
      for j in [i..#cmp] do
        r := cmp[i];  s := cmp[j];
        k := Position( roots, roots[r]+roots[s] );
        l := Position( roots, roots[s]-roots[r] );
        if k ne 0 or l ne 0 then
          Include( ~pairs, <r,s> );
          append( ~right, [k,0,0,0,0,0,0] );
          append( ~left,  [l,0,0,0,0] );
          Append( ~paircmps, c );
          if k ne 0 and not IsDefined( esps[1], k-n ) then
            esps[1][k-n] := r;  esps[2][k-n] := s;
          end if;
        end if;
      end for;
    end for;
  end for;

  if maxMultiplicity( R ) eq 1 then
    R`NontrivialPairs   := pairs;
    R`RightStrings      := right;
    R`LeftStrings       := left;
    if ISA(Category(R), RootDtm) then
      R`ExtraspecialPairs := esps;
    end if;
    return;
  end if;

  mults := [ irredMaxMultiplicity( t ) : t in type ];
  // compute right strings
  for i in [#pairs..1 by -1] do
    if mults[ paircmps[i] ] ge 2 and right[1][i] ne 0 then
        r := pairs[i][1];  s := pairs[i][2];  sum := right[1][i];
        k := Position( pairs, <r,sum> );
        if k ne 0 then  right[2][i] := right[1][k];  end if;
        l := Position( pairs, <s,sum> );
        if l ne 0 then  right[3][i] := right[1][l];  end if;
        if mults[ paircmps[i] ] eq 3 and ( k ne 0 or l ne 0 ) then
          v31 := right[2][k];
          if v31 ne 0 then
            right[4][i] := v31;
            m := Position( pairs, <s,v31> );
            right[6][i] := right[1][m];
          end if;
          v13 := right[2][l];
          if v13 ne 0 then
            right[5][i] := v13;
            m := Position( pairs, <r,v13> );
            right[7][i] := right[1][m];
          end if;
        end if;
    end if;
  end for;
  // compute left strings
  Diff := function( r, s ) // returns position of al_r - al_s
    if r lt s and s le N then
      k := Position( pairs, <r,s> );
      return (k ne 0 and left[1][k] ne 0) select left[1][k]+N else 0;
    elif s lt r and r le N then
      k := Position( pairs, <s,r> );
      return (k ne 0) select left[1][k] else 0;
    elif r gt N and s le N then
      r := r-N;  k := Position( pairs, (r lt s) select <r,s> else <s,r> );
      return (k ne 0 and right[1][k] ne 0) select right[1][k]+N else 0;
    end if;
    return 0;
  end function;
  for i in [1..#pairs] do
    if mults[ paircmps[i] ] ge 2 and left[1][i] ne 0 then
      r := pairs[i][1];  s := pairs[i][2];
      d := Diff( left[1][i], r );
      if d ne 0 then
        left[2][i] := d;
        if mults[ paircmps[i] ] eq 3 then  left[4][i] := Diff( d, r );  end if;
      end if;
      d := Diff( left[1][i]+N, s );
      if d ne 0 then
        left[3][i] := d;
        if mults[ paircmps[i] ] eq 3 then  left[5][i] := Diff( d, s );  end if;
      end if;
    end if;
  end for;

  R`NontrivialPairs   := pairs;
  R`RightStrings      := right;
  R`LeftStrings       := left;
  if ISA(Category(R), RootDtm) then
    R`ExtraspecialPairs := esps;
  end if;
end procedure;


sum := function( R, r, s )
  N := NumPosRoots( R );
  if r gt N and s gt N then
    k := Position( R`NontrivialPairs, (r-N lt s-N) select <r-N,s-N> else <s-N,r-N> );
    if k eq 0 or R`RightStrings[1][k] eq 0 then return 0; end if;
    return R`RightStrings[1][k] + N;
  elif r gt N then           // r < 0, s > 0
    if r-N lt s then
      k := Position( R`NontrivialPairs, <r-N,s> );
      if k eq 0 then return 0; end if;
      return R`LeftStrings[1][k];
    else
      k := Position( R`NontrivialPairs, <s,r-N> );
      if k eq 0 or R`LeftStrings[1][k] eq 0 then return 0; end if;
      return (t le N) select t+N else t-N where t := R`LeftStrings[1][k];
    end if;
  elif s gt N then           // r > 0, s < 0
    if r lt s-N then
      k := Position( R`NontrivialPairs, <r,s-N> );
      if k eq 0 or R`LeftStrings[1][k] eq 0 then return 0; end if;
      return (t le N) select t+N else t-N where t := R`LeftStrings[1][k];
    else
      k := Position( R`NontrivialPairs, <s-N,r> );
      if k eq 0 then return 0; end if;
      return R`LeftStrings[1][k];
    end if;
  elif r lt s then          // 0 < r < s
    k := Position( R`NontrivialPairs, <r,s> );
    if k eq 0 then return 0; end if;
    return R`RightStrings[1][k];
  else                      // 0 < s <= r
    k := Position( R`NontrivialPairs, <s,r> );
    if k eq 0 then return 0; end if;
    return R`RightStrings[1][k];
  end if;
end function;

intrinsic Sum( R::RootSys, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The index of the sum of the rth and sth root of R}
  require IsCrystallographic(R) : "For crystallogrphic root data only";
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  requirerange r, 1, 2*N;
  requirerange s, 1, 2*N;
  require (r ne s) or not IsReduced(R) : "Equal roots not allowed for reduced root data";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return sum( R, r, s );
end intrinsic;

intrinsic Sum( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The index of the sum of the rth and sth root of R}
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  requirerange r, 1, 2*N;
  requirerange s, 1, 2*N;
  require (r ne s) or not IsReduced(R) : "Equal roots not allowed for reduced root data";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return sum( R, r, s );
end intrinsic;

forward leftString;

rightString := function( R, N, r, s )
  if r gt N then             // r < 0
    return leftString( R, N, r-N, s );
  elif s gt N then           // r > 0, s < 0
    str := leftString( R, N, r, s-N );
    return [ (t le N) select t+N else t-N : t in str ];
  elif r lt s then           // 0 < r < s
    k := Position( R`NontrivialPairs, <r,s> );
    if k eq 0 then return []; end if;
    M := R`RightStrings;
    return [ t : i in [1,2,4] | t ne 0 where t is M[i,k]];
  else                       // 0 < s <= r
    k := Position( R`NontrivialPairs, <s,r> );
    if k eq 0 then return []; end if;
    M := R`RightStrings;
    return [ t : i in [1,3,5] | t ne 0 where t is M[i,k]];
  end if;
end function;

intrinsic RightString( R::RootSys, r::RngIntElt, s::RngIntElt ) -> []
{} /* use the description of the next intrinsic */
  require IsCrystallographic(R) : "For crystallogrphic root systems only";
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  require (r ne s) or not IsReduced(R) : "Equal roots not allowed for reduced root data";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return rightString( R, N, r, s );
end intrinsic;

intrinsic RightString( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> []
{The right string through the sth root in the direction of the rth root}
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  require (r ne s) or not IsReduced(R) : "Equal roots not allowed for reduced root data";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return rightString( R, N, r, s );
end intrinsic;

leftString := function( R, N, r, s )
  if r gt N then             // r < 0
    return rightString( R, N, r-N, s );
  elif s gt N then           // r > 0, s < 0
    str := rightString( R, N, r, s-N );
    return [ (t le N) select t+N else t-N : t in str ];
  elif r lt s then           // 0 < r < s
    k := Position( R`NontrivialPairs, <r,s> );
    if k eq 0 then return []; end if;
    M := R`LeftStrings;
    return [ t : i in [1,2,4] | t ne 0 where t is M[i,k] ];
  else                       // 0 < s <= r
    k := Position( R`NontrivialPairs, <s,r> );
    if k eq 0 then return []; end if;
    M := R`LeftStrings;
    str := [ M[i,k] : i in [1,3,5] ];
    if str[1] gt N then
      str[1] -:= N;
    elif str[1] eq 0 then
      ;
    else // 0 < str[1] <= N
      str[1] +:= N;
    end if;
    return [ t : t in str | t ne 0 ];
  end if;
end function;

intrinsic LeftString( R::RootSys, r::RngIntElt, s::RngIntElt ) -> []
{} /* use the description of the next intrinsic */
  require IsCrystallographic(R) : "For crystallogrphic root systems only";
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  require (r ne s) : "Equal roots not allowed";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return leftString( R, N, r, s );
end intrinsic;

intrinsic LeftString( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> []
{The left string through the sth root in the direction of the rth root}
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots(R);
  require (r ne s) : "Equal roots not allowed";
  require (r ne s+N) and (r+N ne s) : "Antipodal roots not allowed";
  return leftString( R, N, r, s );
end intrinsic;

intrinsic LieConstant_p( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant p_rs}
  return #LeftString(R, r, s);
end intrinsic;

intrinsic LeftStringLength( R::RootSys, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{} /* use the description of the next intrinsic */
  require IsCrystallographic(R) : "For crystallogrphic root data only";
  return #LeftString(R, r, s);
end intrinsic;                       

intrinsic LeftStringLength( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The length of the left string through the sth root in the direction of the rth root}
  return LieConstant_p(R, r, s);
end intrinsic;                       

intrinsic LieConstant_q( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant q_rs}
  return #RightString(R, r, s);
end intrinsic;

intrinsic RightStringLength( R::RootSys, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{} /* use the description of the next intrinsic */
  require IsCrystallographic(R) : "For crystallogrphic root data only";
  return #RightString(R, r, s);
end intrinsic;                       

intrinsic RightStringLength( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The length of the right string through the sth root in the direction of the rth root}
  return LieConstant_q(R, r, s);
end intrinsic;

cartanInteger := function(R,N,r,s)
  if IsDefined(R`cartanIntegers[r],s) then
    return R`cartanIntegers[r,s];
  end if;

  if r eq s then                // r = s
    R`cartanIntegers[r,s] := 2;
    return 2;   
  end if;
  
  r_gt_N := r gt N;
  s_gt_N := s gt N;
  rs_gt_N := r_gt_N and s_gt_N;

  if rs_gt_N then 
    ;
  elif r_gt_N and r eq s+N          // r = -s
    or s_gt_N and r eq s-N then
    R`cartanIntegers[r,s] := -2;
    return -2;
  end if;

    

  if rs_gt_N then
    rr   := r-N;
    ss   := s-N;
    sign := 1;
  elif r_gt_N then
    rr   := r-N;
    ss   := s;
    sign := -1;
  elif s_gt_N then
    rr   := r;
    ss   := s-N;
    sign := -1;
  else
    rr   := r;
    ss   := s;
    sign := 1;
  end if;

  ci := sign*(#leftString(R,N,ss,rr) - #rightString(R,N,ss,rr));
  R`cartanIntegers[r,s] := ci;
  return ci;

/*
 *   
 *   case r:
 *     when s:         return 2;
 *     when s+N, s-N:  return -2;
 *     else            return #leftString(R,N,s,r) - #rightString(R,N,s,r);
 *   end case;
 */
end function;

intrinsic CartanInteger( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The Cartan integer for the rth and sth roots}
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  N := NumPosRoots( R );
  return cartanInteger(R,N,r,s);
end intrinsic;



intrinsic ExtraspecialPair( R::RootDtm, r::RngIntElt ) -> RngIntElt, RngIntElt
{The minimal pair of positive roots that add up to al_r}
  require IsCrystallographic(R) : "For crystallogrphic root data only";
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  n := Rank(R);
  requirerange r, n+1, NumPosRoots(R);
//  require r gt n and r le NumPosRoots(R) :
//    "r must be the index of a nonsimple positive root";
  return R`ExtraspecialPairs[1][r-n], R`ExtraspecialPairs[2][r-n];
end intrinsic;

intrinsic ExtraspecialPairs( R::RootDtm ) -> SeqEnum
{The extraspecial pairs}
  if not assigned R`LeftStrings then
    strings( ~R );
  end if;
  n := Rank(R);  N := NumPosRoots(R);
  return [ <R`ExtraspecialPairs[1][r-n], R`ExtraspecialPairs[2][r-n]> :
            r in [n+1..N] ];
end intrinsic;
 
intrinsic NumExtraspecialPairs( R::RootDtm ) -> SeqEnum
{The number of extraspecial pairs}
  N := NumPosRoots(R);  n := Rank(R);
  return N-n;
end intrinsic;

// ====================================================
//
// Epsilon and other constants
//
// This can either be done by formula or by determining values
// for the extraspecial elements (ie. all positive nonfundamental roots).
//
// ====================================================

// ----------------------------------------------------
//
// Computing epsilons from extraspecial pairs.
//
// See Howlett, et al,
// Matrix generators for exceptional groups of Lie type

/*
We need to compute $\ep_{\al\be}$ for  $0 < \al < \be$
Write  $\al+\be = \xi = \al'+\be'$  where $(\al',\be')$ is the esp for $\xi$
Write  $\ga_\xi = \ep_{\al'\be'}$.

if $\al'=\al$ then $\ep_{\al\be} = \ep_{\al'\be'} = \ga_\xi$

[ $\al'=\be$ cannot happen since $\al' <= \al < \be$ ]

else

  \ep_{\al\be} = sgn( N_{-\al'\be}N_{\be'\al} / |\be-\al'|  -  N_{-\al'\al}N_{\be'\be} / |\al-\al'| )

                                   t_1                                      t_2

  if \be-\al' = \be'-\al \notin \Phi  then $t_1=0$
  else  \al' minl summand of \xi  ==>  \be-\al'=\be'-\al > 0
  so  t_1 = ( |\be-\al'| N_{\al',\be-\al'} / |\be| ) . ( |\be-\al'| N_{\al',\be'-\al} / |\be'| )  / |\be-\al'|
          = ( |\be-\al'| / (|be||be'|) ) N_{\al',\be-\al'} N_{\al,\be'-\al}
  end if

  ,
  else  \al' minl summand of \xi  ==>  \al-\al'=\be'-\be > 0
  so  t_2 = ( |\al-\al'| N_{\al',\al-\al'} / |\al| ) . ( |\al-\al'| N_{\be,\be'-\be} / |\be'| )  / |\al-\al'|
          = ( |\al-\al'| / (|al||be'|) ) N_{\al',\al-\al'} N_{\be,\be'-\be}
  end if

  We can cancel the 1/|\be'| from t1 and t_2 since we are only interested in the sign
  Modulo reversing some terms, all the Ns that appear here are already known

end if
*/

epsilonsByExtraspecials := procedure( ~R )

  signs := R`ExtraspecialSigns;  
  if (Type(signs) eq SeqEnum) and IsNull(signs) then signs := [Integers()|]; end if;

  N := NumPosRoots(R);  n := Rank(R);
  if N eq 0 then
    R`Epsilons := [];  return;
  end if;

  structConst := function( r, s )
    if r gt s then
      tmp := r;  r := s;  s := tmp;
      e := -1;
    else
      e := 1;
    end if;
    k := Position( R`NontrivialPairs, <r,s> );
    return e * R`Epsilons[k] *
      (#Exclude({R`LeftStrings[i][k] : i in [1,3,5]},0) +1);
  end function;

  if ISA( Category( signs ), RngElt ) then
    signs := [ Parent(signs) | signs : i in [1..N-n] ];
    R`ExtraspecialSigns := signs;
  end if;
  symbolic := Category(Universe( signs )) ne RngInt;  // for computing signs symbolically

  heights := [ Integers() | RootHeight(R,r) : r in [1..N] ];
  esps := R`ExtraspecialPairs;
  norms := RootNorms( R );
  maxheight := Maximum( heights );

  R`Epsilons := [ Universe(signs) | 0 : p in R`NontrivialPairs ];
  for height in [1..maxheight] do
    for h in [1..height] do
      h2 := height - h;

      for r in [ i : i in [1..N] | heights[i] eq h ] do
        for s in [ i : i in [r+1..N] | heights[i] eq h2 ] do
          k := Position( R`NontrivialPairs, <r,s> );
          if k ne 0 then
            sum := R`RightStrings[1][k];
            if sum ne 0 then  // r+s in R
              rp := esps[1][sum-n];  sp := esps[2][sum-n];
              if rp eq r then
                R`Epsilons[k] := signs[sum-n];
              else

                // term 1
                l := Position( R`NontrivialPairs, <rp,s> );
                if l eq 0 or R`LeftStrings[1][l] eq 0 then
                  t1 := 0;
                else
                  smrp := R`LeftStrings[1][l];
                  t1 := ( norms[smrp] / norms[s] ) * structConst( rp, smrp ) * structConst( r, smrp );
                end if;

                // term 2
                l := Position( R`NontrivialPairs, <rp,r> );
                if l eq 0 or R`LeftStrings[1][l] eq 0 then
                  t2 := 0;
                else
                  rmrp := R`LeftStrings[1][l];
                  t2 := ( norms[rmrp] / norms[r] ) * structConst( rp, rmrp ) * structConst( s, rmrp );
                end if;
                if not symbolic then
                  R`Epsilons[k] := signs[sum-n] * Sign( t1-t2 );
		else //This can be used to compute epsilons symbolically
		  if t1 eq 0 then  R`Epsilons[k] := signs[sum-n] * (-t2);
		  elif t2 eq 0 then  R`Epsilons[k] := signs[sum-n] * t1;
		  else error "Sorry cannot compute signs";
		  end if;
		  if R`Epsilons[k] ne 0 then
                    R`Epsilons[k] /:= Abs( 
		      Coefficients(Numerator(R`Epsilons[k]))[1] );
                  end if;
		end if;
              end if;
            end if;
          end if;

        end for;
      end for;

    end for;
  end for;

end procedure;

/* Example of symbolic computation of epsilons:
X := "A";  n := 3;
name := X cat IntegerToString(n);
N := NumPosRoots( name );
k<[del]> := RationalFunctionField( Rationals(), N-n );
R := RootDatum( name : Signs:= del );

strings( ~R );
epsilonsByExtraspecials( ~R : Z:=k );

for s in [1..2*N] do
  printf "%o\t", Root(R,s);
  for r in [1..s] do
    printf "%o\t", LieConstant_epsilon(R,r,s);
  end for;
  printf "\n";
end for;
*/


// ----------------------------------------------------
//
// Computing epsilons from a formula
//
// See Rylands, Formulas for the signs of structure constants
//

structConstB := function(M,roots,r,s) // alpha+beta MUST be a root
  alpha := roots[r];
  beta  := roots[s];
  gamma := alpha+beta;
  delta := Eltseq((alpha-beta)*M);
  alpha := Eltseq(alpha*M);
  beta  := Eltseq(beta*M);
  gamma := Eltseq(gamma*M);
  sa := &+alpha;
  sb := &+beta;
  case sa*sb :
  when  0 :
    if sa eq 0 and sb eq 0 then
      f := (Position(alpha,-1) eq Position(beta,1)) select 1 else -1;
    elif sa eq 1 or sa eq -1 then
      f := -sa;
    elif sb eq 1 or sb eq -1 then
      f := sb; 
    else // one of sa or sb is 2 or -2.
      dab := sa - sb;
      d := Sign(dab);
      i := Position(delta,-d);
      j := Position(delta,dab);
      k := Position(delta,d);
      f := d*Sign(k-i)*Sign(j-k);
    end if;
  when  1 :
    f := 2*sa*Sign(Position(alpha,sa)-Position(beta,sa));
  when -1 :
    f := 2*sa;
  when -2 :
    d := Sign(sa);
    f := d*Sign(Position(delta,d)-Position(delta,2*d));
  when -4 :
    i := Position(gamma,1);
    j := Position(gamma,-1);
    k := Position(delta,sa);
    f := Sign(sa)*Sign(k-i)*Sign(k-j);
  else
    error "This should not happen.  Please email magma-bugs@maths.usyd.edu.au";
  end case;    
  return f;
end function;


// Type C
structConstC := function(M,roots,r,s) // alpha+beta MUST be a root
  alpha := roots[r];
  beta  := roots[s];
  gamma := alpha+beta;
  alpha := Eltseq(alpha*M);
  beta  := Eltseq(beta*M);
  sa := &+Seqset(alpha);
  sb := &+Seqset(beta);
  if sa eq 0 then
    if sb eq 0 then
      f := (Position(alpha,-1) eq Position(beta,1)) select 1 else -1;
    else
      f := &+Seqset(Eltseq(gamma*M));
    end if;        
  elif sb eq 0 then // sa eq 0 has been dealt with
    f := - &+Seqset(Eltseq(gamma*M));
  else // sa and sb are non-zero and have opposite signs
    f := Sign(sa);
  end if;
  return f;
end function;

// the i-th set is the set of root indices j such that eps(i,j) is positive
F4table := [
     { 2, 6, 9, 10, 13, 16, 23 },{ 3, 7, 11, 15, 18, 22 },
     { 4, 6, 8, 10, 12, 17, 20, 21 },{ 13, 15, 17, 19 },
     { 3, 7, 22 },{ 4, 8, 12, 21 },{ 6, 8, 17, 19 },
     { 4, 13, 16, 21 },{ 4, 5, 12 },{ 7, 8, 11, 19 },
     { 4, 16 },{ 7, 10, 13, 19 },{ 5 },{ 4, 7, 16, 18 },
     { 6, 10, 13 },{ 5 },{ 13, 15 },{ 6, 9 },{},{ 9, 11 }];

structSignF := func< M,roots,r,s | // the constant is assumed non-zero
   Position(M,s) in F4table[Position(M,r)] select 1 else -1 >;

G2table := [{ 2, 3, 4 },{ 5 },{},{ 3 }];

structSignG := func< M,roots,r,s | // the constant is assumed non-zero
   Position(M,s) in G2table[Position(M,r)] select 1 else -1 >;

epsilonsByFormula := function( R )

  FrenkelKacMatrix := function(C)
    F := C;
    n := Nrows(C);
    for i := 1 to n do F[i,i] := 1; end for;
    for i := 1 to n-1 do 
      for j := i+1 to n do F[i,j] := 0; end for;
    end for;
    return F;
  end function;

  FK := func<F,roots,r,s |  // Positive roots only
    IsEven(InnerProduct(ChangeRing(roots[r],Integers())*F,ChangeRing(roots[s],Integers()))) select 1 else -1 >;

  roots := PositiveRoots( R : Basis := "Root" );
  pairs := R`NontrivialPairs;
  C := CartanMatrix( R );
  N := NumPosRoots( R ); 
  epsilons := [ 0 : p in pairs ];
  right := R`RightStrings;

  if maxMultiplicity(R) eq 1 then
    M := FrenkelKacMatrix(C);
      for i in [1..#pairs] do
        if right[1][i] ne 0 then
          epsilons[i] := FK(M,roots,pairs[i][1],pairs[i][2]);
        end if;
      end for;
  else
    n := Rank( R );
    type  := toType( R );   

  // first determine which component each pair belongs to
    if #type eq 1 then
      cmps := [ [1..#pairs] ];
    else
      cmps := [ [] : i in [1..#type] ];
      for ind in [1..#pairs] do
        tmp := exists(i){ i : i in [1..n] | roots[pairs[ind][1]][i] ne 0 };
        tmp := exists(c){ c : c in [1..#type] | i in type[c][2] };
        Append( ~cmps[c], ind );
      end for;
    end if;

    for c in [1..#cmps] do
      t := type[c];  
      inds := t[2];  
      cmp := cmps[c];
      tdim := #inds;
      case t[1] :
      // Construct either a Frenkel-Kac or a transition matrix
      // for each component.
      when "A","D","E" :
        M := FrenkelKacMatrix(Matrix(tdim,tdim,[C[inds[i],inds[j]] : 
          i,j in [1..tdim]]));
        fn := FK;
      when "B" :
        M := Zero(RMatrixSpace(Integers(),n,tdim));
        for i := 1 to tdim do M[inds[i],i] := 1; end for;
        for i := 1 to tdim-1 do M[inds[i],i+1] := -1; end for;
        fn := structConstB;
      when "C" :
        M := Zero(RMatrixSpace(Integers(),n,tdim));
        for i := 1 to tdim-1 do 
          M[inds[i],i] := 1;
          M[inds[i],i+1] := -1; 
        end for;
        M[inds[tdim],tdim] := 2;
        fn := structConstC;
      when "F" :
        M := inds; 
        esp :=  ExtraspecialPairs(RootDatum("F4"));
        for i := 1 to #esp do
          Append(~M,Position(roots,roots[M[esp[i][1]]]+roots[M[esp[i][2]]]));
        end for;
        fn := structSignF;
      when "G" :
        M := inds; 
        esp :=  ExtraspecialPairs(RootDatum("G2"));
        for i := 1 to #esp do
          Append(~M,Position(roots,roots[M[esp[i][1]]]+roots[M[esp[i][2]]]));
        end for;
        fn := structSignG;
      else
        error "This should not happen.  Please email magma-bugs@maths.usyd.edu.au";
      end case;
      for i in cmp do
        if right[1][i] ne 0 then
          epsilons[i] := Sign(fn(M,roots,pairs[i][1],pairs[i][2]));
        end if;
      end for;
    end for;
  end if;
  return epsilons;
end function;

// THE DEFAULT SHOULD BE signs := false  ??? boolean ???
computeEpsilons := procedure( ~R )
  if not assigned R`Epsilons then
    if not assigned R`NontrivialPairs then
      strings( ~R );
    end if;
/*
 *     if Category( signs ) eq BoolElt and not signs then   // boolean ???
 *       epsilonsByFormula( ~R );
 *     else
 */
      epsilonsByExtraspecials( ~R );
/*
 *     end if;
 */
  end if;
end procedure;




intrinsic ExtraspecialSigns( R::RootDtm ) -> SeqEnum
{The values of epsilon on the extraspecial pairs of R}
//  return R`ExtraspecialSigns;
  computeEpsilons( ~R );
  pairs := ExtraspecialPairs( R );
  return [ R`Epsilons[Position(R`NontrivialPairs, pair)] : pair in pairs ];
end intrinsic;

// returns r+s, epsilon_r,s and Abs(N_r,s)
epsilonabsN := function( R, r, s )
  N := R`NumPosRoots;

  r_gt_N := r gt N;
  s_gt_N := s gt N;

  if r_gt_N and s_gt_N then
    k := Position( R`NontrivialPairs, (r-N lt s-N) select <r-N,s-N> else <s-N,r-N> );
    if k eq 0 or R`RightStrings[1][k] eq 0 then return 0,0,0; end if;
    t := R`RightStrings[1][k] + N;
  elif r_gt_N then           // r < 0, s > 0
    if r-N lt s then
      k := Position( R`NontrivialPairs, <r-N,s> );
      if k eq 0 then return 0,0,0; end if;
      t := R`LeftStrings[1][k];
    else
      k := Position( R`NontrivialPairs, <s,r-N> );
      if k eq 0 or R`LeftStrings[1][k] eq 0 then return 0,0,0; end if;
      t := (t le N) select t+N else t-N where t := R`LeftStrings[1][k];
    end if;
  elif s_gt_N then           // r > 0, s < 0
    if r lt s-N then
      k := Position( R`NontrivialPairs, <r,s-N> );
      if k eq 0 or R`LeftStrings[1][k] eq 0 then return 0,0,0; end if;
      t := (t le N) select t+N else t-N where t := R`LeftStrings[1][k];
    else
      k := Position( R`NontrivialPairs, <s-N,r> );
      if k eq 0 then return 0,0,0; end if;
      t := R`LeftStrings[1][k];
    end if;
  elif r lt s then          // 0 < r < s
    k := Position( R`NontrivialPairs, <r,s> );
    if k eq 0 then return 0,0,0; end if;
    t := R`RightStrings[1][k];
  else                      // 0 < s < r
    k := Position( R`NontrivialPairs, <s,r> );
    if k eq 0 then return 0,0,0; end if;
    t := R`RightStrings[1][k];
  end if;

  e := 1;
  if s_gt_N then
    if r_gt_N then
      s := s-N;
      r := r-N;
    else
      e := -1;
    end if;
    tmp := r;  r := s;  s := tmp;
  end if;

  // claim: s > 0
  if r gt N then
    if r-N le s then
      // claim: -r < s, and so r < 0 <= r+s < s
      k := Position( R`NontrivialPairs, <r-N,s> );
      if k eq 0 then
        return t,0,0;
      else
        sum := R`LeftStrings[1][k];  // r+s = LS[1][k]
        if sum eq 0 then return t,0,0; end if;
        m := R`RootNorms[sum] / R`RootNorms[s];
        r := r-N;
        s := sum;
      end if;
    else
      // claim: s < -r, and so r < r+s <= 0 < s
      k := Position( R`NontrivialPairs, <s,r-N> );
      if k eq 0 then
        return t,0,0;
      else
        sum := R`LeftStrings[1][k]+N;  // r+s = -LS[1][k]
        if sum eq N then return t,0,0; end if;
        m := R`RootNorms[sum] / R`RootNorms[r];
        r := s;
        s := sum-N;
      end if;
    end if;
  else
    m := 1;
  end if;

  // claim: r, s > 0
  if r lt s then
    k := Position( R`NontrivialPairs, <r,s> );
    if k eq 0 then  return t,0,0;  end if;
    str := [ R`LeftStrings[i][k] : i in [1,2,4] ];
  else
    k := Position( R`NontrivialPairs, <s,r> );  e := -e;
    if k eq 0 then  return t,0,0;  end if;
    str := [ R`LeftStrings[i][k] : i in [1,3,5] ];
  end if;
  if #str eq 0 then // r+s notin Phi
    return 0,0,0;
  else
    return t,  e * R`Epsilons[k],
      Integers() ! ( m * ( #[ r : r in str | r ne 0 ] + 1 ) );
  end if;
end function;


intrinsic LieConstant_epsilon( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant epsilon_rs}
  computeEpsilons( ~R );  _ := RootNorms( R );
  _, epsilon, _ := epsilonabsN( R, r, s );
  return epsilon;
end intrinsic;


intrinsic LieConstant_N( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant N_rs}
  computeEpsilons( ~R );  _ := RootNorms( R );
  _, epsilon, absN := epsilonabsN( R, r, s );
  return epsilon * absN;
end intrinsic;


intrinsic LieConstant_M( R::RootDtm, r::RngIntElt, s::RngIntElt, i::RngIntElt ) -> RngIntElt
{The constant M_rsi}
  computeEpsilons( ~R );  _ := RootNorms( R );
  _, epsilon, absN := epsilonabsN( R, s, r );
  p := absN-1;  string := RightString( R, r, s );
  if i-1 gt #string then
    return 1;
  else
    M := epsilon * Binomial( p + i, i );
    for j in [1..i-1] do
      M *:= LieConstant_epsilon( R, string[j], r );
    end for;
    return M;
  end if;
end intrinsic;

/*
intrinsic LieConstant_C( R::RootDtm, i::RngIntElt, j::RngIntElt,
            r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant C_ijrs}
  computeEpsilons( ~R );
  if   j eq 1 then            return -  LieConstant_M(R,r,s,i);
  elif i eq 1 then            return    LieConstant_M(R,s,r,j);
  elif i eq 3 and j eq 2 then return -2*LieConstant_M(R,Sum(R,r,s),r,2) div 3;
  elif i eq 2 and j eq 3 then return -  LieConstant_M(R,Sum(R,r,s),s,2) div 3;
  else return 0;
  end if;
end intrinsic;
*/

// This is a version of the above code and does not depend on
// computing the M-constants.  Seems a bit faster but has little
// effect on the speed of multiplication of random elements

intrinsic LieConstant_C( R::RootDtm, i::RngIntElt, j::RngIntElt,
            r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant C_ijrs}
  computeEpsilons( ~R );
  if i eq 1 and j eq 1 then return LieConstant_N(R,r,s); end if;
  roots := Roots(R : Basis := "Root");
  alpha := roots[r];
  beta  := roots[s];
  gamma := alpha+beta;
  t := Position(roots,gamma);         if t eq 0 then return 0; end if;
  if i eq 1 and j eq 2 then
    return LieConstant_N(R,r,s)*LieConstant_N(R,t,s) div 2;
  elif i eq 2 and j eq 1 then
    return LieConstant_N(R,r,s)*LieConstant_N(R,t,r) div 2;
  elif i eq 1 and j eq 3 then
    u := Position(roots,gamma+beta);  if u eq 0 then return 0; end if;
    return LieConstant_N(R,r,s)*LieConstant_N(R,t,s)*LieConstant_N(R,u,s) div 6;
  elif i eq 3 and j eq 1 then
    u := Position(roots,gamma+alpha); if u eq 0 then return 0; end if;
    return LieConstant_N(R,r,s)*LieConstant_N(R,t,r)*LieConstant_N(R,u,r) div 6;
  elif i eq 2 and j eq 3 then
    u := Position(roots,gamma+beta);  if u eq 0 then return 0; end if;
    return -LieConstant_N(R,s,t)*LieConstant_N(R,u,t) div 6;
  elif i eq 3 and j eq 2 then
    u := Position(roots,gamma+alpha); if u eq 0 then return 0; end if;
    return -LieConstant_N(R,r,t)*LieConstant_N(R,u,t) div 3;
  else return 0;
  end if;
end intrinsic;

function lie_eta(R,r,s)

  if IsDefined(R`LieConstant_eta[r],s) then
    return R`LieConstant_eta[r,s];
  end if;
  
  N := NumPosRoots(R);
  
  if (r eq s) or (r eq s+N) or (r+N eq s) then 
    R`LieConstant_eta[r,s] := -1; 
  else
    computeEpsilons( ~R );
    Lstring := leftString( R, N, r, s );   p := #Lstring;
    Rstring := rightString( R, N, r, s );  q := #Rstring;
    if p eq 0 and q eq 0 then 
      R`LieConstant_eta[r,s] :=  1; 
    elif p eq q then 
      R`LieConstant_eta[r,s] := -1; 
    else
      string := Reverse( Lstring ) cat [s] cat Rstring;

      R`LieConstant_eta[r,s] := 
        IsEven(p + Multiplicity({*LieConstant_epsilon( R, string[i], r ) 
                     : i in [Min(p,q)+1..Max(p,q)]*}, -1)
        ) select  1 
            else -1 ;
    end if;
  end if;
/*
  eta := (-1)^p;  pq := Sort( [ p, q ] );
  for i in [ pq[1]..pq[2]-1 ] do
    eta *:= LieConstant_epsilon( R, string[i+1], r );
  end for;
*/
// The changes give a speed up of about 50% for some constants,
// but not much effect on multiplication.
  return R`LieConstant_eta[r,s];
end function;

intrinsic LieConstant_eta( R::RootDtm, r::RngIntElt, s::RngIntElt ) -> RngIntElt
{The constant eta_rs}
  return lie_eta(R,r,s);
end intrinsic;

//
//  This function returns the information needed for a
//  commutator relation:  a sequence of tuples < i, j, t, c > with
//    i*al_r + j*al_s = al_t,  and
//    c = C_{rsij}
//  and ordered with respect to t. 
//
multiplicationData := function( R, r, s )
  data:= [Parent(<1,1,1,1>)|];
  if r eq s then 
      return data;
  end if;

  case Category(R):
  when RootDtm:
    if IsDefined(R`multiplicationData[r],s) then
      return R`multiplicationData[r,s];
    end if;

    m := maxMultiplicity( R );

    computeEpsilons( ~R );  _ := RootNorms( R );
    if m eq 1 then
      sum, eps := epsilonabsN( R, r, s );
      R`multiplicationData[r,s] := ((sum eq 0) select [] else [ <1,1,sum,eps> ]);
    else
      alr := Root(R,r);  als := Root(R,s);
      for i,j in [1..m] do
        t := RootPosition( R , i*alr+j*als );
        if t ne 0 then
          Append( ~data, <i,j,t,LieConstant_C(R,i,j,r,s)> );
        end if;
      end for;
      Sort( ~data, func<x,y|x[3]-y[3]> );
      R`multiplicationData[r,s] := data;
    end if;
    return R`multiplicationData[r,s];

  when RootDtmSprs:
    X := R`Type[1][1];
    n := Rank(R);
    m := maxMultiplicity( R );
    N := NumPosRoots(R);

    rp := InternalGrpLieIndex2Pair(X,n,r,N);
    sp := InternalGrpLieIndex2Pair(X,n,s,N);
    
    if m eq 1 then
        sum := InternalGrpLiePairSum(X,n,rp,sp);
        if sum eq <0,0> then 
            return data;
        else
            return [ <1,1,InternalGrpLiePair2Index(X,n,sum,N),InternalGrpLiePairEpsilon( X,n, R`ExtraspecialSigns, rp,sp, N )> ];
        end if;
    else /* m eq 2 */
        tp := InternalGrpLiePairSum(X,n,rp,sp);
        if tp eq <0,0> then 
            return data;
        else
            Append( ~data, <1,1,InternalGrpLiePair2Index(X,n,tp,N),LieConstant_C(R,1,1,rp,sp)> );
        end if;
        sum := tp;
        tp := InternalGrpLiePairSum(X,n,sum,rp);
        if tp ne <0,0> then
            Append( ~data, <2,1,InternalGrpLiePair2Index(X,n,tp,N),LieConstant_C(R,2,1,rp,sp)> );
        else
            tp := InternalGrpLiePairSum(X,n,sum,sp);
            if tp ne <0,0> then
                Append( ~data, <1,2,InternalGrpLiePair2Index(X,n,tp,N),LieConstant_C(R,1,2,rp,sp)> );
            end if;
        end if;
        Sort( ~data, func<x,y|x[3]-y[3]> );
        return data;
    end if;

  end case;
  
end function;

intrinsic InternalGrpLieMultData( R::RootDtm, r::RngIntElt, s::RngIntElt )
{internal}
    /*
    **   This intrinsic is called from C level collection code.
    */
    _ := multiplicationData( R, r, s ); 
end intrinsic;

// ====================================================
//
// Lie algebras
//
// ====================================================

/*
  Computing the structure constants of the corrresponding Lie algebra:
  Basis    x_r, for al_r a root;  h_i, for i in [1..d].
  Relations   [h_i, h_j] = 0
              [x_r, h_i] = c_i x_r,      where al_r   = \sum c_i e_i
              [x_-r,x_r] = \sum d_i h_i  where al_r^* = \sum d_i f_i
              [x_r, x_s] = { N_rs x_t    if al_t = al_r + al_s
                           { 0           if al_r + al+s not a root
*/

// Indices for x_r, x_-r, and h_i
posnegcar := function( N, dim )
  return func< r | N+dim+r >,    // x_r
         func< r | N-r+1 >,      // x_-r
         func< i | N+i >;        // h_i
end function;


intrinsic StructureConstants( R::RootDtm ) -> SeqEnum
{The structure constants for the integral Lie algebra of R}

  computeEpsilons( ~R );
  N := NumPosRoots(R);  rank := Rank(R);  dim := Dimension(R);
  n := 2*N + dim;
  pos, neg, cart := posnegcar( N, dim );
  Z := Integers();
  Q := Rationals();
  T := [CartesianProduct(<Z,Z,Z,Q>)|];

  // [x_r, x_s] = N_rs x_t
  for i in [1..#R`NontrivialPairs] do
    if R`RightStrings[1][i] ne 0 then
      r := R`NontrivialPairs[i][1];
      s := R`NontrivialPairs[i][2];
      sum := R`RightStrings[1][i];
      eps := R`Epsilons[i];
      str := [ R`LeftStrings[j][i] : j in [1,2,4] ];
      p := #[ t : t in str | t ne 0 ];
      str := [ R`RightStrings[j][i] : j in [1,2,4] ];
      q := #[ t : t in str | t ne 0 ];
      str := [ R`RightStrings[j][i] : j in [1,3,5] ];
      qrev := #[ t : t in str | t ne 0 ];
      e := eps*(p+1);  f := eps*q;  g := eps*qrev;

      Append( ~T, <pos(r), pos(s), pos(sum),  e> );
      Append( ~T, <pos(s), pos(r), pos(sum), -e> );
      Append( ~T, <neg(r), neg(s), neg(sum), -e> );
      Append( ~T, <neg(s), neg(r), neg(sum),  e> );

      Append( ~T, <pos(s), neg(sum), neg(r),  g> );
      Append( ~T, <neg(sum), pos(s), neg(r), -g> );
      Append( ~T, <pos(sum), neg(s), pos(r),  g> );
      Append( ~T, <neg(s), pos(sum), pos(r), -g> );

      Append( ~T, <pos(r), neg(sum), neg(s), -f> );
      Append( ~T, <neg(sum), pos(r), neg(s),  f> );
      Append( ~T, <pos(sum), neg(r), pos(s), -f> );
      Append( ~T, <neg(r), pos(sum), pos(s),  f> );
    end if;
  end for;

  roots   := PositiveRoots( R );
  coroots := PositiveCoroots( R );
  for r in [1..N] do
    for i in [1..dim] do
      // [x_-r,x_r] = \sum d_i h_i  where al_r^* = \sum d_i f_i
      if coroots[r][i] ne 0 then
        e := coroots[r][i];
        Append( ~T, <neg(r), pos(r), cart(i),  e> );
        Append( ~T, <pos(r), neg(r), cart(i), -e> );
      end if;

      // [x_r, h_i] = c_i x_r,      where al_r   = \sum c_i e_i
      if roots[r][i] ne 0 then
        c := roots[r][i];
        Append( ~T, <pos(r), cart(i), pos(r),  c> );
        Append( ~T, <neg(r), cart(i), neg(r), -c> );
        Append( ~T, <cart(i), pos(r), pos(r), -c> );
        Append( ~T, <cart(i), neg(r), neg(r),  c> );
      end if;
    end for;
  end for;
  return T, n;
end intrinsic;

intrinsic LieAlgebra( R::RootDtm, k::Rng ) -> AlgLie
{The Lie algebra of R over k}
  require IsReduced(R) : "Root datum is not reduced";

  if IsTwisted(R) then
    L := TwistedLieAlgebra(R, k);
    return L;
  end if;

  require IsSplit(R) : "Root datum is not split";  // should not be needed

  T, dim := StructureConstants( R );
  if dim eq 0 then
    L := LieAlgebra< k, dim | >;
  else
    L := LieAlgebra< k, dim | T : Rep := "Sparse", Check := false >;
  end if;
  N := NumPosRoots( R );  d := Dimension( R );  n := Rank( R );
 
  // construct standard and Chevalley bases
  pos, neg, cart := posnegcar( N, d );
  B := SimpleCoroots( R );
  cartElt := func< i | &+[ B[i,j] * L.cart(j) : j in [1..d] ] >;
  posL := [ L.pos(r) : r in [1..N] ];
  negL := [ L.neg(r) : r in [1..N] ];
  cartStd := [ L.cart(i) : i in [1..d] ];
  L`StandardBasis := [* posL, negL, cartStd *];

  if ISA( Category(k), Fld ) then
	/* Assign Chevalley basis */
    L`ChevalleyBasis := [* posL, negL, cartStd *];

	/* Assign Cartan subalgebra (if char. 0), split maximal toral subalg (always) */
    H := sub< L | cartStd >;
	L`SplitMaximalToralSubalgebra := H;
    if Characteristic( k ) eq 0 then
       L`SplittingCartanSubalgebra := H;
       L`CartanSubalgebra := H;
     end if;
  end if;
  L`RootSystem := [* [ rts[r] : r in [1..2*N] ],  posL cat negL,
     [ V | S[i] : i in [1..n] ],  CartanMatrix(R) *]
     where rts is Roots(R) 
     where S is SimpleRoots(R) 
     where V is RSpace( Rationals(), d );
  L`RootDatum := R;
  if ISA( Category(k), Fld ) then
    L`IsReductive := true;
    L`IsSemisimple := (n eq d);
  end if;
  
  // p-map
  if ISA( Category(k), Fld ) then
    L`IsRestrictable := true;
    p := Characteristic( k );
    if p eq 0 then
      L`PImages := Basis( L );
    elif p gt maxMultiplicity( R ) then
      L`PImages := [ L!0 : r in [1..N] ] cat [ L.(N+i) : i in [1..d] ]
        cat [ L!0 : r in [1..N] ];
    else
      ad := AdjointRepresentation( L );
      M := Codomain( ad );
      L`PImages := [ (i in [N+1..N+d]) select 
        L.i else ( M!(Matrix(ad(L.i))^p) )@@ad : i in [1..2*N+d] ];
    end if;
  end if;
    
  return L;
end intrinsic;

intrinsic MatrixLieAlgebra( R::RootDtm, k::Rng ) -> AlgMatLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( R, k ) ) );
end intrinsic;


intrinsic ReductiveLieAlgebraOld( R::RootDtm, k::Rng ) -> AlgLie
{The Lie algebra of R over k}
  return LieAlgebra( R, k );
end intrinsic;
intrinsic ReductiveMatrixLieAlgebraOld( R::RootDtm, k::Rng ) -> AlgMatLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( R, k ) ) );
end intrinsic;

intrinsic LieAlgebra( R::RootSys, k::Rng ) -> AlgLie
{The Lie algebra of R over k}
  require IsReduced( R )          : "The root system must be reduced";
  require IsCrystallographic( R ) : "The root system must be crystallographic";
  L := LieAlgebra( RootDatum( R ), k );
  return L;
end intrinsic;
intrinsic MatrixLieAlgebra( R::RootSys, k::Rng ) -> AlgMatLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( R, k ) ) );
end intrinsic;

intrinsic SemisimpleLieAlgebraOld( R::RootSys, k::Rng ) -> AlgLie
{The Lie algebra of R over k}
  return LieAlgebra( R, k );
end intrinsic;
intrinsic SemisimpleMatrixLieAlgebraOld( R::RootSys, k::Rng ) -> AlgMatLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( R, k ) ) );
end intrinsic;

// NB: Isogeny not documented
intrinsic LieAlgebra( N::MonStgElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The semisimple Lie algebra with Cartan name N over k}
  return LieAlgebra( RootDatum(N:Isogeny:=Isogeny), k );
end intrinsic;
intrinsic MatrixLieAlgebra( N::MonStgElt, k::Rng : Isogeny:="Ad" ) -> AlgMatLie
{The matrix Lie algebra with Cartan name N over k}
  return Image( StandardRepresentation( LieAlgebra( N, k ) ) );
end intrinsic;

intrinsic LieAlgebra( C::AlgMatElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The semisimple Lie algebra with Cartan matrix C over k}
  return LieAlgebra( RootDatum(C:Isogeny:=Isogeny), k );
end intrinsic;
intrinsic MatrixLieAlgebra( C::AlgMatElt, k::Rng : Isogeny:="Ad" ) -> AlgMatLie
{The matrix Lie algebra of with Cartan matrix C over k}
  return Image( StandardRepresentation( LieAlgebra( C, k ) ) );
end intrinsic;

intrinsic LieAlgebra( D::GrphDir, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The semisimple Lie algebra with Dynkin digraph D over k}
  return LieAlgebra( RootDatum(D:Isogeny:=Isogeny), k );
end intrinsic;
intrinsic MatrixLieAlgebra( D::GrphDir, k::Rng : Isogeny:="Ad" ) -> AlgMatLie
{The matrix Lie algebra of with Dynkin digraph D over k}
  return Image( StandardRepresentation( LieAlgebra( D, k ) ) );
end intrinsic;

intrinsic ReductiveLieAlgebraOld( N::MonStgElt, k::Rng : Isogeny:="Ad") -> AlgLie
{The Lie algebra of R over k}
  return LieAlgebra( N, k );
end intrinsic;
intrinsic ReductiveMatrixLieAlgebraOld( N::MonStgElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( N, k ) ) );
end intrinsic;

intrinsic SemisimpleLieAlgebraOld( N::MonStgElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The semisimple Lie algebra with Cartan name N over k}
  return LieAlgebra( RootDatum(N:Isogeny:=Isogeny), k );
end intrinsic;
intrinsic SemisimpleMatrixLieAlgebraOld( N::MonStgElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( N, k ) ) );
end intrinsic;

intrinsic SimpleLieAlgebraOld( X::MonStgElt, n::RngIntElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The simple Lie algebra with Cartan name X_n}
  return LieAlgebra( IrreducibleRootDatum( X, n : Isogeny:=Isogeny ), k );
end intrinsic;
intrinsic SimpleMatrixLieAlgebraOld( X::MonStgElt, n::RngIntElt, k::Rng : Isogeny:="Ad" ) -> AlgLie
{The matrix Lie algebra of R over k}
  return Image( StandardRepresentation( LieAlgebra( X cat IntegerToString(n), k ) ) );
end intrinsic;

intrinsic RightAdjointMatrix( L::AlgLie, x::AlgLieElt ) -> AlgMatLieElt
{The matrix for the right adjoint action of x on L}
  require x in L : "The element is not in the Lie algebra";
  d := Dimension(L);  k := BaseRing(L);
  return MatrixLieAlgebra(k,d)![ RSpace(k,d) | L.i*x : i in [1..d] ];
end intrinsic;

intrinsic ChangeRingAlgLie( L::AlgLie, R::Rng ) -> AlgLie
{Internal}
  M := ChangeRing( L, R );  S := BaseRing( L );
  if ISA( Category(R), Fld ) and Category(S) eq Category(R) and S subset R then
    if assigned L`SemisimpleType then
      M`SemisimpleType := L`SemisimpleType;
    end if;
    if assigned L`RootDatum then
      M`RootDatum := L`RootDatum;
    end if;
    if assigned L`IsReductive then
      M`IsReductive := L`IsReductive;
    end if;
    if assigned L`IsSemisimple then
      M`IsSemisimple := L`IsSemisimple;
    end if;
    if assigned L`RootSystem then
      RS := L`RootSystem;
      M`RootSystem :=  [* RS[1], [ M | Eltseq(x) : x in RS[2] ],
        [ ChangeRing( s, R ) : s in RS[3] ],  ChangeRing( RS[4], R ) *];
    end if;
  end if;
  return M;
end intrinsic; 
    

// --------------------- eof --------------------------



