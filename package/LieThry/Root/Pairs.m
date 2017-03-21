freeze;

// 
//  Pairs.m
//
//  $Id: Pairs.m 18797 2008-11-29 07:51:42Z murray $
// 
//  Code for computing with classical root systems with roots represented by
//  pairs.
//
//  Note that we assume all root data are classical and irreducible.
//
//  <i,j> is identified with <-j,-i>
//  the negative of <i,j> is <-i,-j>=<j,i>
//
//  Pairs are kept normalised with the rule:
//    1. Make i > 0 if possible.
//    2. Make Abs(i) < Abs(j) if this does not conflict with (1).
//
//  (Co)roots are constructed wrt the Root basis
//

import "../Root/Cartan.m" : numPosRootsOfType;
Pair_Parent := car<IntegerRing(), IntegerRing()>;

// ===================================================================
//
//  Creation and conversion functions
//

numPosRoots := func< X, n | numPosRootsOfType( [* <X,[1..n]> *] ) >;

poszero := func< i | i ge 0 >;
/*
 * replaced by C-level InternalGrpLiePairNormalise
 * 
 * Pair_Normalise := function( X, n, t )
 *   i := t[1];  j := t[2];
 *   if Sign(i) eq Sign(j) or j eq 0 then
 *     return (Sign(i) eq 1) select t else <-j,-i>;
 *   elif i eq 0 then
 *     return (Sign(j) eq 1) select t else <-j,-i>;
 *   else
 *     return (Abs(i) le Abs(j)) select t else <-j,-i>;
 *   end if;
 * end function;
 */

/*
 * replaced by C-level InternalGrpLiePairIsNegative
 * 
 * Pair_IsNegative := func< X, n, t | (Sign(t[1]) eq Sign(t[2]))
 *   select (t[1] ge t[2]) else (t[1] le 0) >;
 */

/*
 * replaced by C-level InternalGrpLiePairNegative
 * 
 * Pair_Negative := func< X, n, t | (poszero(t[1]) eq poszero(t[2])) 
 *   select <t[2],t[1]> else <-t[1],-t[2]> >;
 */

// this can be used to check if a (normalised) pair is a valid pair
Pair_Check := function( X, n, t )
  // assume normalised
  if InternalGrpLiePairIsNegative(X,n,t) then
    return $$(X,n,InternalGrpLiePairNegative(X,n,t));
  end if;
  i,j := Explode(t);
  if j eq 0 then 
    return X eq "B" and i in [1..n];
  elif j in [2..n] then
    return i in [1..j-1];
  elif j eq n+1 then
    return X eq "A" and i in [1..j-1];
  elif j in [-n..-1] then
    return X eq "C"       and i in [1..-j] 
        or X in ["B","D"] and i in [1..-j-1];
  else
    return false;
  end if;
end function;



RootToPairDO := function( X, n, v )
  case X :
  when "A" :
    _ := exists(i){ i : i in [1..n] | v[i] ne 0 };
    _ := exists(j){ j : j in [n..1 by -1] | v[j] ne 0 };
    return (v[i] eq 1) select <i,j+1> else <j+1,i>;
  when "B" :
    _ := exists(i){ i : i in [1..n] | v[i] ne 0 };
    _ := exists(j){ j : j in [n..1 by -1] | v[j] ne 0 };
    if j eq n then
      if exists(k){ k : k in [i..n] | v[k] notin {0,1,-1} } then
        return (v[i] eq 1) select <i,-k> else <-i,k>;
      else
        return (v[i] eq 1) select <i,0> else <0,i>;
      end if;
    else
      return (v[i] eq 1) select <i,j+1> else <j+1,i>;
    end if;
  when "C" :
    _ := exists(i){ i : i in [1..n] | v[i] ne 0 };
    _ := exists(j){ j : j in [n..1 by -1] | v[j] ne 0 };
    if j eq n then
      if exists(k){ k : k in [i..n] | v[k] notin {0,1,-1} } then
        return (v[i] gt 0) select <i,-k> else 
	  ((i eq k) select <-i,i> else <-i,k>);
      else
        return (v[i] eq 1) select <i,-n> else 
	  ((i eq n) select <-n,n> else <-i,n>);
      end if;
    else
      return (v[i] eq 1) select <i,j+1> else <j+1,i>;
    end if;
  when "D" :
    _ := exists(i){ i : i in [1..n] | v[i] ne 0 };
    _ := exists(j){ j : j in [n..1 by -1] | v[j] ne 0 };
    if j eq n then
      if i eq n then
        return (v[i] eq 1) select <n-1,-n> else <-n+1,n>;
      elif exists(k){ k : k in [i..n] | v[k] notin {0,1,-1} } then
        return (v[i] eq 1) select <i,-k> else <-i,k>;
      elif v[n-1] eq 0 then
        return (v[i] eq 1) select <i,-n> else <-i,n>;
      else
        return (v[i] eq 1) select <i,-n+1> else <-i,n-1>;
      end if;
    else
      return (v[i] eq 1) select <i,j+1> else <j+1,i>;
    end if;
  end case;
end function; 

forward PairToRoot;
RootToPair := function( X, n, v )
    t := RootToPairDO( X, n, v );
    return v eq PairToRoot(X,n,t) select t else <0,0>;
end function; 

CorootToPairDO := function( X, n, v )
  case X :
  when "A", "D" :
    return RootToPair( X, n, v );
  when "B" :
    t := RootToPair( "C", n, v );
    if t[2] eq -t[1] then
      t[2] := 0;
    end if;
    return t;
  when "C" :
    t := RootToPair( "B", n, v );
    if t[2] eq 0 then
      t[2] := -t[1];
    end if;
    return t;
  end case;
end function; 

forward PairToCoroot;
CorootToPair := function( X, n, v )
    t := CorootToPairDO( X, n, v );
    return v eq PairToCoroot(X,n,t) select t else <0,0>;
end function; 




PairToRoot := function( X, n, t )  /* : OutBasis:="Standard" ) */
  neg := InternalGrpLiePairIsNegative(X,n,t);
  if neg then  t := InternalGrpLiePairNegative(X,n,t);  end if;
  if t[2] gt 0 then
    v := Vector( [0:i in [1..t[1]-1]] cat [1:i in [t[1]..t[2]-1]] cat 
      [0: i in [t[2]..n]] );
  else
    case X :
    when "B" :
      if t[2] eq 0 then  t[2] := n+1;  end if;
      v := Vector( [0:i in [1..t[1]-1]] cat [1:i in [t[1]..Abs(t[2])-1]] cat
        [2: i in [Abs(t[2])..n]] );
    when "C" :
      v := Vector( [0:i in [1..t[1]-1]] cat [1:i in [t[1]..Abs(t[2])-1]] cat 
        [2: i in [Abs(t[2])..n-1]] cat [1] );
    when "D" :
      if t[2] eq -n then
        v := Vector( [0:i in [1..t[1]-1]] cat [1:i in [t[1]..n-2]] cat [0,1] );
      else
        v := Vector( [0:i in [1..t[1]-1]] cat [1:i in [t[1]..Abs(t[2])-1]] cat
          [2: i in [Abs(t[2])..n-2]] cat [1,1] );
      end if;
    end case;
  end if;
  v := ChangeRing( v, Rationals() );
  return neg select -v else v;
end function;

PairToCoroot := function( X, n, t )
  if InternalGrpLiePairIsNegative(X,n,t) then
    return -$$(X,n,InternalGrpLiePairNegative(X,n,t));
  end if;
  case X :
  when "A", "D" :
    return PairToRoot( X, n, t );
  when "B" :
    if t[2] eq 0 then
      t[2] := -t[1];
    end if;
    return PairToRoot( "C", n, t );
  when "C" :
    if t[2] eq -t[1] then
      t[2] := 0;
    end if;
    return PairToRoot( "B", n, t );
  end case;
end function;




/* TEST for PairToIndex:

    for X in ["A","B","C","D"], n in [10,20] do
      R := SparseRootDatum(Sprintf("%o%o",X,n));
      N := NumPosRoots(R);
      rts := [1..N];
      prs := [InternalGrpLieIndex2Pair(X,n,r,N):r in rts];
      [ InternalGrpLiePair2Index(X,n,p,N) : p in prs ] eq rts;
    end for;

    for X in ["A","B","C","D"], n in [4..30] do
      R := SparseRootDatum(Sprintf("%o%o",X,n));
      N := NumPosRoots(R);
      rts := [1..N];
      prs := [InternalGrpLieIndex2Pair(X,n,r,N):r in rts];
      X,n, [ InternalGrpLiePair2Index(X,n,p,N) : p in prs ] eq rts;
    end for;

*/

/*  !!  PairToIndex is time critical                          */
/*  !!  please use Pair_Check and InternalGrpLiePairNormalise */
/*  !!  before calling it if at all necessary                 */

/* AND try to use InternalGrpLiePair2Index */

/*
 * replaced by C level InternalGrpLiePair2Index(X,n,r,N);
 * 
 * PairToIndex := function( X, n, t )
 *   // t := InternalGrpLiePairNormalise(X,n,t);
 *   // assert Pair_Check(X,n,t);
 *   return InternalGrpLiePair2Index(X,n,t,numPosRoots(X,n));
 * end function;
 * 
 */


/*
 * replaced by C level InternalGrpLieIndex2Pair(X,n,r,N);
 * 
 * IndexToPair := function(X,n,r,N)
 *     return InternalGrpLieIndex2Pair(X,n,r,N);
 * end function;
 */

/*
    time
    for n in [4..17], X in ["A","B","C","D"] do
      N := NumPosRoots( Sprintf("%o%o",X,n) );
      for i in [1..N] do
        if InternalGrpLieIndex2Pair(X,n,i,N) cmpeq 0 then
          error X,n,i;
        end if;
      end for;
    end for;
*/

// ===================================================================
//
//  Root orderings
//

// all the roots in the standard order by height
Pair_Roots := function( X, n )
  pos := [];  neg := [];
  case X :
  when "A" :
    for h in [1..n] do
      pos cat:= [ <i,i+h> : i in [1..n-h+1] ];
      neg cat:= [ <i+h,i> : i in [1..n-h+1] ];
    end for;
  when "B" :
    for h in [1..2*n-1] do
      pos cat:= [ <i,i+h> : i in [1..n-h] ];
      neg cat:= [ <i+h,i> : i in [1..n-h] ];
      if h le n then 
        Append( ~pos, <n-h+1,0> );
        Append( ~neg, <0,n-h+1> );
      end if;
      pos cat:= [ <i,-(2*n-h+2-i)> : i in [Max(1,n-h+2)..n-(h div 2)] ];
      neg cat:= [ <-i,(2*n-h+2-i)> : i in [Max(1,n-h+2)..n-(h div 2)] ];
    end for;
  when "C" :
    for h in [1..2*n-1] do
      pos cat:= [ <i,i+h> : i in [1..n-h] ];
      neg cat:= [ <i+h,i> : i in [1..n-h] ];
      pos cat:= [ <i-1,-(2*n-h+2-i)> : i in [Max(2,n-h+2)..n-(h div 2)+1] ];
      neg cat:= [ <-i+1,(2*n-h+2-i)> : i in [Max(2,n-h+2)..n-(h div 2)+1] ];
    end for;
   when "D" :
    for h in [1..2*n-1] do
      pos cat:= [ <i,i+h> : i in [1..n-h] ];
      neg cat:= [ <i+h,i> : i in [1..n-h] ];
      h1 := h+1;
      pos cat:= [ <i-1,-(2*n-h1+2-i)> : i in [Max(2,n-h1+2)..n-(h1 div 2)+1-(h1 mod 2)] ];
      neg cat:= [ <-i+1,(2*n-h1+2-i)> : i in [Max(2,n-h1+2)..n-(h1 div 2)+1-(h1 mod 2)] ];
    end for;
  end case;
  return pos cat neg;
end function;

// the positive roots in weight order
Pair_WeightOrder := function( X, n )
  roots := [];
  if X eq "A" then  n+:=1;  end if;
  for i in [1..n] do
    roots cat:= [ <i,j> : j in [i+1..n] ];
    if X eq "B" then
      Append( ~roots, <i,0> );
    end if;
    if X ne "A" then
      roots cat:= [ <i,-j> : j in [n..i+1 by -1] ];
    end if;
    if X eq "C" then
      Append( ~roots, <i,-i> );
    end if;
  end for;
  return roots;
end function;



// ===================================================================
//
//  Sums and strings
//

// isPositive and negative are in the previous section

/*
 * replaced by C-level InternalGrpLiePairSum
 * 
 * Pair_Sum := function( X, n, t, u )
 *   if <0,0> in {t,u} then return <0,0>; end if;
 *   if   t[2] eq u[1]  then sum := <t[1],u[2]>;
 *   elif t[1] eq u[2]  then sum := <u[1],t[2]>;
 *   elif t[2] eq -u[2] then sum := <t[1],-u[1]>;
 *   elif t[1] eq -u[1] then sum := <-u[2],t[2]>;
 *   else sum := <0,0>;
 *   end if;
 *   if sum[1] eq sum[2] or
 *   X ne "C" and Abs(sum[1]) eq Abs(sum[2]) then
 *     sum := <0,0>;
 *   end if;
 *   return InternalGrpLiePairNormalise(X,n,sum);
 * end function;
 * 
 */

Pair_RightString := function( X, n, t, u )
  str := [Pair_Parent|];
  sum := InternalGrpLiePairSum( X, n, u, t );
  while sum ne <0,0> do
    Append( ~str, sum );
    u := sum;
    sum := InternalGrpLiePairSum( X, n, u, t );
  end while;
  return str;
end function;

Pair_LeftString := function( X, n, t, u )
  return Pair_RightString( X, n, InternalGrpLiePairNegative(X,n,t), u );
end function;

Pair_RightStringLength := function( X, n, t, u )
  case X :
  when "A" :
    return (t[2] eq u[1] or t[1] eq u[2]) select 1 else 0;
  when "B" :
    if (t[2] eq 0 and (t[1] eq u[2] or t[1] eq -u[1])) or
    (t[1] eq 0 and (t[2] eq -u[2] or t[2] eq u[1])) 
    then
      return 2;
    elif (t[1] eq u[1] and t[2] eq -u[2]) or (t[1] eq -u[1] and t[2] eq u[2]) or
    (t[1] eq -u[2] and t[2] eq u[1]) or (t[1] eq u[2] and t[2] eq -u[1]) then
      return 0;
    end if;
  when "C" :
    if (u[1] eq -u[2] and 
    (t[2] eq u[1] or t[2] eq -u[2] or -t[1] eq u[1] or -t[1] eq -u[2])) then
      return 2;
    end if;
  when "D" :
    if (t[1] eq u[1] and t[2] eq -u[2]) or (t[1] eq -u[1] and t[2] eq u[2]) or
    (t[1] eq -u[2] and t[2] eq u[1]) or (t[1] eq u[2] and t[2] eq -u[1]) then
      return 0;
    end if;
  end case;
  return (t[2] eq u[1] or t[2] eq -u[2] or -t[1] eq u[1] or -t[1] eq -u[2]) 
    select 1 else 0;
end function;

Pair_LeftStringLength := function( X, n, t, u )
  return Pair_RightStringLength( X, n, InternalGrpLiePairNegative(X,n,t), u );
end function;



// ===================================================================
//
//  Norms and Heights
//


/* 
 * replaced by C-level InternalGrpLiePairNorm
 * 
 * Pair_Norm := function( X, n, t )
 *   case X :
 *   when "A", "D" : return 1;
 *   when "B" : return (t[1] eq 0 or t[2] eq 0) select 1 else 2;
 *   when "C" : return (Abs(t[1]) ne Abs(t[2])) select 1 else 2;
 *   end case;
 * end function;
 * 
 */

Pair_Height := function( X, n, t )
  if t[1] gt 0 and t[2] gt 0 then
    return t[2]-t[1];
  elif t[2] eq 0 then  // type B only
    return n-t[1]+1;
  elif t[1] eq 0 then  // type B only
    return -(n-t[2]+1);
  else  // types BCD
    neg := InternalGrpLiePairIsNegative(X,n,t);
    if neg then  t := InternalGrpLiePairNegative(X,n,t);  end if;
    h := 2*n - t[1] + t[2] + 1;
    if X eq "B" then  h+:=1;  end if;
    if X eq "D" then  h-:=1;  end if;
    if neg then       h:=-h;  end if;
    return h;
  end if;
end function;

Pair_CoHeight := function( X, n, t )
  case X :
  when "A", "D" :
    return Pair_Height( X, n, t );
  when "B" :
    if t[2] eq 0 then
      t[2] := -t[1];
    end if;
    return Pair_Height( "C", n, t );
  when "C" :
    if t[2] eq -t[1] then
      t[2] := 0;
    end if;
    return Pair_Height( "B", n, t );
  end case;
end function;



// ===================================================================
//
//  Reflection permutations
//

Pair_ReflectionPermutation := function( X, n, t )

  // the image of u under reflection in t
  if t[1] ne 0 and t[2] ne 0 then
    i := t[1]; j := t[2];
    im := function( u )
      u[1] := case< u[1] | i:j, -i:-j, j:i, -j:-i, default:u[1] >;
      u[2] := case< u[2] | i:j, -i:-j, j:i, -j:-i, default:u[2] >;
      return InternalGrpLiePairNormalise(X,n,u);
    end function;
  else
    i := (t[1] eq 0) select t[2] else t[1];
    im := function( u )
      u[1] := case< u[1] | i:-i, -i:i, default:u[1] >;
      u[2] := case< u[2] | i:-i, -i:i, default:u[2] >;
      return InternalGrpLiePairNormalise(X,n,u);
    end function;
  end if;

  rts := Pair_Roots( X, n );
  ims := [ im( u ) : u in rts ];
  return Sym(#rts)![ Position( ims, rt ) : rt in rts ];

end function;




// ===================================================================
//
//  Signs
//

/*
 * replaced by C-level InternalGrpLiePairExtraspecialPair
 * 
 * Pair_ExtraspecialPair := function( X, n, t )
 *   if X in {"B", "D"} and -t[2] eq t[1]+1 then
 *     if t[1]+2 gt n then
 *       return < <t[1]+1,0>, <t[1],0> >;
 *     else
 *       return < <t[1]+1,t[1]+2>, <t[1],-(t[1]+2)> >; 
 *     end if;
 *   else
 *     ret := < <t[1],t[1]+1>, <t[1]+1,t[2]> >;
 *     if X eq "C" then  ret[2] := InternalGrpLiePairNormalise(X,n,ret[2]);  end if;
 *     return ret;
 *   end if;
 * end function;    
 */

/*
 * replaced by C-level InternalGrpLiePairEpsilon
 * 
 * // eps_t,u computed from the given extraspecial signs
 * Pair_epsilon := function( X, n, espsigns, t, u )
 *   sum := InternalGrpLiePairSum( X, n, t, u );
 *   if sum eq <0,0> then  return 0;  end if;
 *   if InternalGrpLiePairIsNegative(X,n,u) then
 *     t := InternalGrpLiePairNegative(X,n,t);  u := InternalGrpLiePairNegative(X,n,u);
 *     sum := InternalGrpLiePairNegative(X,n,sum);
 *     m := -1;
 *   else
 *     m := 1;
 *   end if;				// 0 < u
 *   if InternalGrpLiePairIsNegative(X,n,t) then
 *     if InternalGrpLiePairIsNegative(X,n,sum) then    // t < t+u < 0 < u
 *       oldt := t;
 *       t := u;  u := InternalGrpLiePairNegative(X,n,sum);  sum := InternalGrpLiePairNegative(X,n,oldt);
 *     else                                // t < 0 < t+u < u
 *       oldu := u;
 *       u := InternalGrpLiePairNegative(X,n,t);  t := sum;  sum := oldu;
 *       m := -m;
 *     end if;
 *   end if;                               // 0 < t,u
 *   
 *   recurse := function( t, u, sum )
 *     //print t,u,sum;
 *     i := PairToIndex(X,n,t);  j := PairToIndex(X,n,u);
 *     if i gt j then
 *       tmp := t;  t := u;  u := tmp;  mp := -1;
 *     else
 *       mp := 1;
 *     end if;				  // 0 < t < u
 *     
 *     esp := InternalGrpLiePairExtraspecialPair(X, n, sum);
 *     if t eq esp[1] then 
 *       return mp * espsigns[PairToIndex(X,n,sum)-n];
 *     end if;
 *     tp := esp[1];  up := esp[2];
 *   
 *     umtp := InternalGrpLiePairSum(X,n,u,InternalGrpLiePairNegative(X,n,tp));
 *     if umtp ne <0,0> then
 *       return mp * (InternalGrpLiePairNorm(X,n,umtp)/InternalGrpLiePairNorm(X,n,u)) *
 *         $$(tp,umtp,u) * $$(t,umtp,up) *
 *         espsigns[ PairToIndex(X,n,sum)-n ];
 *     else 
 *       tmtp := InternalGrpLiePairSum(X,n,t,InternalGrpLiePairNegative(X,n,tp));
 *       return - mp * (InternalGrpLiePairNorm(X,n,tmtp)/InternalGrpLiePairNorm(X,n,t)) *
 *         $$(tp,tmtp,t) * $$(u,tmtp,up) *
 *         espsigns[ PairToIndex(X,n,sum)-n ];
 *     end if;
 *   end function;
 *   
 *   // return intgers!
 *   return Integers()!(m * recurse(t,u,sum)); 
 * end function;
 *
 */




/*

// ===================================================================
//
//  Test code
//

Attach("Pairs.m");
import "Pairs.m" :
RootToPair, PairToRoot,
Pair_Roots, Pair_WeightOrder, 
Pair_RightString, Pair_LeftString, 
Pair_RightStringLength, Pair_LeftStringLength,
Pair_Height,
Pair_ReflectionPermutation;


n := 5;


"is positive";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  for r in [1..2*N] do 
    v := Root(R,r);
    t := RootToPair(X,n,v);
    if IsNegative(R,r) ne InternalGrpLiePairIsNegative( X, n, t ) then
      error X, r;
    end if;
  end for;
end for;

"negative";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  for r in [1..2*N] do 
    v := Root(R,r);
    if RootToPair(X,n,-v) ne InternalGrpLiePairNegative(X,n, RootToPair(X,n,v) ) then
      error X, r;
    end if;
  end for;
end for;

"root/pair conversion";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  for r in [1..2*N] do 
    v := Root(R,r);
    t := RootToPair(X,n,v);
    if PairToRoot(X,n,RootToPair(X,n,v)) ne v or
    RootToPair(X,n,PairToRoot(X,n,t)) ne t then
      error X, r;
    end if;
  end for;
end for;

"coroot/pair conversion";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n:Isogeny:="SC");
  N := NumPosRoots(R);
  for r in [1..2*N] do 
    v := Coroot(R,r);
    t := CorootToPair(X,n,v);
    if PairToCoroot(X,n,CorootToPair(X,n,v)) ne v or
    CorootToPair(X,n,PairToCoroot(X,n,t)) ne t then
      error X, r, t;
    end if;
  end for;
end for;

"pair/index conversion";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  for r in [1..2*N] do 
    t := RootToPair(X,n,Root(R,r));
    if InternalGrpLiePair2Index(X,n,t,N) ne r then
      error X, r;
    end if;
  end for;
end for;


"roots in std order";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  roots := Pair_Roots( X, n );
  if Setseq(Roots(R)) ne [ PairToRoot(X,n,t) : t in roots ] then
    error X;
  end if;
end for;

"roots in weight order";  // this is false for type C
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  roots := Pair_WeightOrder( X, n );
  if Seqset(roots) ne Seqset(Pair_Roots(X,n)[[1..N]]) then
     error X, 0;
  end if;
  idxs := [ InternalGrpLiePair2Index(X,n,t,N) : t in roots ];
  if Seqset(idxs) ne {1..N} then
    error X, 1;
  end if;
  print X, IsAdditiveOrder( R, idxs );
end for;


"sum check";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,5);
  N := NumPosRoots(R);
  for r in [1..2*N] do
    for s in [1..2*N] do 
      u := Root(R,r);  v := Root(R,s);
      x := RootToPair(X,n,u);
      y := RootToPair(X,n,v);
      if (RootPosition(R,u+v) eq 0) ne (InternalGrpLiePairSum(X,n,x,y) eq <0,0>) then
        error 1,X, u,v;
      end if;
      if (InternalGrpLiePairSum(X,n,x,y) ne <0,0>) and
      (RootToPair(X,n,u+v) ne InternalGrpLiePairSum(X,n,x,y)) then
        error 2,X, u,v;
      end if;
    end for;
  end for;
end for;

"string check";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  rtp := Pair_Roots( X, n );
  for r in [1..2*N] do
    for s in [1..2*N] do
      if r notin {s,s+N,s-N} then
	str := RightString(R,r,s);
	if [ rtp[i] : i in str ] ne Pair_RightString(X,n,rtp[r],rtp[s]) then
	  error "R",X,n, r, s;
	end if;
	str := LeftString(R,r,s);
	if [ rtp[i] : i in str ] ne Pair_LeftString(X,n,rtp[r],rtp[s]) then
	  error "L",X,n, r, s;
	end if;
      end if;
    end for;
  end for;
end for;

"string length check";
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  rtp := Pair_Roots( X, n );
  for r in [1..2*N] do
    for s in [1..2*N] do
      if r notin {s,s+N,s-N} then
	if RightStringLength(R,r,s) ne Pair_RightStringLength(X,n,rtp[r],rtp[s]) then
	  error "right",X,n, r, s;
	end if;
        if LeftStringLength(R,r,s) ne Pair_LeftStringLength(X,n,rtp[r],rtp[s]) then
	  error "left",X,n, r, s;
        end if;
      end if;
    end for;
  end for;
end for;


"Norm & height check";
n := 5;
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  roots := Pair_Roots( X, n );
  if RootNorms(R) ne [ InternalGrpLiePairNorm(X,n,t) : t in roots ] then
    error "Norm", X, n;
  end if;
  if [RootHeight(R,r):r in [1..2*N]] ne [ Pair_Height(X,n,t) : t in roots ] then
    error "Height", X, n;
  end if;
end for;


"Reflection perm check:";
n := 5;
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  roots := Pair_Roots( X, n );
  if ReflectionPermutations(R) ne 
  [ Pair_ReflectionPermutation(X,n,t) : t in roots ] then
    error X, n;
  end if;
end for;


"Extraspecial pairs check";
n := 5;
for X in ["A","B","C","D"] do
  R := IrreducibleRootDatum(X,n);
  N := NumPosRoots(R);
  roots := Pair_Roots( X, n );
  esp := ExtraspecialPairs(R);
  if [ <roots[c[1]],roots[c[2]]> : c in esp ] ne 
  [ InternalGrpLiePairExtraspecialPair(X,n,t) : t in roots[[n+1..N]] ] then
    error X, n;
  end if;
end for;

"Epsilons test"
n := 5;
for X in ["A","B","D","C"] do
  N := NumPosRoots(X cat IntegerToString(n));
  signs := [ Random([+1,-1]) : i in [n+1..N] ];
  R := IrreducibleRootDatum(X,n:Signs:=signs);
  N := NumPosRoots(R);
  rtp := Pair_Roots( X, n );
  for r in [1..2*N] do
    for s in [1..2*N] do
      if LieConstant_epsilon(R,r,s) ne InternalGrpLiePairEpsilon(X,n,signs,rtp[r],rtp[s],N) then
        error X,n, r, s;
      end if;
    end for;
  end for;
end for;
*/

/* This code computes epsilons symbolically
   It only works after changes to RootDtm.m and Const.m

X := "A";  n := 5;
name := X cat IntegerToString(n);
N := NumPosRoots( name );
k<[e]> := RationalFunctionField( Rationals(), N-n );
R := RootDatum( name : Signs:= e );

strings( ~R );
epsilonsByExtraspecials( ~R : Z:=k );

rts := Pair_Roots( X, n );

for r in [1..2*N] do
  for s in [1..2*N] do
    eps1 := LieConstant_epsilon(R,r,s);
    eps2 := InternalGrpLiePairEpsilon(X,n,e,rts[r],rts[s],N);
    if eps1 ne eps2 then
      print r, s, eps1, eps2;
    end if;
  end for;
end for;

*/

