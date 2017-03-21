freeze;

/*=========================================================
  Don Taylor

  24 September 2015 

  $Id: ClassicOrd.m 51624 2015-11-23 03:41:41Z don $

==========================================================
  Compute the orders of all finite classic groups.
  The intrinsic for OrderGL is in the file 
      Group/GrpPC/count-pgrps/subgroups.m
  
*/

intrinsic OrderGU(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the full unitary group}
  if n eq 0 then return 1; end if;
  return q^Binomial(n,2) * &*[(q^i - (-1)^i): i in [1..n]];
end intrinsic;

intrinsic OrderSp(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the symplectic group}
  require IsEven(n) : "degree must be even";
  if n eq 0 then return 1; end if;
  m := n div 2;
  return q^(m^2) * &*[(q^(2*i) - 1): i in [1..m]];
end intrinsic;

intrinsic OrderCSp(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the conformal symplectic group}
  return OrderSp(n,q)*(q-1);
end intrinsic;

intrinsic OrderGOPlus(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the orthogonal group of maximal Witt index}
  require IsEven(n) : "degree must be even";
  if n eq 2 then return 2*(q-1); end if;
  m := n div 2;
  return 2*q^(m*(m-1)) * (q^m - 1)* &*[(q^(2*i) - 1): i in [1..m-1]];
end intrinsic;

intrinsic OrderGOMinus(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the orthogonal group of non-maximal Witt index}
  require IsEven(n) : "degree must be even";
  if n eq 2 then return 2*(q+1); end if;
  m := (n div 2) - 1;
  return 2*q^(m*(m+1)) * (q^(m+1) + 1)* &*[(q^(2*i) - 1): i in [1..m]];
end intrinsic;

intrinsic OrderGO(n :: RngIntElt, q :: RngIntElt) -> RngIntElt
{The order of the orthogonal group of odd degree}
  require IsOdd(n) : "degree must be odd";
  if (n eq 1) then return IsEven(q) select 1 else 2; end if;
  m := (n - 1) div 2;
  val := q^(m^2) * &*[(q^(2*i) - 1): i in [1..m]];
  return IsEven(q) select val else 2*val;
end intrinsic;

