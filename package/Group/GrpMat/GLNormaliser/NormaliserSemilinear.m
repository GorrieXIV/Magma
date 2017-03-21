freeze;

/*
contains functions:
ConjElts
AbsIrredSemilin
NormaliserSemilinear
*/

/*
needs GLNormaliser_functions for GammaL(d,q,s) where s divides d and q is a prime power
*/

import "GLNormaliser_functions.m": GammaL1, GammaL, get_derived_group;

/***************************/

/*
ConjElts takes 2 (centralizing) matrices and returns [true and conjelt] or false
*/

ConjElts:= function(Z_G, Z_C,qe)
  centralisers_conj:= false;
  og:=Order(Z_G);
  a:= (qe-1) div og;
  Z_C:= Z_C^a;
  assert Order(Z_C) eq og;
  done:=0;
  i:=1;
  while done eq 0 and i lt qe-1 do
    if Gcd(i,qe-1) eq 1 then
      if Order(Z_C^i) eq og then
        centralisers_conj, x:= IsSimilar(Z_C^i, Z_G);
        if centralisers_conj then
          done:=1;
          return true, x;
        end if;
      end if;
    end if;
    i:=i+1;
  end while;
  return false, _;
end function;


/**********************************/



/*
takes an absolutely irreducible group and returns a record in group_norm format
*/

group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;


function AbsIrredSemilin(group:der_group:=0)
  assert IsAbsolutelyIrreducible(group);
  n:=Dimension(group);
  q:=#BaseRing(group);
  K,A,ims:=WriteOverLargerField(group);
  //K is kernel of map
  mat:=GL(n,q).0;

  if Type(der_group) eq GrpMat then
    D:=der_group;
  else 
    D:=get_derived_group(group);
  end if;

  s:=DegreeOfFieldExtension(group);
  //see if there's enough space in |G/G'| for two different groups of order s.
  d:=#D;
  g:=#group;
  a:=Integers()!(g/d);
  b:=Integers()!(a/s);
  if IsEmpty(Set(PrimeDivisors(s)) meet Set(PrimeDivisors(b))) then
    //not enough space, only one way of writing G over a larger field
    N:=GLNormaliser(K:Overgroup:=true,der_group:=D);
    N`full_norm:=false;
    N`derived_group:=D;
    return N;
  end if;

/*
may be several maps from G to Aut(GF)
look  for a normal subgroup L of G/G' which is isomorphic to K_1/G', then 
L=K_2/G'
*/

  k:=g/#A;
  o:=Integers()!(k/#D);
  Q,phi:=quo<group|D>;
  norms:=[M`subgroup@@phi:M in NormalSubgroups(Q:OrderEqual:=o)];
  good:=[m:m in norms | IsIrreducible(m) and not IsAbsolutelyIrreducible(m) ];
  //takes a little while
  if #good eq 1 then
    N:=GLNormaliser(K:Overgroup:=true,der_group:=D);
    N`full_norm:=false;
    N`derived_group:=D;
    return N;
   //only one normal subgp that can be embedded into GammaL

  else
    return rec<group_norm|got_overgroup:=false, derived_group:=D>;
  end if;

end function;

/*************************************/

/*
Takes a semilinear group G and returns a record in group_norm format
*/


function NormaliserSemilinear(group: der_group:=0)
  assert IsIrreducible(group);
  n:=Dimension(group);
  q:=#BaseRing(group);
  bool,gen,e:=IsAbsolutelyIrreducible(group);
  if bool then
    return AbsIrredSemilin(group:der_group);
  end if;

  /*
  gen is (matrix algebra) generator of end algebra E of G (always a field) = centraliser
  e is the dimension of E
*/

  Z_G:= GL(n, q)!gen;
  ovgroup:= GammaL(n, q, e);
  singer:=GammaL1(e,q).1;
  /*
  singer has order q^n-1 and is isomorphic to F_(q^e)*
  this is the matrix with the coeffs of a prim polynomial on bottom row, that is equivalent to mult by an elt in F_{q^e} \ F_q
  */
  Z_C:=KroneckerProduct(IdentityMatrix(GF(q),n div e),singer);
  bool, x:= ConjElts(Z_G, Z_C,q^e);
  x:= GL(n, q)!x;

  return rec<group_norm|overgroup:=ovgroup, cob:=x, got_overgroup:=true, full_norm:=false>;
end function;




