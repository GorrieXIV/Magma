freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

////////////////////////////////////////////////////////////////////////
//                                                                    
//  Frobenius Form of an alternating matrix. See Lemma VI.3.1, p90 of
//  "Introduction to algebraic and abelian functions" by Serge Lang.
//
//  P. van Wamelen (June 2003)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//    FrobeniusFormAlternating
//     
////////////////////////////////////////////////////////////////////////

Z := IntegerRing();

// returns true if u can be orthogonalized wrt e and v,
//    that is, find a and b such that u-a*e-b*v is orthogonal to e and v.
//    then also return u-a*e-b*v
// returns false if this can not be done, then also return [v1,v2,v3]
//    such that E(v1,v2) > 0 is less than E(e,v) and 
//    span[v1,v2,v3] = span[e,v,u]
function orthogonalize(u,e,v,E)
  d1 := (e*E*Transpose(v))[1,1];
  dum := (u*E*Transpose(e))[1,1];
  b,r := Quotrem(dum,d1);
  if r eq 0 then
    dum := (u*E*Transpose(v))[1,1];
    a, r := Quotrem(dum,d1);
    if r eq 0 then
      return true, u+b*v-a*e;
    else
      return false, [u-a*e,v,e];
    end if;
  else
    return false, [u+b*v,e,v];
  end if;
end function;

function FindNonZeroPair(base,E)
  for i in [2..#base] do
    dum := (base[1]*E*Transpose(base[i]))[1,1];
    if dum gt 0 then
      return [base[1],base[i]] cat [base[j] : j in [2..#base] | j ne i];
    elif dum lt 0 then
      return [base[i],base[1]] cat [base[j] : j in [2..#base] | j ne i];
    end if;
  end for;
end function;

function FrobeniusAlternatingForm(base,E)
  base := FindNonZeroPair(base,E);
  if #base eq 2 then
    return base;
  else
    minQ := (base[1]*E*Transpose(base[2]))[1,1];
    newbase := [];
    for i in [3..#base] do
      bool, dum := orthogonalize(base[i],base[1],base[2],E);
      if bool then
        Append(~newbase,dum);
      else
        base[1] := dum[1];
        base[2] := dum[2];
        base[i] := dum[3];
        return FrobeniusAlternatingForm(base,E);
      end if;
    end for;
    newbase := FrobeniusAlternatingForm(newbase,E);
    min2 := (newbase[1]*E*Transpose(newbase[2]))[1,1];
    if minQ le min2 then
      return [base[1], base[2]] cat newbase;
    else
      return FrobeniusAlternatingForm([newbase[1],newbase[2],base[1],base[2]] cat Remove(Remove(newbase,1),1),E);
    end if;
  end if;
end function;

function standardbasis(n)
  return [Matrix(Z,1,n,[i eq j select 1 else 0 : i in [1..n]]) : j in [1..n]];
end function;

intrinsic FrobeniusFormAlternating(M::AlgMatElt) -> SeqEnum
{Given an non-singular 2nx2n integer alternating matrix M, this returns the
Frobenius form of M. That is, a block matrix C = [0, D; -D, 0], where
D is a diagonal matrix with positive diagonal entries d_i satisfying
d_1 | d_2 | ... | d_n. The second return value is the change of basis
matrix B, such that B*M*B^t = C.}
  require BaseRing(M) eq IntegerRing():
    "The argument must have integer entries";
  n := NumberOfRows(M);
  require n mod 2 eq 0: 
    "The argument must have an even number of rows";
  require n gt 0: 
    "The argument must have more than 0 rows";
  require M+Transpose(M) eq Matrix(IntegerRing(),n,n,[]):
    "The argument must be an alternating matrix";
  require Determinant(M) ne 0:
    "The matrix must be non-singular";
  basis := FrobeniusAlternatingForm(standardbasis(n),M);
  A := VerticalJoin([basis[2*i-1] : i in [1..#basis div 2]] cat 
                    [basis[2*i] : i in [1..#basis div 2]]);
  return A*M*Transpose(A), A;
end intrinsic;
