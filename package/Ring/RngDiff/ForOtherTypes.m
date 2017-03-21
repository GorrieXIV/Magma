freeze;


////////////////////////////////////////////////////////////////////
//                                                                //
//                                                                //
//                             Written by                         //
//                         Alexa van der Waall                    //
//                                                                //
//                            Last updated:                       //
//                            09 June 2009                        //
//                                                                //
//                                                                //
////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////
//                                                                //
//               Predicates and Booleans on Diff Rings            //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic IsOrderTerm(x::RngSerElt) -> BoolElt
  {True iff x is an order term in the series ring.}
  valx := Valuation(x);
  if valx lt Infinity() and (RelativePrecision(x) eq 0) then
    return true;
  else
    return false;
  end if;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                        Element Operations                      //
//                                                                //
////////////////////////////////////////////////////////////////////



intrinsic Exponents(x::RngSerElt) -> SeqEnum
  {The interval from the valuation of x to (including) the degree of x.
  The empty sequence is returned for the zero element.} 
  S:=Parent(x);
  require ISA(Type(S),RngSerPow) or ISA(Type(S),RngSerLaur):
    "The argument must be a power series or a Laurent series.";
  if IsWeaklyZero(x) then 
      // x is 0, or 0 + order term
    return [Integers()|];
  else 
    return [Integers()|Valuation(x) .. Degree(x)];
  end if; 
end intrinsic;

intrinsic Exponents(x::RngUPolElt) -> SeqEnum
  {The interval from the valuation of x to (including) the degree of x.
   The empty sequence is returned for the zero element.} 
  S:=Parent(x);
  if IsZero(x) then 
    return [Integers()|];
  else 
    return [Integers()|Valuation(x) .. Degree(x)];
  end if; 
end intrinsic;




////////////////////////////////////////////////////////////////////
//                                                                //
//                    Sequence Operations                         //
//                                                                //
////////////////////////////////////////////////////////////////////



intrinsic Indices(S::SeqEnum,x::.) -> SeqEnum
  {The list of all integers i such that S[i] equals x}
  bl, x :=IsCoercible(Universe(S),x);
  require bl:
    "The second argument is not coercible in the universe of the sequence.";
  return [Integers()| i: i in [1..#S]|S[i] eq x];
end intrinsic;

intrinsic ZeroSequence(R::Rng, n::RngIntElt) -> SeqEnum
  {The zero sequence over R of length n.}  
  require n ge 0:
    "The second argument must be a non-negative integer.";
  return [R|0 : i in [1..n]];
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                             Precision                          //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic RelativePrecision(K::RngSer) -> RngElt
   {Returns the relative precision of K.}
   require not ISA(Type(K), RngSerPow):
     "Relative precision not defined for a power series ring.";
   return K`DefaultPrecision;
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                      Matrix Operations                         //
//                                                                //
////////////////////////////////////////////////////////////////////


function ReplaceColumn(M,i,v)
//  {Replace the i-th column of M by the sequence v.}
  F:=BaseRing(Parent(M));
  numberofrows:=NumberOfRows(M);
  assert numberofrows eq #v;
  F:=BaseRing(Parent(M));
  T:=Transpose(M);
  T[i]:=Vector(F,Matrix(F,1,numberofrows,v));
  return Transpose(T);
end function;
