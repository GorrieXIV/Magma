freeze;

/*
intrinsic GaloisGroup(f::RngUPolElt: Al := "pAdic", 
                          Prime := false, Precision := false,
                            Conditional := false) -> GrpPerm, SeqEnum, Any
{The Galois group of the polynomial f (of degree <= 23), the roots of f
 and the ideal giving the embedding of the coefficients into the
 splitting field.}

 if Prime cmpeq false then
   if Precision cmpeq false then
     if Al cmpeq "pAdic" and Conditional cmpeq false then
       return InternalGaloisGroup(f);
     else
       return InternalGaloisGroup(f: Al := Al, Conditional := Conditional);
     end if;
   else
     return InternalGaloisGroup(f: Al := Al, Conditional := Conditional,
                                   Precision := Precision);
   end if;
 else
   if Precision cmpeq false then
     return InternalGaloisGroup(f: Al := Al, Prime := Prime, 
                                   Conditional := Conditional);
   else
     return InternalGaloisGroup(f: Al := Al, Prime := Prime, 
                                   Conditional := Conditional,
                                   Precision := Precision);
   end if;
 end if;
end intrinsic;

intrinsic GaloisGroup(O::RngOrd: Al := "pAdic", 
                          Prime := false, Precision := false,
                            Conditional := false) -> GrpPerm, SeqEnum, Any
{}

 if Prime cmpeq false then
   if Precision cmpeq false then
     return InternalGaloisGroup(O: Al := Al, Conditional := Conditional);
   else
     return InternalGaloisGroup(O: Al := Al, Conditional := Conditional,
                                   Precision := Precision);
   end if;
 else
   if Precision cmpeq false then
     return InternalGaloisGroup(O: Al := Al, Prime := Prime, 
                                   Conditional := Conditional);
   else
     return InternalGaloisGroup(O: Al := Al, Prime := Prime, 
                                   Conditional := Conditional,
                                   Precision := Precision);
   end if;
 end if;
end intrinsic;

intrinsic GaloisGroup(K::FldAlg: Al := "pAdic", 
                          Prime := false, Precision := false,
                            Conditional := false) -> GrpPerm, SeqEnum, Any
{}

 if Prime cmpeq false then
   if Precision cmpeq false then
     return InternalGaloisGroup(K: Al := Al, Conditional := Conditional);
   else
     return InternalGaloisGroup(K: Al := Al, Conditional := Conditional,
                                   Precision := Precision);
   end if;
 else
   if Precision cmpeq false then
     return InternalGaloisGroup(K: Al := Al, Prime := Prime, 
                                   Conditional := Conditional);
   else
     return InternalGaloisGroup(K: Al := Al, Prime := Prime, 
                                   Conditional := Conditional,
                                   Precision := Precision);
   end if;
 end if;
end intrinsic;
*/

intrinsic IsAbelian(K::FldAlg[FldAlg[FldRat]]) -> BoolElt
  {Test if the automorphism group of the normal field over its coefficient field is abelian}
  G := GaloisGroup(K);
  return #G eq Degree(K) and IsAbelian(G);
end intrinsic;
