freeze;

//////////////////////////////////////////////////////////////////// 
//                                                                //  
//                  Residue Class Rings and Fields                //
//                      and Modular Unit Groups                   // 
//                        by David Kohel                          // 
//                                                                // 
//             Last modified April 2010, Steve Donnelly           // 
//                                                                // 
//////////////////////////////////////////////////////////////////// 

// Intrinsics: CRT, UnifomizingElement 

// April 2010, SRD: split off the recursive part, return least residue

function crt(X,M,O)
   if #X eq 1 then
      return X[1];
   end if;
   x := X[1]; y := X[2];
   Remove(~X,1);
   I := M[1]; J := M[2];
   Remove(~M,1);   
   K := I+J; 
   if O!1 notin K then
      error if (x mod K) ne (y mod K), 
         "Elements do not satisfy a common congruence";
      fact := Factorization(K); // TO DO: should not factor
      for p in fact do
         if Valuation(I,p[1]) eq p[2] then
            I *:= (p[1]^-p[2]);
         else
            J *:= (p[1]^-p[2]);
         end if;
      end for; 
   end if;
   X[1] := CRT(O!!I,O!!J,x,y);
   M[1] := I*J;
   return crt(X,M,O);      
end function;

intrinsic CRT(X::[RngOrdElt],M::[RngOrdIdl]) -> RngOrdElt
{The Chinese remainder lifting of the sequence of elements
with respect to the sequence of moduli}

   require #X eq #M : "Arguments must be of the same length";
   require #X ge 1 : "Arguments must be nonempty";
   require &and[ IsIntegral(I) : I in M ] : "The given ideals must be integral";

   O := Order(M[1]);
   x := crt(X, M, O);

   // return least residue
   _, modM := quo<O| &meet M>;
   return x @modM @@modM;
end intrinsic;

intrinsic UniformizingElement(P::RngOrdIdl) -> RngOrdElt
{A uniformizing element for the prime P.}
   require IsPrime(P) : "Argument 1 must be prime";
   return PrimitiveElement(P); // KANT function
end intrinsic;


////////////////////////////////////////////////////////////////////
// SRD Sep 2014
////////////////////////////////////////////////////////////////////

intrinsic CRTZ(X::[RngOrdElt], M::[RngOrdIdl] : LCM:=0) -> RngOrdElt

{CRT by straightforward conversion to linear algebra over Z.
Returns a reduced residue only when parameter 'LCM' is given.}

   require #X eq #M : "Arguments must be of the same length";
   require #X ge 1  : "Arguments must be nonempty";
   require &and[ IsIntegral(I) : I in M ] : "The given ideals must be integral";

   O := Ring(Universe(M));
   d := Degree(O);
   n := #X;
   Z := Integers();

   require IsAbsoluteOrder(O) : "Only implemented for orders with base ring Z";

   B := [BasisMatrix(I) : I in M];
//assert B eq [Matrix(Z, [Eltseq(O!b) : b in Basis(I)]) : I in M];

   MM := RMatrixSpace(Z, n*d, (n-1)*d) ! 0;

   for i := 1 to n-1 do
       InsertBlock(~MM, -B[1], 1, 1 + (i-1)*d);
   end for;

   for i := 1 to n-1 do
       InsertBlock(~MM, B[i+1], 1 + i*d, 1 + (i-1)*d);
   end for;

   A := [Vector(Z, Eltseq(O!(X[1]-x))) : x in X[2..n]];
   XX := HorizontalJoin(A);

   YY := Solution(MM, XX);

   Y1 := Submatrix(YY, 1, 1, 1, d);
   y1 := O ! Eltseq(Y1 * B[1]);

   x := X[1] + y1;

   if ISA(Type(LCM), RngOrdIdl) then
       x := x mod LCM;
   end if;

   for i := 1 to n do assert (x - X[i]) in M[i]; end for;

   return x;

end intrinsic;

