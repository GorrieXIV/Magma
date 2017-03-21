freeze;

/******************************************************************************
  Local invariants of quadratic forms: pSignature, Oddity, pExcess.
      
  Steve, 2007-03
******************************************************************************/

function IsAntisquare(n,p) 
   v := Valuation(n,p);
   if IsEven(v) or n eq 0 then return false; end if;
   n div:= p^v;
   return KroneckerSymbol(n,p) eq -1;
end function;

function psig(ds,p)
 if p eq -1 then return &+[Integers()| Sign(d) : d in ds ];  end if;
  sum := p eq 2 select &+[ Integers()| d div p^Valuation(d,p) : d in ds ]
                 else  &+[ Integers()| p^Valuation(d,p) : d in ds ];
  return (sum + 4*#[ d : d in ds | IsAntisquare(d,p) ]) mod 8; end function;

intrinsic pSignatures(f::RngMPolElt) -> SeqEnum
{The p-signatures at bad primes, given in tuples}
 return pSignatures(SymmetricMatrix(f)); end intrinsic;
 
intrinsic pSignatures(M::Mtrx) -> SeqEnum
{The p-signatures at bad primes, given in tuples}
 require IsSymmetric(M) : "The given matrix is not symmetric"; BR:=BaseRing(M);
 require BR eq Rationals() or BR eq Integers(): "Base ring is not Q or Z";
 D := Diagonalization(M); ds := [ D[i,i] : i in [1..Ncols(D)] | D[i,i] ne 0 ];
 ds := [Integers()| d * Denominator(d)^2 : d in ds ]; det:=Determinant(M);
 if det eq 0 then F:=[];
 else FAC:=Factorization(4*Numerator(det))*Factorization(Denominator(det));
  F:=[-1] cat Sort(SetToSequence({f[1] : f in FAC})); end if;
 return [<p,psig(ds,p)> : p in F]; end intrinsic;

intrinsic pSignature(f::RngMPolElt, p::RngIntElt) -> RngIntElt
{The p-signature of the quadratic form, where p is a prime integer or -1
 (as defined in the book of Conway and Sloane).}
   return pSignature(SymmetricMatrix(f), p); end intrinsic;

intrinsic pSignature(M::Mtrx, p::RngIntElt) -> RngIntElt
{The p-signature of the quadratic form given by the symmetric matrix M, 
 where p is a prime integer or -1 (as defined in Conway/Sloane).}
  require IsSymmetric(M) : "The given matrix is not symmetric";
  BR:=BaseRing(M);
  require BR cmpeq Rationals() or BR cmpeq Integers():
  "Base ring is not Q or Z";
  D := Diagonalization(M); ds := [ D[i,i] : i in [1..Ncols(D)] | D[i,i] ne 0 ];
  ds := [Integers()| d * Denominator(d)^2 : d in ds ];
  require p eq -1 or IsPrime(p): "Second argument is not prime or -1";
 return psig(ds,p); end intrinsic;

intrinsic pSignature(L::Lat, p::RngIntElt) -> RngIntElt
{The p-signature of the quadratic form, where p is a prime integer or -1
 (as defined in Conway and Sloane's book).}
   return pSignature(GramMatrix(L), p); end intrinsic;

intrinsic Oddity(f::RngMPolElt) -> RngIntElt
{Returns pSignature(f,2) for the given quadratic form f.}
   return pSignature(f,2); end intrinsic;

intrinsic Oddity(L::Lat) -> RngIntElt
{Returns pSignature(L,2) for the given lattice L.}
   return pSignature(L,2); end intrinsic;

intrinsic Oddity(M::Mtrx) -> RngIntElt
{Returns pSignature(M,2) for the given symmetric matrix M.}
   return pSignature(M,2); end intrinsic;

intrinsic pExcess(f::RngMPolElt, p::RngIntElt) -> RngIntElt
{The p-excess of the quadratic form, where p is a prime integer or -1
 (as defined in Conway and Sloane's book).}
   return pExcess(SymmetricMatrix(f), p); end intrinsic;

intrinsic pExcess(M::Mtrx, p::RngIntElt) -> RngIntElt
{The p-excess of the quadratic form given by the symmetric matrix M, 
 where p is a prime integer or -1 (as defined in Conway/Sloane).}
 require p eq -1 or IsPrime(p): "Second argument must be prime";
 require IsSymmetric(M): "Matrix must be symmetric"; BR:=BaseRing(M);
 require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring must be Integers or Rationals"; 
 if p eq -1 then return pSignature(M,-1)-Rank(M); end if;
 if p eq 2 then return (Rank(M) - pSignature(M,2)) mod 8;
 else return (pSignature(M,p) - Rank(M)) mod 8; end if; end intrinsic;

intrinsic pExcess(L::Lat, p::RngIntElt) -> RngIntElt
{The p-excess of the quadratic form, where p is a prime integer or -1
 (as defined in Conway/Sloane).}
 return pExcess(GramMatrix(L),p); end intrinsic;

intrinsic pExcesses(M::Mtrx) -> SeqEnum
{The p-excesses at bad primes.}
 require IsSymmetric(M): "Matrix must be symmetric"; BR:=BaseRing(M);
 require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring must be Integers or Rationals"; 
 S:=pSignatures(M);
 function f(X,p) if p[1] eq -1 then return p[2]-Rank(M); end if;
                 if p[1] eq 2 then return (Rank(M)-p[2]) mod 8; end if;
                 return (p[2]-Rank(M)) mod 8; end function;
 E:=[<p[1],f(M,p)> : p in S]; return E; end intrinsic;

intrinsic pExcesses(L::Lat) -> SeqEnum
{The p-excesses at bad primes.}
 return pExcesses(GramMatrix(L)); end intrinsic;

intrinsic pExcesses(f::RngMPolElt) -> SeqEnum
{The p-excesses at bad primes.}
 return pExcesses(SymmetricMatrix(f)); end intrinsic;

procedure test_pSignatures(L)
   D := Determinant(Diagonalization(GramMatrix(L)));
   FAC:=Factorization(Numerator(D))*Factorization(Denominator(D));
   ps := Set([-1,2] cat [ tup[1] : tup in FAC ]); 
   error if &+[Integers()| pExcess(L,p) : p in ps ] mod 8 ne 0, 
        "Detected an error1 in Steve's new pSignature functions";
   eqn16 :=  pSignature(L,-1) - Oddity(L) + 
             &+[Integers()| pExcess(L,p) : p in ps | p ge 3 ];
   error if eqn16 mod 8 ne 0,
        "Detected an error2 in Steve's new pSignature functions";
end procedure;

  
////////////////////////////////////////////////////////////////////////////////
//                     Gauss sums for lattices                                // 
//                    Steve Donnelly, April 2009                              //
////////////////////////////////////////////////////////////////////////////////

procedure GaussSumCheck(L : C:=ComplexField() )
   assert IsIntegral(L) and IsEven(L);
   test_pSignatures(L); 
   gauss := GaussSum(L, Determinant(L));
   assert Abs( gauss - z8^Dimension(L) ) lt 10^-10 where z8 is (1+C.1)/Sqrt(2);
end procedure;


intrinsic GaussSum(N::RngIntElt : C:=ComplexField()) -> FldComElt
  {The Gauss sum of the quadratic character modulo N, returned as a complex number}

  require N gt 1 : "The given integer must be greater than 1";
  require ISA(Type(C), FldCom) : "C must be a complex field";

  i := C.1;
  case N mod 4 :
        when 0 : return (1+i) * Sqrt(N);
        when 1 : return C! Sqrt(N);
        when 2 : return C! 0;
        when 3 : return i * Sqrt(N);
  end case;
end intrinsic;


intrinsic GaussSum(L::Lat, q::RngIntElt : C:=ComplexField()) -> FldComElt
   {The Gauss sum of the q-part of the dual quotient of the given integral lattice.
   This is normalized to be an eighth root of unity, and returned as a complex number}

   require IsIntegral(L) and IsEven(L) : "Only implemented for even integral lattices";

   ee := Exponent(DualQuotient(L));
q := GCD(q, ee);
   require ee mod q eq 0 and GCD(q, ee div q) eq 1 :
          "The given integer q must exactly divide the exponent of the dual quotient";

   // Method 1: Rains-Sloane 'Shadow theory...', Lemma 1 (only for even lattices)
   Lq := RescaledDual(L, q);
   exp := 0;
   for p in PrimeDivisors(q) do
     if p eq 2 then
       exp +:= Oddity(Lq);
     else
       exp -:= pExcess(Lq, p); end if;
   end for;
   gauss1 := ((1+C.1)/Sqrt(2)) ^ (exp mod 8);
   
   if IsEven(q) or not IsSquarefree(q) then  
     gauss := gauss1;
   else 
   //Dq := q_qprime_split(Determinant(L), q);
   //gauss := C! 1/Sqrt(Dq);
     gauss := C! 1;
     Ldiag := Diagonalization(GramMatrix(L));
     for p in PrimeDivisors( GCD(q,Determinant(L)) ) do
     //Ldiag := GramMatrix(pAdicDiagonalization(L,p));
       if IsOdd(p) then
 assert IsDiagonal(Ldiag);
         diag := [ Ldiag[i,i] : i in [1..Nrows(Ldiag)] ];
         diag := [Integers()| a*Denominator(a)^2 : a in diag ];
         diag := [ a div p^Valuation(a,p) : a in diag | IsOdd(Valuation(a,p)) ];
         gauss *:= GaussSum(p : C:=C) ^ #diag / p ^ (#diag div 2);
         n := #[ a : a in diag | LegendreSymbol(2*a,p) eq -1 ];
         gauss *:= (-1)^n; 
       else
         error "GaussSum not implemented yet for p = 2";
       end if;
     end for;
gauss /:= Abs(gauss); // certainly |gauss| was not 1 in cases where #diag is odd
     error if Abs(1-gauss^8) gt 10^-10, 
          "Failed to obtain an eighth root of unity in GaussSum";
   end if;
    
   /* CHECK
   if Abs(gauss-gauss1) gt 10^-10 then 
     print "Oops -- the two formulae for the Gauss sum don't agree:"; 
     print "       ", gauss1; "       ", gauss; //"#diag =", #diag, "n =", n; 
   end if;
   // TO DO: also use GaussSumCheck 
   */

   return gauss1;
end intrinsic;

