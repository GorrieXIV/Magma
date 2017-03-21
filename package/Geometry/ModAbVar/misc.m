freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: misc.m
   DESC: Miscellaneous useful functions

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

forward
   FactorPrint,
   GatherFactorExponents,
   IsSquareFree,
   NoSpaces,
   idxG0;


function NoSpaces(s)
   t := "";
   for i in [1..#s] do
      if s[i] ne " " then
         t *:= s[i];
      end if;
   end for;
   return t;
end function;

function IsSquareFree(N)
   return SquarefreeFactorization(N) eq N;
end function;


function GatherFactorExponents(X)
// X is obtained by cat-ing a bunch of factorizations together.
   Y := [];
   seen := [];
   for F in X do 
      if not (F[1] in seen) then
         Append(~Y, <F[1], &+[G[2] : G in X | G[1] eq F[1]]>);
         Append(~seen,F[1]);
      end if;
   end for;
   return Y;
end function;


function FactorPrint(n)
   if Type(n) ne RngIntElt then
      return Sprintf("%o",n);
   end if;
   s := "";
   if n lt 0 then
      n := -n;
      s := "-";
   end if;
   if n le 1 then
      s := s*Sprintf("%o",n);
      return s;
   end if;
   F := Factorization(n);
   for f in F do
      s := s*Sprintf("%o", f[1]);
      if f[2] gt 1 then
         s := s*Sprintf("^%o", f[2]);
      end if;
      if f ne F[#F] then
         s :=  s*"*";
      end if;
   end for;
   return s;
end function;


function idxG0(n)
   return 
      &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(n)];
end function;

function OddPart(x)
   // The odd part of x.
   if x eq 0 then
      return x;
   end if;
   return x / 2^Valuation(x,2);
end function;
