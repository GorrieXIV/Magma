freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                         VELU ISOGENIES                         //
//                           David Kohel                          //
//                                                                // 
////////////////////////////////////////////////////////////////////

forward VeluRecursion, KernelPowerSums, PowerToSymmetricSums;

function VeluRecursion(e2,e4,e6,f4,f6,l) 
   E0 := EllipticCurve([0,0,0,-e4/48,-e6/864]); 
   E1 := EllipticCurve([0,0,0,-l^2*f4/48,l^3*f6/864]); 
   WP0 := WeierstrassSeries(E0,Max(4,l-1)); 
   WP1 := WeierstrassSeries(E1,Max(4,l-1)); 
   p1 := l*e2; // the first power sum  
   Pow := KernelPowerSums(WP0,WP1,p1,l); 
   Sym := PowerToSymmetricSums(Pow); 
   return Sym;
end function;
 
function KernelPowerSums(WP0,WP1,p1,l) 
   if l eq 2 then 
      return [ 2*p1 ]; 
   end if; 
   R := Parent(p1); 
   n := (l - 1) div 2; 
   a4 := -Coefficient(WP0,2)*5;  
   a6 := -Coefficient(WP0,4)*7; 
   Pow := [ p1 : i in [1..n] ];  
   A := Zero(RMatrixSpace(R,n,n+1)); 
   A[1,2] := 1;  
   for k in [1..n-1] do 
      for h in [0..k+1] do 
         A[k+1,h+1] := 0; 
         if (h gt 0) then 
            A[k+1,h+1] := A[k+1,h+1] + (2*h-2)*(2*h-1)*A[k,h]; 
         end if; 
         if (h lt k) then 
            A[k+1,h+1] := A[k+1,h+1] + (2*h+2)*(2*h+1)*a4*A[k,h+2]; 
         end if; 
         if (h lt k-1) then 
            A[k+1,h+1] := A[k+1,h+1] + (2*h+4)*(2*h+2)*a6*A[k,h+3]; 
         end if; 
      end for; 
   end for; 
   for k in [1..n-1] do 
      Pow[k+1] :=  
         ( Coefficient(WP1,2*k) - Coefficient(WP0,2*k) )/(2*(2*k+1)) 
         - ( &+[ A[k+1,h+1]*Pow[h] : h in [1..k] ]  
              + A[k+1,1]*n )/Factorial(2*k+1); 
   end for; 
   return Pow; 
end function; 
 
function PowerToSymmetricSums(Pow)
   Sym := Pow; 
   for j in [2..#Sym] do 
      Sym[j] := ( (-1)^(j-1)*Pow[j] +  
         &+[ (-1)^(k-1)*Pow[k]*Sym[j-k] : k in [1..j-1] ] )/j; 
   end for; 
   return Sym; 
end function;
 
function VeluImageCurve(E0,psi0)
   // {Returns codomain E1 of the isogeny of Velu, defined with 
   // respect to the monic kernel polynomial psi0.} 

   R := BaseRing(E0); 
   F := FunctionField(R);
   a1,a2,a3,a4,a6 := Explode(aInvariants(E0)); 
   b2,b4,b6 := Explode(bInvariants(E0)); 
   Psi0 := Numerator(F!Eltseq(psi0)[1]); 
   S := Parent(Psi0); X := S.1;
   Psi2 := 4*X^3 + b2*X^2 + 2*b4*X + b6; // a polynomial. 
   r := Degree(Psi0); 
   e := Degree(GCD(Psi2,Psi0)); 
   N := 2*r + e + 1;  
   s1 := -Coefficient(Psi0,r-1); 
   s2 := R!0; s3 := R!0; 
   if r ge 3 then 
      s2 := Coefficient(Psi0,r-2);  
      s3 := -Coefficient(Psi0,r-3); 
   elif r ge 2 then  
      s2 := Coefficient(Psi0,r-2);  
   end if; 
   a1,a2,a3,a4,a6 := Explode(aInvariants(E0)); 
   b2,b4,b6,b8 := Explode(bInvariants(E0)); 
   p1 := s1; p2 := s1^2 - 2*s2; p3 := s1^3 - 3*s1*s2 + 3*s3; 
   t0 := 6*p2 + b2*p1 + r*b4; 
   w0 := 10*p3 + 2*b2*p2 + 3*b4*p1 + r*b6; 
   if (N mod 2) eq 1 then 
      E1 := EllipticCurve([a1,a2,a3,a4 - 5*t0,a6 - b2*t0 - 7*w0]); 
   else  
      E1 := EllipticCurve([a1,a2,a3,a4 - 5*t0/2,a6 - b2*t0/2 - 7*w0/2]); 
   end if; 
   return E1; 
end function;

