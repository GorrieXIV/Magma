freeze;

forward WeierstrassFunction;

function ElkiesKernel(E,F,p,p1)
   // Find the kernel polynomial for E -> F of degree p with
   // first power sum p1.

   FF := CoefficientRing(E);
   extra := 4;
   bEven := IsEven(p);
   deg := bEven select p-1 else (p-1) div 2;
    
   _,_,_,e4, e6 := Explode(Coefficients(E));
   _,_,_,e4_tilde, e6_tilde := Explode(Coefficients(F));
   c := WeierstrassFunction(E,deg+extra+1);
   c_tilde := WeierstrassFunction(F,deg+extra+1);

   P := PolynomialRing(FF);
   X := P.1;
   psi2 := 4*X^3 + 4*e4*X + 4*e6;
   dpsi2 := 6*X^2 + 2*e4;
   mulist := [ dpsi2 ];
   for k in [2..deg+extra] do
      coeffs := Eltseq(mulist[k-1]);
      np := coeffs[2] * dpsi2;
      for i in [2..#coeffs-1] do
	 np +:= i * coeffs[i+1] * 
	        (dpsi2 * X^(i-1) + (i-1) * psi2 * X^(i-2) );
      end for;
      Append(~mulist, np);
   end for;

   M := KMatrixSpace(FF, deg+extra, deg+2+extra)!0;
   r := bEven select FF!1 else FF!2;
   for k in [1..deg+extra] do
      coeffs := Eltseq(mulist[k]);
      for i in [1..#coeffs] do
	 M[k,i] := coeffs[i] * r / Factorial(2*k);
      end for;
   end for;

   B := VectorSpace(FF, deg+extra)!
        [ (Coefficient(c_tilde, 2*i) - Coefficient(c, 2*i)) 
                              : i in [1..deg+extra] ];
   v0, V := Solution(Transpose(M), B);
   error if Dimension(V) ne 2,
      "Power sums not uniquely determined in kernel reconstruction";
   v1, v2 := Explode(Basis(V));
       
   p0 := deg;
   v0 +:= (p0 - Eltseq(v0)[1]) * v1;
   v0 +:= (p1 - Eltseq(v0)[2]) * v2;
   ps := Eltseq(v0);

   // Using Newton sums
   symm := [ FF!0 : i in [1..deg+1+extra] ];
   symm[deg+1+extra] := FF!1;
   for k in [1..deg+extra] do
      sk := ps[k+1];
      for i in [1..k-1] do
	 sk +:= symm[deg+extra-i+1] * ps[k-i+1];
      end for;
      symm[deg+extra-k+1] := -sk / k;
   end for;
   success := &and[ symm[i] eq 0 : i in [1..extra] ];
   return P!symm[extra+1..deg+extra+1], success;
end function;

function WeierstrassFunction(E,num_terms)
    // The Weierstrass series of E, assumes that E is in 
    // simplified Weierstrass form. 

    _, _, _, a4, a6 := Explode(Coefficients(E));
    Q := LaurentSeriesRing(BaseRing(E));
    z := Q.1;

    c := [ -a4/5, -a6/7 ];
    for k in [3..num_terms-1] do
        Append(~c, 3*( &+[ c[h]*c[k-1-h] : h in [1..k-2] ] )
                 / ((k-2) * (2*k + 3)) );
    end for;
    return z^-2 + &+[ c[k]*z^(2*k) : k in [1..num_terms-1] ] 
               + O(z^(2*num_terms));
end function;

