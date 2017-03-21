freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        CLASS POLYNOMIALS                           //
//                       Created November 1999                        //
//                     Last modified April 2001                       //
//          (mch) Updated April 2005 for new real/complex types       //
//           mch June 2005 - Generalised WeberClassPolynomial to      //
//            cover all discriminants D with D != 5 mod 8             //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// Intrinsics: HilbertClassPolynomial, WeberClassPolynomial
 
forward NormalizedWeber,WeberToj,Type,WeberTojConsts; 

intrinsic WeberToHilbertClassPolynomial(
    f::RngUPolElt,D::RngIntElt : Al := "Roots") -> RngUPolElt
    {Returns the Hilbert class polynomial for D.} 
    if Al eq "Roots" then
	r,A,B,C := Explode(WeberTojConsts(D));
	CC := ComplexField();
	fseq := Roots(f,CC);
	jseq := [ A*(B*f+C)^3/f where f := rt[1]^r : rt in fseq ];
	prec := Ceiling(1.1*Log(10,1+Abs(Real(&*jseq))));
	if Precision(CC) lt prec then
	    print "Setting new precision to ", prec;
	    CC := ComplexField(prec);
	    fseq := Roots(f,CC);
	    jseq := [ A*(B*f+C)^3/f where f := rt[1]^r : rt in fseq ];
	end if;
	PC := PolynomialRing(CC);
	h := &*[ X - j : j in jseq ] where X := PC.1;
	return Parent(f)![ Round(Real(c)) : c in Eltseq(h) ];
    end if;
    R := WeberToj(D);
    P2<X,J> := PolynomialRing(RationalField(),2);
    /* (mch) Resultant seems a bit quicker than EliminationIdeal */
    H := UnivariatePolynomial( Resultant(J*Evaluate(Denominator(R),X) - 
             Evaluate(Numerator(R),X),Evaluate(f,X),X) );
    return Parent(f)!Normalise(H);
end intrinsic;

intrinsic HilbertClassPolynomial(D::RngIntElt) -> RngUPolElt 
    {"} // "
    require D lt 0 : "Argument must be negative"; 
    require D mod 4 in {0,1} : "Argument is not a discriminant."; 
    CC := ComplexField(); 
    ClassForms := ReducedForms(D);
    sqrtD := Sqrt(D);
    prec := Ceiling( &+ [ Log(10,1+Abs( jInvariant(
         (q[2] + sqrtD)/(2*q[1]) ) ) ) : q in ClassForms ] ) + 8;
    CC := ComplexField(prec); 
    sqrtD := Sqrt(CC!D);
    PC := PolynomialRing(CC); Y := PC.1;
    h := &*[ Y - jInvariant( (q[2] + sqrtD)/(2*q[1]) ) : q in ClassForms ]; 
    PZ := PolynomialRing(Integers()); X := PZ.1; 
    return &+[ Round(Real(Coefficient(h,i)))*X^i : i in [0..Degree(h)] ]; 
end intrinsic; 
 
intrinsic WeberClassPolynomial(D::RngIntElt : Lambda := 1.1) 
   -> RngUPolElt,FldFunRatUElt
   {The class polynomial of binary quadratic forms of discrimant D, 
   in terms of Weber functions. Also returned is the rational function
   expressing the corresponding j-invariants in terms of the roots }

   require D lt 0: "Argument must be negative.";
   require (D mod 4) in {0,1} : "Argument is not a discrimiant."; 
   require (D mod 8) ne 5: "Argument congruent to 5 mod 8.";
   require Lambda gt 1 : "Parameter Lambda must be greater than 1";
   prec := Max(16,Ceiling(Sqrt(-D/4)));
   CC<i> := ComplexField(prec); 
   PC := PolynomialRing(CC); Y := PC.1;
   ClassForms := ReducedForms(D);
   e := GCD(D,3);
   coeffs := Coefficients( 
      &*[ Y - NormalizedWeber(F,i)^e : F in ClassForms ] );
   MaxImag := Max([ Abs(Imaginary( coeffs[i] )) : i in [1..#coeffs] ]); 
   MaxReal := Max([ Abs(Real( coeffs[i] )) : i in [1..#coeffs] ]); 
   LogMaxReal := Ceiling(Log(10,1+MaxReal));
   while prec lt Lambda*LogMaxReal or 0.1 lt MaxImag do
      prec := Ceiling( Lambda*Max(LogMaxReal,prec) );
      CC<i> := ComplexField(prec);
      PC := PolynomialRing(CC); Y := PC.1; 
      coeffs := Coefficients( 
         &*[ Y - NormalizedWeber(F,i)^e : F in ClassForms ] );
      MaxImag := Max([ Abs(Imaginary( coeffs[j] )) : j in [1..#coeffs] ]); 
      prec := Ceiling(Lambda*prec);
   end while;
   PZ := PolynomialRing(Integers()); X := PZ.1; 
   return &+[ Round( Real( coeffs[i] ) )*X^(i-1) : i in [1..#coeffs] ],
             WeberToj(D); 
end intrinsic;

/* Types:
		0 - D = 7 mod 8
		1 - D/4 = 1 mod 8
		2 - D/4 = 2 mod 4
		3 - D/4 = 3 mod 8
		4 - D/4 = 4 mod 8
		5 - D/4 = 5 mod 8
		6 - D/4 = 7 mod 8
		7 - D/4 = 8 mod 8
*/
function Type(D)
    if IsOdd(D) then return 0; end if;
    d1 := (D div 4) mod 8;
    if (d1 gt 0) and (d1 lt 6) then return d1; end if;
    case d1:
	when 0: return 7;
	when 6: return 2;
	when 7: return 6;
    end case;
end function;

/* 
   For form aX^2+bXY+cY^2 of disc D, find an SL2-equivalent form
   a1X^2+b1XY+c1Y^2, where 
   i) a1 is odd and 32|b1 if D=0 mod 4 or b1=a1 mod 16 if D=1 mod 8
   ii) if D !=0 mod 3 then 3|b1 or (3|a1 and 3|c1) [unless D odd - see below]
   Returns M^-1,a1 where M is the SL2(Z) matrix giving the transformation.
*/
function NormaliseForm(abc,D)

    a := abc[1]; b := abc[2]; c := abc[3];

    Z := IntegerRing();
    M := Matrix(Z,[[1,0],[0,1]]);
    div3 := ((D mod 3) ne 0);
    
    // first transform to make a odd
    if IsEven(a) then
	if IsEven(c) then // only poss for D = 1 mod 8
	    a +:= b+c; b +:= 2*c;
	    M[2,1] := 1;
	else
	    b := -b; t := c; c := a; a := t;
	    M := Matrix(Z,[[0,-1],[1,0]]);
	end if;
    end if;
        
    // if D != 0 mod 3 then transform so 3|b or (3|a and 3|c)
    //  - slightly different for D=1 mod 8 where the normalisation
    //    is equiv to normalising [a,2*(b-a),4*c-2*b+a] for D=4 mod 32
    if div3 then
	if (a mod 3) eq 0 then
	    h := (-c * (b mod 3)) mod 3;
	else  
	    h := (b * (a mod 3)) mod 3;
	end if; 
	if IsOdd(D) then h -:= 1;
	elif h eq 2 then h -:= 3; end if;
	c +:= h*(b+h*a);
	b +:= 2*h*a;
	M *:= Matrix(Z,[[1,h],[0,1]]); 
   end if;
   
   // now transform by [a,b,c] -> [a,b+2*h*a,c+h*b+h^2*a] 
   // where h=0 mod 3 if div3
   B := IsOdd(D) select (a-b) div 2 else -b div 2;
   if div3 then
        A := [a,1]; B := [B,0]; N := [32,3];
   else   
        A := [a]; B := [B]; N := [32];
   end if;
   h := Solution(A,B,N);
   M *:= Matrix(Z,[[1,h],[0,1]]);
   
   return Matrix(Z,2,2,[M[2,2],-M[1,2],-M[2,1],M[1,1]]),a;
 
end function;

function GenFEval(z,M,r,n,j,i)
   // z in the upper half-plane, M in SL2(Z), r =0,1,2, j,n in Z.
   //  returns zeta48^j*Fr(Mz)^n where Fr is the rth Weber function
   //   and zeta48 is exp(pi*i/24)
   
   zeta_p := j;
   
   //convert to r=2 case
   case r:
     when 0:  zeta_p -:= n; M := Matrix(Integers(),[[1,0],[1,1]]) * M;
     when 1:  M := Matrix(Integers(),[[0,1],[-1,0]]) * M;
   end case;  
   
   // and now convert again with appropriate zeta48 multiplier   
   a,b,c,d := Explode(Eltseq(M));
   if IsEven(c) then
      r:=2;
   elif IsEven(d) then
      r:=1;
      d0 := c; c := -d; b0 := a; 
      a := -b; d := d0; b := b0;
   else
      r := 0;
      zeta_p +:= n;
      a -:= b; c -:= d;
   end if;
   //multiplier:
   zeta_p +:= n*(a*(2*b+c)+(d*c+3)*(a^2-1));
   zeta_p mod:= 48;
   if zeta_p ge 24 then zeta_p -:= 48; end if;
   
   //compute zeta48 multiplier in C
   m := GCD(zeta_p,48);
   zeta_p div:= m; m := 48 div m;
   if m eq 1 then
     zm := 1;
   elif m eq 2 then
     zm := -1;
   else
     zm := Exp(2*Pi(Parent(i))*zeta_p*i/m);
   end if;
   
   case r:
     when 0:  fn := WeberF(z)^n;
     when 1:  fn := WeberF1(z)^n;
     when 2:  fn := WeberF2(z)^n;
   end case;
   
   return zm*fn;
   
end function;   

/* A normalized Weber function on binary quadratic forms.
   By type (see above):
		0 - zeta48*F2(z)
		1 - F(z)^2/Sqrt(2)
		2 - F1(z)^2/Sqrt(2)
		3 - F(z)
		4 - F1(z)^4/(2*Sqrt(2))
		5 - F(z)^4/2
		6 - F(z)/Sqrt(2)
		7 - F1(z)^8/8
   If D = 0 mod 3 then the cubes of these values are used.
*/
function NormalizedWeber(F,i)

   D := Discriminant(F);
   type := Type(-D);
   CC := Parent(i); 
   a, b, c := Explode(Eltseq(F));
   M,a1 := NormaliseForm(Eltseq(F),D);
   tau := ( -b + Sqrt(CC!(b^2 - 4*a*c)) )/( 2*a );

   case type:
     when 0:  val := GenFEval(tau,M,2,1,1,i);
     when 1:  val := GenFEval(tau,M,0,2,0,i)/Sqrt(CC!2);
     when 2:  val := GenFEval(tau,M,1,2,0,i)/Sqrt(CC!2);
     when 3:  val := GenFEval(tau,M,0,1,0,i);
     when 4:  val := GenFEval(tau,M,1,4,0,i)/(2*Sqrt(CC!2));
     when 5:  val := GenFEval(tau,M,0,4,0,i)/2;
     when 6:  val := GenFEval(tau,M,0,1,0,i)/Sqrt(CC!2);
     when 7:  val := GenFEval(tau,M,1,8,0,i)/8;
   end case;
   
   //for types 0,1,2,4,6, val must be multiplied by Jacobi symbol (2/a1)
   if ((a1^2 mod 16) ne 1) and (IsEven(type) or (type eq 1)) then
      val := -val;
   end if;
   
   return val;
   
end function;

function WeberToj(D)
   // for discriminant D, returns the rational function f(X) s.t.
   // j(t) := f(W(t)) where W is the normalised Weber function for D
   
   F := RationalFunctionField(Rationals());
   x := F.1;
   seq := WeberTojConsts(D);
   return seq[2]*(seq[3]*(x^seq[1])+seq[4])^3/(x^seq[1]);   
   
end function;

function WeberTojConsts(D)
   // The rational WeberToj function (see above fn) is of the form
   // f(x) = A*(B*x^r+C)^3/x^r for some r|24 and A,B,C +- pows of 2
   // Fn returns [r,A,B,C]
   
   type := Type(-D);
   r := ((D mod 3) eq 0) select 1 else 3;
   case type:
     when 0:  return [8*r,1,1,-16];
     when 1:  return [4*r,64,4,-1];
     when 2:  return [4*r,64,4,1];
     when 3:  return [8*r,1,1,-16];
     when 4:  return [2*r,8,32,1];
     when 5:  return [2*r,64,4,-1];
     when 6:  return [8*r,1,256,-1];
     when 7:  return [r,8,32,1];
   end case;

end function;
