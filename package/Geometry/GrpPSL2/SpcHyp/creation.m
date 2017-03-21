freeze;

////////////////////////////////////////////////////////////////
//                                                            // 
//                   Creation functions                       // 
//                                                            //
////////////////////////////////////////////////////////////////

// creation of the upper half plane:

intrinsic UpperHalfPlane() -> SpcHyp
    {The set of points in the complex plane which are
    rational or have positive imaginary part, together
    with infinity.}
    H := New(SpcHyp); 
    H`dimension := 1;
    return H;
end intrinsic;

intrinsic UpperHalfPlaneWithCusps() -> SpcHyp
   {Don't use this -- use UpperHalfPlane instead.}
   return UpperHalfPlane();
end intrinsic;
   
intrinsic UpperHalfPlaneUnionCusps() -> SpcHyp
   {Don't use this -- use UpperHalfPlane instead.}
   return UpperHalfPlane();
end intrinsic; 


intrinsic UpperHalfPlane(G::GrpPSL2) -> SpcHyp
    {For internal use.}

    require assigned G`EichlerOrder:
        "Argument 1 must have an Eichler order";
    f := G`MatrixRepresentation;
    H := New(SpcHyp); 
    H`dimension := 1;
    H`scalar_field := BaseRing(Codomain(f));
    H`discriminants := [];
    H`quadratic_fields := [];
    return H;
end intrinsic;




// following functions are called by the coercions below.

function HalfPlaneEltReal(X,x)
   // X::SpcHyp,x::FldComElt) -> SpcHypElt
    error if Imaginary(x) lt 0, "Second argument must have non
    negative imaginary part";
    z := New(SpcHypElt);
    z`is_exact := false;
    z`is_cusp  := false;
    z`complex_value := x;
    z`exact_value := x;
    z`parent := X;
    return z;
end function;

function HalfPlaneEltCusp(X,x)
   // (X::SpcHyp,x::SetCspElt) -> SpcHypElt
    z := New(SpcHypElt);
    z`is_exact := true;
    z`is_cusp  := true;
    u,v:= Explode(Eltseq(x));
    if v eq 0 then z`complex_value := Infinity();
    else z`complex_value := 1.0*ComplexField()!(u/v);
    end if;
    z`exact_value := x;
    z`parent := X;
    return z;
end function;

function HalfPlaneEltRat(X,x)
   // X::SpcHyp,x::FldRatElt) -> SpcHypElt
    return HalfPlaneEltCusp(X,Cusps()!x);
end function;

// the following is replaces by
// HalfPlaneFldQuadElt below.
// temporarilty kept for reference

function HalfPlaneEltQuad(X,x)
   // X::SpcHyp,x::FldQuadElt) -> SpcHypElt
    z := New(SpcHypElt);
    z`is_exact := true;
    z`is_cusp  := false;
    C := ComplexField();
    z`complex_value := 1.0*C!x; 
    if Imaginary(z`complex_value) lt 0 then
       z`complex_value := Real(z`complex_value)
       - Imaginary(z`complex_value);
    end if;
    // if Imaginary(v) eq 0 and Real(v) lt 0 then v:=-v; end if;
    if assigned X`scalar_field then
	L := X`scalar_field;
        K := Parent(x);
	dL := SquarefreeFactorization(Discriminant(L));
	dK := SquarefreeFactorization(Discriminant(K));
	if not ((dK eq dL) or (dK eq 1)) then
	    error if dK gt 0, "Argument 2 must be defined over an " *
	    "imaginary quadratic field";
	    // cF := GCD(dK,dL);
	    // dF := dK div cF;
	    PL := PolynomialRing(L);
	    t := PL.1;
	    LK := NumberField(t^2-dK);
	    x := LK!Eltseq(x);
	end if;
    end if;    
    z`exact_value := x;
    z`parent := X;
    return z;
end function;



function HalfPlaneFldQuadElt(X,x)
    // Constructor for FldQuad -- supporting automatic coercion
    // into the complex field and using a generator of trace 0.
    z := New(SpcHypElt);
    z`is_exact := true;
    // note, if the imaginary part is zero,
    // something is still not a cusp unless it's rational.
    z`is_cusp := (Discriminant(Parent(x)) gt 0) and
    IsCoercible(Rationals(),x);
    // note, to avoid more work, this case should be dealt with
    // separately from the working below.
	   
    z`complex_value := 1.0*ComplexField()!x; 

    if Imaginary(z`complex_value) lt 0 then
       z`complex_value := Real(z`complex_value)
       - Imaginary(z`complex_value);
    end if;

    // have replaced the following by the above.
    // if Imaginary(z`complex_value) lt 0 then
    // x *:=  -1;
    // z`complex_value *:=  -1;
    // end if;
    
    if assigned X`scalar_field then
        L := X`scalar_field;
        K := Parent(x);
        dL := SquarefreeFactorization(Discriminant(L));
        dK := SquarefreeFactorization(Discriminant(K));
        // error if dK gt 0,
        //    "Argument 2 must be an element of an imaginary quadratic field";
        cF := GCD(dK,dL);
        dF := (dL div cF)*(dK div cF);
        PL := PolynomialRing(L); 
        dE := Max(dK,dF);
        i := Index(X`discriminants, dE);
        if i eq 0 then
            E := NumberField(PL![-dE,0,1]);
            Append(~X`discriminants,dE);
            Append(~X`quadratic_fields,E);
        else
            E := X`quadratic_fields[i];
        end if;
        if dE eq dK then
            // A quadratic field has x^2-dE as defining equation.
            x := E ! Eltseq(x); 
        else
            t1 := L.1;
            a1 := Trace(t1)/2;
            _, m1 := IsSquare(Rationals()!(t1-a1)^2/dL);
            b1, b2 := Explode(Eltseq(x));
            x := E ! [ b1, cF*m1*b2/(t1-a1) ];
        end if;
    end if;    
    z`exact_value := x;
    z`parent := X;
    return z;
end function;

   
function HalfPlaneEltBiQuad(X,x)
   // (X::SpcHyp,x::FldNumElt) -> SpcHypElt
    z := New(SpcHypElt);
    z`is_exact := true;
    z`is_cusp  := false;
    C := ComplexField();
    u, v := Explode(Eltseq(x));
    
    //    z`complex_value := C!x; 
    if Parent(x) eq ScalarField(X) then
	KL := Parent(x);
	f := DefiningPolynomial(KL);
	D := -Integers()!Coefficient(f,0);
	KD := QuadraticField(D);    
	root_D := C!(KD.1);
	z`complex_value := u + v*root_D;
	z`exact_value := x;  
	z`parent := X;    
    return z;
    end if;
    
    KL := Parent(x);
    f := DefiningPolynomial(KL);
//    d1 := AbsoluteDiscriminant(KL);
    
    
    D := -Integers()!Coefficient(f,0);

    // for defining the complex embedding:

    KD := QuadraticField(D);    
    root_D := C!(KD.1);


    // should have Ku equal to scalar_field of X.
    u := ScalarField(X)!u;
    v := ScalarField(X)!v;
    
    Ku := Parent(u);
    du := SquarefreeFactorization(Discriminant(Ku));
    Ku_quad := QuadraticField(du);
    u1, u2 := Explode(Eltseq(u));
    v1, v2 := Explode(Eltseq(v));
    root_du := C!(Ku_quad.1);
    z`complex_value:=u1 + u2*root_du + (v1 + v2*root_du)*root_D;
    if Imaginary(z`complex_value) lt 0 then
       z`complex_value :=
       Real(z`complex_value) - C.1*Imaginary(z`complex_value);
    end if;
    
    z`exact_value := x;  
    z`parent := X;
    
    return z;
end function;
    


    
////////////////////////////////////////////////////////////////
//                                                            //
//                     Coercions                              //
// from:                                                      //
// SpcHypElt, SetCspElt, FldComElt,  FldRatElt, FldNumElt.     // 
////////////////////////////////////////////////////////////////

forward comparable;

intrinsic IsCoercible(X::SpcHyp,x::.) -> BoolElt, SpcHypElt
    {}
    case Type(x):
      when SpcHypElt:
         return true, x;
      when SetCspElt:
         return true, HalfPlaneEltCusp(X,x);
      when SeqEnum:
         if Type(Universe(x)) eq SetCsp then
	    return true, [HalfPlaneEltCusp(X,y) : y in x];	    
	 end if;
	 return false, "Illegal coercion"; 
      when FldComElt:
         if Imaginary(x) lt 0 then 
             return false, "elements of the upper half plane union 
                            rationals
                            must have non negative imaginary value";
         end if;
         return true, HalfPlaneEltReal(X,x);
      when FldRatElt:
         return true, HalfPlaneEltCusp(X,Cusps()!x);
      when RngIntElt:
         return true, HalfPlaneEltCusp(X,Cusps()!x);
      when Infty:
         return true, HalfPlaneEltCusp(X,Cusps()!x);
      when FldQuadElt, FldNumElt, RngOrdElt, RngQuadElt:
         if x eq 0 then
	    return true, HalfPlaneEltCusp(X,Cusps()!0);
	 end if;	   
	 K := Parent(x);
	 if Type(x) eq FldQuadElt and Discriminant(K) gt 0 then
	    return true, HalfPlaneFldQuadElt(X,x);
	 end if;
	 deg := Degree(K);
	 if deg gt 2  then
	     return false, "Illegal coercion";	
	 elif deg eq 1 then
	     L := ScalarField(X);
	     val, x := IsCoercible(L,x); 
	     return val, HalfPlaneFldQuadElt(X,x);
	  elif assigned X`scalar_field then
	    require BaseField(Parent(x)) eq X`scalar_field
	    or BaseField(Parent(x)) eq Rationals()
	    or Parent(x) eq X`scalar_field:
	    "second argument must be in a quadratic extension of
	    the rationals, or of the BaseField of the
	    first argument";
	    return true, HalfPlaneEltBiQuad(X,x); 
	 else
	    deg_abs := AbsoluteDegree(K);
	    if deg_abs eq 2 then
	       poly := AbsoluteMinimalPolynomial(x);
	       if Degree(poly) lt 2 then
		  val, x := IsCoercible(Rationals(),x);
		  return val, HalfPlaneFldQuadElt(X,x);
	       end if;
	       disc := Discriminant(poly);		 
	       coefs := Coefficients(poly);
	       a := coefs[3];
	       b := coefs[2];
	       c := Denominator(Rationals()!disc);
	       D,sq := SquarefreeFactorization(Integers()!(disc*c^2));
	       K := QuadraticField(D);
	       y := K.1;	       
	       A := -b/(2*a);
	       sign := 1;
	       if D gt 0 and Degree(Parent(x)) eq 2 then
		  sign := Sign(Eltseq(x)[2]);
	       end if;
	       B :=  sign*sq/(2*a*c);
	       return true, HalfPlaneFldQuadElt(X,K!(A+B*y));
	    end if;
	 end if;
      else 
	 return false, "Illegal coercion"; 
      end case;
end intrinsic;


// this function is not used and does not work!
function comparable(x,K)
    // this function tests whether x is in a quadratic
    // extension of K, or can be forced to be in such an
    // extension
    error if not
	(Type(Parent(x)) in {RngInt, FldRat, FldNum, FldQuad}),
	"First arguement should be an integer or rational or
	in a number field or quadratic field";
    if Parent(x) cmpeq Rationals() or
	Parent(x) cmpeq Integers() then
	return true, x;
    end if;
    if Degree(Parent(x)) gt 2 then 
	return false, 0;
    end if;
    if Degree(Parent(x)) eq 2 then
	return true, x;
    end if;
    return false, 0;
end function;
 

////////////////////////////////////////////////////////////////////////
//                                                                    //
//              Special Constructor for Roots of Unity                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic RootOfUnity(H::SpcHyp,n::RngIntElt) -> SpcHypElt
    {An nth root of unit in H, where n is in 3, 4, or 6.}
    require n in {3,4,6} : "Argument 2 must be 3, 4, or 6.";
    P := PolynomialRing(Integers());
    if n eq 4 then
        K := QuadraticField(-1);
        u := (-1 + K.1)/2;
    else 
        K := QuadraticField(-3);
        u := n eq 3 select (-1 + K.1)/2 else (1 + K.1)/2;
    end if;
    z := HalfPlaneFldQuadElt(H,u);
    return z;
end intrinsic;
