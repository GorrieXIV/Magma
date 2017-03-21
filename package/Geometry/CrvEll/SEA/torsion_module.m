freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         TORSION MODULES                            //
//   (Capturing data of a finite approximations to the Tate module)   //
//                  Based on code of Richard Rannard                  //
//                      Rewritten by David Kohel                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "atkin.m": TorsionModuleTraceRamified, 
        TorsionModuleTraceNonmaximal, TorsionModuleTraceAtkin;        
import "elkies.m": CodomainAtkin, CodomainCanonical, KernelPolynomial,
        IsogenyPhi, Prime2BigChar;
import "lercier.m": Lercier;
import "menezes.m": Menezes;
import "schoof.m": TraceSchoof, TraceSchoofExtend;

forward TorsionModuleTraceElkies, TorsionModuleTraceElkiesPower,
        Prime2PowerTraceChar2;  

////////////////////////////////////////////////////////////////////////
//               Definition of Torsion Module Record                  //
////////////////////////////////////////////////////////////////////////

ModTors := recformat< 
    E              : CrvEll,   // The elliptic curve.
    char_type      : RngIntElt,  // Parity of characteristic of base ring of E.
    prime          : RngIntElt,  // The prime level.
    prime_exponent : RngIntElt,  // The current exponent of the prime.
    prime_type     : MonStgElt,	 // The prime type ("Elkies", "Atkin", 
                                 // "Ramified", or "Nonmaximal").
    trace,         // Trace of Frobenius mod (prime^prime_exponent). 
                   // Type is RngIntElt if uniquely determined, else SeqEnum.
    modular_model  : MonStgElt,  // Either "canonical" or "star" model.
    modular_eqn    : RngMPolElt, // The prime'th modular equation coerced
       				 // into the polynomial ring associated to E.
    modular_points : SeqEnum,    // Points on modular curve. 
    kernel_poly    : RngUPolElt, // Elkies kernel polynomial.
    lambda         : RngIntElt,  // Elkies eigenvalue.
    x_pow	   : RngUPolElt,  // x^#BaseRing(E) mod modular_eqn
    entropy        : FldReElt,   // Log(#trace) - Log(prime).
    // 
    I_im2,         // : FldFunRatUElt, ??? Unknown. ???
    E_im1          : CrvEll,   // ??? First image curve. ???
    E_im2          : CrvEll   // ??? Second image curve. ???
>;

////////////////////////////////////////////////////////////////////////
//                     Torsion Module Constructor                     //
////////////////////////////////////////////////////////////////////////

function TorsionModule(E,ell : Initialize := true) 
    // Initialize a torsion module for prime ell.
    odd_even := #BaseRing(E) mod 2;
    T := rec< ModTors | E := E, prime := ell, char_type := odd_even >;
    if Initialize then
	P2 := CoordinateRing(AffinePatch(Ambient(E),1));
	T`prime_exponent := 0;  
	if ell le 101 then
	    T`modular_eqn := P2 ! CanonicalModularEquation(ell);
	    T`modular_model := "canonical";
	else
	    T`modular_eqn := P2 ! AtkinModularEquation(ell);
	    T`modular_model := "star";
	end if;
    else 
	T`prime_exponent := 1;  
	T`prime_type := "Atkin";
        T`trace := [0..ell-1];
    end if;
    return T;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

procedure Prime2TraceChar2(~T)
    // Process the prime 2 when the characteristic is 2.
    // Doesn't matter if T is Elkies or Atkin.
    // Assumes that E is ordinary.

    if (T`prime_exponent eq 0) then
        // Always these values.
        T`lambda := 1;
        T`prime_exponent := 2;
        T`trace := 1;
        T`entropy := -2*Log(2);
    else
        Prime2PowerTraceChar2(~T);
    end if;
    return;
end procedure;

procedure Prime2PowerTraceChar2(~T)
    // Process the prime 2 when the characteristic is 2.
    // Doesn't matter if T is Elkies or Atkin.

    T`prime_exponent +:= 1;
    T`kernel_poly := Menezes(T`E,T`prime_exponent);
    TraceSchoofExtend(~T);
    T`entropy := -(T`prime_exponent)*Log(2);
end procedure;

procedure TorsionModuleTypeChar2(~T)
   // Fills in the type of the prime, which can be
   // "Elkies", "Atkin", "Ramified", or "Pathological".

   if (assigned T`prime_type) then return; end if;
   if (assigned T`modular_points) then return; end if;

   if (T`prime eq 2) then
      T`prime_type := "Pathological";
      return;
   end if;

   modular_poly := UnivariatePolynomial(
      Evaluate(T`modular_eqn,2,jInvariant(T`E)) );
   x := Parent(modular_poly).1;

   d := Degree(modular_poly);
   vprintf SEA, 2:
       "Computing x^q mod modular equation (degree %o).\n", d;
   vtime SEA, 2: 
   x_pow := Modexp(x,#BaseRing(T`E),modular_poly);

   T`x_pow := x_pow;

   modular_roots := Roots(GCD(x_pow - x, modular_poly));
   multiplicities := { r[2] : r in modular_roots };

   if T`modular_model eq "canonical" then
      T`modular_points := [ 1/r[1] : r in modular_roots | r[1] ne 0 ];
   else
      T`modular_points := [ r[1] : r in modular_roots ];
   end if;

   if T`prime eq 2 then
      if #T`modular_points eq 0 then
	 T`prime_type := "Atkin";
      else
	 T`prime_type := "Pathological";
      end if;
   else
      if #multiplicities gt 0 and multiplicities ne { 1 } then 
	 T`prime_type := "Pathological";
      else
	 case #T`modular_points:
	    when 0:  T`prime_type := "Atkin";
	    when 1:  T`prime_type := "Ramified";
	    when 2:  T`prime_type := "Elkies";
	    when T`prime+1: T`prime_type := "Nonmaximal";
	 else
	    T`prime_type := "Pathological";
	 end case;
      end if;
   end if;
end procedure;

procedure TorsionModuleType(~T)
    // Fills in the type of the prime, which can be
    // "Elkies", "Atkin", "Ramified", "Nonmaximal",
    // or (in characteristic two) "Pathological".

    if T`char_type eq 0 then 
	TorsionModuleTypeChar2(~T);
	return;
    end if;

    if (assigned T`prime_type) then return; end if;
    if (assigned T`modular_points) then return; end if;

    modular_poly := UnivariatePolynomial(
        Evaluate(T`modular_eqn,2,jInvariant(T`E)) );
    x := Parent(modular_poly).1;

    if T`prime eq 2 then  
        // Small degree, so don't try to optimize.
        num_rts := #Roots(modular_poly);
	if num_rts eq 0 then
	    T`prime_type := "Atkin";
	elif num_rts eq 1 then
	    T`prime_type := "Ramified";
	else
	    T`prime_type := "Nonmaximal";
	end if;
	return;
    end if;

    // This rarely happens, and if so, the curve has CM by 
    // a very small endomorphism ring.  
    // If taking time to check this case, then best to treat 
    // this completely and exit.

    if Degree(GCD(modular_poly, Derivative(modular_poly))) gt 0 then
        // Isogenies with multiplicities:
	T`prime_type := "Pathological";
	return;
    end if;

    d := Degree(modular_poly);
    vprintf SEA, 2: 
       "Computing x^q mod modular equation (degree %o).\n", d;
    vtime SEA, 2: 
    x_pow := Modexp(x,#BaseRing(T`E),modular_poly);
    T`x_pow := x_pow;

    linears := GCD(x_pow - x,modular_poly);

    num_roots := Degree(linears);
    vprint SEA, 2: "Number of roots:", num_roots;
    if num_roots eq 2 then	
	c, b, a := Explode(Coefficients(linears));
	s := Sqrt(b^2 - 4*a*c);
	assert (s ne 0);
	denom := 1/(2*a);
        T`modular_points := [ (-b + s)*denom, (-b - s)*denom ];
    end if;

    case num_roots:
        when 0:  T`prime_type := "Atkin";
        when 1:  T`prime_type := "Ramified";
        when 2:  T`prime_type := "Elkies";
        when T`prime+1:  T`prime_type := "Nonmaximal";
        else T`prime_type := "Pathological";
    end case;
end procedure;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

procedure TorsionModuleTrace(~T)
    // Finds candidates for the trace of E mod the prime in 
    // the torsion module.
    
    if (T`char_type eq 0) and (T`prime eq 2) then
	Prime2TraceChar2(~T);
	return;
    end if;

    error if not (assigned T`prime_type), 
        "Prime type undetermined in torsion module trace computation.";
    error if not (assigned T`modular_eqn), 
	"Modular equation undetermined in torsion " * 
	"module trace computation.";

    FF := BaseRing(T`E);
    non_optimized := not ( Characteristic(FF) gt (2*(T`prime)+1)
                         or Characteristic(FF) eq 2 );
    case T`prime_type:
        when "Atkin":
            TorsionModuleTraceAtkin(~T);
        when "Elkies":
            if non_optimized then 
		TorsionModuleTraceAtkin(~T);
            else
                TorsionModuleTraceElkies(~T);
            end if;
        when "Ramified":
            TorsionModuleTraceRamified(~T);
        when "Nonmaximal":
            TorsionModuleTraceNonmaximal(~T);
        when "Pathological":
	    // put in dummy values and return
            T`trace := 1;
            T`prime_exponent := 0;
        else
	    error "Prime type unrecognized in torsion " *
	    " module trace computation.";
    end case;
    // Should be set elsewhere:
    // T`prime_exponent := 1;
    return;
end procedure;

procedure TorsionModuleTracePower(~T)
    // Finds (candidates for) the trace of E mod a power of the prime 
    // in this prime_block.  The power is incremented by one each time 
    // this function is called.

    error if not (assigned T`prime_type), 
        "Prime type undetermined in torsion module trace computation.";
    error if (T`prime_exponent eq 0), 
       "Zero prime exponent in torsion module prime power computation.";

    if (T`char_type eq 0) and (T`prime eq 2) then
	Prime2TraceChar2(~T);
	return;
    end if;

    if T`prime_type eq "Elkies" then
	TorsionModuleTraceElkiesPower(~T);
    else 
	error "Unable to find trace modulo a power " *
	"of a non-Elkies prime.";
    end if;
    return;
end procedure;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

procedure ElkiesCanonicalInit(~T, ef)
    if T`prime eq 2 then
        T`E_im1, T`kernel_poly, success := Prime2BigChar(T`E, ef);
    else
        E_im1, p1_im1:= 
            CodomainCanonical(T`E, T`prime, T`modular_eqn, ef);
	if Type(E_im1) eq CrvEll then
	  T`E_im1 := E_im1;
          T`kernel_poly, success :=
            KernelPolynomial(T`E_im2, T`prime, T`E_im1, p1_im1);
	else /* division by 0 problem - treat as pathological case */
	  success := false;
	end if;
    end if;
    if not success then
    /* usually because of 'divide by 0 probs' in the parameter
       processing - treat as pathological                      */
	  T`kernel_poly := PolynomialRing(BaseField(T`E))!0;
    end if;	
end procedure;

procedure ElkiesAtkinInit(~T, ef)
    Pf := UnivariatePolynomial(Evaluate(T`modular_eqn, 1, ef));
    rts_Pf := [ r[1] : r in Roots(Pf) ];
    success := false;
    for j_tilde in  rts_Pf do
        E_im1, p1 := 
            CodomainAtkin(T`E, T`prime, T`modular_eqn, ef, j_tilde);
	if Type(E_im1) eq CrvEll then
	  T`E_im1 := E_im1;
          T`kernel_poly, success := 
            KernelPolynomial(T`E, T`prime, T`E_im1, p1);
          if success then break; end if;
	end if;
    end for;
    if not success then
    /* probably because of 'divide by 0 probs' in the parameter
       processing - treat as pathological                      */
	T`kernel_poly := PolynomialRing(BaseField(T`E))!0;
    end if;
end procedure;

procedure ElkiesChar2Init(~T, ef)
    Pf := Evaluate(T`modular_eqn, 1, ef);
    rts_Pf := [r[1] : r in Roots(UnivariatePolynomial(Pf))]; // !!
    vprint SEA, 2: "Found", #rts_Pf, "roots of modular equation.";
    success := false;
    for j_tilde in rts_Pf do
        T`E_im1 := EllipticCurveWithjInvariant(BaseRing(T`E) ! j_tilde);
        vtime SEA, 2:
        success, T`kernel_poly := Lercier(T`E, T`E_im1, T`prime); 
	if success then break; end if;
    end for;
    error if not success, "Failed to find Elkies kernel polynomial.";
end procedure;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

procedure TorsionModuleTraceElkies(~T)
    // Finds candidates for the trace of E mod the prime in this
    // torsion module.

    if (T`prime_exponent eq 0) then
        T`prime_exponent := 1;
    else
        TorsionModuleTraceElkiesPower(~T);
        return;
    end if;
    P := PolynomialRing(BaseRing(T`E));
    x := P.1;
    T`I_im2 := x;
    T`E_im2 := T`E;
    ef := T`modular_points[1];
    if (T`char_type eq 0) then
        ElkiesChar2Init(~T,ef);
    else
        if T`modular_model eq "canonical" then
            ElkiesCanonicalInit(~T,ef);
        else
            ElkiesAtkinInit(~T,ef);
        end if;
    end if;
    if T`kernel_poly eq 0 then /* treat as pathological */
      vprint SEA, 1: "Failed to find isogenous curve - ignoring prime.";
      T`prime_type := "Pathological"; T`trace := 1; T`prime_exponent := 0;
    else
      vprint SEA, 2: "Entering Schoof computation on kernel polynomial."; 
      TraceSchoof(~T);
    end if;
end procedure;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function VerifyKernelPolynomial(T, g_i, k_im1)
    qr := Numerator(Evaluate(g_i, k_im1 / (T`kernel_poly^2)));
    return DivisionPolynomial(T`E_im2, T`prime, qr) ne 0;
end function;

function ElkiesCanonicalLoop(T, eigen_roots, k_im1)
    // Find the exact kernel polynomial for given
    // a split prime with a Canonical modular equation. 
    for ei in [ r[1] : r in eigen_roots ] do
	if T`prime eq 2 then
	    E_i, g_i, success := Prime2BigChar(T`E_im1, ei);
	else
	    E_i, p1_i :=
	        CodomainCanonical(T`E_im1, T`prime, T`modular_eqn, ei);
	    g_i, success := KernelPolynomial(T`E_im1, T`prime, E_i, p1_i);
	end if;
	if success and VerifyKernelPolynomial(T, g_i, k_im1) then 
	    return E_i, g_i; 
	end if;
    end for;
    error "Failed to find kernel polynomial for canonical modular equation.";
end function;

function ElkiesAtkinLoop(T, eigen_roots, k_im1)
    // Find the exact kernel polynomial for given
    // a split prime with an Atkin modular equation. 
    for ei in [ r[1] : r in eigen_roots ] do
        Pf := UnivariatePolynomial(Evaluate(T`modular_eqn, 1, ei));
	rtsj := [ r[1] : r in Roots(Pf) ];
        vprint SEA, 2: "Found", #rtsj, "roots of modular equation.";
	success := false;
        for ji in rtsj do
	    E_i, p1_i := CodomainAtkin(T`E_im1, T`prime,
	        T`modular_eqn, ei, ji);
	    g_i, success := KernelPolynomial(T`E_im1, T`prime, E_i, p1_i);
	    if success then break; end if;
	    vprint SEA, 2: "Wrong curve, trying another.";
        end for;
	if success and VerifyKernelPolynomial(T, g_i, k_im1) then 
	    return E_i, g_i; 
	end if;
    end for;
    error "Failed to find kernel polynomial for Atkin modular equation.";
end function;

function ElkiesChar2Loop(T, modular_roots, k_im1)
    for ei in modular_roots do
        Pf := UnivariatePolynomial(Evaluate(T`modular_eqn, 1, ei));
	rtsj := [ r[1] : r in Roots(Pf) ];
        vprint SEA, 2: "Found", #rtsj, "roots of modular equation.";
	success := false;
        for ji in rtsj do
	    E_i := EllipticCurveWithjInvariant(BaseRing(T`E) ! ji);
            success, g_i := Lercier(T`E_im1, E_i, T`prime);
	    if success then break; end if;
	    vprint SEA, 3: "Incorrect curve, trying another.";
        end for;
	if success and VerifyKernelPolynomial(T, g_i, k_im1) then 
	    return E_i, g_i; 
	end if;
    end for;
    error "Failed to find kernel polynomial for Atkin modular equation.";
end function;

function IsogenyPhiChar2(T)
    _, II := IsogenyFromKernel(T`E_im2,T`kernel_poly);
    k_im1 := IsogenyMapPhi(II);
    return k_im1;
end function;

function IsogenyPhiBigChar(T)
    if T`prime eq 2 then
	_, II := IsogenyFromKernel(T`E_im2,  T`kernel_poly);
	k_im1 := IsogenyMapPhi(II);	
    else
	k_im1 := IsogenyPhi(T`E_im2, T`E_im1, T`kernel_poly, T`prime+1); 
    end if;
    return k_im1;
end function;

procedure TorsionModuleTraceElkiesPower(~T)
    // Finds (candidates for) the trace of E mod a power of the prime in
    // this prime_block.  The power is incremented by one each time this
    // function is called.

    error if (T`prime_exponent eq 0), 
       "Trace modulo prime undefined in Elkies power computation.";

    T`prime_exponent +:= 1;

    P := PolynomialRing(BaseRing(T`E));
    x := P.1;
    if T`char_type eq 0 then
        k_im1 := IsogenyPhiChar2(T);
    else
        k_im1 := IsogenyPhiBigChar(T);
    end if;
    j_inv := jInvariant(T`E_im1);
    modular_poly := UnivariatePolynomial(
        Evaluate(T`modular_eqn,2,j_inv) );
    if T`char_type eq 0 then
        if T`modular_model eq "canonical" then
            modular_roots := [ 1/r[1] : r in Roots(modular_poly) ];
        else
            modular_roots := [ r[1] : r in Roots(modular_poly) ];
        end if;
	E_i, g_i := ElkiesChar2Loop(T, modular_roots, k_im1);
    else
	vprint SEA, 2: "Elkies: computing modular points.";
	vtime SEA, 2: modular_roots := Roots(modular_poly);
	if T`modular_model eq "canonical" then
	    E_i, g_i := ElkiesCanonicalLoop(T, modular_roots, k_im1);
	else
	     E_i, g_i := ElkiesAtkinLoop(T, modular_roots, k_im1);
	end if;
    end if;
    I_im1 := Evaluate(k_im1, T`I_im2)/(Evaluate(T`kernel_poly, T`I_im2)^2);
    T`kernel_poly := Numerator(Evaluate(g_i, I_im1));
    TraceSchoofExtend(~T); 
    T`I_im2 := I_im1;
    T`E_im2 := T`E_im1;
    T`E_im1 := E_i;
    T`kernel_poly := g_i;
    T`entropy := -(T`prime_exponent)*Log(T`prime);
end procedure;
