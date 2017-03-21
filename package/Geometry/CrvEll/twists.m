freeze;
////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    TWISTS OF ELLIPTIC CURVES                       //
//                          David Kohel                               //
//                        Created May 2000                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        QUADRATIC TWISTS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic QuadraticTwist(E::CrvEll,d::RngElt) -> CrvEll
   {The quadratic twist of E by d. If j(E) != 1728, this is isomorphic
    to E precisely over the field extension determined by d (maybe trivial).
    In the 1728 case, d may define a non-trivial extension but the twist
    can still be isomorphic to E over the base field.}
   K := BaseRing(E);
   yes, d := IsCoercible(K,d);
   require yes :
      "Argument 2 does not coerce into the base ring of argument 1";
   case Characteristic(K):
      when 2:
	 require Type(K) eq FldFin :
	   "In characteristic 2, function only works for finite fields";
         E := SimplifiedModel(E);
         if Trace(d) eq 0 then
            return E;
         else
            return QuadraticTwist(E);
         end if;
      when 3:
         E := SimplifiedModel(E);
         a := Eltseq(E);
         if a[2] eq 0 then
            return EllipticCurve([d^2*a[4],d^3*a[5]]);
         else
            return EllipticCurve([0,d*a[2],0,d^2*a[4],d^3*a[5]]);
         end if;
      else
        a:=Eltseq(E);
        if a[1] ne 0 or a[3] ne 0 then
	  if Characteristic(K) eq 0 then
	      a := Eltseq(WeierstrassModel(E));
	  else
	      a := Eltseq(SimplifiedModel(E));
	      if a[1] ne 0 or a[3] ne 0 then	// shouldn't happen
		c4,c6 := Explode(cInvariants(E));
		a := [ 0, 0, 0, -27*c4, -54*c6 ];
	      end if;
	  end if;
        end if;
        return EllipticCurve([0,d*a[2],0,d^2*a[4],d^3*a[5]]);
   end case;
end intrinsic;

intrinsic QuadraticTwists(E::CrvEll) -> CrvEll
   {The quadratic twists of E over a finite field.}
   require Type(BaseRing(E)) eq FldFin :
      "Base ring must be a finite field.";
   E := SimplifiedModel(E);
   E1,boo := QuadraticTwist(E);
   if boo then
       return [ E, E1 ];
   else
       return [E];
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       TWIST ENUMERATION                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function TraceCokernelRepresentatives(K,q)
   // The trace K -> GF(q) has kernel spanned by x^q - x,
   // where x runs over a basis for K, and q = 2^r.
   V := VectorSpace(GF(2),Degree(K));
   W, pi := quo< V | [ V!Eltseq(x^q-x)
       where x is K!Eltseq(v) : v in Basis(V) ] >;
   return [ K!Eltseq(y@@pi) : y in W ];
end function;

function SupersingularTwists2(E)
// Changed 04/08 by mch - old code was missing out one twist
// in some cases. Here, do it by formula over GF(2^n):
//  if n is odd : have 3 twists (same as over GF(2)!)
//  if n is even: have 7 twists that can be written down
//   explicitly given an element of trace 1 and a cubic
//   non-residue of the field (take a primitive element)

    K := BaseRing(E);
    if IsOdd(Degree(K)) then
	return [EllipticCurve([K|0,0,1,0,0]),
		EllipticCurve([K|0,0,1,1,0]),
		EllipticCurve([K|0,0,1,1,1]) ];
    end if;
    // even degree case
    u := PrimitiveElement(K);
    c := u;
    while AbsoluteTrace(c) eq K!0 do c := Random(K); end while;
    //first 3 curves
    crvs1 := [EllipticCurve([K|0,0,1,0,0]),
	      EllipticCurve([K|0,0,1,c,0]),
	      EllipticCurve([K|0,0,1,0,c]) ];
    // and the next 4
    crvs2 := [EllipticCurve([K|0,0,a,0,a^2*b]) :
		a in [u,u^-1], b in [0,c]];
    return crvs1 cat crvs2;
end function;

function SkewTraceCokernelReps(a)
   // Cokernel representatives for the 'skew trace kernel'
   // spanned by x^3 - a*x.
   k := Parent(a);
   V := VectorSpace(GF(3),Degree(k));
   W, pi := quo< V | [ V!Eltseq(x^3-a*x)
               where x is k!Eltseq(v) : v in Basis(V) ] >;
   return [ k!Eltseq(y@@pi) : y in W ];
end function;

function SupersingularTwists3(E)
// Changed 04/08 by mch - old code was missing out twists
// in many cases. Here, do it by formula over GF(3^n):
//  if n is odd : have 4 twists that can be written down
//   explicitly given an element of non-0 trace.
//  if n is even: have 7 twists that can be written down
//   explicitly given an element of non-0 trace & a quadratic
//   non-residue of the field (take a primitive element)
    K := BaseRing(E);
    d := Degree(K);

    // get element of trace !=0
    if (d mod 3) ne 0 then
	c := K!1;
    else
	c := K.1;
	while AbsoluteTrace(c) eq K!0 do 
	    c := Random(K);
	end while;
    end if;

    // odd degree case
    if IsOdd(d) then
	return [EllipticCurve([K!1,0]),
		EllipticCurve([-K!1,0]),
		EllipticCurve([-K!1,c]),
		EllipticCurve([-K!1,-c]) ];
    end if;
    // even degree case
    u := PrimitiveElement(K);
    // first 4 curves
    crvs1 := [EllipticCurve([-u^i,0]) : i in [0..3]];
    return crvs1 cat 
      [EllipticCurve([-K!1,c]),EllipticCurve([-u^2,(u^3)*c])];

end function;

intrinsic Twists(E::CrvEll[FldFin]) -> SeqEnum
   {The twists of E over a finite field.}
   k := BaseRing(E);
   p := Characteristic(k);
   j := jInvariant(E);
   if j ne 0 and j ne 12^3 then
      return [ E, QuadraticTwist(E) ];
   elif p eq 2 then
      return SupersingularTwists2(E);
   elif p eq 3 then
      return SupersingularTwists3(E);
   elif j eq 0 then
      a := PrimitiveElement(k);
      c := -cInvariants(E)[2]/864;
      n := GCD(6, #k-1);
      return [ EllipticCurve([0,c*a^i]) : i in [0..n-1] ];
   elif j eq 12^3 then
      a := PrimitiveElement(k);
      c := -cInvariants(E)[1]/48;
      n := GCD(4, #k-1);
      return [ EllipticCurve([c*a^i,0]) : i in [0..n-1] ];
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        TWIST PREDICATES                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsTwist(E::CrvEll,F::CrvEll) -> BoolElt
    {Returns true if and only if the curves E and F have the same
    j-invariant.}
    return jInvariant(E) eq jInvariant(F);
end intrinsic;

intrinsic IsQuadraticTwist(E::CrvEll,F::CrvEll) -> BoolElt, RngElt
    {}
    if not IsTwist(E,F) then
	return false, _;
    end if;
    j := jInvariant(E);
    c4, c6 := Explode(cInvariants(E));
    d4, d6 := Explode(cInvariants(F));
    p := Characteristic(BaseField(E));
    if p in {2,3} then
	return &or[ IsIsomorphic(E1,F) : E1 in QuadraticTwists(E) ];
    elif j eq 0 then
	return IsPower(d6/c6,3);
    elif j eq 12^3 then
	return IsSquare(d4/c4);
    else
	return true, (c4*d6)/(c6*d4);
    end if;
end intrinsic;
