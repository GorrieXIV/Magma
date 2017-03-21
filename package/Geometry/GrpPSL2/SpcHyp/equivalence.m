freeze;

/////////////////////////////////////////////////////////////
//                                                         //
//         Upper Half Plane                                //
// Equivalence functions, for testing equivalence of       //
// points and arcs under the action of a congruence group  //
//                                                         //
/////////////////////////////////////////////////////////////



intrinsic IsEquivalent(G::GrpPSL2,a::SetCspElt,b::SetCspElt)
   -> BoolElt, GrpPSL2Elt
   {for a congruence subgroup G,
   finds whether the cusps a and b are equivalent under the
   action of G, and if so returns true and a matrix in G
   taking a to b.  If not, returns false and the identity.}

   if a eq b then return true, G!1;
   end if;
	 
   ic := CongruenceIndices(G);
   
   // currently only works for congruence subgroups with
   // no non trivial conjugation.
   assert #ic eq 1;
   K := PolynomialRing(Integers());
   GK2 := MatrixAlgebra(K,2);
   a1, a2 := Explode(Eltseq(a));
   b1, b2 := Explode(Eltseq(b));

   g,r,s := Xgcd(a1,a2);
   assert g eq 1;
   m1 := GK2![a1,-s,a2,r];
   g,r,s := Xgcd(b1,b2);
   assert g eq 1;
   m2 := GK2![b1,-s,b2,r];
   t := GK2![1,K.1,0,1];  
   m3 := m2*t*m1^(-1);

    // From this point onward, changed by Geoff to use Solution rather
    // than the previous cumbersome approach (which, to be fair, was
    // somewhat required due to the apparent restrictions on both CRT
    // and Solution).

    // we need to find x such that:
    //   m3[2,1] =   0 mod N
    //   m3[1,1] = +-1 mod M
    //   m3[1,2] =   0 mod P
    // where N,M,P are the coefficients from ic

    pols := [ m3[2,1], m3[1,1], m3[1,2] ];
    avals := [  Coefficient(f,1) : f in pols ];
    bvals := [ -Coefficient(f,0) : f in pols ];
    mvals := ic[1];

    // first solution type (B = 1 mod M):
    bvals[2] +:= 1;
    x := Solution(avals, bvals, mvals);
    if x lt 0 then
	// second solution type (B = -1 mod M):
	bvals[2] -:= 2;
	x := Solution(avals, bvals, mvals);
    end if;

    if x lt 0 then
	return false,_;
    end if;

    matrix := G![ Evaluate(f,x) : f in Eltseq(m3) ];
    return true, matrix;   
end intrinsic;


intrinsic IsEquivalent(G::GrpPSL2,a::FldRatElt,b::FldRatElt)
   -> BoolElt, GrpPSL2Elt
   {for a congruence subgroup G,
   finds whether the cusps a and b are equivalent under the
   action of G, and if so returns true and a matrix in G
      taking a to b.  If not, returns false and the identity.}
   return IsEquivalent(G,Cusps()!a,Cusps()!b);
end intrinsic;


//////////////////////////////////////////////////////////////////////

function infinityToCusp(x);
    G := GL(2,Integers());
    a, b := Explode(Eltseq(x));
    g, d, c := Xgcd(a,-b);
    a := Integers()!a/g;
    b := Integers()!b/g;
    return G![a,c,b,d];
end function;


function IToValue(x)
    // need to add a test that t is in a quadratic
    // extension of Q.    
    K := Parent(x`exact_value);
    G := GL(2,K);
    t := K.1;
    a,b :=Explode(Eltseq(x));
    return G![a,b,0,1];
end function;


intrinsic EquivalentPoint(x::SpcHypElt) -> SpcHypElt, GrpPSL2Elt
   {returns a point z equivalent to x under the action of
   PSL(2,Z), which is in the standard fundamental domain
   given by the region -1/2 < x <= 1/2 and |x| >= 1 for
   x >= 0, and |x| > 1 for x < 0, and also the matrix g in PSL(2,Z)
   with g*x = z}
   // in the non exact case, we only return a value in a special case:
   if not IsExact(x) then
      z := ComplexValue(x) - Floor(Real(x) + 0.5);
      require Abs(z) ge 1: "enter points with exact values, or large
      imaginary part";
      if Real(z) ge 0 then
	 return Parent(x)!z;
      end if;
      if Abs(z) gt 1 then
	 return Parent(x)!z;
      else
	 return Parent(x)(1/z);
      end if;
   end if;
   if IsCusp(x) then
      inf := Parent(x)!Infinity();
      _,g := IsEquivalent(PSL2(Integers()),x,inf);
      return inf, g;
   end if;
   // the remaining case is exact valued points which are not cusps.
   require Imaginary(x) gt 0: "must enter a point in the upper half
   plane union cusps";
   z := ExactValue(x);
   // for simplicity, currently assume z is a point in a quadratic extension
   // of Q
   require Type(z) eq FldQuadElt: "points in the upper half plane should
   be in quadratic extenions of Q, defined by adjoining the root
   of some integer to Q";
   // now apply the usual algorithm
   K := Parent(z);
   d := -Integers()!((K![0,1])^2);
   G := PSL2(Integers());
   T := G![1,1,0,1];
   S := G![0,-1,1,0];
   H := Parent(x);
   
   g := G!1;
   i := 0;
   while i lt 100000 do
      // note, the imaginary part here is divided by the root of d.
      real,imag := Explode(Eltseq(z));
      t := Ceiling(real - 1/2);
      z := z - t;
      if t ne 0 then
	 g := T^(-t)*g;
      end if;
      abs_square := (real - t)^2 + d*imag^2;
      if abs_square gt 1 then
	 return H!z, g;	 
      elif abs_square eq 1 then
	 if real ge t then
	    return H!z, g;
	 else
	    return H!(-1/z), g;
	 end if;
      else
	 g := S*g;
	 z := -1/z;
      end if;
      i +:=1;
   end while;
   // if we get to this point, it has carried out more than 100000
   // steps, and has given up.
   require false: "error: too many iterations required to find point";
end intrinsic;


intrinsic IsEquivalent(G::GrpPSL2,a::SpcHypElt,b::SpcHypElt)
   -> BoolElt, GrpPSL2Elt
   {for a congruence subgroup G,
   finds whether the points a and b in the upper half plane
   are equivalent under the action of G, and if so returns
   true and a matrix in G taking a to b.  If not, returns false}
   require IsCongruence(G): "G must be a congruence subgroup";
      
   require (IsExact(a) and IsExact(b)): "Points must be given with
   exact values, in the rationals or in a number field";
   
   if IsCusp(a) and IsCusp(b) then
      // this uses the intinsic defined in cusp.m
      return IsEquivalent(G,ExactValue(a),ExactValue(b));
   end if;

   if IsCusp(a) ne IsCusp(b) then
      return false, _;
   end if;

   // the remaining cases have exact values and are not
   // cusps

   // for simplicity, require points to have positive imaginary
   // part if they are not cusps:
   require Imaginary(a) gt 0 and Imaginary(b) gt 0:
   "points should be points in the upper half plane union the cusps";
   
   a_val := ExactValue(a);
   b_val := ExactValue(b);

   // for simplicity, require points to be in quadratic extensions
   require Type(a_val) eq FldQuadElt and
   Type(b_val) eq FldQuadElt:
   "points should be defined over a quadratic extension of Q";

   // given the above condition on the fields, if the points are
   // not defined over the same field, then they are not equivalent
   // under the action of a matrix with integer entries:
   if Parent(b_val) ne Parent(a_val) then
      return false, _;
   end if;
   a1,g1 := EquivalentPoint(a);
   b1,h1 := EquivalentPoint(b);
   if a1 ne b1 then return
      false, _;
   end if;
   // the following matrix translates from a to b:
   matrix := h1*g1^(-1);
   if matrix in G then
      return true, matrix;
   else
      return false, _;
   end if;
end intrinsic;
   

intrinsic IsEquivalent(G::GrpPSL2,E1::[SetCspElt],E2::[SetCspElt])
   -> BoolElt, GrpPSL2Elt
   {For a congruence subgroup G and edges a and b, which are given
   by pairs of cusps, return true or false depending on whether the
   edges are equivalent under the action of G, and if they are, also
   return a matrix g with g*a=b  (g is not necessarily unique)}
   require (#E1 eq 2) and (#E2 eq 2): "the second and third argument must
   be edges, which must have two end points, which should be cusps";
   require IsCongruence(G): "the first argument must be a congruence subgroup";
   E1_start := Eltseq(E1[1]);
   E1_end   := Eltseq(E1[2]);
   E2_start := Eltseq(E2[1]);
   E2_end   := Eltseq(E2[2]);
   MatAlg := MatrixAlgebra(Integers(),2);
   M1 := MatAlg![E1_start[1],E1_end[1],E1_start[2],E1_end[2]];
   M2 := MatAlg![E2_start[1],E2_end[1],E2_start[2],E2_end[2]];

   d1 := Determinant(M1);
   d2 := Determinant(M2);
   
   // first, consider the case where one of the edges
   // is trivial
   
   if (d1*d2 eq 0) then
      if (d1 ne d2) then
	 return false, _;
      else
	 return IsEquivalent(G,Cusps()!E1_start,Cusps()!E2_start);
      end if;
   end if;
   
   // the following will make both M1 and M2 have the same determinant:

   if Sign(d1) ne Sign(d2) then
      M2 := M2*MatAlg![-1,0,0,1];
      d2 := -d2;
   end if;

   // now consider the case where M1 = M2:

   if M1 eq M2 or M1 eq -M2 then
      S := MatAlg![0,-1,1,0];
      M3a := M2*S*Adjoint(M1);
      //  normalize M3a:
      M3aelts := Eltseq(M3a);
      M4a := MatAlg![Integers()|e/ga where ga := GCD(M3aelts) : e in M3aelts];
      if Determinant(M4a) eq 1 and IsCoercible(G,M4a) then
	 return true,G!M4a;
      else
	 return true, G!1;
      end if;
   end if;

   // finally, the case where M1 and M2 are different:
   
   M3a := M2*Adjoint(M1);
   // normalize M3a:
   M3aelts := Eltseq(M3a);
   M4a := MatAlg![Integers()|e/ga where ga := GCD(M3aelts) : e in M3aelts];
   
   if Determinant(M4a) eq 1 and IsCoercible(G,M4a) then            
      return true, G!M4a;
   end if;

   // now check the other orientation:
   
   S := MatAlg![0,-1,1,0];
   M3b := M2*S*Adjoint(M1);
   M3belts := Eltseq(M3b);
   M4b := MatAlg![Integers()|e/gb where gb := GCD(M3belts) : e in M3belts];
   
   if Determinant(M4b) eq 1 and IsCoercible(G,M4b) then     
      return true, G!M4b;
   end if;

   return false, _;

end intrinsic;



intrinsic IsEquivalent(G::GrpPSL2,a::[SpcHypElt],b::[SpcHypElt])
   -> BoolElt, GrpPSL2Elt
   {For a congruence subgroup G and edges a and b, which are given
   by pairs of cusps, return true or false depending on whether the
   edges are equivalent under the action of G, and if they are, also
   return the matrix g with g*a=b}
   require (#a eq 2) and (#b eq 2): "the second and third argument must
   be edges, which must have two end points, which should be cusps";
   require IsCongruence(G): "the first argument must be a congruence subgroup";
   require &and[IsCusp(e) : e in a cat b] : "the second and third
   argument must consist of edges with end points which are cusps";
   return IsEquivalent(G,[ExactValue(u) : u in a], [ExactValue(u) : u in b]);
end intrinsic;














