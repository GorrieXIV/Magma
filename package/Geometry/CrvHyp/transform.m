freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/*******************************************
 * Hyperelliptic/transform.m               *
 *                                         *
 * Transformations/Isomorphisms of hyper-  *
 * elliptic curves and their Jacobians     *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 26-Apr-1999                     *
 *******************************************/

/* Modified by David Kohel, 2000 */

/* ------------------------------------------------------------------
  
  Changed by Michael Stoll 2000-08-08:
 
    Functions that used to return two maps C1 -> C2, C2 -> C1 now
      only return the map C1 -> C2; this map can be inverted.
  
    Transformations are now represented as records <g, mat, e, pol>
      and can be multiplied using '*' and exponentiated using '^'.
      [This is a temporary representation until a type for these
       transformations is created.]
    
    IsGL2Equivalent is an intrinsic again.
    
    New function IsQuadraticTwist(C1::CrvHyp, C2::CrvHyp).
    
    New verbose flag CrvHypIso for IsGL2Equivalent, IsIsomorphic,
      IsQuadraticTwist.
  
  2000-08-09:
  
    New function HyperellipticInvolution(C::CrvHyp) -> Rec
      giving the hyperelliptic involution on C as a transformation
    
    New function AutomorphismGroup(C::CrvHyp) -> GrpPerm, Map
    
    Reintroduced Roots1 as a workaround -- factorisation of polynomials
      over relative number fields still does not work in all cases.
  
  2000-09-28:
  
    Fixed a bug in Transformation(JacHyp) -- Second value gave map in
      reverse direction.
  
  2001-04-11:
  
     Fixed a bug in Transformation(JacHyp) -- elt< J | a, b, d > insists
       on d = Degree(a) when the curve has exactly one point at infinity.

  2001-01-24:
    
    Fixed a bug in AutomorphismGroup causing it to produce an error
      message for finite base fields.

  2001-03-19:

  Check AbsoluteInvariants in IsIsomorphic for curves of genus 2.
	  (Paulette Lieby)
		  
  Modified by David Kohel, June 2001:

  Extracted all code relating to defining datatypes and constructors
  for isomorphisms of curves, and incorporated these in the defining
  code for isomorphims: hyperelliptic_isoms.m.
	  
  Modified IsIsomorphic and AutomorphismGroup to use automatic coercion
  constructors for hyperelliptic isomorphisms.
       
  N.B. The isomorphisms have been changed from their definition as
  records, in that the defining data of the map on points is stored,
  which is the inverse of the isomorphism data in the records.
  
  Changed Roots1 to a function -- probably should now be removed.
  Factorization of polys over relative number fields is now supported 
  in the kernel and should be better than creating the absolute
  extension.  I haven't removed this since it does do the membership
  test on the roots, and this is still a bug in poly factorization
  over the real field (also returning complex roots).


  2001-07:  Scheme merge. PL.

  2001-07-20: Change CrvHypIso verbose flag back to CrvHypIso
  
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   EllipticCurve returned a SeqEnum!!! (fixed now)

  2001-07-26: Geoff
    EllipticCurve(CrvHyp) is intrinsic in the EC directory (which does
    more than the version which was here); the version in this file has
    been removed.

  2001-08-31 Nicole Sutherland
  Use scheme maps
   
  2001-09 David Kohel
    Created IsomorphismData function, minor bug fixes.
   
  2001-10-04 David Kohel
    Bug fix in Automorphism group -- correct normalization of Y variable.
    
  2004-02-04 Michael Harrison
    Added code to QuadraticTwist for finite field char 2 case.
  
  2012-02 Brendan Creutz
    IsIsomorphic now changes to even degree models before calling
    IsGL2Equivalent. 
  ------------------------------------------------------------------- */

import "isomorphisms.m" : HyperellipticIsomorphism;

//////// Conversion from Scheme Isomorphism to Defining Data ///////////

function IsomorphismData(m)
    // Note that this function has the same name as that on elliptic
    // curves -- they should be merged into one function on MapIsoSch.

    C := Domain(m);
    P := CoordinateRing(Ambient(C));
    x := P.1; y := P.2; z := P.3;
    g := Genus(C);
    eqns := DefiningEquations(m);
    t := [ MonomialCoefficient(f,m) : m in [x,z], f in eqns[[1,3]] ]; 
    e := MonomialCoefficient(eqns[2], y);
    u := Polynomial(BaseRing(C), coeffs) where coeffs := 
        [ MonomialCoefficient(eqns[2],x^i*z^(g+1-i)) : i in [0..g+1] ];
    return t, e, u;
end function;

//////////////////////////// Declarations /////////////////////////////

declare verbose CrvHypIso, 3;

/////////////// Polynomial Root Finding with Sanity Tests /////////////

function Roots1(f,F)
    // The roots of f in the extension field, F, of the 
    // coefficient field of f, with a test.
    return [ <r[1], r[2]> : r in Roots(f, F) | r[1] in F ];
end function;

////////////////////////// Quadratic twists ///////////////////////////

intrinsic QuadraticTwist(C::CrvHyp, d::RngElt) -> CrvHyp
{The quadratic twist of the curve C by d.}
   f := HyperellipticPolynomials(SimplifiedModel(C));
   return Ambient(C)!!HyperellipticCurve(d*f);
end intrinsic;

intrinsic QuadraticTwist(C::CrvHyp) -> CrvHyp
{The quadratic twist of the curve C defined over a finite field.}
   F := BaseField(C);
   require Type(F) eq FldFin :  
      "Argument must be defined over a finite field";
   if Characteristic(F) eq 2 then
       f,h := HyperellipticPolynomials(C);
       u := IsOdd(Degree(F)) select F!1 else NormalElement(F);
       // u satisfies Trace(u) = 1
       return Ambient(C)!!HyperellipticCurve([f+u*(h^2),h]);  
   else
       f := HyperellipticPolynomials(SimplifiedModel(C));
       return Ambient(C)!!HyperellipticCurve(PrimitiveElement(F)*f);
   end if;
end intrinsic;

intrinsic QuadraticTwists(C::CrvHyp) -> SeqEnum
    {The quadratic twists of the curve C defined over a finite field.}
    F := BaseField(C);
    require Type(F) eq FldFin :  
        "Argument must be defined over a finite field";
    return [ C, QuadraticTwist(C) ]; 
end intrinsic;

///////////////////////// Isomorphism Testing //////////////////////////

function TransformPolynomial(f,n,mat)
    // Transforms f, considered as a homogeneous polynomial of 
    // degree n, by the matrix with entries mat = [a,b,c,d].
    a,b,c,d := Explode(mat);
    x1 := a*Parent(f).1 + b; z1 := c*Parent(f).1 + d;
    return &+[Coefficient(f,i)*x1^i*z1^(n-i) : i in [0..n]];
end function;

intrinsic IsQuadraticTwist(C1::CrvHyp, C2::CrvHyp) -> BoolElt, RngElt
    {True if and only if C2 is a quadratic twist of C1 over their
    common base field. If so, the second value is the twisting factor.}
    // Verbose flag: CrvHypIso.

    K := BaseField(C1);
    require K cmpeq BaseField(C2): "Arguments must have a common base field.";
    require Characteristic(K) ne 2: "Not implmented in characteristic 2.";

    g := Genus(C1);
    if Genus(C2) ne g then return false, _; end if;
    P := PolynomialRing(K);
    f1, h1 := HyperellipticPolynomials(C1);
    f2, h2 := HyperellipticPolynomials(C2);
    // Transform into y^2 = f(x)
    if h1 ne 0 then
	f1 := 4*f1 + h1^2;
    end if;
    if h2 ne 0 then
	f2 := 4*f2 + h2^2;
    end if;
    flag, list := IsGL2Equivalent(f1, f2, 2*g+2);
    if flag then
	vprintf CrvHypIso, 1: " Transformation matrix: %o\n", list[1];
	f3 := TransformPolynomial(f1, 2*g+2, list[1]);
	// f3 = const*f2
	c := LeadingCoefficient(f2)/LeadingCoefficient(f3);
	return true, c;
    else
	vprintf CrvHypIso, 1: " No transformation.\n";
    end if;
    return false, _;
end intrinsic;

intrinsic IsIsomorphic(C1::CrvHyp, C2::CrvHyp) -> BoolElt, MapIsoSch
    {True if and only if C1 and C2 are isomorphic as hyperelliptic curves
    over their common base field, followed by a transformation giving
    the isomorphism as a second value when the curves are isomorphic.}

    require BaseField(C1) cmpeq BaseField(C2): 
            "The curves must have a common base field.";
    g := Genus(C1);
    if Genus(C2) ne g then return false, _; end if;
    if g eq 2 and AbsoluteInvariants(C1) ne AbsoluteInvariants(C2) then
	return false;
    end if;

    K := BaseField(C1);
    require Characteristic(K) ne 2:
            "IsIsomorphic currently does not work in characteristic 2.";
    P := PolynomialRing(K);
    f1, h1 := HyperellipticPolynomials(C1);
    f2, h2 := HyperellipticPolynomials(C2);
    // Transform into y^2 = f(x)
    if h1 eq 0 then
	tr1 := IdentityMap(C1);
    else
	f1 := 4*f1 + h1^2;
	C1, tr1 := Transformation(C1,[K|1,0,0,1],K!2,h1);
    end if;
    if h2 eq 0 then
	tr2 := IdentityMap(C2);
    else
	f2 := 4*f2 + h2^2;
	C2, tr2 := Transformation(C2,[K|1,0,0,1],K!2,h2);
    end if;
    if IsOdd(Degree(f1)) then
        C1, tr1b := Transformation(C1,[K|0,1,1,0]);
        f1 := HyperellipticPolynomials(C1);
    else
        tr1b := IdentityMap(C1);
    end if;
    if IsOdd(Degree(f2)) then
        C2, tr2b := Transformation(C2,[K|0,1,1,0]);
        f2 := HyperellipticPolynomials(C2);
    else
        tr2b := IdentityMap(C2);
    end if;
    _, list := IsGL2Equivalent(f1, f2, 2*g+2);
    vprintf CrvHypIso, 1: " Possible matrices:\n    %o\n", list;
    for t in list do
	vprintf CrvHypIso, 1: "  Matrix %o", t;
	f3 := TransformPolynomial(f1, 2*g+2, t);
	// f3 = const*f2
	c := LeadingCoefficient(f3)/LeadingCoefficient(f2);
	fl, rc := IsSquare(c);
	if fl then
	    vprintf CrvHypIso, 1: " ==> yes!\n";
	    tr := HyperellipticIsomorphism(C2, C1, t, rc, P!0);
	    return true, tr1*tr1b*Inverse(tr2*tr2b*tr);
	else
	    vprintf CrvHypIso, 1: " ==> no.\n";
	end if;
    end for;
    return false, _;
end intrinsic;

///////////////////////// Automorphism group ///////////////////////////

intrinsic AutomorphismGroup(C::CrvHyp) -> GrpPerm, Map, Map
    {The automorphism group G of C as a permutation group.  The second
    value is a map from G to the group of automorphisms of C.
    The third value gives the action C x G -> C.}
    // Verbose flag: CrvHypIso.
    K := BaseField(C);
    g := Genus(C);
    require g gt 0: "AutomorphismGroup not implemented for genus 0.";
    require Characteristic(K) ne 2:
        "AutomorphismGroup currently does not work in characteristic 2.";
    f, h := HyperellipticPolynomials(C);
    P := PolynomialRing(K);
    if h eq 0 then
	C1 := C; 
	m := IdentityMap(C);
    else
	C1, m := Transformation(C, [K|1,0,0,1], K!2, h);
	f := 4*f + h^2;
    end if;
    M1 := Aut(Codomain(m));
    m1 := Inverse(m);
    _, list := IsGL2Equivalent(f, f, 2*g+2);
    vprintf CrvHypIso, 1: " Possible matrices:\n    %o\n", list;
    list1 := [ HyperellipticInvolution(C) ];
    for t in list do
	vprintf CrvHypIso, 1: "  Matrix %o", t;
	f3 := TransformPolynomial(f, 2*g+2, t);
	// f3 = const*f
	c := LeadingCoefficient(f3)/LeadingCoefficient(f);
	fl, rtc := IsSquare(c);
	if fl then
	    vprintf CrvHypIso, 1: " ==> yes!\n";
	    tmp := HyperellipticIsomorphism(C1, C1, t, rtc, P!0);
	    bool, tmp := IsAutomorphism(tmp);
	    Append(~list1, m * tmp * m1);
	else
	    vprintf CrvHypIso, 1: " ==> no.\n";
	end if;
    end for;
    // Now, list1 contains all transformations (modulo the hyperelliptic
    // involution) giving an automorphism of C, plus the involution as
    // first element.
    //
    // Make an indexed set of `generic images' of all automorphisms:
    // An element is <X,Y> such that t(x,y) = (X,Y*y) for an automorphism t
    // and a generic point (x,y).
    F := FieldOfFractions(P); xx := F.1;
    genlist := &join[ {@<X,Y>, <X,-Y>@}
          where Y := e/(c*xx+d)^(g+1)
          where X := (a*xx+b)/(c*xx+d)
          where a,b,c,d := Explode(Mat)
	  where Mat, e is IsomorphismData(t)
              : t in list1[2..#list1] ];
    // Find the permutation each t induces on this indexed set
    act := func< t, pt | Position(genlist,
          <(a*pt[1]+b)/(c*pt[1]+d),e*pt[2]/(c*pt[1]+d)^(g+1)>)
	  where a,b,c,d := Explode(Mat) 
	  where Mat, e is IsomorphismData(t)>;
    // Construct the corresponding permutation group
    G := PermutationGroup< #genlist |
              [ [ act(t,pt) : pt in genlist ] : t in list1 ] >;
    // The construction of the map is somewhat primitive, but should be OK,
    // since the groups are small...
    GT := car< G, Aut(C) >;
    m := map< G -> Aut(C) |
              [ GT | <G.j, list1[j]> : j in [2..#list1] ] cat 
	      [ GT | <G.1*G.j, list1[1]*list1[j]> : j in [2..#list1] ] >;
    return G, m, map< car<C, G> -> C | p :-> f(p[1])
              where _, f := Transformation(C, m(p[2])) >;
end intrinsic;

////////////////////// GL2 Equivalence Testing /////////////////////////

intrinsic IsGL2Equivalent(f1::RngUPolElt, f2::RngUPolElt, n::RngIntElt)
  -> BoolElt, SeqEnum
{f1 and f2 are considered as homogeneous polynomials of degree n.
 It is checked whether they belong to the same GL(2,k)-orbit, where 
 k is the coefficient field, modulo multiplication by scalars. 
 As a second value, a sequence of matrix entries [a,b,c,d] is returned 
 such that 
 f2(x) = const * (c*x + d)^n * f1((a*x + b)/(c*x + d)).
 Verbose flag: CrvHypIso}
    vprintf CrvHypIso: "IsGL2Equivalent(%o, %o, %o):\n", f1, f2, n;
    K := CoefficientRing(Parent(f1));
    require IsField(K): "Coefficient ring must be a field.";
    require K cmpeq CoefficientRing(Parent(f2)):
            "Polynomials must have the same coefficient field.";
    require n ge 4: "Argument 3 must be at least 4.";
    require Degree(f1) in {n-1,n} and Degree(f2) in {n-1,n}:
            "Associated homogeneous polynomials of degree",n,
            "must be square-free.";
    fact1 := Factorization(f1);
    if f1 ne f2 then fact2 := Factorization(f2); else fact2:=fact1; end if;
    vprintf CrvHypIso: " Factorization of f1:\n%o\n", fact1;
    vprintf CrvHypIso: " Factorization of f2:\n%o\n", fact2;
    require forall{a : a in fact1 cat fact2 | a[2] eq 1}:
            "Associated homogeneous polynomials of degree",n,
            "must be square-free.";
    degs1 := {* Degree(a[1]) : a in fact1 *};
    if Degree(f1) lt n then degs1 join:= {* 1 *}; end if;
    degs2 := {* Degree(a[1]) : a in fact2 *};
    if Degree(f2) lt n then degs2 join:= {* 1 *}; end if;
    vprintf CrvHypIso: " Degrees of homogeneous factors:\n  %o\n  %o\n", 
                       degs1, degs2;
    if degs1 ne degs2 then
      // Degrees don't match -> no transformation possible
      return false, [];
    else
      // find largest degree with factor
      d := Max(degs1);
      for a in fact1 do
        if Degree(a[1]) eq d then f := a[1]; break; end if;
      end for;
      vprintf CrvHypIso, 2: " Largest degree factor of f1:\n   %o\n", f;
      result := [];
      if d ge 3 then
        vprintf CrvHypIso, 2: " Degree %o > 2; construct extension field.\n", d;
        L := ext< K | f >;
        e1 := Eltseq(L!1);
        rf := [ r[1] : r in Roots1(f, L) ][1];
        ex := Eltseq(-rf);
        vprintf CrvHypIso, 3: "  1        = %o,\n  -root(f) = %o\n", e1, ex;
        // loop through factors of f2 of same degree
        for a in [ h[1] : h in fact2 | Degree(h[1]) eq d ] do
          vprintf CrvHypIso, 2: "  Consider factor g of f2:\n   %o\n", a;
          // find roots in L and loop through them
          for root in { r[1] : r in Roots1(a, L) } do
            // check for linear dependence
            vprintf CrvHypIso, 3: "   For root, have\n";
            ey := Eltseq(root);
            exy := Eltseq(-rf*root);
            vprintf CrvHypIso, 3: "   root(g)          = %o\n", ey;
            vprintf CrvHypIso, 3: "   -root(f)*root(g) = %o\n", exy;
            ker := Kernel(Matrix(#e1, ey cat e1 cat exy cat ex));
            vprintf CrvHypIso, 2: "  Kernel has dimension %o\n", Dimension(ker);
            if Dimension(ker) eq 1 then
              t := Eltseq(Basis(ker)[1]);
              vprintf CrvHypIso, 2: "   ==> Matrix = %o\n", t;
              f3 := TransformPolynomial(f1, n, t);
              if f3*LeadingCoefficient(f2) eq f2*LeadingCoefficient(f3) then
                vprintf CrvHypIso, 2: "   Gives transformation f1 -> f2.\n";
                Append(~result, t);
              else
                vprintf CrvHypIso, 2: 
                        "   Does not give transformation f1 -> f2.\n";
              end if;
            end if; // Dimension(ker) eq 1
          end for; // root
        end for; // a
      elif d eq 2 then
        // need to check 2 factors
        vprintf CrvHypIso, 2: " Degree = 2. Construct first extension field.\n";
        L1 := ext< K | f >;
        rf := [ r[1] : r in Roots1(f, L1) ][1];
        d1 := Max(Exclude(degs1, d));
        for a in fact1 do
          if Degree(a[1]) eq d1 and a[1] ne f then ff := a[1]; break; end if;
        end for;
        vprintf CrvHypIso, 2:
                " Second highest degree factor ff of f:\n  %o\n", ff;
        if d1 eq 2 then
           vprintf CrvHypIso, 2:
                   " Degree = 2. Construct second extension field.\n";
          L2 := ext< K | ff>;
          rff := [ r[1] : r in Roots1(ff, L2) ][1];
          e1 := Eltseq(L1!1) cat Eltseq(L2!1);
          ex := Eltseq(-rf) cat Eltseq(-rff);
          vprintf CrvHypIso, 3: "  1        = %o,\n  -root(f) = %o\n", e1, ex;
          // loop through factors of f2 of degrees 2, 2
          for a in [ h[1] : h in fact2 | Degree(h[1]) eq 2 ] do
            vprintf CrvHypIso, 2: "  Consider factor g of f2:\n   %o\n", a;
            // find roots in L1
            for root1 in { r[1] : r in Roots1(a, L1) } do
              // second factor
              vprintf CrvHypIso, 3: "  For root %o of g:\n", root1;
              for b in [ h[1] : h in fact2 
                              | Degree(h[1]) eq 2 and h[1] ne a ] do 
                vprintf CrvHypIso, 3:
                        "   Consider factor gg of f2:\n   %o\n", b;
                // find roots in L2
                for root2 in { r[1] : r in Roots1(b, L2) } do
                  vprintf CrvHypIso, 3: "   For root %o of gg:\n", root2;
                  // check for linear dependence
                  ey := Eltseq(root1) cat Eltseq(root2);
                  exy := Eltseq(-rf*root1) cat Eltseq(-rff*root2);
                  vprintf CrvHypIso, 3: "    root(g)          = %o\n", ey;
                  vprintf CrvHypIso, 3: "    -root(f)*root(g) = %o\n", exy;
                  ker := Kernel(Matrix(4, ey cat e1 cat exy cat ex));
                  vprintf CrvHypIso, 2: 
                          "   Kernel has dimension %o\n", Dimension(ker);
                  if Dimension(ker) eq 1 then
                    t := Eltseq(Basis(ker)[1]);
                    vprintf CrvHypIso, 2: "    ==> Matrix = %o\n", t;
                    f3 := TransformPolynomial(f1, n, t);
                    if f3*LeadingCoefficient(f2) eq f2*LeadingCoefficient(f3) 
                      then 
                      vprintf CrvHypIso, 2:
                              "    Gives transformation f1 -> f2.\n";
                      Append(~result, t);
                    else
                      vprintf CrvHypIso, 2: 
                              "    Does not give transformation f1 -> f2.\n";
                    end if;
                  end if; // Dimension(ker) eq 1
                end for; // root2
              end for; // b
            end for; // root1
          end for; // a
        else // d1 eq 1
          rff := Roots(ff)[1,1];
          vprintf CrvHypIso, 2: " Degree = 1. Take root %o of f1.\n", rff;
          e1 := Eltseq(L1!1) cat [1];
          ex := Eltseq(-rf) cat [-rff];
          vprintf CrvHypIso, 3: "  1        = %o,\n  -root(f) = %o\n", e1, ex;
          // loop through factors of f2 of degrees 2, 1
          for a in [ h[1] : h in fact2 | Degree(h[1]) eq 2 ] do
            vprintf CrvHypIso, 2: "  Consider factor g of f2:\n   %o\n", a;
            // find roots in L1
            for root1 in { r[1] : r in Roots1(a, L1) } do
              vprintf CrvHypIso, 3: "  For root %o of g:\n", root1;
              // second factor
              for b in [ h[1] : h in fact2 | Degree(h[1]) eq 1 ] do 
                vprintf CrvHypIso, 2:
                        "   Consider factor gg of f2:\n   %o\n", b;
                root2 := Roots(b)[1,1];
                // check for linear dependence
                ey := Eltseq(root1) cat [root2];
                exy := Eltseq(-rf*root1) cat [-rff*root2];
                vprintf CrvHypIso, 3: "    root(g)          = %o\n", ey;
                vprintf CrvHypIso, 3: "    -root(f)*root(g) = %o\n", exy;
                ker := Kernel(Matrix(3, ey cat e1 cat exy cat ex));
                vprintf CrvHypIso, 2:
                        "   Kernel has dimension %o\n", Dimension(ker);
                if Dimension(ker) eq 1 then
                  t := Eltseq(Basis(ker)[1]);
                  vprintf CrvHypIso, 2: "    ==> Matrix = %o\n", t;
                  f3 := TransformPolynomial(f1, n, t);
                  if f3*LeadingCoefficient(f2) eq f2*LeadingCoefficient(f3) 
                    then 
                    vprintf CrvHypIso, 2:
                            "    Gives transformation f1 -> f2.\n";
                    Append(~result, t);
                  else
                    vprintf CrvHypIso, 2: 
                            "    Does not give transformation f1 -> f2.\n";
                  end if;
                end if; // Dimension(ker) eq 1
              end for; // b
              if Degree(f2) lt n then
                // take point at infinity into account
                vprintf CrvHypIso, 2: "   Consider point at infinity.\n";
                // MS, 2000-12-20
                // change e1 and ex into e1i and exi to avoid overwriting
                // of e1 and ex.
                e1i := Eltseq(L1!1) cat [0];
                exi := Eltseq(-rf) cat [0];
                ey := Eltseq(root1) cat [1];
                exy := Eltseq(-rf*root1) cat [-rff];
                vprintf CrvHypIso, 3: "    1                = %o\n", e1;
                vprintf CrvHypIso, 3: "    -root(f)         = %o\n", ex;
                vprintf CrvHypIso, 3: "    root(g)          = %o\n", ey;
                vprintf CrvHypIso, 3: "    -root(f)*root(g) = %o\n", exy;
                ker := Kernel(Matrix(3, ey cat e1i cat exy cat exi));
                vprintf CrvHypIso, 2:
                        "   Kernel has dimension %o\n", Dimension(ker);
                if Dimension(ker) eq 1 then
                  t := Eltseq(Basis(ker)[1]);
                  vprintf CrvHypIso, 2: "    ==> Matrix = %o\n", t;
                  f3 := TransformPolynomial(f1, n, t);
                  if f3*LeadingCoefficient(f2) eq f2*LeadingCoefficient(f3) 
                    then 
                    vprintf CrvHypIso, 2:
                            "    Gives transformation f1 -> f2.\n";
                    Append(~result, t);
                    else
                      vprintf CrvHypIso, 2: 
                              "    Does not give transformation f1 -> f2.\n";
                  end if;
                end if; // Dimension(ker) eq 1
              end if;
            end for; // root1
          end for; // a          
        end if; // d1 eq 2
      else // d eq 1
        // take three zeroes of f1
        vprintf CrvHypIso, 2: " Degree = 1. Take three zeroes of f1:";
        rs := [ r[1] : r in Roots(f1) ][[1,2,3]];
        vprintf CrvHypIso, 2: "  %o\n", rs;
        // and try to map them to any triple of zeroes of f2
        rootsf2 := [ <r[1],K!1> : r in Roots(f2) ];
        // take point at infinity into account if necessary
        if Degree(f2) lt n then Append(~rootsf2, <K!1, K!0>); end if;
        vprintf CrvHypIso,2 : " Roots of f2:\n %o\n", rootsf2;
        for r1 in rootsf2 do
          for r2 in [ r : r in rootsf2 | r ne r1 ] do
            for r3 in [ r : r in rootsf2 | r ne r1 and r ne r2 ] do
              vprintf CrvHypIso, 2: " Triple %o\n", [r1,r2,r3];
              t := Eltseq(Basis(Kernel(Matrix(3,
                      [r1[1],        r2[1],        r3[1],
                       r1[2],        r2[2],        r3[2],
                       -rs[1]*r1[1], -rs[2]*r2[1], -rs[3]*r3[1],
                       -rs[1]*r1[2], -rs[2]*r2[2], -rs[3]*r3[2]] )))[1]);
              vprintf CrvHypIso, 2: "    ==> Matrix = %o\n", t;
              f3 := TransformPolynomial(f1, n, t);
              if f3*LeadingCoefficient(f2) eq f2*LeadingCoefficient(f3) then 
                vprintf CrvHypIso, 2: "    Gives transformation f1 -> f2.\n";
                Append(~result, t);
              else
                vprintf CrvHypIso, 2: 
                        "    Does not give transformation f1 -> f2.\n";
              end if;
            end for; // r3
          end for; // r2
        end for; // r1
      end if; // d ge 3
      return not IsEmpty(result), result;
    end if; // degs1 eq degs2
end intrinsic;

