freeze;

/*********************************************************************
ellmodel.m

Nils Bruin, October 2002.

Intrinsics to obtain an elliptic curve from a planar curve or other scheme
birational to a genus 1 curve. Defined interface:

intrinsic EllipticCurve(C::Sch)->CrvEll,Map
intrinsic EllipticCurve(C::Sch,Point::Pt)->CrvEll,MapSch
intrinsic EllipticCurve(C::Crv,Place::PlcCrvElt)->CrvEll,MapSch      

The first accepts cubics, quartics of special form and hyperelliptics.
Cubics should have a rational flex, quartics should be recognisable as a double
cover of a P^1 with a rational ramification point and hyperelliptics should have
rational points at infinity or a rational branch point wrt. the double cover.
Clearly, this routine is for convenience only. If C is already in Weierstrass
form, it will be recognised and the origin will be chosen accordingly, i.e.
EllipticCurve(Curve(E)) should return a map corresponding to the identity.

The second intrinsic returns an elliptic curve with a map such that the given
(smooth) point maps to the origin on the elliptic curve. Cubics and special
quartics are dome more efficiently. In general, a Riemann-Roch computation is
used. For hyperelliptics again, Riemann-Roch computations are avoided (same code
as for special quartics)

The third does a Riemann-Roch computation using the given degree 1 place.

Programming model: Each of the functions ...ToEC returns BoolElt,CrvEll,MapSch.
The first indicating whether finding the model worked. If so, the resulting
elliptic curve and the map to it are returned.


  ***** CHANGES ****

 Feb 2010, Steve:
   For C over a finite field, EllipticCurve(C) now always finds a point 
   (by calling a general routine when no special point is found).

 Jan 2007, Steve: 
   Added QuadricIntersectionToEC.
   As a consequence, one has another (indirect!) route for dealing with 
   quartics, but which should work in all characteristics.

**********************************************************************/

declare verbose EllModel, 3;

function SimpleExpand(phi)
    // Expands the map phi if the appropriate coefficient ring is
    // "simple".  e.g., Q, finite fields.
    R := BaseRing(Domain(phi));
    t := Type(R);
    if t in {RngInt,FldRat,FldFin} then
	return Expand(phi);
    else
	return phi;
    end if;
end function;

function GCDMPolRemove(pols)
    // Returns a GCD for the multivariate polynomials that attempts to do
    // something sensible with the coefficients as well (when rational)
    g := GCD(pols);
    pols := [ f div g : f in pols ];
    if Type(BaseRing(Universe(pols))) eq FldRat then
	coeffs := &cat[ Coefficients(f) : f in pols ];
	n := GCD([Numerator(c) : c in coeffs]);
	d := GCD([Denominator(c) : c in coeffs]);
	if coeffs[1] lt 0 then n *:= -1; end if;
	if n ne d then
	    pols := [ f*(d/n) : f in pols ];
	end if;
    elif Type(BaseRing(Universe(pols))) eq RngInt then
	coeffs := &cat[ Coefficients(f) : f in pols ];
	if coeffs[1] lt 0 then
	    pols := [ -f : f in pols ];
	end if;
    end if;
    return pols;
end function;

function scheme_is_nice(X)
    // Returns whether the scheme has a single grading consisting
    // solely of ones
    return NumberOfGradings(X) eq 1 and &*Gradings(X)[1] eq 1;
end function;

function GCDRemove(phi)
    // Removes GCD components of the defining equations of the map.
    // It is possible this is not always the right thing to do. :(
    // However, an error (impossible projective point) is unlikely to be useful
    if not ISA(Type(phi), MapSch) then return phi; end if;
    if Type(BaseRing(Domain(phi))) notin { RngInt, FldRat } then
	return phi;
    end if;
    fpols := DefiningPolynomials(phi);
    if scheme_is_nice(Codomain(phi)) then
	fpols := GCDMPolRemove(fpols);
    end if;
    if not HasKnownInverse(phi) then
	return map<Domain(phi) -> Codomain(phi) | fpols : Check:=false >;
    end if;
    ipols := InverseDefiningPolynomials(phi);
    if scheme_is_nice(Domain(phi)) then
	ipols := GCDMPolRemove(ipols);
    end if;
    return map<Domain(phi) -> Codomain(phi) | fpols, ipols : Check:=false >;
end function;

function TrivialCubicToEC(C)
  //makes an elliptic curve from a plane curve that is almost in
  //weierstrass form:
  //   a*Y^2*z+c1*x*y*z+c3*y*z^2-b*X^3-c2*X^2*Z-c4*X*Z^2-c6*Z^3
  //i.e., it does the scaling on X and Y.

  // This works in all characteristics, I think    --- Steve
  
  //[  1,     2,     3,   4,     5,     6,     7,     8,     9,  10];
  //[X^3, X^2*Z, X*Z^2, Z^3, X^2*Y, X*Y*Z, Y*Z^2, X*Y^2, Y^2*Z, Y^3];
  //[ -1,   -a2,   -a4, -a6,     0,    a1,    a3,     0,     1,   0];

  assert IsProjective(C) and IsCurve(C) and Degree(C) eq 3;
  //guess we should test for IsNonSingular(C) as well, but
  //that's rather expensive and EllipticCurve downstairs will
  //complain anyway if passed a singular curve.

  F := DefiningPolynomial(C);
  vprint EllModel,3: "Testing if",F,
    "if in Weierstrass form up to scaling";
  A := Parent(F);
  X,Y,Z := Explode([A.1,A.2,A.3]);
  lcfY := MonomialCoefficient(F, Y^2*Z);
  lcfX := -MonomialCoefficient(F, X^3);
  if not(IsUnit(lcfY) and IsUnit(lcfX)) then
    vprint EllModel,3: "This is not the case.";
    return false,_,_;
  end if;
  F := Evaluate(F, [lcfY*X, Y, lcfY^2*lcfX*Z]) / lcfX/lcfY^3;
  c := [MonomialCoefficient(F,mn) : mn in
          [X^3, X^2*Z, X*Z^2, Z^3, X^2*Y, X*Y*Z, Y*Z^2, X*Y^2, Y^2*Z, Y^3]];
  if [c[1],c[5],c[8],c[9],c[10]] ne [-1,0,0,1,0] then
    vprint EllModel,2: "This is not the case.";
    return false,_,_;
  end if;
  bl,E := IsEllipticCurve([c[6],-c[2],c[7],-c[3],-c[4]]);
  error if not(bl), "Given curve is not of genus 1";
  cE := CoordinateRing(Ambient(E));
  toE := map<C->E | [lcfY*lcfX*X, lcfY^2*lcfX*Y, Z],
		    [lcfY*cE.1, cE.2, lcfY^2*lcfX*cE.3]  : Check:=false >;
  vprint EllModel,3: "Yes. Returning model",E;
  return true,E,GCDRemove(toE);
end function;

function CrossProduct(a,b)
  return [a[2]*b[3]-a[3]*b[2],a[3]*b[1]-a[1]*b[3],a[1]*b[2]-a[2]*b[1]];
end function;

function TangentToInfinity(C,P)
  //Transforms a curve such that P is mapped to [0:1:0] and
  //the tangent line of C at P is the line through [1:0:0] and [0:1:0]
  //(i.e., the tangent is the line at infinity in the first affine patch)

  assert IsProjective(C) and IsCurve(C);  
  tP:=TangentLine(P);
  P2:=Ambient(C);
  Crd:=CoordinateRing(Ambient(C));
  vP:=Vector(Eltseq(P));
  Normal:=[MonomialCoefficient(Equation(tP),Crd.i): i in [1,2,3]];
  vtP:=Kernel(Transpose(Matrix([Normal])));
  vQ:=ExtendBasis([vP],vtP)[2];
  vR:=ExtendBasis([vP,vQ],Parent(vP))[3];
  mp:=Automorphism(P2,Matrix([vQ,vP,vR])^(-1));
  Cnew:=mp(C);
  return Cnew,Restriction(mp,C,Cnew);
end function;

function CubicToEC(C,P)
  // This should work in all characteristics, I think    --- Steve
  assert IsCurve(C) and IsProjective(C) and Degree(C) eq 3;
  P2:=Ambient(C);
  R:=BaseRing(P2);
  bool, P:=IsCoercible(C(R),P);
  assert bool;
  vprint EllModel,2:
    "Putting",C,"with",P,"in Weierstrass form ...";
  if IsFlexFast(C,P) then
    vprint EllModel,2:
      "Point is a flex. Simple linear transformation will do.";
    C2,CtoC2:=TangentToInfinity(C,P);
    bl,E,C2toE:=TrivialCubicToEC(C2); assert bl;
    // Use SimpleExpand to make the map nicer; OK since C2toE is simple
    return true,E,GCDRemove(SimpleExpand(CtoC2*C2toE));
  else
    vprint EllModel,2:
      "Point is not a flex. Use Nagell's construction (Acta Math 52).";
    tP:=TangentLine(P);
    assert exists(R){R: R in Support(tP meet C)| R ne P};
    Crd:=CoordinateRing(P2);
    X,Y,Z:=Explode([Crd.i:i in [1,2,3]]);
    vP:=Vector(Eltseq(P));
    vR:=Vector(Eltseq(R));
    vQ:=ExtendBasis([vP,vR],Parent(vP))[3];
    CtoC2:=Automorphism(P2,Matrix([vQ,vP,vR])^(-1));
    C2:=CtoC2(C);
    CtoC2:=Restriction(CtoC2,C,C2);
    F:=DefiningPolynomial(C2);
    F1:=Crd!(Term(F,Z,2)/Z^2);
    F2:=Crd!(Term(F,Z,1)/Z);
    F3:=Term(F,Z,0);
    assert F-(F1*Z^2+F2*Z+F3) eq 0;
    G1:=Evaluate(F1,[Z,X,0]);
    G2:=Evaluate(F2,[Z,X,0]);
    G3:=Evaluate(F3,[Z,X,0]);
    if Characteristic(BaseRing(C)) ne 2 then
      C3:=Curve(P2,Z*Y^2-G) where G:=Crd!((G2^2-4*G1*G3)/Z);
      C2toC3:=map<C2->C3|[X*Y*Z,2*F3+F2*Z,X^2*Z],
                         [Z^2*Y-Z*G2,X*Y*Z-X*G2,2*G3] : Check:=false >;
    else   
      // This case was added by Steve 
      //  ... same idea, just don't complete the square.
      // Note that P was moved to [0:1:0]
      // We are projecting from [0:0:1] to the t-line where Y=t*X, and
      // setting s := F3(1,t)*X we find s^2 + F2(1,t)*s = F1(1,t)*F3(1,t)
      // which is a cubic Weierstrass equation in s,t. 
      // Define the curve in P2 using t=X/Z, s=Y/Z.
      assert Evaluate(F3,[0,1,0]) eq 0 and Evaluate(F2,[0,1,0]) eq 0; 
          // tangency condition at [0:1:0]
      C3:=Curve(P2, Crd! (Z*Y^2 + G2*Y + G1*G3/Z) );
      C2toC3:=map<C2->C3| [ X*Y*Z, F3, X^2*Z], 
                         // s = F3(X,Y)/X^2, t = Y/X
                          [ Y*Z^2, X*Y*Z, G3] : Check:=true >;
                         // X = s/F3(1,t), Y = tX, Z = 1
    end if;  
    bl,E,toE:=TrivialCubicToEC(C3); assert bl;
    // Use SimpleExpand to make the map nicer; OK since toE is simple
    return true,E,GCDRemove(CtoC2*SimpleExpand(C2toC3*toE));
  end if;
end function;

function MonicQuarticWork(f3,f2,f1,f0,L,wtY)
  //computes the transformation to put
  //Y^2=X^4+f3*X^3+f2*X^2+f1*X+f0
  //in weierstrass form.
  //L should be a list of variables
  //it returns the resulting elliptic curve E, a list
  //[U,V,W] that has to be equated to L and a list that expresses the inverse
  //map.
  //wtY can be either 1 or 2, corresponding to the weight of L[2].
  g1:= 1/2*f3;
  g0:= 1/2*f2-1/8*f3^2;
  h1:= -1/2*f3*f2+1/8*f3^3+f1;
  h0:= -1/4*f2^2+1/8*f2*f3^2-1/64*f3^4+f0;
  //with these definitions,
  //    X^4+f3*X^3+f2*X^2+f1*X+f0=(X^2+g1*X+g0)^2+(h1*X+h0)
  X:=L[1];Y:=L[2];Z:=L[3];
  E:=EllipticCurve([2*g1,-4*g0,2*h1,-4*h0,0]);
  crd:=CoordinateRing(Ambient(E));
  T:=crd.1;S:=crd.2;U:=crd.3;
  GXZ:=X^2+g1*X*Z+g0*Z^2;
  GST:=S^2+g1*S*2*T+g0*4*T^2;
  if wtY eq 1 then
    return E,
      [2*(Y*Z^2+Z*GXZ),4*(X*Y*Z+X*GXZ),Z^3],
      [2*S*T*U,2*T^3-GST*U,4*T^2*U];
  elif wtY eq 2 then
    return E,
      [2*(Y*Z+Z*GXZ),4*(X*Y+X*GXZ),Z^3],
      [S*U,2*T^3*U-U^2*GST,2*T*U];
  else
    error "not supported";
  end if;
end function;

function SpecialCuspQuartic(C)
  /*****************************************
   * Takes a genus 1 quartic with a unique (cuspidal) singularity
   * with a tangent cone that is a double counted line that C only in the cusp.
   *
   * It returns an equation of the form
   * d*Y^2*Z^2+G(X,Z)
   * together with the transformation.
   *****************************************/
   
  assert IsCurve(C) and IsProjective(C) and Degree(C) eq 4;
  P2:=Ambient(C);
  X:=P2.1;Y:=P2.2;Z:=P2.3;

  vprint EllModel,2: "Testing whether",C,"is a cuspidal quartic";
  S:=Support(SingularSubscheme(C));
  if #S ne 1 then
    vprint EllModel,2: "It is not.";
    return false,_,_;
  end if;
  
  //this is the singular point:
  S:=C!Rep(S);
  
  //The line that makes up the tangent cone
  T:=ReducedSubscheme(TangentCone(S));
  //check it's a line and the intersection
  if Degree(T) ne 1 or Degree(ReducedSubscheme(C meet T)) ne 1 then
    vprint EllModel,2:"Tangent cone has other intersection with curve.";
    return false,_,_;
  end if;
  
  vNT:=Kernel(Transpose(Matrix([
     [MonomialCoefficient(DefiningEquation(T),mn):mn in [X,Y,Z]]])));
  vS:=Vector(Eltseq(S));
  vR:=ExtendBasis([vS],vNT)[2]; //A point on T different from S
  vQ:=ExtendBasis([vS,vR],Parent(vS))[3];

  //We move S to (0:1:0) and R to (1:0:0), so that T becomes the line Z=0
  //We map vQ to (0:0:1) because something should go there ...
  CtoC2:=Automorphism(P2,Matrix([vR,vS,vQ])^(-1));
  C2:=CtoC2(C);
  CtoC2:=Restriction(CtoC2,C,C2);
  
  F:=DefiningPolynomial(C2);
  d:=MonomialCoefficient(F,Y^2*Z^2);
  
  //because CtoC2(T) meets C2 only in (0:1:0), B should be divisible by Z.
  B:=Parent(Y)!(Term(F,Y,1)/Y/Z);
  C2toC3:=map<P2->P2|[2*d*X*Z,2*d*Y*Z+B,2*d*Z^2],[2*d*X*Z,2*d*Y*Z-B,2*d*Z^2] : Check:=false >;
  C2toC3 := Normalization(C2toC3);	// avoid problems at infinity -- GB
  C3:=C2toC3(C2);
  C2toC3:=Restriction(C2toC3,C2,C3);
  vprint EllModel,2:"Quartic standard model found:",C3;
  return true,C3,GCDRemove(CtoC2*C2toC3);
end function;

function QuarticToEC(C,P)
  //    1,     2,       3,     4,   5,
  // [X^4, X^3*Y, X^2*Y^2, X*Y^3, Y^4,
  //       6,       7,       8,     9,
  //   X^3*Z, X^2*Y*Z, X*Y^2*Z, Y^3*Z,
  //       10,      11,      12,
  //    X^2*Z^2, X*Y*Z^2, Y^2*Z^2, 
  //             13,    14,
  //          X*Z^3, Y*Z^3,
  //                 15
  //                Z^4];
  assert IsCurve(C) and IsProjective(C) and Degree(C) eq 4;

  bl,C2,CtoC2:=SpecialCuspQuartic(C);
  if not(bl) then
    return false,_,_;
  end if;
  P:=CtoC2(P);

  P2:=Ambient(C2);
  X:=P2.1;Y:=P2.2;Z:=P2.3;

  //Next step is to move P to (0:1:0);
  
  if P[2] eq 0 then
    vprint EllModel,2: P,
      "is ramification point of double cover. Weierstrass model is immediate.";
    C2toC3:=map<P2->P2|[Z*(P[3]*X-P[1]*Z),Z*Y,(P[3]*X-P[1]*Z)^2],
                       [Z*X+P[1]*X^2,P[3]*Y*Z,P[3]*X^2] : Check:=false >;
    C3:=C2toC3(C2);
    C2toC3:=Restriction(C2toC3,C2,C3);
    bl,E,C3toE:=TrivialCubicToEC(C3);
    assert bl;
    return true,E,GCDRemove(CtoC2*C2toC3*C3toE);
  else
    if P[3] eq 1 then
      vprint EllModel,2: "Moving",P,"to infinity ...";
      C2toC3:=map<P2->P2|[P[2]*Z*(X-P[1]*Z),Y*Z,P[2]*(X-P[1]*Z)^2],
                         [X*Z+P[1]*X^2,P[2]*Y*Z,X^2] : Check:=false >;
    elif P[3] eq 0 then
      vprint EllModel,2: "Point already at infinity. Try rescaling.";
      F:=DefiningPolynomial(C2);
    //lcf:=-MonomialCoefficient(F,Y^2*Z^2)/MonomialCoefficient(F,X^4);
      lcf:=-MonomialCoefficient(F,X^4)/MonomialCoefficient(F,Y^2*Z^2);
      bl,sqrt:=IsSquare(lcf);
      error if not(bl),
         "Point at infinity does not split upon desingularisation";
      C2toC3:=map<P2->P2|[sqrt*X,Y,sqrt*Z],[X,sqrt*Y,Z] : Check:=false >;
    end if;
    
    C3:=C2toC3(C2);
    C2toC3:=Restriction(C2toC3,C2,C3);
         
    F:=DefiningPolynomial(C3);
    F:=F/MonomialCoefficient(F,Z^2*Y^2);
    c:=[MonomialCoefficient(F,m): m in [X^4,X^3*Y,X^2*Y^2,X*Y^3,Y^4,X^3*Z,
         X^2*Y*Z,X*Y^2*Z,Y^3*Z,X^2*Z^2,X*Y*Z^2,Y^2*Z^2,X*Z^3,Y*Z^3,Z^4]];
    assert forall{i: i in [2,3,4,5,7,8,9,11,14]|c[i] eq 0};
    assert c[12] eq 1;
    assert c[1] eq -1;
    //assert F eq Y^2*Z^2-(X^4-c[6]*X^3*Z-c[10]*X^2*Z^2-c[13]*X*Z^3-c[15]*Z^4);
    E,v,vi:=MonicQuarticWork(-c[6],-c[10],-c[13],-c[15],[X,Y,Z],1);
    vprint EllModel,2: "Found",E;
    return true,E,GCDRemove(CtoC2*C2toC3*map<C3->E|v,vi : Check:=false >);
  end if;
end function;


// Added by Steve, also following Cassels book, p 36. 
// The idea is simply to project from P, obtaining a plane cubic.
// This should work in all characteristics.

function QuadricIntersectionToEC(C,P)
  error if not IsProjective(C) or Dimension(Ambient(C)) ne 3 or not IsQuadricIntersection(C),
       "The curve should be an intersection of two homogeneous quadrics in P^3";
  X,Y,Z,T := Explode([C.i : i in [1..4]]);
  // Move P to [0:0:0:1]
  Pcoords := Vector(BaseRing(C), Eltseq(C!P)); 
  V := Parent(Pcoords);
  trans := Matrix(4,4, Reverse(ExtendBasis([Pcoords],V)));  // [0,0,0,1]*trans = Pcoords
  q1,q2 := Explode([ Evaluate(quadric, Eltseq(Vector([X,Y,Z,T])*ChangeRing(trans,Parent(X)))) 
                     : quadric in DefiningEquations(C) ]);
  Q1 := [ [ MonomialCoefficient(q1, Exponents(C.i*C.j)) : i in [1..4]] : j in [1..4]];  
  Q2 := [ [ MonomialCoefficient(q2, Exponents(C.i*C.j)) : i in [1..4]] : j in [1..4]];  
  //        Note: cross-terms are not divided by 2
  assert Q1[4,4] eq 0 and Q2[4,4] eq 0;  // both vanish at [0:0:0:1]
  // Write Q1 = T*L+R and Q2 = T*M+S (in the notation from Cassels)
  L := Q1[4,1]*X + Q1[4,2]*Y + Q1[4,3]*Z;
  M := Q2[4,1]*X + Q2[4,2]*Y + Q2[4,3]*Z;
  R := Q1[1,1]*X^2 + Q1[2,2]*Y^2 + Q1[3,3]*Z^2 + Q1[1,2]*X*Y + Q1[1,3]*X*Z + Q1[2,3]*Y*Z;
  S := Q2[1,1]*X^2 + Q2[2,2]*Y^2 + Q2[3,3]*Z^2 + Q2[1,2]*X*Y + Q2[1,3]*X*Z + Q2[2,3]*Y*Z;

  // Project (vertically) from [0:0:0:1]
  // (Assume genus 1 here, EllipticCurve will check in the end.)
  cubic := L*S - M*R;
  // This has a rational point given by L = M = 0
  solspace := Kernel(Transpose(Matrix(2,3, [[Q1[4,1],Q1[4,2],Q1[4,3]], 
                                            [Q2[4,1],Q2[4,2],Q2[4,3]]] )));
  error if Dimension(solspace) gt 1, "I reckon that curve ain't got genus one.";
  pt := Eltseq(Basis(solspace)[1]);                                            
  Pr2 := ProjectiveSpace(BaseRing(C),2);
  CC := Curve(Pr2, Evaluate(cubic, [Pr2.1,Pr2.2,Pr2.3,0]) );
  proj_map := Eltseq( Vector([X,Y,Z,T])*ChangeRing(trans^-1,Parent(X)) )[1..3];
  Pr2_trans := Eltseq( Vector([Pr2.1,Pr2.2,Pr2.3,0])*ChangeRing(trans,Parent(Pr2.1)) );
  XX,YY,ZZ,LL,MM,RR,SS := Explode([ Evaluate(pol, [Pr2.1,Pr2.2,Pr2.3,0]) 
                                  : pol in [X,Y,Z,L,M,R,S] ]);
  inverse_map := [[XX*LL,YY*LL,ZZ*LL,-RR], [XX*MM,YY*MM,ZZ*MM,-SS]]; // alt. equations
  inverse_map := [ Eltseq( Vector(seq)*ChangeRing(trans,Parent(XX)) ) 
                                : seq in inverse_map ]; 
  CtoCC := map< C -> CC | proj_map, inverse_map : Check:=false >;
  bool, E, CCtoE := CubicToEC(CC, CC!pt );  assert bool;
  return E, GCDRemove(SimpleExpand(CtoCC*CCtoE));
end function;

function IsRamificationPoint(C,P)
  /* NB: this also works in characteristic 2! */
  if P[3] eq 0 then // point at infinity
    return NumberOfPointsAtInfinity(C) eq 1;
  end if;
  x := P[1]/P[3];
  f,h:=HyperellipticPolynomials(C);
  return (Evaluate(F,x) eq 0) where F is h^2+4*f;
end function;

function HyperellipticToEC(C,P)
  //assert Degree(C) eq 4 and IsHyperellipticCurve(C);
  R:=BaseRing(C);
  bool, P:=IsCoercible(C(R),P); assert bool;
  f,h:=HyperellipticPolynomials(C);

  // Characteristic 2 case, added by Steve:
  // silly trick of converting to an intersection of quadrics, 
  // because that case is coded to work in all characteristics.
  // Substitute R=X^2, S=X*Z, T=Y, U=Z^2 (in terms of weighted proj X,Y,Z)
  if Characteristic(R) eq 2 and h ne 0 then
    h0,h1,h2 := Explode([ Coefficient(h,i) : i in [0,1,2] ]);
    f0,f1,f2,f3,f4 := Explode([ Coefficient(f,i) : i in [0,1,2,3,4] ]);
    Pr3 := ProjectiveSpace(R,3);  R,S,T,U := Explode([Pr3.i: i in [1..4]]);
    QI := Curve(Pr3, [ S^2 - R*U, 
                       T^2 + T*(h2*R+h1*S+h0*U) - (f4*R^2+f3*R*S+f2*S^2+f1*S*U+f0*U^2) ]);
    CtoQI := map< C -> QI | [C.1^2, C.1*C.3, C.2, C.3^2], [S,T*U,U] : Check:=false >;
    E, QItoE := QuadricIntersectionToEC(QI, P@CtoQI);
    return true, E, GCDRemove(SimpleExpand(CtoQI*QItoE));
  end if;

  //compensate with square of determinant of FracLinTran
  if not IsRamificationPoint(C,P) then
    vprint EllModel,2:
      "Moving",P,"to infinity";
    if P[3] eq 0 then
      L:=[1,0,0,1];
    elif P[1] ne 0 then
      L:=[1,0,-P[3]/P[1],1];
    else
      L:=[0,1,1,0];
    end if;
    Ca,CtoCa:=Transformation(C,L,1,h/2);
    e:=1/CtoCa(P)[2];
    C2,CatoC2:=Transformation(Ca,e);
    CtoC2:=CtoCa*CatoC2;
    f,h:=HyperellipticPolynomials(C2);
    assert IsWeaklyZero(h) and IsWeaklyZero(LeadingCoefficient(f)-1);

    f0,f1,f2,f3:=Explode(Eltseq(f));
    Crd:=Ambient(C2);
    vprint EllModel,2:
      "Resulting curve:",C2;
    E,v,vi:=MonicQuarticWork(f3,f2,f1,f0,[Crd.1,Crd.2,Crd.3],2);
    C2toE:=map<C2->E|v,vi : Check:=false >;
    vprint EllModel,2:
      "Returning",E;
    return true,E, GCDRemove(CtoC2*C2toE);
  else
    if P[3] eq 0 then
      vprint EllModel,2:
      P,"is ramification point at infinity. We leave it there.";
      f,h:=HyperellipticPolynomials(C);
      C2,CtoC2:=Transformation(C,h/2);
    else
      vprint EllModel,2:
        P,"is ramification point. Moving to infinity";
      if P[1] ne 0 then
        L:=[1,0,-P[3]/P[1],1];
      elif P[3] ne 0 then
        L:=[0,1,1,0];
      end if;
      C2,CtoC2:=Transformation(C,L,1,h/2);
    end if;
    f,h:=HyperellipticPolynomials(C2);
    assert h eq 0 and Degree(f) eq 3;
    e:=LeadingCoefficient(f);
    C3,C2toC3:=Transformation(C2,[e,0,0,1],e);
    vprint EllModel,2:
      "Result:",C3,"Scaling to Weierstrass model.";
    f,h:=HyperellipticPolynomials(C3);
    assert h eq 0 and LeadingCoefficient(f) eq 1;
    E:=EllipticCurve([0,c[3],0,c[2],c[1]]) where c:= Eltseq(f);
    X,Y,Z:=Explode([K.1,K.2,K.3]) where K:=CoordinateRing(Ambient(C3));
    T,S,U:=Explode([K.1,K.2,K.3]) where K:=CoordinateRing(Ambient(E));
    C3toE:=map<C3->E|[X*Z,Y,Z^2],[E.1,E.2*E.3,E.3] : Check:=false >;
    vprint EllModel,2:
      "Returning",E;
    return true,E,GCDRemove(CtoC2*C2toC3*C3toE);
  end if;
end function;

///////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve(C::Crv)->CrvEll,Map
  {Returns an elliptic curve from certain genus 1 curves with an easily
  recognised rational point.}

  R := BaseRing(C);
  found := false;
  vprint EllModel:"No point given. Trying some obvious tricks.";

  //plane cubics without a given point

  if IsHyperellipticCurve(C) and Characteristic(R) ne 2 then
    vprint EllModel:C,"is a hyperelliptic curve";
    if Type(C) ne CrvHyp then
      _,C := IsHyperellipticCurve(C);
    end if;
    error if Genus(C) ne 1, "Curve is not genus 1.";
    f,h:=HyperellipticPolynomials(C);
    F := f+(1/4)*h^2;
    if Degree(F) eq 3 then
      if Degree(h) le 1 then
        vprint EllModel:"of degree 3! Using (1:0:0)";
        P:=C![1,0,0];
      else // deg(f)=4, deg(h)=2
        vprint EllModel:"of degree 3! Using point at infinity";
        P:=C![1,-(1/2)*Coefficient(h,2),0];
      end if;
      found := true;
    else 
      assert Degree(F) eq 4;
      vprint EllModel:"of degree 4. Any rational ramification points?";
      Ps:=Roots(F);
      if not(IsEmpty(Ps)) then
        P:=C![v,-(1/2)*Evaluate(h,v),1] where v is Rep(Ps)[1];
        vprint EllModel:"Yes! Using",P;
        found := true;
      else
        vprint EllModel:"No. Trying points at infinity";
        Ps:=PointsAtInfinity(C);
        if #Ps gt 0 then
          P:=Rep(Ps);
          vprint EllModel:"Found one. Using",P;
          found := true;
        end if;
      end if;
    end if;
    if found then
      bl,E,CtoE:=HyperellipticToEC(C,P);
      assert bl;
      vprint EllModel:"Returning",E;
      return E, CtoE;
    end if;

  elif (Degree(C) eq 3) and IsOrdinaryProjective(C) and (Dimension(Ambient(C)) eq 2) then
    require IsProjective(C): "Curve must be projective";
    require IsIrreducible(DefiningPolynomial(C)): "Curve must be irreducible and reduced";
    require IsNonsingular(C): "Curve is not Genus 1"; 
    vprint EllModel:"Degree 3 tricks may apply.";
    //First try the easy case: See if a permutation allows immediate
    //recognition of a Weierstrass model.
    P2:=Ambient(C);
    vprint EllModel:"Does any axis meet",C,"in a flex?";
    // Note that this method of going through the permutations of the
    // coordinates does the identity first, as is desirable
    coords := [P2.1, P2.2, P2.3];
    for g in Sym(3) do
      // It also makes it easy to get the inverse
      CtoC2:=map<P2->P2|coords^g, coords^(g^-1) : Check:=false >;
      C2:=CtoC2(C);
      found,E,C2toE:=TrivialCubicToEC(C2);
      if found then
        vprint EllModel:"Yes! returning",E;
	// Use Expand to make the map nicer; OK since CtoC2 is a permutation
        return E,GCDRemove(Expand(Restriction(CtoC2,C,C2)*C2toE));
      end if;
    end for;

    //More expensive option: see if there are any rational flexes.
    //(those are the only geometrically recognisable points that can
    //easily be tested for rationality).
    vprint EllModel:"Are there any rational flexes?";
    flexes := Flexes(C);
    if Dimension(flexes) eq 0 then
      V:=Support(flexes);
      if not(IsEmpty(V)) then
        P:=Rep(V);
        vprint EllModel:"Yes! We have",P;
        found := true;
        bl,E,CtoE:=CubicToEC(C,P);
        assert bl;
        vprint EllModel:"returning",E;
        return E,CtoE;
      end if;
    end if;

  elif (Degree(C) eq 4) and (Characteristic(R) ne 2) and IsOrdinaryProjective(C) and
		(Dimension(Ambient(C)) eq 2) then
    require IsProjective(C):"Curve must be projective";
    require IsIrreducible(DefiningPolynomial(C)): "Curve must be irreducible and reduced";
    vprint EllModel:"Degree 4 tricks may apply";

    vprint EllModel:"Perhaps",C,
      "has a unique cusp with a tangent cone meeting only there?";
    bl,C2,CtoC2:=SpecialCuspQuartic(C);
    if bl then
      vprint EllModel:"Yes! We use a new model",C2;
      P2:=Ambient(C2);
      vprint EllModel:"Perhaps there is a point (*:0:*)?";
      Ps:=Support(C2 meet Curve(P2,P2.2));
      if IsEmpty(Ps) then
        vprint EllModel:"Or perhaps (0:1:0) splits upon desingularisation?";
        F:=DefiningPolynomial(C2);
        if IsSquare(-MonomialCoefficient(F,P2.2^2*P2.3^2)/
                     MonomialCoefficient(F,P2.1^4)) then
          P:=C2![0,1,0];
          found := true;
        end if;
      else
        found := true;
        P:=Rep(Ps);
        vprint EllModel:"Found:",Ps,"Using:",P;
      end if;
    end if;
  
    if found then
      _,E,C2toE:=QuarticToEC(C2,P);
      vprint EllModel:"Returning",E;
      return E,GCDRemove(CtoC2*C2toE);
    end if;
  end if;

  // Added Feb 2010, SRD
  if IsFinite(R) then
    vprintf EllModel: "No special points found. "*
      "Now looking for a point using the fibration method ... ";
    vtime EllModel:
    // calling fibration method because it has Max option
    pts := RationalPointsByFibration(C : Max:=1); 
    return EllipticCurve(C, pts[1]);
  end if;
  
  error "Sorry, you'll have to specify a point for that one.";
    
end intrinsic;

///////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve(C::Crv,Point::Pt)->CrvEll,MapSch
  {Returns a Weierstrass model of a genus 1 curve with a point and also
  the map from C to that model. The point should be nonsingular.}

  require Genus(C) eq 1 : "Curve must have genus 1";

  if Scheme(Point) cmpne C then
    bool, Point := IsCoercible(C, Point);
    require bool : "Point does not lie on curve";
  end if;

  //if Type(C) eq CrvHyp and Characteristic(BaseRing(C)) ne 2 then
  if Type(C) eq CrvHyp then
    vprint EllModel:"Hyperelliptic curve. Using Cassels' trick (LMSST 24).";
    bl,E,CtoE:=HyperellipticToEC(C,Point);
    return E,CtoE;
  end if;

  if IsOrdinaryProjective(C) and Length(Ambient(C)) eq 3 then  
    //cubics... This algorithm should always work
    if Degree(C) eq 3 and Characteristic(BaseRing(C)) notin {2,3} then
      vprint EllModel:
        "Cubic (better be smooth). Using Nagell or linear transformation.";
      bl,E,CtoE:=CubicToEC(C,Point);
      if bl then
        return E,CtoE;
      else
        error "I bet that curve is not smooth.";
      end if;

    //This algorithm only applies to genus 1 quartics with a cusp
    //and a tangent cone that meets exclusively in that cusp.
    //The algorithm will return false if this doesn't hold.
    elif Degree(C) eq 4 and Characteristic(BaseRing(C)) ne 2 then
      vprint EllModel:"Quartic curve. First try Cusp trick.";
      bl,E,CtoE:=QuarticToEC(C,Point);
      if bl then
        return E,CtoE;
      end if;
      vprint EllModel:"Failed.";
    end if;

  elif IsQuadricIntersection(C) then 
    vprint EllModel: "Curve is a QuadricIntersection. Projecting to a plane cubic."; 
    return QuadricIntersectionToEC(C,Point); 

  end if;
  require IsProjective(C): "Curve must be projective";
  vprint EllModel:"Reverting to Riemann Roch computation.";

  pl:=Places(Point);
  error if not(exists(pl){p:p in pl| Degree(p) eq 1}),
    "No degree 1 place above this point";

  FF,fmp := AlgorithmicFunctionField(FunctionField(C));

  plFF := FunctionFieldPlace(pl);
  bl:=exists(x){b@@fmp : b in Basis(2*plFF)| Valuation(b,plFF) eq -2};
  assert bl;
  bl:=exists(y){b@@fmp : b in Basis(3*plFF)| Valuation(b,plFF) eq -3};
  assert bl;
  
  P2:=Ambient(C);
  if (not IsOrdinaryProjective(C)) or (Length(P2) ne 3) then
	P2 := ProjectiveSpace(BaseRing(C),2);
  end if;
  mp:=ProjectiveMap([x,y,1],P2);
  L:=Basis(Relations([y^2,y*x,y,x^3,x^2,x,1] @ fmp,BaseRing(C)))[1];
  X:=P2.1;Y:=P2.2;Z:=P2.3;
  C2:=Curve(P2,L[1]*Y^2*Z+L[2]*X*Y*Z+L[3]*Y*Z^2+L[4]*X^3+
                 L[5]*X^2*Z+L[6]*X*Z^2+L[7]*Z^3);
  bl,E,C2toE:=TrivialCubicToEC(C2);
  assert bl;
  vprint EllModel:"returning",E;
  // Use SimpleExpand to make the map nicer; OK since C2toE is simple
  return E,GCDRemove(SimpleExpand(Restriction(mp,C,C2:Check:=false)*C2toE));
end intrinsic;

///////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve(C::Crv,Place::PlcCrvElt)->CrvEll,MapSch      
  {Returns a Weierstrass model of a genus 1 curve with a degree 1 place and also
  the map from C to that model.}

  require Degree(Place) eq 1: "Place must be of degree 1.";
  require IsProjective(C): "Curve must be projective";

  vprint EllModel:"Doing Riemann Roch computation.";

  FF,fmp := AlgorithmicFunctionField(FunctionField(C));
  
  plFF := FunctionFieldPlace(Place);
  bl:=exists(x){b@@fmp : b in Basis(2*plFF)| Valuation(b,plFF) eq -2};
  assert bl;
  bl:=exists(y){b@@fmp : b in Basis(3*plFF)| Valuation(b,plFF) eq -3};
  assert bl;
  
  P2:=Ambient(C);
  if (not IsOrdinaryProjective(C)) or (Length(P2) ne 3) then
	P2 := ProjectiveSpace(BaseRing(C),2);
  end if;
  mp:=ProjectiveMap([x,y,1],P2);
  L:=Basis(Relations([y^2,y*x,y,x^3,x^2,x,1] @ fmp,BaseRing(C)))[1];
  X:=P2.1;Y:=P2.2;Z:=P2.3;
  C2:=Curve(P2,L[1]*Y^2*Z+L[2]*X*Y*Z+L[3]*Y*Z^2+L[4]*X^3+
                 L[5]*X^2*Z+L[6]*X*Z^2+L[7]*Z^3);
  bl,E,C2toE:=TrivialCubicToEC(C2);
  assert bl;
  vprint EllModel:"returning",E;
  // Use SimpleExpand to make the map nicer; OK since C2toE is simple
  return E,GCDRemove(SimpleExpand(Restriction(mp,C,C2:Check:=false)*C2toE));
  
end intrinsic;

intrinsic CubicModel(E::CrvEll) -> CrvEll, Map, Map
{Convert an elliptic curve model to y^2 = cubic, in characteristic not 2}
 require Characteristic(BaseRing(E)) ne 2: "Cannot have characteristic 2";
 a1,_,a3:=Explode(aInvariants(E));
 if BaseRing(E) cmpeq Rationals() and
    Denominator(a1) eq 1 and Denominator(a3) eq 1 and
    (IsOdd(Integers()!a1) or IsOdd(Integers()!a3)) then
      return Transformation(E,[0,a1,4*a3,2]);
 else return Transformation(E,[0,a1/2,a3/2,1]); end if; end intrinsic;
