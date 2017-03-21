freeze;

///////////////////////////////////////////////////////////////////////
// param.m
// Florian Hess. Installed GDB May 2001
// May 2002: David Kohel 
// Revised to include inverse maps and multiple defining sequences
///////////////////////////////////////////////////////////////////////

import "../Sch/funcoord.m": NonEmptyPatchIndex;

import "../CrvCon/points.m": reduce_ideal, small_element;

// The function below does conic parametrisation Denis Simon's way
// ("Sur la parametrisation des solutions des equations quadratiques")

primitivecoords:=function(p);
  p:=Eltseq(p);
  K:=Parent(p[1]);
  R:=RingOfIntegers(K);
  L:=LCM([Denominator(x): x in p]);
  p:=[R!(L*x): x in p];
  G:=GCD(p);
  p:=[R!(x/G): x in p];
  return(p);
end function;

// return integral elementes u,v such that g=a*u+b*v (assumes coprimality)
function represent(g,a,b)
  R:=Integers(NumberField(Parent(a)));
  if IsUnit(R!a) then return R!(g/a),0; 
  elif IsUnit(R!b) then return 0,R!(g/b); end if;
  Ia:=ideal<R|a>; 
  _,modIa:=quo<R|Ia>;
  v:=(g@modIa/(b@modIa))@@modIa;
  u:=R!((g-b*v)/a);
  assert g eq a*u+b*v;
  return u,v;
end function;

function Xgcd_FldNum(a,b) 
  R:=Integers(NumberField(Parent(a)));
  g:=small_element(ideal<R|a,b>);
  u,v:=represent(g,a,b); 
  return g,u,v; 
end function;

function ds_param(Con,pt : P1:=0)
  p := Coordinates(pt);
  if (p[1] eq 0) and (p[2] eq 0) then
     // p = [0:0:1] and the hardcoded formulae below degenerate to 0/0.
     // Work-around by Steve: swap y and z, run the function, switch back. 
     Con1 := Conic(P2, Evaluate(DefiningEquation(Con),[P2.1,P2.3,P2.2])) where P2 is Ambient(Con);
     m1 := ds_param(Con1, Con1![0,1,0] : P1:=P1);
     return map< Domain(m1) -> Con | [m1eqs[1],m1eqs[3],m1eqs[2]] where m1eqs is DefiningEquations(m1) >;
  end if;

  FC:=DefiningEquation(Con);
  MC:=Matrix(Con);
  P<X,Y,Z>:=AmbientSpace(Con);
  K:=FieldOfFractions(BaseRing(P));
  R:=RingOfIntegers(K);

  if Type(K) in {FldRat, FldFunRat} then 
    p:=primitivecoords(p);
  //G:=GCD(p);
  //p:=[R!(x/G): x in p];
    assert GCD(p) eq 1;
    a:=p[1];b:=p[2];c:=p[3];
    g,u,v:=Xgcd(a,b);
    h,w,z:=Xgcd(g,c);
    M:=Matrix(3, [R| a,b,c, -v,u,0, -a*z/g,-b*z/g,w]);
    assert Determinant(M) eq 1;

  elif ISA(Type(K), FldAlg) then 
    // The change of basis won't be integral, but hopefully not too far off.
    // First clear denominators, and common factors as much as possible
    _,s:=reduce_ideal(ideal<R|p>);
    p:=[R| s*x : x in p];
    a,b,c:=Explode(p);
    g,u,v:=Xgcd_FldNum(a,b);
    h,w,z:=Xgcd_FldNum(g,c);
    M:=Matrix(3, [R| a,b,c, -v,u,0, -a*z/g,-b*z/g,w]);
  end if;

  Mt:=Transpose(M);
  qp:=M*MC*Mt;
  assert qp[1,1] eq 0;
  qh:=Matrix(3, [qp[2,2],     2*qp[2,3], qp[3,3],
                 -2*qp[1,2], -2*qp[1,3], 0,
                 0,          -2*qp[1,2], -2*qp[1,3] ]);
  q:=Mt*qh;

  if P1 cmpeq 0 then P1:=ProjectiveSpace(K,1); end if;
  eq1:=q[1,1]*P1.1^2+q[1,2]*P1.1*P1.2+q[1,3]*P1.2^2;
  eq2:=q[2,1]*P1.1^2+q[2,2]*P1.1*P1.2+q[2,3]*P1.2^2;
  eq3:=q[3,1]*P1.1^2+q[3,2]*P1.1*P1.2+q[3,3]*P1.2^2;
  par:=[eq1,eq2,eq3];
  m:=map<P1->Con|par>;

  return m;
end function;


function ConicParametrization(C,p,P)     /* added 02/05 - mch. */

    F := DefiningPolynomial(C);
    CR := Parent(F);
    inds := [1,2,3];
    pcs := Coordinates(p);
    L1 := [Evaluate(Derivative(F,i),pcs) : i in inds];
    // L1 = coeffs of tangent line at p

    cnz := Min([j : j in inds | L1[j] ne 0]);
    Remove(~inds,cnz);
    L2 := [pcs[inds[2]],-pcs[inds[1]]];
    Insert(~L2,cnz,0); // L2 = coeffs of another line through p
    
    // Now replace L1 by another line through the second intersection
    // of L1 and C
    vec := [CR.i : i in [1..3]];
    if L2[inds[1]] ne 0 then
	assert (L2[inds[1]] eq 1);
	vec[inds[1]] := -L2[inds[2]]*CR.inds[2];
	cnz := inds[1];
    else
	assert (L2[inds[2]] eq -1);
	vec[inds[2]] := 0;
	cnz := inds[2];
    end if;
    inds := Remove([1,2,3],cnz);
    F1 := Evaluate(F,vec)/&+[L1[i]*vec[i]:i in [1..3]];
    assert(Denominator(F1) eq 1);
    L1 := [MonomialCoefficient(num,CR.i): i in [1..3]] where 
    				num is Numerator(F1); 
    t := Min([j : j in [1..3] | L1[j] ne 0]);
    L1 := [e/L1[t] : e in L1];
    
     // The isomorphism C -> P will be given by [X:Y:Z] -> [L1:L2]=[s:t]
     // - we'll find the inverse of this.
     //  If we work over the field k(s/t) then the inverse map gives a
     // generic point for which L1=(s/t)*L2. The line L1-(s/t)*L2 meets C in
     // two points over k(s/t) : the other zero of L1 on C (fixed point of
     // linear sys) and the generic point.
     //  We express CR.cnz as a k(s/t) linear comb. of the other two CR.j from
     // L2=(t/s)*L1 and substitute into the equation of C to get a quadratic
     // form in the other 2 vars over k(s/t). Dividing this by the equation
     // for L1 (with CR.cnz similarly substituted gives a linear relation
     // L3 for the two CR.j. Then expressions for X,Y,Z in the inverse map
     // as quadratic polys in s and t can be recovered by rehomogenising
     // (wrt s,t) L3 and the 3 lin indep relations in X,Y,Z:
     //    L1= lin*s, L2=lin*t, L3=0 for some linear s,t form lin.
     //  Below, s is (t/s)!
        
    K<s> := RationalFunctionField(BaseRing(CR): Global := false);
    R := PolynomialRing(K: Global := false); x := R.1;
    Lst := ((s*L1[inds[1]]-L2[inds[1]])*x +
	    (s*L1[inds[2]]-L2[inds[2]]) )/ L2[cnz];

    vec := [x,R!1];
    Insert(~vec,cnz,Lst);
    F1 := Evaluate(F,vec)/(x*L1[inds[1]]+L1[inds[2]]);
    assert(Denominator(F1) eq 1);
    F1 := Numerator(F1);
    vec := [IntegerRing(K)|Coefficient(F1,0),-Coefficient(F1,1)];
    vec := [v div g: v in vec] where g is GCD(vec);
    deg := Maximum([Degree(v) : v in vec]);
    assert (deg le 2) and (deg gt 0);

    // here L3 given by v2*CR.inds[1]-v1*CR.inds[2]=0 where
    //   vi(s,t) is the homogenized vec[i](s)
    //  Can now build the inverse map
    L := L1[inds[1]]*vec[1]+L1[inds[2]]*vec[2];
    // Now if l2 is the common linear factor of CR.1 and CR.2 (as deg <= 2
    //  forms in s) then L*l2 = lin with lin as described above.
    //  So l2|all CR.i => l2 = const and can take l2=1
    s := IntegerRing(K)!s;
    assert (L ne 0) and (Degree(L) le 1); 
    Xst := (s*L-L2[inds[1]]*vec[1]-L2[inds[2]]*vec[2])/ L2[cnz];
    Insert(~vec,cnz,Xst);

    return iso<P->C | [Evaluate(v,s_t) : v in vec],
		[ &+[L1[i]*CR.i : i in [1..3]], &+[L2[i]*CR.i : i in [1..3]] ] 
		: Check := false> where s_t is R.2/R.1
		where R is CoordinateRing(Ambient(P));
		
end function;

/* special case code for when C is a plane line */
function LineParametrization(C,p,P)
    A := Ambient(C);
    f := DefiningPolynomial(C);
    a, b, c := Explode([ MonomialCoefficient(f,A.i) : i in [1..3] ]);
    if b ne 0 then
	return map< P -> C | [b*P.1,-a*P.1-c*P.2,b*P.2], [A.1,A.3] >;
    elif c ne 0 then
	return map< P -> C | [c*P.1,c*P.2,-a*P.1-b*P.2], [A.1,A.2] >;
    else 
	return map< P -> C | [-b*P.1-c*P.2,a*P.1,a*P.2], [A.2,A.3] >;
    end if;
end function;

/* special case code for when C is a general plane curve -
    a bit more efficient than the general curve code. */
function PlaneParametrization(C,p,P)

    // test for only ordinary singularities - if so, use the
    //  generally faster adjoint mapping method.
    if IsOrdinaryProjective(C) then
      boo,_,Iadj := HasOnlyOrdinarySingularities(C);
      if boo then
	prm := ParametrizeOrdinaryCurve(C,p,Iadj);
	return iso<P->C|ChangeUniverse(DefiningEquations(prm),
	  CoordinateRing(Ambient(P))),InverseDefiningPolynomials(prm) :
		Check := false>;
      end if;
    end if;

    F := FunctionField(C);
    FF,m := AlgorithmicFunctionField(F);
    // The exisiting ff parametrisation intrinsic uses the 'infinite'
    // function fields, so I translate further to that for the calculation.
    FFF := UnderlyingRing(FF);
    x, fncs := Parametrization(FFF,
        DivisorGroup(FFF)!FunctionFieldDivisor(Divisor(p)));
    // This answer has two parts:  x and fncs.
    // x is a function and should be regarded as a map to P^1
    // fncs is a seq of 2 functions in the coeff ring of the ff,
    // and these should be regarded as a map from P^1 to the curve.
    // We merely need to translate this info to our situation and build the map.

    // Order of generators of FF may be reversed.
    fncs1 := Insert(fncs,4-NonEmptyPatchIndex(C),1);
    pol := DefiningPolynomial(C);
    if (Evaluate(pol,fncs1) ne 0) then
        Reversion(~fncs);
	fncs1 := Insert(fncs,4-NonEmptyPatchIndex(C),1);
	assert (Evaluate(pol,fncs1) eq 0);
    end if;

    // get equations of map P^1 to curve
    FP := FunctionField(P);
    mp := hom<Universe(fncs1)->FP | [FP.1]>;
    eqs :=  fncs1 @ mp;

    return map< P -> C | eqs,[Inverse(m)(FF!x),1] : Check:=false >;
end function;

intrinsic Parametrization(C::Crv, p::Pt) -> MapSch
{Parametrization of the rational curve C given a rational point or a place p on C. 
 If provided, the projective line P will be used as the domain of this map} 
    K := BaseRing(C); 
    require IsField(K): "Base ring of argument 1 must be a field.";
    require Type(C) in {CrvCon,CrvRat} or Genus(C) eq 0: "Argument 1 must be of genus 0.";
    require IsCoercible(C,p):
        "Argument 2 must be a point of argument 1 over its base ring.";
    require IsProjective(Ambient(C)):
        "Argument 1 must be projective.";
    if IsRationalCurve(C) then
	return LineParametrization(C,p,Curve(ProjectiveSpace(K, 1)));
    elif IsConic(C) and Type(K) eq FldFunRat and Type(Integers(K)) eq RngUPol then 
        // TO DO: should we use Denis' formula in the generic Parametrization too?
        return ds_param(C,p);
    elif IsConic(C) then
        return ConicParametrization(C,p,Curve(ProjectiveSpace(K, 1)));
    elif IsPlaneCurve(C) and IsOrdinaryProjective(C) then
	boo,_,Iadj := HasOnlyOrdinarySingularities(C);
        if boo then
	  require IsNonsingular(C,p):
		"The given point should be a NON-SINGULAR point on the curve";
	  return ParametrizeOrdinaryCurve(C,p,Iadj);
        end if;  
    end if;  
    p := Places(p);
    require #p eq 1 and Degree(p[1]) eq 1 : "Point must determine a unique place of degree 1";
    return Parametrization(C, p[1], Curve(ProjectiveSpace(K, 1)));
end intrinsic;

intrinsic Parametrization(C::Crv, p::PlcCrvElt) -> MapSch
    {"} // "
    K := BaseRing(C); 
    require IsField(K): "Base ring of argument 1 must be a field.";
    require Type(C) in {CrvCon,CrvRat} or Genus(C) eq 0: "Argument 1 must be of genus 0.";
    require IsCoercible(Places(C),p) and Degree(Places(C)!p) eq 1:
        "Argument 2 must be a place of argument 1 of degree 1.";
    require IsProjective(Ambient(C)):
        "Argument 1 must be projective.";
    return Parametrization(C, p, Curve(ProjectiveSpace(K, 1),[]));
end intrinsic;

intrinsic Parametrization(C::CrvCon, p::Pt, P::Crv) -> MapSch
    {"} // "
    require Gradings(P) eq [[1,1]] : 
	"Argument 3 must be an ordinary projective line.";
    require IsOrdinaryProjective(Ambient(C)):
        "Argument 1 must have ordinary projective ambient space.";
    K := BaseRing(C);
    require IsField(K): "Base ring of argument 1 must be a field.";
    require BaseRing(P) cmpeq K : 
	"Argument 3 should have same base ring as argument 1";
    require IsCoercible(C,p):
        "Argument 2 must be a point of argument 1 over its base ring.";

    return ConicParametrization(C,p,P);
end intrinsic;

intrinsic Parametrization(C::CrvRat, p::Pt, P::Crv) -> MapSch
{"} // "
    require Gradings(P) eq [[1,1]] : 
	"Argument 3 must be an ordinary projective line.";
    require IsOrdinaryProjective(Ambient(C)):
        "Argument 1 must have ordinary projective ambient space.";
    K := BaseRing(C);
    require IsField(K): "Base ring of argument 1 must be a field.";
    require BaseRing(P) cmpeq K : 
	"Argument 3 should have same base ring as argument 1";
    require IsCoercible(C,p):
        "Argument 2 must be a point of argument 1 over its base ring.";

    return LineParametrization(C,p,P);
end intrinsic;

intrinsic Parametrization(C::CrvCon, p::PlcCrvElt, P::Crv) -> MapSch
{"} // "
    require Gradings(P) eq [[1,1]] : 
	"Argument 3 must be an ordinary projective line.";
    require IsOrdinaryProjective(Ambient(C)):
        "Argument 1 must have ordinary projective ambient space.";
    K := BaseRing(C);
    require IsField(K): "Base ring of argument 1 must be a field.";
    require BaseRing(P) cmpeq K : 
	"Argument 3 should have same base ring as argument 1";
    bool, p := IsCoercible(Places(C),p);
    require bool and Degree(p) eq 1 :
        "Argument 2 must be a place on argument 1 of degree 1.";
    return Parametrization(C, RepresentativePoint(p), P);
end intrinsic;

intrinsic Parametrization(C::CrvRat, p::PlcCrvElt, P::Crv) -> MapSch
{"} // "
    require Gradings(P) eq [[1,1]] : 
	"Argument 3 must be an ordinary projective line.";
    require IsOrdinaryProjective(Ambient(C)):
        "Argument 1 must have ordinary projective ambient space.";
    K := BaseRing(C);
    require IsField(K): "Base ring of argument 1 must be a field.";
    require BaseRing(P) cmpeq K : 
	"Argument 3 should have same base ring as argument 1";
    bool, p := IsCoercible(Places(C),p);
    require bool and Degree(p) eq 1 :
        "Argument 2 must be a place on argument 1 of degree 1.";
    return Parametrization(C, RepresentativePoint(p), P);
end intrinsic;

intrinsic Parametrization(C::Crv, p::Pt, P::Crv) -> MapSch
{"} // "
    require p in C :
        "The given point should lie on the curve";
    require IsNonsingular(C,p) :
	"The given point should be a NON-SINGULAR point on the curve";
    return Parametrization(C, Place(p), P);
end intrinsic;

intrinsic Parametrization(C::Crv, p::PlcCrvElt, P::Crv) -> MapSch
{"} // "
    require Gradings(P) eq [[1,1]] : 
	"Argument 3 must be an ordinary projective line.";
    require IsProjective(Ambient(C)):
        "Argument 1 must be projective.";
    K := BaseRing(C);
    require IsField(K): "Base ring of argument 1 must be a field.";
    require Genus(C) eq 0: "Argument 1 must be of genus 0.";
    require BaseRing(P) cmpeq K : 
	"Argument 3 should have same base ring as argument 1";
    bool, p := IsCoercible(Places(C),p);
    require bool and Degree(p) eq 1 :
        "Argument 2 must be a place on argument 1 of degree 1.";

    /* check for special cases */
    if IsRationalCurve(C) then
	return LineParametrization(C,RepresentativePoint(p),P);
    elif IsConic(C) then
        return ConicParametrization(C,RepresentativePoint(p),P);
    elif IsPlaneCurve(C) then 
 	return PlaneParametrization(C,p,P);
    end if;

    F := FunctionField(C);
    _,m := AlgorithmicFunctionField(F);
    D := Divisor(p);
    x :=  Representative( [ b : b in Basis(D) | not IsConstant(m(b)) ] );

    toP := map<C->P|[x,1]>;
    Ca := AffinePatch(C,NonEmptyPatchIndex(C));
    eqs := [Pushforward(toP,F!(Ca.i)) : i in [1..Length(Ca)]];
    toC := Expand(map<P->Ca|eqs> * 
		Restriction(ProjectiveClosureMap(Ambient(Ca)),Ca,C) );
    return map<P->C | DefiningEquations(toC),DefiningEquations(toP) :
                              CheckInverse := false>;
end intrinsic;

intrinsic Parametrization(C::CrvCon) -> MapSch
{Parametrization of the conic curve C, returned as a map from the projective line to C}
    K := BaseRing(C);
    require Type(K) in {RngInt,FldRat,FldFunRat} or ISA(Type(K), FldAlg) :
        "The conic must be defined over the integers, the rationals, " *
        "a number field or a rational function field";
    require IsOrdinaryProjective(Ambient(C)):
        "The conic must be in an ordinary projective space.";
    return Parametrization(C, Curve(ProjectiveSpace(K,1),[]));
end intrinsic;

intrinsic Parametrization(C::CrvCon, P::Crv) -> MapSch
{Parametrization of the conic curve C, returned as a map from the given projective line P to C}
    K := BaseRing(C);
    require Type(K) in {RngInt,FldRat,FldFunRat} or ISA(Type(K), FldAlg) :
        "The conic must be defined over the integers, the rationals, " *
        "a number field or a rational function field";
    require IsOrdinaryProjective(Ambient(C)):
        "The conic must be in an ordinary projective space.";
    require BaseRing(P) cmpeq K : "Base rings of arguments must be equal.";
    require Gradings(P) eq [[1,1]] : 
	"The second argument must be an ordinary projective line.";

    if Type(K) in {RngInt,FldRat} then
      PX2 := [ P.1^2, P.1*P.2, P.2^2 ]; // 2-uple embedding of P1
      M := ParametrizationMatrix(C);    // variable change for 2-uple image   
      if Type(K) eq RngInt then M:=ChangeRing(M,Integers()); end if;
      eqns0 := [ &+[ M[i,j]*PX2[i] : i in [1..3] ] : j in [1..3] ];
      N := Adjoint(M);                  // inverse variable change
      eqns1 := [ &+[ N[i,j]*Ambient(C).i : i in [1..3] ] : j in [1..3] ];
      return iso< P -> C | [ eqns0 ],
             [ eqns1[[1,2] ], eqns1[[2,3]] ] : CheckInverse := false >;
    else 
       haspt, pt := HasPoint(C);
       require haspt : "The conic does not have a rational point over its base field";
       return Parametrization(C,pt,P);
    end if;
end intrinsic;


