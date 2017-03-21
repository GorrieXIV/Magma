freeze;

/****************************************************************************
funcoord.m

Oct 2002, Nils Bruin

glue for coordinate rings & function fields.

Interface:

IntegralSplit(f,X):
Given f in FunctionField(X), returns num,den, where num,den in
CoordinateRing(X) and f = num/den.

Numerator(f,X):
First value of IntegralSplit.

Denominator(f,X):
Second value of IntegralSplit.

RationalFunction(X, num, den):
Given num,den in CoordinateRing(X), returns num/den in FunctionField(X).

Restriction(f, X, Y):
Given f in FunctionField(X), returns the restriction of f to Y (subsscheme of
X) as an element of FunctionField(Y). If f has a pole along Y, then Infty() is
returned. It is an error if f is not defined on Y.

ProjectiveMap(L::[FldElt], Y::Prj)->MapSch
Gives the projective map X->Y defined by the functions in L.

IsInvertible(phi::MapSch)->BoolElt,MapSch
Tests if a birational inverse exists using a groebner basis computation.
If so, returns the inverse (with phi installed as its inverse).

GenericPoint(X::Sch)->Pt
Returns a point on X over its function field, with coordinates generating the
function field. This points acts as a generic point of X over the base ring of
X. Obviously, X must have a function field.

// mch (12/04)
RestrictionToPatch(f::FldFunFracSchElt,Xi::Sch)-> FldFracElt
Takes an element f of the FunctionField of X and returns a representative
of f on the ith affine patch of X (in the field of fraction of the coordinate 
ring of the ambient of the patch)

****************************************************************************/
import "../Arith/loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate;

// mch (17/12/04) added non-empty patch attribute - hopefully this
//  can replace functionfieldpatch in most cases - also added
// accesor function
// NS (3/2/05) removed unused attribute

declare attributes Sch:nonemptypatch;

function NonEmptyPatchIndex(X)
  // Finds a non-empty affine patch on the scheme (if one exists)
  //  of the same dimension as X.
  // If X non-empty, there is still the current problem in
  //  weighted projective space where not all affine patchs are
  //  implemented. If there is no-such patch, 0 is returned.
  // In many cases, this could replace the use of functionfieldpatch
  //  with the new coercions allowed between rational functions on
  //  the different patches with new function field machinery.

  if not(assigned X`nonemptypatch) then
    error if not(IsProjective(X)),
      "Only defined for projective schemes";

    if HasFunctionField(X) then
        /* for curves want the function field patch if defined.
	   NB: this may be different from the 1st non-empty patch ! */
	F := FunctionField(X);
	pi := FFPatchIndex(X);
	if pi gt 0 then return pi; end if;
	for i in [1 .. NumberOfAffinePatches(X)] do
	    if Integers(F) eq CoordinateRing(AffinePatch(X, i)) then
		X`nonemptypatch := i;
		return i;
	    end if;
	end for;
    end if;

    if IsEmpty(X) then
      X`nonemptypatch:=0;
      return X`nonemptypatch;
    end if;

    // look for fiddly weighted projective case
    booWgt := false;
    if NGrad(Ambient(X)) eq 1 then
       wgts := Reverse(Gradings(X)[1]);
       booWgt := &or[wgt ne 1 : wgt in wgts];
    end if;
    if ISA(Type(X),Prj) then
      if booWgt then
         X`nonemptypatch:=Index(wgts,1);
      else
         X`nonemptypatch:=1;
      end if;
    else
      for i in [1..NumberOfAffinePatches(X)] do
         if booWgt and (wgts[i] ne 1) then continue; end if;
          A:=AffinePatch(X,i);
          if Dimension(A) eq Dimension(X) then
            X`nonemptypatch:=i; break;
          end if;
      end for;
      if not(assigned X`nonemptypatch) then // weighted prj problem!
       X`nonemptypatch:=0;
      end if;
    end if;
  end if;
  return X`nonemptypatch;
end function;

intrinsic MyEval(f::.,x::[RngElt])->RngElt
  {Evaluate a multivariate polynomial or a multivariate function field element
   in a point, represented by a sequence of values}
  if ISA(Type(f),RngMPolElt) then
    return Evaluate(f,x);
  elif ISA(Type(f),FldFunRatMElt) then
    return Evaluate(Numerator(f),x)/Evaluate(Denominator(f),x);
  end if;
end intrinsic;

intrinsic RestrictionToPatch(f::FldFunFracSchElt,Xi::Sch) -> FldFracElt
{Takes an element f of the FunctionField of X and returns a representative
of f on Xi, the ith affine patch of X (in the field of fractions of the 
coordinate ring of the ambient of the patch)}
    X := Scheme(Parent(f));
    require IsAffine(Xi) and ProjectiveClosure(Xi) eq X : 
		"Argument 2 is not a patch of the scheme of argument 1";

  fp := ProjectiveFunction(f);
  m := Inverse(ProjectiveClosureMap(Ambient(Xi)));
  fpn := Numerator(fp);
  fpd := Denominator(fp);
  return FieldOfFractions(CoordinateRing(Ambient(Xi)))!(m(fpn)/m(fpd));
  
end intrinsic;   

intrinsic Degrees(X::Sch, f::RngMPolElt)->SeqEnum
  {Return the degrees of f with respect to the gradings of X. f is required to
   be homogeneous with respect to all gradings of X}
  require IsHomogeneous(X,f):
    "f must be homogeneous with respect to all gradings of X";
  L:=Monomials(f);
  if #L eq 0 then
    return [0:i in Gradings(X)];
  else
    e:=Exponents(L[1]);
    return [&+[e[i]*g[i]:i in [1..#e]]: g in Gradings(X)];
  end if;
end intrinsic;

//what type for a function field element??
  
intrinsic IntegralSplit(f::FldFunFracSchElt, X::Sch)->RngMPolElt,RngMPolElt
  {Returns num and den in the coordinate ring of Ambient(X)
   that represent f as num/den on X}
   
/*
"HERE f:", f;
"HERE P f:", Parent(f);
"HERE FF:", FunctionField(X);
*/

  require f in FunctionField(X) : "Argument 1 must be a function on argument 2";

  f := ProjectiveFunction(f);
  num := Numerator(f);
  den := Denominator(f);

  if IsProjective(X) then
    return CR!num, CR!den where CR is CoordinateRing(Ambient(X));
  end if;

  m := Inverse(ProjectiveClosureMap(Ambient(X)));

  return m(num), m(den);

end intrinsic;

intrinsic Numerator(f::FldFunFracSchElt,X::Sch)->RngMPolElt
  {Returns the first argument of IntegralSplit}
  return num where num:=IntegralSplit(f,X);
end intrinsic;

intrinsic Denominator(f::FldFunFracSchElt,X::Sch)->RngMPolElt
  {Returns the first argument of IntegralSplit}
  return den where _,den:=IntegralSplit(f,X);
end intrinsic;

intrinsic Restriction(f::FldFunFracSchElt, Y::Sch)->FldFunFracSchElt
  {Given a function f in the function field of X, returns the restriction of f
   to Y as an element of the function field of Y. If f has a pole along Y, then
   Infty() is returned. It is an error if f is not defined along Y.}
  
  X := Scheme(Parent(f));
  require Y subset X: "Argument 2 must be a subscheme of the scheme argument 1 is a function on";
  require HasFunctionField(Y) : "Argument 2 must have a function field";

  assert Ambient(X) eq Ambient(Y);
  is_c, f := IsCoercible(FunctionField(Ambient(Y)), f);
  assert is_c;

  is_c, g := IsCoercible(FunctionField(Y), f);
  if is_c then
    return g;
  end if;

  den := FunctionField(Y)!Denominator(f);
  num := FunctionField(Y)!Numerator(f);
  assert den eq 0;
  require num ne 0 : "Argument 1 is not defined on argument 2";
  return Infinity();
	
end intrinsic;

intrinsic ProjectiveMap(L::[FldFunFracSchElt], Y::Prj)->MapSch
  {Returns the projective map defined by the functions in L}
  X := Scheme(Universe(L));
  assert IsProjective(X);
  require Dimension(Y) eq #L-1:
    "Argument 3 must be a projective space of dimension 1 less than the length of argument 1.";

  R:=CoordinateRing(X);
  RA:=CoordinateRing(Ambient(X));
  fs:=[num/den where num:=RA!num
               where den:=RA!den
               where num,den:=IntegralSplit(f,X):f in L];
  if ISA(Type(Universe(fs)),FldFunRat) then
    D:=LCM([Denominator(f): f in fs]);
    fs:=[RA!(f*D): f in fs];
  end if;
  return map<X->Y|fs>;  
end intrinsic;

intrinsic ProjectiveMap(L::[FldFunFracSchElt])->MapSch
  {Returns the projective map X->Y defined by the functions in L}
  X := Scheme(Universe(L));
  assert IsProjective(X);
  return ProjectiveMap(L,ProjectiveSpace(BaseRing(X),#L-1));
end intrinsic;

intrinsic ProjectiveMap(f::FldFunFracSchElt, Y::Prj)->MapSch
  {Returns the projective map X->Y defined by f}
  X := Scheme(Parent(f));
  assert IsProjective(X);
  require Type(Y) eq Prj and Dimension(Y) eq 1:
    "Argument 2 must be a projective space of dimension 1 less than the length of argument 1.";
  return ProjectiveMap([f,1],Y);
end intrinsic;

intrinsic ProjectiveMap(f::FldFunFracSchElt)->MapSch
  {Returns the projective map defined by f}
  X := Scheme(Parent(f));
  assert IsProjective(X);
  return ProjectiveMap([f,1],ProjectiveSpace(BaseRing(X),1));
end intrinsic;

/*
function MyEval(f,v)
  if Type(f) eq FldFunRatMElt then
    return Evaluate(Numerator(f),v)/Evaluate(Denominator(f),v);
  else
    return Evaluate(f,v);
  end if;
end function;
*/

intrinsic GenericPoint(X::Sch  : NoFunctionField:=false,
                                 UseAlgorithmicFunctionField:=false) -> Pt
  {Returns a generic point on X, i.e., a point over the function field of X
  if a function field is available. Otherwise, an affine coordinate ring of X is
  chosen such that the intersection of X with the infinite hyperplane is of
  strictly lower dimension than X (if X is equidimensional, this means none of
  the components lie at infinity). A point is returned in an appropriate affine
  algebra over a multivariate rational function field. If NoFunctionField is
  supplied then the latter strategy is followed even for curves and ambient
  spaces.}
  if not(NoFunctionField) and HasFunctionField(X) then
    if IsProjective(X) then
      Xp:=AffinePatch(X,NonEmptyPatchIndex(X));
    else
      Xp:=X;
    end if;
    K:=FunctionField(Xp);
    Pseq := [K!(A.i) : i in [1 .. Dimension(A)]]
				where A is Ambient(Xp);
    if UseAlgorithmicFunctionField then
      K, mK := AlgorithmicFunctionField(K);
      Pseq := [K| x@mK : x in Pseq];
    end if;
    if IsProjective(X) then
      Pseq := [Evaluate(f,Pseq) : f in DefiningPolynomials(
			ProjectiveClosureMap(Ambient(Xp))) ];
    end if;
    return X(K)!Pseq;
  else
    if IsAffine(X) then
      I:=Ideal(X);
      d,vr:=Dimension(I);
      if d eq 0 then
        A,toA:=quo<Generic(I)|I>;
      elif IsZero(I) then
        E:=FieldOfFractions(Generic(I));
        toE:=Coercion(Generic(I),E);
        A:=E; toA:=Coercion(E,A);
      else
        E,toE:=Extension(I,vr);
        A,toA:=quo<Generic(E)|E>;
      end if;
      return X(A)![toA(toE(X.i)): i in [1..Rank(CoordinateRing(X))]];
    else
      require #Gradings(X) eq 1:
       "Domain is only allowed to have 1 grading.";
      require exists(Xa){AffinePatch(X,i): i in [1..Length(X)]|
         Gradings(X)[1][i] eq 1 and Dimension(AffinePatch(X,i)) eq Dimension(X)}:
           "None of the standard patches seems to work for X";
      XaPC:=map<Xa->X|DefiningPolynomials(f),InverseDefiningPolynomials(f)>
         where f:=ProjectiveClosureMap(Ambient(Xa));
      return XaPC(GenericPoint(Xa:NoFunctionField:=NoFunctionField));
    end if;
  end if;
end intrinsic;

function CrossProduct(a,b)
  return [a[2]*b[3]-a[3]*b[2],a[3]*b[1]-a[1]*b[3],a[1]*b[2]-a[2]*b[1]];
end function;

intrinsic FormalPoint(P::Pt)->Pt
  {Returns a power series expansion around the given point}
  C:=Scheme(P);
  require IsCurve(C) and IsProjective(C) and IsNonsingular(P):
    "Only implemented for smooth points on projective curves";
  R:=BaseRing(C);
  P2:=Ambient(C);
  tP:=DefiningEquation(TangentLine(P));
  NP:=[MonomialCoefficient(tP,P2.i):i in [1,2,3]];

  _,V,W:=Explode(ExtendBasis([v],Parent(v))) where v:=Vector(Eltseq(P));
  if &+[V[i]*NP[i]:i in [1,2,3]] eq 0 then
    V,W:=Explode([W,V]);
  end if;

  assert &+[V[i]*NP[i]:i in [1,2,3]] ne 0;

  Rtt:=LaurentSeriesRing(R);
  RttY:=PolynomialRing(Rtt);
  Ptt:=[P[i]+Rtt.1*W[i]+RttY.1*V[i]:i in [1,2,3]];
  rt:=Roots(Evaluate(DefiningEquation(C),Ptt));
  rt:=[r:r in rt| Valuation(r[1]) gt 0];
  assert #rt eq 1 and rt[1][2] eq 1;
  return C(Rtt)![P[i]+Rtt.1*W[i]+rt[1][1]*V[i]:i in [1,2,3]];
end intrinsic;

intrinsic EvaluateByPowerSeries(mp::MapSch,P::Pt)->Pt
  {Uses power series expansion around a point P to evaluate mp at P if P is in
  the base scheme of mp}
  P2:=Ambient(Domain(mp));
  deqs:=DefiningEquations(BaseScheme(mp));
  if P in BaseScheme(mp) then
    D:=Codomain(mp(RingMap(Parent(P))));
    mpfp:=Eltseq(mp(FormalPoint(P)));
    pi:=UniformizingElement(Universe(mpfp));
    v:=MinValuation(mpfp);
    mpfp:=[t*pi^(-v):t in mpfp];
    return D![Evaluate(g,0): g in mpfp];
  else
    return mp(P);
  end if;
end intrinsic;
    
intrinsic UniformizingElement(R::RngSerLaur)->RngSerLaurElt
  {Uniformizing element}
  return R.1;
end intrinsic;

intrinsic UniformizingElement(R::RngSerPow)->RngSerPowElt
  {Uniformizing element}
  return R.1;
end intrinsic;
