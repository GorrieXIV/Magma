freeze;

/****************************************************************************
locsol.m

November 2002, Nils Bruin

Several routines to test local solubility and to work with points over local
fields.

intrinsic IsEmpty(Xm::SetPt:Smooth:=false)->BoolElt,Pt

Tests local solubility. Hyperelliptic curves are handled by their own code. For
general schemes, the routine descends in the filtration of singular loci to find
points. For curves one can specify the optional parameter "Smooth" to test if
there are any smooth points on the curve. This question is equivalent to asking
whether the desingularisation of the curve has any points and to asking if there
is an infinite number of points on the curve.

Internal functions:

HyperellipticHasPoint(F)

F is a bivariate homogeneous form of even degree over a complete local ring.
Decides local solubility of associated hyperelliptic y^2=F(x,z) quickly. Must be
in odd residue characteristic and the residue field must be big enough.

HasSquareIntegralValues(F)

Takes a univariate polynomial F. Tests (in a slow way) for solubility of
y^2=F(x), for integral x,y in the complete local ring over which F is defined.

HasSquareValue(F)

Takes a polynomial F over a complete local field and tests if the hyperelliptic
curve y^2=F(x) has any solutions. It calls HyperellipticHasPoint or
HasSquareIntegralValues, depending on applicability.

HasIntegralPoints(L,d)

Tests if the equations in L (over a complete local ring) have a integral
solution smooth of dimension d. Singular points may cause infinite loops.

HasLocalPoints(X,m)

Takes a scheme and a base change map m to a complete local field. Decides if X
is locally soluble. The routine recurses into components unless
AssumeIrreducible is supplied (in which case the whole variety is assumed to be
equidimensional) The routine recurses into the singular locus first, unless
AssumeNonsingular is supplied. If components have locally rational singular
points, one may get into an infinite loop.

HasSmoothIntegralPoints(F,Sing)

F is a bivariate polynomial over a local ring. Sing is a set of coordinate pairs
describing singular points of F. This function tests F for integral points,
blowing up the singularities.

QuadHasPoint(Q,T)

takes two homogeneous quadric forms in 4 variables. Q must be only in the first
3 variables; T should have only the square of the first variable in it. Their
base ring should be a complete local field. This routine first tests Q for local
solubility. If it is soluble, parametrizes and substitutes in T and then tests T
for local solubility.

intrinsic IsEmpty(Xm::SetPt:Smooth:=false)->BoolElt,Pt

Makes a smart choice to test local solubility of the scheme X over the field of
the given point set (the parameter "Smooth" applies to curves. If given,
singularities are blown up rather than returned as rational points)

******************************************************************************/

declare verbose LocSol,2;

import "sqfroots.m":IntegralSquarefreeRoots;
import "loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate, 
       CoefficientByExponentVector;
import "pointlift.m": Hensel;

intrinsic BaseChangedDefiningEquations(X::Sch,m::Map)->SeqEnum
  {Returns defining equations wrt given base change map}
  R:=CoordinateRing(Ambient(X));
  mR:=PolynomialRing(Codomain(m),Rank(R));
  RtomR:=hom<R->mR|m*Bang(Codomain(m),mR),[mR.i:i in [1..Rank(R)]]>;
  return [RtomR(f):f in DefiningEquations(X)];
end intrinsic;


/////////////////////////////////////////////////////////////////////////////
// Rational points of a cluster over a p-adic field.

function scale(f)
    if f eq 0 then
	return f, 0;
    end if;

    x := Min([Valuation(x) : x in Coefficients(f)]);
    return f * UniformizingElement(CoefficientRing(Parent(f)))^-x, x;
end function;

function min_prec(f)
    if f eq 0 then
	return 10000;
    end if;

    return Min([AbsolutePrecision(x) : x in Coefficients(f)]);
end function;

function resultant(f, g, n)
    F := CoefficientRing(Parent(f));
    if ISA(Type(F), FldPad) then
	R := RingOfIntegers(F);
    else
	R := F;
    end if;
    
    f2, fx := scale(f);
    g2, gx := scale(g);

    prec := Min(min_prec(f2), min_prec(g2));

    Q := quo<R | UniformizingElement(R)^prec>;
    P := PolynomialRing(Q, Rank(Parent(f)));
    f3 := P ! f2;
    g3 := P ! g2;

    c := UniformizingElement(F)^(fx * Degree(g, n) + gx * Degree(f, n));
    return (Parent(f) ! Resultant(f3, g3, n)) * c;
end function;

function iszero(f)
  return TotalDegree(f) lt 1 and forall{c:c in Coefficients(f)|
           RelativePrecision(c) eq 0};
end function;

function IntegralSolutions(L,d)
  vprint LocSol,2:"Entering IntegralSolutions with d = ",d;
  L:=[ls: l in L | ls ne 0 where ls:=StripPrecisionlessTerms(l)];
  R:=Universe(L);
  r:=Rank(R);
  K:=BaseRing(R);
  x:=PolynomialRing(K).1;
  assert forall{l: l in L| forall{i: i in [d+1..r] | Degree(l,i) eq 0}};
  if d eq 1 then
    rts:= {rt[1]: rt in Roots(Evaluate(L[1],[x] cat [0: i in [2..r]]))
                                               | Valuation(rt[1]) ge 0};
    for l in L[2..#L] do
      rts:={rt: rt in rts |
        RelativePrecision(Evaluate(l,[rt] cat [0: i in [2..r]])) eq 0};
    end for;
    return {[r]:r in rts};
  else
    Lrs:=[R: l,m in L | l ne m and R ne 0 where
                R:=StripPrecisionlessTerms(resultant(l,m,d))];
    Vrs:=IntegralSolutions(Lrs,d-1);
    vprint LocSol,2:"Integral solutions of recursive step:",Vrs;
    R:={};
    for v in Vrs do
      Lsbs:=[f: l in L| f ne 0 where
                f:=StripPrecisionlessTerms(
                   Evaluate(l,v cat [x] cat [0: i in [d+1..r]]))];
      rts:={rt[1] : rt in Roots(Lsbs[1]) | Valuation(rt[1]) ge 0};
      for l in Lsbs[2..#Lsbs] do
        rts:={rt: rt in rts | RelativePrecision(Evaluate(l, rt)) eq 0};
      end for;
      R join:={v cat [rt]: rt in rts};
    end for;
    return R;
  end if;
end function;

function AllIntegralPoints(L,prec)
  //takes a list of polynomials L and an assumed dimension 0
  //finds all integral points and tries to lift them to precision prec
  //integral points. (assumes no rational singular points exist!)
  //returns a set of sequences.

  //some quantities that don't change during the computations.
  Rpol:=Universe(L);
  R:=BaseRing(Rpol);
  error if not ISA(Type(R),RngPad), "must have polynomials over local ring";
  u:=UniformizingElement(R);
  n:=Rank(Rpol);
  cd:=n;
  k,Rtok:=ResidueClassField(R);
  Ak:=AffineSpace(k,n);
  kpol:=CoordinateRing(Ak);
  Rpoltokpol:=hom<Rpol->kpol|[kpol.i:i in [1..n]]>;

  //the hard (recursive) work.
  test:=function(L,lvl)
    vprint LocSol,2: "Entering test level ",lvl;
    vprint LocSol,2: "Passed argument:",L;
    L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
    vprint LocSol,2: "Primmed and stripped:",L;
    error if #L lt cd,
      "Variety appears to have too high dimension. Precision loss?";
    Lk:=[Rpoltokpol(P):P in L];
    Lkschm:=Scheme(Ak,Lk);
    J:=JacobianMatrix(Lk);
    kpoints:=RationalPoints(Lkschm);
    vprint LocSol,2: "Points on reduction:",kpoints;
    result:={};
    for p in kpoints do
      Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
      E,T:=EchelonForm(Jp);
      rk:=Rank(E);
      error if rk gt cd, "Jacobian has too large a rank. d wrong?";
      if rk eq cd then
        vprint LocSol,2: "Found ",p,". This point will lift.";
        plift:=Hensel(L,0,[c@@Rtok+O(u):c in Eltseq(p)],prec-lvl:
                  Strict:=false);
        if exists(l){l:l in L| RelativePrecision(Evaluate(l,plift)) ne 0} then
          vprint LocSol,2:
            "After lifting, one equation does not vanish at point.",
            "Value",Evaluate(l,plift),"Disregarding point";
        else
          result join:={plift};
        end if;
      else
        vprint LocSol,2: "Looking around ",p,"...";
        plift:=[p[i]@@Rtok+u*Rpol.i:i in [1..n]];
        L2:=[MyPrimitivePart(Evaluate(f,plift)):f in L];
        repeat
          B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                             [j eq i select 1 else 0:j in [1..n]])):
                                 i in [1..Rank(Rpol)]]:f in L2]);
          E,T:=EchelonForm(B);
          vprint LocSol,2:"Changing the basis of the ideal by:",T;
          TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
          L2:=Eltseq(Vector(L2)*Transpose(TT));
          flag:=false;
          vprint LocSol,2:"to",L2;
          for i in [1..#L2] do
            v:=MinValuation(L2[i]);
            if v gt 0 then
              L2[i]:=ShiftVal(L2[i],-v);
              vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
              flag:=true;
            end if;
          end for;
        until not(flag); 
        vprint LocSol,2:"Newly obtained basis is:",L2;

        IndentPush();
        newresult:=$$(L2,lvl+1);
        IndentPop();
        if #newresult gt 0 then
          vprint LocSol,2: "Found points. We tranform them back and add them.";
          vprint LocSol,2: "Leaving test level ",lvl;
          result join:={[Evaluate(c,pt):c in plift]:pt in newresult};
        end if;
      end if;
    end for;
    vprint LocSol,2: "Leaving test level ",lvl;
    return result;
  end function;
  
  return test(L,1);
end function;

intrinsic MyRationalPoints(V::SetPt:AssumeReduced:=false)->SetEnum
  {For internal use only}
  S:=Scheme(V);
  mp:=RingMap(V);
  if Dimension(S) eq -1 then
    return {V|};
  end if;
  require Dimension(S) eq 0: "Only implemented for 0 dimensional schemes";
  require ISA(Type(Codomain(mp)),FldPad):
    "Pointset must take values in a padic field";
  require IsProjective(S): "Only implemented for projective schemes";

  if AssumeReduced then
    vprint LocSol: "Assuming the scheme is reduced";
    L:=BaseChangedDefiningEquations(S,mp);
  else
    vprint LocSol: "Reducing the scheme";
    L:=BaseChangedDefiningEquations(ReducedSubscheme(S),mp);
  end if;
  R:=Universe(L);
  pi:=UniformizingElement(IntegerRing(Codomain(mp)));
  A:=PolynomialRing(Parent(pi),Dimension(Ambient(S)));
  result:={V|};
  for t in [Rank(R)..1 by -1] do
    w:=[A.i: i in [1..t-1]] cat [1] cat [pi*A.(i-1): i in [t+1..Rank(R)]];
    vprint LocSol,2:"Looking on patch",w;
    affmp:=hom<R->A|
             Coercion(Codomain(mp),Parent(pi))*
             Coercion(Parent(pi),A),w>;
    Laff:=[affmp(ShiftVal(l,-MinValuation(l))):l in L];
    IndentPush();
    affpts:=AllIntegralPoints(Laff,Codomain(mp)`DefaultPrecision);
    IndentPop();
    vprint LocSol,2:"Found points",affpts;
    affpts2:=[[Evaluate(crd,a):crd in w]: a in affpts];
    vprint LocSol,2:"In coordinates",affpts2;
    vprint LocSol,2:"Equations:",[[Evaluate(l,a):l in L]:a in affpts2];
    result join:={V![Codomain(mp)|Evaluate(crd,a):crd in w]: a in affpts};
  end for;
  return result;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
// Local solubility tester

//First the hyperelliptic tester ...

//fast hyperelliptic solubility tester. Residue field must be large enough.

function HyperellipticHasPoint(F)
  //fast tester for local solubility of y^2=F(x,z).
  //F must be a square free bivariate homogeneous form over a local ring R.
  //The residue class field k of R must be of odd characteristic and
  //#k must be big enough to have
  //#k+1-(TotalDegree(F)-2)*Sqrt(#k) gt 0.
  //(i.e., such that if F has good reduction, the Weil bound guarantees
  //a point on the curve)
  R:=BaseRing(Parent(F));
  X:=Parent(F).1;
  Z:=Parent(F).2;
  pi:=UniformizingElement(R);
  k,Rtok:=ResidueClassField(R);
  kXZ<Xk,Zk>:=PolynomialRing(k,2);
  tokXZ:=hom<Parent(F)->kXZ|[kXZ.1,kXZ.2]>;
  assert IsHomogeneous(F) and TotalDegree(F) mod 2 eq 0;
  assert Characteristic(k) ne 2 and #k+1-(TotalDegree(F)-2)*Sqrt(#k) gt 0;
  vprint LocSol,2:"Using fast method";
  work:=function(F)
    // This one's strict. It doesn't want Valuation(Z) > 0.
    v:=MinValuation(F) div 2;
    F:=ShiftVal(F,-2*v);
    vprint LocSol,2:"Considering:",F;
    error if MinPrec(F) lt 1, "Lost precision";
    f:=tokXZ(F);
    if f eq 0 then
      vprint LocSol,2:
        "Polynomial generically has odd valuation. Recurse into finite roots.";
      //in this case, F=pi*G where G is ne 0 mod pi, so in order for
      //F to have a square value, G(X,Z)=0 mod pi.
      G:=ShiftVal(F,-1);
      error if MinPrec(G) lt 1, "Lost precision";
      L:=Factorisation(tokXZ(G));
      for g in [g[1]: g in L | TotalDegree(g[1]) eq 1] do
        x0:=Coefficient(g,Zk,1)@@Rtok; z0:=-Coefficient(g,Xk,1)@@Rtok;
        if RelativePrecision(z0) ne 0 then
          vprint LocSol,2:"Taking root [x,z] =",[x0,z0];
          sbs:=[x0*Z+pi*z0*X,z0*Z];
          IndentPush();
          bl,pt:=$$(Evaluate(F,sbs));
          IndentPop();
          if bl then
            pt:=[Evaluate(sbs[1],[pt[1],pt[3]]),
                    // Bug fix: this was the wrong v!   -- Steve
                    // pi^v*pt[2],  
                    pi^vv*pt[2] where vv:=MinValuation(F),
                    Evaluate(sbs[2],[pt[1],pt[3]])];
            vprint LocSol,2:
              "Found point:",pt,"F(pt):",Evaluate(F,[pt[1],pt[3]])-pt[2]^2;
            return true,pt;
          end if;
        end if;
      end for;
      vprint LocSol,2: "No point.";
      return false,_;
    end if;
    L:=Factorisation(f);
    //first roots of f with multiplicity one. They're smooth ...
    if exists(g){g[1]:g in L| TotalDegree(g[1]) eq 1 and g[2] eq 1 and
      Coefficient(g[1],Xk,1) ne 0} then
      vprint LocSol,2:
        "Polynomial has root of multiplicity 1 in reduction. This gives a point";
      if Coefficient(g,Zk,1) eq 0 then
        vprint LocSol,2:"Found point:",[0+O(pi),0+O(pi),1+O(pi)];
        return true,[0+O(pi),0+O(pi),1+O(pi)];
      elif Coefficient(g,Xk,1) eq 0 then
        vprint LocSol,2:"Found point:",[1+O(pi),0+O(pi),0+O(pi)];
        return true,[1+O(pi),0+O(pi),0+O(pi)];
      else
        pt:=[ Coefficient(g,Zk,1)@@Rtok+O(pi),
                     0+O(pi),
                    -Coefficient(g,Xk,1)@@Rtok+O(pi)];
        return true, pt;
      end if;
    end if;
    h:=&*[h[1]^(h[2] div 2):h in L];
    g:=f/h^2;
    //f = g*h^2 and g is square-free. 
    if TotalDegree(g) gt 0 then
      // y^2=g defines a proper curve with sufficient points to guarantee
      // the existence of one with f(x) ne 0. Such a point will be smooth
      // and thus lift.
      vprint LocSol,2:
        "Polynomial in reduction is not completely a square. There is a point.";
      repeat
        x:=Random(k); z:=Random(k);
        bl,y:=IsSquare(Evaluate(f,[x,z]));
      until bl and y ne 0;
      pt:=[x@@Rtok+O(pi),pi^v*(y@@Rtok+O(pi)),z@@Rtok+O(pi)];
      vprint LocSol,2:"Returning point:",pt,
          "F(pt):",Evaluate(F,[pt[1],pt[3]])-pt[2]^2;
      return true,[x@@Rtok+O(pi),pi^v*(y@@Rtok+O(pi)),z@@Rtok+O(pi)];
    else
      //only case left: f=a*g^2
      bl,y1:=IsSquare(k!g);
      if bl then
        vprint LocSol,2:
          "Polynomial reduces to a square. Any non-root will do.";
        //ok, that's easy. Any [x,y] avoiding the roots of f will lift
        repeat
          x:=Random(k); z:=Random(k);
          y2:=Evaluate(h,[x,z]);
        until y2 ne 0;

        x:=x@@Rtok+O(pi^MinPrec(F));
        z:=z@@Rtok+O(pi^MinPrec(F));
        bl,y:=IsSquare(Evaluate(F,[x,z]));
        assert bl;
        pt:=[x,y,z];
        vprint LocSol,2:"Returning point:",pt,"F(pt):",Evaluate(F,[x,z])-y^2;

        return true,pt;
      else
        //great, so y ne 0 is not gonna work. Therefore, recurse for the
        //roots of f.
        vprint LocSol,2:
          "Polynomial reduces to (non-square scalar)*g^2. Recursing into finite roots.";
        for g in [g[1]: g in L | TotalDegree(g[1]) eq 1] do
          x0:=Coefficient(g,Zk,1)@@Rtok; z0:=-Coefficient(g,Xk,1)@@Rtok;
          if RelativePrecision(z0) ne 0 then
            sbs:=[x0*Z+pi*z0*X,z0*Z];
            vprint LocSol,2:"Taking root [x,z] =",[x0,z0];
            IndentPush();
            bl,pt:=$$(Evaluate(F,sbs));
            IndentPop();
            if bl then
              pt:=[Evaluate(sbs[1],[pt[1],pt[3]]),
                      pi^v*pt[2],
                      Evaluate(sbs[2],[pt[1],pt[3]])];
              vprint LocSol,2: "Found point:",pt,
                   "F(pt):",Evaluate(F,[pt[1],pt[3]])-pt[2]^2;
              return true, pt;
            end if;
          end if;
        end for;
        vprint LocSol,2: "No point.";
        return false,_;
      end if;
    end if;
  end function;
  vprint LocSol,2:"Looking on finite patch of y^2 =",F;
  IndentPush();
  bl,pt:=work(F);
  IndentPop();
  if bl then
    vprint LocSol,2:"Found point:",pt,"F(pt):",Evaluate(F,[pt[1],pt[3]])-pt[2]^2;
    return true,pt;
  end if;
  vprint LocSol,2:"Looking on infinite ,i.e., y^2 =",Evaluate(F,[Z,pi*X]);
  IndentPush();
  bl,pt:=work(Evaluate(F,[Z,pi*X]));
  IndentPop();
  if bl then
    vprint LocSol,2:"Found point. Transformed back:",[pt[3],pt[2],pi*pt[1]];
    vprint LocSol,2:"F(pt):",Evaluate(F,[pt[1],pt[3]])-pt[2]^2;
    return true,[pt[3],pt[2],pi*pt[1]];
  else
    vprint LocSol,2:"Found no point.";
    return false,_;
  end if;
end function;

//This is the slow version (well ... probably pretty fast still for tiny residue
//class fields)

function HasSquareIntegralValues(F : Neighbourhood:=false, NoRoots:=false)

/*Tests for integral solutions to y^2=F(x). The second return value
is an approximation of the x of such a point, if it exists. If the optional
parameter Neighbourhood is given, then only x that match up with Neighbourhood
(given the precision of Neighbourhood) are tried. If the flag NoRoots is
supplied, then F is not tested for having a p-adic root. Since p-adic
factorisation is slow, this saves some time, but may lead to very poor
performance and failure (loss of precision) if there is such a root*/

  // first test if F has integral roots. Then 0^2=F(x) has a solution.
  // in fact, for this test, it's not even important that F is over a
  // local ring. (*SKIPPED IF NoRoots is true*)
  
  vprint LocSol,2:"Looking for integral points taking square values in",F;
  
  if not(NoRoots) then
    rts:=Roots(F);
    if #rts gt 0 then
      vprint LocSol,2:"Found",[rts[1][1],0];
      return true,[rts[1][1],0];
    end if;
  end if;
    
  // now test the conditions 
  
  Op:=BaseRing(F);
  pi:=UniformizingElement(Op);
  error if not ISA(Type(Op),RngPad), "Polynomial needs to be over a local ring";
  if Neighbourhood cmpeq false then
    Neighbourhood:=O(pi^0);
  end if;
  error if not( Parent(Neighbourhood) cmpeq Op),
    "Neighbourhood (if given) must be a member of the local ring";
  resfld,toresfld:=ResidueClassField(Op);
  resfldreps:={ u@@toresfld+O(pi): u in resfld };
 
  if (Prime(Op) ne 2) then
    // this is the test-function for odd primes
    // this function takes an element (an origin) and
    // recursively looks in smaller neigbourhoods around it (while
    // perturbing it within its given precision)
    // to decide if F takes square values somewhere near origin.
    // if true is returned, then the second value gives a certificate
    // (i.e. an x for which F takes square values for all x+d within
    // the given precision of x)
    u:=elt<Op|UniformizingElement(Op),2>;
    test:=function(origin)
    
        // first, if we've really run out of precision, give an error
	
	if (Precision(Op) le Precision(origin)) then
          error "Insufficient precision for decision";
	end if;
	prc:=Precision(origin);

	//increase precision of origin in order to represent pertubations
	origin:=elt<Op|origin,prc+1>;
	vprint LocSol,2:"Looking for point in",origin;
	// loop through pertubations	
	for perturb in resfldreps do
          x:=origin+elt<Op|prc,perturb,prc+1>;
	  y:=Evaluate(F,x);
	  vly:=Valuation(y);
	  if vly ge AbsolutePrecision(y) then
	  
	    // if y is indiscernible from 0 then recurse and look around
	    // current x.
            IndentPush();
	    pred,val:=$$(x);
            IndentPop();
	    if pred then
              vprint LocSol,2:"Found",val;
	      return pred,val;
	    end if;
	  elif ((vly mod 2) eq 0) and IsSquare(resfld!(y/u^vly)) then
	  
	    //otherwise, we can decide by looking at the parity of
	    //the valuation and the squareness of the first digit in the
	    //residue field.
            y:=u^(vly div 2)*(Sqrt(resfld!(y/u^vly))@@toresfld+O(u));
            vprint LocSol,2:"Found",[x,y];
	    return true,[x,y];
	  end if;
	end for;

	//by now, we've tested everything and haven't found any square value
	//therefore, there are none.
        vprint LocSol,2:"Found none.";
	return false,_;
      end function;
  else
  
    // we construct the square units. That is, we take all units with precision
    // Valuation(2)+1 and square them. This gives us precision Valuation(4)+1
    // which is enough precision to tell square units from non-square ones.
    sqr:={
      (&+[pi^(i-1)*(u[i]@@toresfld)+O(pi^(#u)) : i in [1..#u]])^2
      +O(pi^(Valuation(Op!4)+1))  :
           u in Flat(car<{u : u in resfld | u ne 0},
                      CartesianPower(resfld,Valuation(Op!2))>)};
    v4p1:=Valuation(Op!4)+1;
    u:=pi+O(pi^(v4p1+1));
    f:=Eltseq(F);
    test:=function(origin)
    
        // first, if we've really run out of precision, give an error
	// It's not clear how this generalizes to the new locals ...
	//if (Precision(Op) lt AbsolutePrecision(origin)+v4p1) then
        //  error "Insufficient precision for decision";
	//end if;
	prc:=AbsolutePrecision(origin);

	//increase precision of origin in order to represent pertubations
	origin:=elt<Op|origin,prc+1>;
	vprint LocSol,2:"Looking for point in",origin;
	// loop through pertubations	
	for perturb in resfldreps do
          x:=origin+pi^prc*(perturb@@toresfld)+O(pi^(prc+1));
	  y:=&+[f[i]*(x^(i-1)):i in [1..#f]];
	  vly:=Valuation(y);
	  
	  // is there *ANY* information in y?
	  if RelativePrecision(y) gt 0 then
	  
	    // if y has odd valuation, there's no points around this x.
	    if (vly mod 2) eq 0 then
	    
	      // otherwise, multiply y into a unit (by a square!)
	      // and throw away any possibly excess precision.
	      yrd:=y/u^vly+elt<Op|v4p1,0,v4p1>;
	      
	      // now see if yrd is a square up to its precision
	      // (because we've thrown out excess precision, ALL digits
	      // of yrd should correspond to a listed square in sqr)
	      
	      if exists{sq: sq in sqr|
                           RelativePrecision(yrd-sq) eq 0} then
	        // if yrd had full precision, then we're really done.
	        if AbsolutePrecision(yrd) ge v4p1 then
                  m:=Minimum([Precision(c):c in f]);
                  x:=ChangePrecision(x,m);
	          bl,y:=MyIsSquare(&+[f[i]*(x^(i-1)):i in [1..#f]]);
                  assert bl;
                  y:=ChangePrecision(y,Precision(x)-Valuation(Op!4)-1);
                  vprint LocSol,2:"Found",[x,y];
	          return true,[x,y];
		
	        // Otherwise, look closer (i.e. recurse around this x)
	        else
                  IndentPush();
	          pred,val:=$$(x);
                  IndentPop();
	          if pred then
                    vprint LocSol,2:"Found",val;
                    vprint LocSol,2:"Testing this value in the equation:",
                         val[2]^2-Evaluate(F,val[1]);
	            return pred,val;
	          end if;
		end if;
              end if;
	    end if;
	    
	  // if there was no info in y, look closer (recurse around this x).
	  else
            IndentPush();
	    pred,val:=$$(x);
            IndentPop();
	    if pred then
              vprint LocSol,2:"Found",val;
              vprint LocSol,2:"Testing this value in the equation:",
                val[2]^2-Evaluate(F,val[1]);
	      return pred,val;
	    end if;
          end if;
	end for;

 	//by now, we've tested everything and haven't found any square value
	//therefore, there are none.
        vprint LocSol,2:"Found none.";
	return false,_;
      end function;
   
  end if;
  vprint LocSol,2:"Looking for point in",Neighbourhood;
  IndentPush();
  a,b:=test(Neighbourhood);
  IndentPop();
  if a then
    vprint LocSol,2:"Found",b;
    return a,b;
  else
    vprint LocSol,2:"Found none.";
    return a,_;
  end if;
end function;

function HasSquareValue(Fin:NoRoots:=false)
  /*Tests whether y^2=F(x) has a solution in a local field. If so,
  the second value describes such a solution, in the style of
  rational points on hyperelliptic curves.
  If NoRoots is supplied, then F is not tested for having
  roots. Since p-Adic factorisation is slow, this speed things up a bit, but
  if there is such a root, it might cause a loss of precision error.*/
 
  vprint LocSol,2:"Deciding if",Fin,"takes any square values.";
  F:=Fin;
  Kp:=BaseRing(F); 
  pi:=UniformizingElement(Kp);

  error if not ISA(Type(BaseRing(F)),FldPad),
      "Needs polynomial over local field";

  //If 0 is a root, things are nasty. Just return that root regardless
  //of NoRoots is set or not.
  f:=Coefficients(F);
  if f[1] eq 0 then
    vprint LocSol,2:"That's easy! Returning [0,0,1]";
    return true,[Kp!0,Kp!0,Kp!1];
  end if;
  
  //In the following, we use that Kp is a truly floating field, i.e., although
  //a priori the minimal polynomial of Kp may be only of finite precision,
  //precision is not truncated. That's very convenient here!
  
  //flatten out the newton polygon. (remember u for later use!);
  e:=-Round((Valuation(f[#f])-Valuation(f[1]))/(#f-1));
  u:=UniformizingElement(Kp)^e;
  F:=Parent(F)![f[i]*u^(i-1):i in [1..#f]];

  //and shift the polygon above the axis, as close to the axis as possible.
  //(note that v will be even)
  v:=MinValuation(F) div 2;
  //so we're multiplying f with a square here.	 
  F:=ShiftVal(F,-2*v);
    
  vprint LocSol,2:"After flattening the Newton Polygon:",F;

  // test for infinity and roots of F (if not inhibited)
  if not(NoRoots) then
    if (Degree(F) mod 2) eq 1 then
      vprint LocSol,2:"Point at infinity! Returning [1,0,0]";
      return true,[Kp!1,Kp!0,Kp!0];
    end if;
    rt:=SquarefreeRoots(F);
    if #rt ne 0 then
      vprint LocSol,2:"Polynomial has a root. Returning",
          [rt[1][1]*u,Kp!0,Kp!1];
      return true,[rt[1][1]*u,Kp!0,Kp!1];
    end if;
  end if;
  
  F:=Polynomial(IntegerRing(BaseRing(F)),F);  
  R:=IntegerRing(Kp);
  k:=ResidueClassField(R);
  g:=(Degree(F)-1) div 2;
  if Characteristic(k) ne 2 and #k+1-2*g*Sqrt(#k) gt 0 then
    _<x,z>:=PolynomialRing(R,2);
    cf:=Eltseq(F);
    mn:=[x^i*z^(2*g+2-i):i in [0..#cf -1]];
    Fhom:=&+[cf[i]*mn[i]:i in [1..#cf]];
    bl,pt:=HyperellipticHasPoint(Fhom);
  else
    // TO DO : if degree 4 (or degree 3?), call InternalIsSoluble?
    vprint LocSol,2:"Look for integral points with square value...";
    bl,x:=HasSquareIntegralValues(F:NoRoots);
    if bl then
      vprint LocSol,2:"Found",[u*Kp!x[1],x[2]*pi^v,1];
      pt:=[Kp|x[1],x[2],1];
    else
      // next we reverse F, so that we can test values for which 1/x is
      // integral. If F is of odd degree, then shift the polynomial.
      // we're considering y^2=F(x) as a hyperelliptic curve, so this takes
      // care of the point "at infinity".
      vprint LocSol,2:"Look for integral points on reversal...";
      F:=Polynomial(BaseRing(F),Reverse(Eltseq(F)))*Parent(F).1^(Degree(F) mod 2);
      bl,x:=HasSquareIntegralValues(F :
             Neighbourhood:=O(UniformizingElement(BaseRing(F))),NoRoots);
      if bl then
        vprint LocSol,2:"Found",[u,x[2]*pi^v,Kp!x[1]];
        pt:=[Kp|1,x[2],x[1]];
      end if;
    end if;
  end if;
  if bl then
    pt:=[u*Kp!pt[1],Kp!pt[2]*pi^v,Kp!pt[3]];
    vprint LocSol,2:"Found:",pt;
//    vprint LocSol,2:"Evaluation of eq. at it:",
//                  pt[2]^2-Evaluate(Fin,pt[1]/pt[3]);
    pt:=[Kp|c: c in pt];
    return true,pt;
  else
    vprint LocSol,2:"Found no points.";
    return false,_;
  end if;
end function;

///////////////////////////////////////////////////////
// Smooth local solubility tester

function HasIntegralPoints(L,d)
  //takes a list of polynomials L and an assumed dimension d and looks for
  //integral points. (assumes no rational singular points exist!)
  //returns false,_ or true,[coordinates].

  //some quantities that don't change during the computations.
  Rpol:=Universe(L);
  L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
  R:=BaseRing(Rpol);
  error if not ISA(Type(R),RngPad), "must have polynomials over local ring";
  u:=UniformizingElement(R);
  n:=Rank(Rpol);
  cd:=n-d;
  if cd ne #L and d eq 0 then
    vprint LocSol,1: "0 dimensional non-complete intersection. Using cluster code";
    V:=AllIntegralPoints(L,Minim([MinPrec(l):l in L]));
    if #V eq 0 then
      return false,_;
    else
      return true, Rep(V);
    end if;
  end if;
  error if not #L eq cd, 
       "Not implemented for this case (dimension", d, "and not a complete intersection)";
  k,Rtok:=ResidueClassField(R);
  Ak:=AffineSpace(k,n);
  kpol:=CoordinateRing(Ak);
  Rpoltokpol:=hom<Rpol->kpol|[kpol.i:i in [1..n]]>;

  //the hard (recursive) work.
  test:=function(L,lvl)
    vprint LocSol,2: "Entering test level ",lvl;
    vprint LocSol,2: "Passed argument:",L;
    L:=[MyPrimitivePart(Q) : P in L | Q ne 0 where Q:=StripPrecisionlessTerms(P)];
    vprint LocSol,2: "Primmed and stripped:",L;
    error if #L lt cd,
      "Variety appears to have too high dimension. Precision loss?";
    Lk:=[Rpoltokpol(P):P in L];
    Lkschm:=Scheme(Ak,Lk);
    J:=JacobianMatrix(Lk);
    kpoints:=RationalPoints(Lkschm);
    vprint LocSol,2: "Points on reduction:",kpoints;
    vprint LocSol,2: "Testing if there are any smooth ones ...";
    for p in kpoints do
      Jp := Matrix(Ncols(J), [ Evaluate(f,Eltseq(p)) : f in Eltseq(J) ]);
      E,T:=EchelonForm(Jp);
      rk:=Rank(E);
      error if rk gt cd, "Jacobian has too large a rank. d wrong?";
      if rk eq cd then
        vprint LocSol,2: "Found ",p,". This point will lift."; 
        vprint LocSol,2: "Leaving test level ",lvl;
        return true,[c@@Rtok+O(u):c in Eltseq(p)];
      end if;
    end for;
    vprint LocSol,2: "No smooth points. Looking around each point ...";
    for p in kpoints do
      vprint LocSol,2: "Looking around ",p,"...";
      plift:=[p[i]@@Rtok+u*Rpol.i:i in [1..n]];
      L2:=[MyPrimitivePart(Evaluate(f,plift)):f in L];
      repeat
        B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                           [j eq i select 1 else 0:j in [1..n]])):
                               i in [1..Rank(Rpol)]]:f in L2]);
        E,T:=EchelonForm(B);
        vprint LocSol,2:"Changing the basis of the ideal by:",T;
        TT:=Matrix(Rpol,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
        L2:=Eltseq(Vector(L2)*Transpose(TT));
        flag:=false;
        vprint LocSol,2:"to",L2;
        for i in [1..#L2] do
          v:=MinValuation(L2[i]);
          if v gt 0 then
            L2[i]:=ShiftVal(L2[i],-v);
            vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
            flag:=true;
          end if;
        end for;
      until not(flag); 
      vprint LocSol,2:"Newly obtained basis is:",L2;
      
      IndentPush();
      rs,pt:=$$(L2,lvl+1);
      IndentPop();
      if rs then
        vprint LocSol,2: "Found a point. We tranform it back and return.";
        vprint LocSol,2: "Leaving test level ",lvl;
        return true,[Evaluate(c,pt):c in plift];
      end if;
    end for;
    vprint LocSol,2: "Leaving test level ",lvl;
    return false,_;
  end function;
  
  rs,pt:=test(L,1);
  if rs then
    return true,pt;
  else
    return false,_;
  end if;
end function;

//////////////////////////////////////////////////////
// general local solubility tester. Recurses into the singular locus.

function HasLocalPoints(X,m:AssumeIrreducible:=false,
                                         AssumeNonsingular:=false)
  //tests local solubility of the scheme X. m should be a map
  //with which the appropriate pointset can be made.
  //For affine schemes, actually
  //tests for *integral* points.
  
  error if Domain(m) cmpne BaseRing(X), "m must be a base change map";
  Kp:=Codomain(m);
  error if not ISA(Type(Kp),FldPad), "Codomain of m must be a local field";
  vprint LocSol: "Determining local solubility of ",X;
  if not(AssumeIrreducible) then
    AssumeIrreducible:=IsIrreducible(X);
  end if;
  if not(AssumeIrreducible) then
    vprint LocSol: "We iterate over a minimal set of prime components...";
    for Y in MinimalPrimeComponents(X) do
      IndentPush();
      bl,pt:=HasLocalPoints(Y,m:
                       AssumeIrreducible:=true,
                       AssumeNonsingular:=AssumeNonsingular);
      IndentPop();
      if bl then
        vprint LocSol: "Found a point on one of the components. Return that.";
        return true,PointSet(X,m)!pt;
      end if;
    end for;
    vprint LocSol: "None of the components seem solvable. Return false.";
    return false,_;
  elif not(AssumeNonsingular) then
    vprint LocSol: "We first recurse into the singular locus ...";
    Y:=SingularSubscheme(X);
    if not(IsEmpty(Y)) then
      IndentPush();
      bl,pt:=HasLocalPoints(Y,m);
      IndentPop();
      if bl then
        vprint LocSol: "Found a point in the singular locus. Return that.";
        return true,PointSet(X,m)!pt;
      else
        vprint LocSol:
          "No points in the singular locus. Continue with the smooth part ...";
      end if;
    else
      vprint LocSol:
        "The singular locus is an empty scheme. Continue with the smooth part ...";
    end if;
  else
    vprint LocSol:
      "Assuming non-singularity. We might get into an infinite loop.";
  end if;
  Kp:=Codomain(m);
  R:=IntegerRing(Kp);
  pi:=UniformizingElement(R);
  L:=BaseChangedDefiningEquations(X,m);
  RX:=PolynomialRing(R,Rank(Universe(L)));
  L:=[RX!ShiftVal(P,-MinValuation(P)):P in L];
  if IsAffine(X) then
    vprint LocSol:
      "Looking for *integral* points on the affine variety ...";
    IndentPush();
    dm:=Dimension(X);
    if dm eq -1 then
      return false,_;
    elif dm eq 0 then
      vprint LocSol: "Using special routine for 0-dimensional scheme";
      V:=AllIntegralPoints(L,Minim([MinPrec(l):l in L]));
      bl:=not(IsEmpty(V));
      if bl then
        pt:=Rep(V);
      end if;
    else
      bl,pt:=HasIntegralPoints(L,Dimension(X));
    end if;
    IndentPop();
    if bl then
      vprint LocSol:
        "Found a point. Returning that";
      return true,PointSet(X,m)![Kp!u:u in pt];
    else
      return false,_;
    end if;
  elif IsProjective(X) then
    is_weighted := #Gradings(X) gt 1 or {g : g in Gradings(X)[1]} ne {1};
    error if is_weighted, 
      "HasLocalPoints is not implemented for schemes in weighted projective spaces." 
         * "\nIf this case is needed, please email magma-bugs@maths.usyd.edu.au.";
    vprint LocSol:
      "Iterating over affine patches of projective variety ...";
    RXaff:=PolynomialRing(R,Rank(RX)-1);
    for i in [1..Rank(RX)] do
      patch:=[pi*RXaff.j:j in [1..i-1]] cat [1] cat
                     [RXaff.j: j in [i..Rank(RXaff)]];
      vprint LocSol:
        "Looking on patch ",patch;
      IndentPush();        
      bl,pt:=HasIntegralPoints([Evaluate(P,patch):P in L],Dimension(X));
      IndentPop();
      if bl then
        vprint LocSol:
          "Found point ",[Kp!Evaluate(P,pt):P in patch],"Returning that.";
        return true,PointSet(X,m)![Kp!Evaluate(P,pt):P in patch];
      else
        vprint LocSol:
          "No point found.";
      end if;
    end for;
    return false,_;
  else
    error "Wow, we've found a scheme that's neither affine nor projective.";
  end if;
end function;

//////////////////////////////////////////////////////
// Smooth local solubility tester for planar curve.
// Does the blowing up for you.

function HasSmoothIntegralPoints(F,Sing)
  //Decides if the curve described by the bivariate polynomial F has any smooth
  //points with integral coordinates. F should be over a complete local ring.
  //Sing should contain a list of tuples [<x[i],y[i]>], where x[i],y[i] are
  //sufficient approximations to the singularities of F
  
  Rxy:=Parent(F);
  error if Rank(Rxy) ne 2,"Must have bivariate polynomial";
  R:=BaseRing(Rxy);
  Rx:=PolynomialRing(R);
  k,Rtok:=ResidueClassField(R);
  error if not ISA(Type(R),RngPad),
         "Must be a polynomial over a complete local ring";
  pi:=UniformizingElement(R);
  
  //augment Sing with a 'radius' so that all singularities are separated
  Sing:=[<p[1],p[2],0>:p in Sing];
  for i in [1..#Sing-1] do
    for j in [i+1..#Sing] do
      v:=Minimum([Valuation(Sing[i][k]-Sing[j][k]): k in [1,2]]);
      Sing[i][3]:=Maximum(Sing[i][3],v+1);
      Sing[j][3]:=Maximum(Sing[j][3],v+1);
    end for;
  end for;
  
  Ak:=AffineSpace(k,2);
  tokxy:=func<f|Evaluate(f,[Ak.1,Ak.2])>;
  removeYs:=function(F)
    F:=StripPrecisionlessTerms(FlattenPrecision(F));
    cf:=Coefficients(F);
    mn:=Monomials(F);
    Ypower:=Minimum([Degree(mon,2):mon in mn]);
    return &+[cf[i]*
       Rxy.1^Degree(mn[i],1)*Rxy.2^(Degree(mn[i],2)-Ypower):
           i in [1..#mn]];
  end function;
  
  work:=function(F,sing)
    //Strip any content from F - useless anyway
    F:=MyPrimitivePart(F);

    error if exists{c : c in Coefficients(F)| AbsolutePrecision(c) eq 0},
      "Loss of precision in F";
      
    vprint LocSol,2:
      "Determining local solubility of",F,"with singularity list",sing;
    if #sing eq 1 and Rep(sing)[3] eq 0 then
      Spt:=Rep(sing);
      vprint LocSol,2:"Blowing up singularity neighbourhood ...";
      //Let (x0,y0) be the singularity. We blow up, getting
      //(x,y;u:v), subject to (x-x0)*v=(y-y0)*u.
      //We consider two patches:
      //A. (u:v)=(X:1)
      //  here x=X*Y+x0, y=Y+y0
      //B. (u:v)=(1:pi*X)
      //  here y=pi*X*Y+y0 x=Y+x0
      //
      //in both cases, Y=0 is the exceptional component, which we remove
      //by dividing out Y from G, which is F in terms of [X,Y].
      G:=removeYs(Evaluate(F,[Rxy.1*Rxy.2+Spt[1],Rxy.2+Spt[2]]));

      //Since the singularity we have just blown up is the only with
      //integral coordinates in the present model, new singularities will
      //all lie on the exceptional component. So we first find all intersections
      //of G with Y=0 and then test which are singular.
      GX:=Derivative(G,1);
      GY:=Derivative(G,2);
      Gsing:=[<x[1],0,0>:x in IntegralSquarefreeRoots(
                           SquarefreePart(Evaluate(G,[Rx.1,Rx!0])))|
         RelativePrecision(Evaluate(GX,[x[1],0])) eq 0 and
         RelativePrecision(Evaluate(GY,[x[1],0])) eq 0];

      //and fill in the "precision" field.
      for i in [1..#Gsing-1] do
        for j in [i+1..#Gsing] do
          v:=Valuation(Gsing[i][1]-Gsing[j][1]);
          Gsing[i][3]:=Maximum(Gsing[i][3],v+1);
          Gsing[j][3]:=Maximum(Gsing[i][3],v+1);
        end for;
      end for;
      
      //we're ready to recurse on the first patch ...
      vprint LocSol,2:
        "Patch A:",[Rxy.1,Rxy.2],"<-",
             [Rxy.1*Rxy.2+Spt[1],Rxy.2+Spt[2]];
      
      IndentPush();
      bl,witness:=$$(G,Gsing);
      IndentPop();
      
      if bl then
        vprint LocSol,2:"Returning",
           [witness[1]*witness[2]+Spt[1],witness[2]+Spt[2]];
        return true,[witness[1]*witness[2]+Spt[1],witness[2]+Spt[2]];
      end if;

      //patch B.      
      G:=removeYs(Evaluate(F,[Rxy.2+Spt[1],pi*Rxy.1*Rxy.2+Spt[2]]));
      GX:=Derivative(G,1);
      GY:=Derivative(G,2);
      Gsing:=[<x[1],0,0>:x in IntegralSquarefreeRoots(SquarefreePart(
           Evaluate(G,[Rx.1,Rx!0])))|
         RelativePrecision(Evaluate(GX,[x[1],0])) eq 0 and
         RelativePrecision(Evaluate(GY,[x[1],0])) eq 0];
      for i in [1..#Gsing-1] do
        for j in [i+1..#Gsing] do
          v:=Valuation(Gsing[i][1]-Gsing[j][1]);
          Gsing[i][3]:=Maximum(Gsing[i][3],v+1);
          Gsing[j][3]:=Maximum(Gsing[i][3],v+1);
        end for;
      end for;
      vprint LocSol,2:
        "Patch B:",[Rxy.1,Rxy.2],"<-",
           [Rxy.2+Spt[1],pi*Rxy.1*Rxy.2+Spt[2]];
           
      IndentPush();
      bl,witness:=$$(G,Gsing);
      IndentPop();
      
      if bl then
        vprint LocSol,2:"Returning",
           [witness[2]+Spt[1],pi*witness[1]*witness[2]+Spt[2]];
        return true,[witness[2]+Spt[1],pi*witness[1]*witness[2]+Spt[2]];
      end if;
    else
      //we determine points over k 

      Fbar:=tokxy(F);
      FbarX:=Derivative(Fbar,Ak.1);
      FbarY:=Derivative(Fbar,Ak.2);
      
      vprint LocSol,2:
        "Determining rational points over residue class field ...";
      V:=[Eltseq(a):a in RationalPoints(Scheme(Ak,Fbar))];
      
      //This part is just to beautify the diagnostic output.
      //The subsequent code would nicely fall through if V is empty,
      //but it looks stupid if it finds no local points and still goes
      //on "checking" for smoothness and zooming in.
      
      if #V eq 0 then
        vprint LocSol,2:
          "No points in reduction. Returning false.";
        return false,_;
      end if;
      
      vprint LocSol,2:
        "Testing if there are any smooth points in reduction ...";
      if exists(witness){
           [p[1]@@Rtok+O(pi),p[2]@@Rtok+O(pi)] : p in V |
                 Evaluate(FbarX,p) ne 0 or Evaluate(FbarY,p) ne 0} then
        vprint LocSol,2:
          "Found one. That will lift. Returning",witness;
        return true,witness;
      end if;
      
      vprint LocSol,2:
        "No smooth point in reduction. Looking around each point individually.";

      for p in V do
        // since we're changing coordinates [x,y]=[p1+pi*u,p2+pi*v]
        //and Sing is in x,y coordinates, we have to replace those by
        //[u,v]=[(x-p1)/pi,(y-p2)/pi]. Obviously, we only have to consider
        //have to take those that end up with integral [u,v]. The radius just
        //gets adjusted by -1 (i.e., made *larger* (:-))

        vprint LocSol,2:"Looking around",p;

        IndentPush();
        bl,witness:=$$(
               Evaluate(F,[p[1]@@Rtok+pi*Rxy.1,p[2]@@Rtok+pi*Rxy.2]),
               [<u div pi,v div pi,q[3]-1>:q in sing |
                      Valuation(u) ge 1 and Valuation(v) ge 1
                        where u:=q[1]-p[1]@@Rtok where v:=q[2]-p[2]@@Rtok]);
        IndentPop();
                        
        if bl then
          vprint LocSol,2:"Returning",[p[i]@@Rtok+pi*witness[i]:i in [1,2]];
          return true,[p[i]@@Rtok+pi*witness[i]:i in [1,2]];
        end if;
      end for;
    end if;
    return false,_;
  end function;
  
  bl,pt:=work(F,Sing);
  if bl then
    return bl,pt;
  else
    return false,_;
  end if;
end function;

////////////////////////////////////////////////////////////////////
// Local solubility tester for intersection of two quadric surfaces.
// Equations must be of the form
// Q:=Quadric(u0,u1,u2)
// T:=a*u3^2-Quadric(u0,u1,u2)


function QuadHasPoint(Q,T);
  P3:=Parent(Q);
  K:=BaseRing(P3);
  pi:=UniformizingElement(K);
  Kx:=PolynomialRing(K);
  Kxyz<x,y,z>:=PolynomialRing(K,3);
  R:=IntegerRing(K);
  Rxyz:=PolynomialRing(R,3);
  k:=ResidueClassField(R);

  vprint LocSol,2:"Testing Q=",Q,"and T=",T,"for local solubility";
  assert Degree(Q,4) eq 0;
  Qxyz:=HomogeneousComponent(Evaluate(Q,[x,y,z,0]),2);
  Qd,Tmat:=DiagonalForm(Qxyz);
  vprint LocSol,2:"First testing diagonal form",Qd,"for local solubility";
  
  f:=-Evaluate(Qd,[Kx.1,0,1])/CoefficientByExponentVector(Qd,[0,2,0]);
  bl,pt:=HasSquareValue(f);
  if not(bl) then
    vprint LocSol,2:"Is not locally soluble. Therefore Q=T=0 has no solution.";
    return false,_;
  end if;
  if RelativePrecision(pt[2]) ne 0 then
    pt:=[ChangePrecision(c,R`DefaultPrecision):c in pt];
    bl,pt[2]:=MyIsSquare(Evaluate(-Qd,[pt[1],0,pt[3]])/
                           CoefficientByExponentVector(Qd,[0,2,0]));
    assert bl;
  end if;
  P:=pt;
  //P:=LiftPoint([Qd],2,pt,R`DefaultPrecision+MinValuation(pt):Strict:=false);
  vprint LocSol,2:"Found point:",P;
  vprint LocSol,2:"Diagonal form at P:",Evaluate(Qd,P);
  P0:=Vector(P)*Tmat;
  vprint LocSol,2:"Q evaluated at P:",Evaluate(Qxyz,Eltseq(P0));
  P1,P2:=Explode(Basis(NullspaceOfTranspose(Matrix(P0))));
  M:=SymmetricBilinearForm(Qxyz);
  U:=-(x^2*InnerProduct(P1*M,P1)+
        2*x*z*InnerProduct(P1*M,P2)+
        z^2*InnerProduct(P2*M,P2));
  V:=2*x*InnerProduct(P0*M,P1)+2*z*InnerProduct(P0*M,P2);
  parm:=[U*P0[i]+V*(x*P1[i]+z*P2[i]):i in [1..3]] cat [0];
  vprint LocSol,2:"Parametrization of Q:",parm;
  f:=y^2+Evaluate(T,parm)/CoefficientByExponentVector(T,[0,0,0,2]);
  vprint LocSol,2:"Substituting this parametrization in T gives:",f;
  bl,pt:=HasSquareValue(Evaluate(-f,[Kx.1,0,1]));
  if not(bl) then
    vprint LocSol,2:"T is not locally soluble. Q=T=0 has no solution.";
    return false,_;
  end if;

  if RelativePrecision(pt[2]) ne 0 then
    pt:=[ChangePrecision(c,R`DefaultPrecision):c in pt];
    bl,pt[2]:=MyIsSquare(Evaluate(-f,[pt[1],0,pt[3]]));
    assert bl;
  end if;
  
  vprint LocSol,2:"Point found:",pt;
  P:=[Evaluate(f,pt):f in parm];
  P[4]:=pt[2];
  P:=[c+O(pi^v):c in P] where v:=MinPrec(P);
  v:=Minimum([Valuation(c):c in P|c ne 0]);
  P:=[c/pi^v:c in P];
  vprint LocSol,2:"This corresponds to the point on Q=T=0:",P;
  vprint LocSol,2:"Q and T at that point:",Evaluate(Q,P),Evaluate(T,P);
  return true,P;
end function;

//////////////////////////////////////////////////////////////////

intrinsic IsEmpty(Xm::SetPt:Smooth:=false,
                            Singularities:=false,
                            AssumeIrreducible:=false,
                            AssumeNonsingular:=false)->BoolElt,Pt
  {Decides whether the point set over a local field has any points in it. For
  curves, the optional parameter Smooth specifies to only look for smooth
  points.}
  m:=RingMap(Xm);
  X:=Scheme(Xm);
  K:=Codomain(m);
  require IsProjective(X): "Scheme has to be projective";
  require ISA(Type(K),FldPad):
    "Points must have values in a local field.";
  if Singularities cmpne false then
    require Smooth: 
      "Singularities can only be supplied if ''Smooth'' is specified";
  end if;

  // Use known attributes (TO DO: use SingularSubscheme too?) 
  // (April 2010, SRD)
  if assigned X`Nonsingular and X`Nonsingular then
    AssumeNonsingular:=true;
  end if;
  if assigned X`GeometricallyIrreducible and X`GeometricallyIrreducible then
    AssumeIrreducible:=true;
  end if;

  if ISA(Type(X),CrvHyp) then
    if BaseRing(X) cmpeq Rationals() and Degree(X) eq 4 and Valuation(2@m) gt 0 then
      // ModelG1 of degree 2
      // The advantage here is the handling of cross terms 
      // (so only makes a difference at places above 2)
      vprint LocSol:"Calling IsLocallySolvable from the GenusOneModel package";
      model:=GenusOneModel(X);
      p := Integers()!( UniformizingElement(K)@@m ); assert IsPrime(p);
      bl,pt:=IsLocallySolvable(model,p);
      if bl then 
        pt:=X(K)![pt[1],pt[3],pt[2]]; // the model curve has variables x,z,y
        vprint LocSol:"Returning",pt;
        return false,pt;
      else
        vprint LocSol:"Curve has no local points.";
        return true,_;
      end if;
    end if;

    vprint LocSol:"Deciding whether",X,"has any points over",K;
    f,h:=HyperellipticPolynomials(X);
    C2,XtoC2:=Transformation(X,h/2);
    vprint LocSol:"Transformed curve to",C2;
    f,h:=HyperellipticPolynomials(C2);
    assert IsWeaklyZero(h);
    f:=PolynomialRing(K)![m(c):c in Eltseq(f)];
    k:=ResidueClassField(IntegerRing(K));
    bl,pt:=HasSquareValue(f);
    if bl then
      vprint LocSol:"Found point",pt,"Trying to put it on C2";

// This avoids a bug sometimes
// Don't know if it always works, hence try/catch (TO DO)
// November 2013 SRD
flag := true;
if BaseRing(C2) cmpeq K then
try
      if IsWeaklyZero(pt[3]) then
         pt:=Points(C2, Infinity())[1];
      else
         pt:=Points(C2, pt[1]/pt[3])[1];
      end if;
flag := false;
catch argh
      vprintf LocSol: "Points(C2, x) failed:\n%o\n", argh`Object;
end try;
end if;
if flag then
      // Bug fix: coercion can fail if point is not close enough to a solution
      // pt:=PointSet(C2,m)!([K|] cat pt);
      pt_fits,pt1:=IsCoercible(PointSet(C2,m), ([K|] cat pt));
      if not pt_fits then 
         prec10:=10+K`DefaultPrecision;
         pt:=[ChangePrecision(coord,prec10):coord in pt];
         
         //BMC: changed to fix coercion problem
         g := HyperellipticPolynomials(C2); 
         degg := 2*Genus(C2)+2;
         ycoord_squared := &+[m(Coefficient(g,i))*pt[3]^(degg-i)*pt[1]^i : i in [0..degg] ];
         //ycoord_squared:=Evaluate(-DefiningEquation(C2),[pt[1],0,pt[3]]);

         bl,ycoord:=IsSquare(ChangePrecision(ycoord_squared,prec10));
         pt_fits,pt1:=IsCoercible(PointSet(C2,m), [K| pt[1],ycoord,pt[3]]);
         require pt_fits : "Can't coerce local point into pointset";
      end if;
      pt:=pt1;
end if;

      vprint LocSol:"Found point",pt,"Transforming it back";
      pt:=Inverse(XtoC2)(pt);
      vprint LocSol:"Returning",pt;
      return false,pt;
    else
      vprint LocSol:"Curve has no local points.";
      return true,_;
    end if;
  end if;

  L:=DefiningEquations(X);
  if Dimension(Ambient(X)) eq 3 and 
           #L eq 2 and
           forall{g:g in L| TotalDegree(g) eq 2} and
           Degree(L[1],4) eq 0 and
           Degree(L[2],4) eq 2 and
           Term(L[2],4,1) eq 0 and
           IsNonsingular(X) then
    vprint LocSol:"Special intersection of quadrics. Using dedicated code.";
    _<u0,u1,u2,u3>:=PolynomialRing(K,4);
    mp:=m*Bang(K,Parent(u0));
    bsch:=hom<CoordinateRing(Ambient(X))->Parent(u0)|mp,[u0,u1,u2,u3]>;
    L:=[bsch(f):f in L];    
    bl,pt:=QuadHasPoint(L[1],L[2]);
    if bl then
      return false,PointSet(X,m)!pt;
    else
      return true,_;
    end if;
  elif BaseRing(X) cmpeq Rationals() and IsQuadricIntersection(X) and IsNonsingular(X) then 
    // ModelG1 of degree 4
    vprint LocSol:"Calling IsLocallySolvable from the GenusOneModel package";
    model:=GenusOneModel(Curve(X));
    p := Integers()!( UniformizingElement(K)@@m ); assert IsPrime(p);
    bl,pt:=IsLocallySolvable(model,p);
    if bl then 
      pt:=X(K)!Eltseq(pt);
      vprint LocSol:"Returning",pt;
      return false,pt;
    else
      vprint LocSol:"Curve has no local points.";
      return true,_;
    end if;
  elif BaseRing(X) cmpeq Rationals() and IsPlaneCurve(X) and Degree(X) eq 3 and IsNonsingular(X) then
    // ModelG1 of degree 3
    vprint LocSol:"Calling IsLocallySolvable from the GenusOneModel package";
    model:=GenusOneModel(Curve(X));
    p := Integers()!( UniformizingElement(K)@@m ); assert IsPrime(p);
    bl,pt:=IsLocallySolvable(model,p);
    if bl then 
      pt:=X(K)!Eltseq(pt);
      vprint LocSol:"Returning",pt;
      return false,pt;
    else
      vprint LocSol:"Curve has no local points.";
      return true,_;
    end if;
  end if;

  // TO DO: what happens in the case that Smooth:=true, but in fact 
  // X is (known to be) nonsingular?  (For example, X is a QI)
  // Shouldn't we skip the next part in that situation?
  // In any case, I'm putting all the (nonsingular) special cases 
  // above this (previously, the QuadHasPoint case was below it)
  //  --- April 2010, SRD

  if Smooth then
    require IsCurve(X):
      "Can only test for smooth points on a curve";
    vprint LocSol:"Deciding whether",X,"has any smooth points over",K;

    if Singularities cmpne false then
      U:=Universe(Singularities);
      require ISA(Type(U),SetPt):
        "Singularities must be points";
      require Scheme(U) subset Ambient(X):
        "Points must lie in the ambient of X";
      require Codomain(RingMap(U)) eq Codomain(m):
        "Point must take values in the same ring as the point set";      
      vprint LocSol:"Assuming supplied singularities suffice";
      sing:={Xm!Eltseq(P): P in Singularities};
    else
      vprint LocSol:"Determining the rational singularities of the curve";
      sing:=MyRationalPoints(PointSet(SingularSubscheme(X),m));
    end if;
    vprint LocSol:"Singular points over local field:",sing;    
    
    R:=IntegerRing(K);
    Kxy:=PolynomialRing(K,2);
    Rxy:=PolynomialRing(R,2);
    pi:=UniformizingElement(K);
    Fhom:=BaseChangedDefiningEquations(X,m)[1];
    for i in [1..3] do
      patch:=[[Kxy.1,Kxy.2,1],[Kxy.1,1,pi*Kxy.2],[1,pi*Kxy.1,pi*Kxy.2]][i];
      F:=Evaluate(Fhom,patch);
      F:=Rxy!ShiftVal(F,-MinValuation(F));
      vprint LocSol:"Looking on affine patch:",F;
      mp:=function(a)
          b:=Eltseq(a);
          if i eq 1 then
            if RelativePrecision(b[3]) eq 0 then
              return false;
            else
              return <b[1]/b[3],b[2]/b[3]>;
            end if;
          elif i eq 2 then
            if RelativePrecision(b[2]) eq 0 then
              return false;
            else
              return <b[1]/b[2],b[3]/b[2]/pi>;
            end if;
          else
            if RelativePrecision(b[1]) eq 0 then
              return false;
            else
              return <b[2]/b[1]/pi,b[3]/b[1]/pi>;
            end if;
          end if;
      end function;
      singA:=[<R!pt[1],R!pt[2]>: P in sing | pt cmpne false and
              Valuation(pt[1]) ge 0 and Valuation(pt[2]) ge 0
                      where pt:=mp(P)];
      vprint LocSol:"Integral valued singular points on this patch:",singA;
      IndentPush();
      bl,witness:=HasSmoothIntegralPoints(F,singA);
      IndentPop();
      if bl then
        point:=Xm![Evaluate(p,witness):p in patch];
        vprint LocSol:"found",point,"Returning that";
        return false,point;
      end if;
    end for;
    vprint LocSol:"no point found";
    return true,_;
  end if;

  if Dimension(X) le 0 then
    V:=MyRationalPoints(PointSet(X,m):AssumeReduced:=AssumeNonsingular);
    if #V eq 0 then
      return true,_;
    else
      return false,Rep(V);
    end if;
  else
    bl,pt:=HasLocalPoints(X,m:AssumeIrreducible:=AssumeIrreducible,
                              AssumeNonsingular:=AssumeNonsingular);
    if bl then
      return false,pt;
    else
      return true,_;
    end if;
  end if;
end intrinsic;

intrinsic IsLocallySolvable(X::Sch,p::RngOrdIdl:Smooth:=false,
                            AssumeIrreducible:=false,
                            AssumeNonsingular:=false)->BoolElt,Pt
{Tests if X is locally solvable at a prime p}
  v := LookupPrime(p);
  df := DefiningEquations(X);
  pb := Max(&cat[ [Valuation(c,v) : c in Coefficients(g)] : g in df ]);
  _,cmpl:=MyCompletion(v : Precision := 50+pb);
  Xm:=PointSet(X,cmpl);
  bl,pt:=IsEmpty(Xm : Smooth:=Smooth,
                      AssumeIrreducible:=AssumeIrreducible,
                      AssumeNonsingular:=AssumeNonsingular);
  if bl then
    return false,_;
  else
    return true,pt;
  end if;
end intrinsic;

intrinsic IsLocallySolvable(X::Sch,p::RngIntElt:Smooth:=false,
                            AssumeIrreducible:=false,
                            AssumeNonsingular:=false)->BoolElt,Pt
{Tests if X is locally solvable at a prime p}
  require BaseRing(X) cmpeq Rationals():
    "X must be over the rationals when p is a prime integer.";
  require IsPrime(p):
    "p must be prime";
  df := DefiningEquations(X);
  pb := Max(&cat[[Valuation(c,p) : c in Coefficients(g)] : g in df ]);
  Xm:=X(pAdicField(p,50+pb));
  bl,pt:=IsEmpty(Xm : Smooth:=Smooth,
                      AssumeIrreducible:=AssumeIrreducible,
                      AssumeNonsingular:=AssumeNonsingular);
  if bl then
    return false,_;
  else
    return true,pt;
  end if;
end intrinsic;
