freeze;

/****************************************************************************
sqfroots.m

November 2002, Nils Bruin

squarefree root finder
******************************************************************************/
import "loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate;

//////////////////////////////////////////////////////////////////////////
// Square free univariate root finder

function IntegralSquarefreeRoots(F)
  //Returns the integral roots of a square-free polynomial over a local field}
  R:=BaseRing(F);
  error if not ISA(Type(R),RngPad),
        "Polynomial should be over a local ring";
  if false and ISA(Type(R),RngPad) then
    return Roots(F:IsSquarefree);
  end if;
  pi:=UniformizingElement(R);
  F:=MyPrimitivePart(F);
  v:=MinPrec(F);
  if v eq 0 then
    error "insufficient precision to separate roots";
  end if;
  Rbar,red:=ResidueClassField(R);
  Fbar:=Polynomial(Rbar,[red(f):f in Eltseq(F)]);
  dF:=Derivative(F);
  dFbar:=Derivative(Fbar);

  //note that any root over the integer ring should reduce to a root over the
  //finite field. We take representatives of these.
  RootsApprox:=[(u[1])@@red:u in Roots(Fbar)];
  Result:=[];
  for x0 in RootsApprox do
  
    //if the derivative in reduction is non-zero, then the derivative
    //at x0 is a unit. We can now use newton approximation (very fast)
    if Evaluate(dFbar,red(x0)) ne 0 then
      x1:=x0;
      
      //repeat steps until value of polynomial at our root is
      //indistinguishable from 0. We can't do better than that.
      //also, this suggests that the precision in x1 is not exaggerated
      //provided that precision is kept track of properly.
      Delta:=-Evaluate(F,x1) div Evaluate(dF,x1);
      while RelativePrecision(Evaluate(F,x1)) gt 0 do
        Delta:=-Evaluate(F,x1) div Evaluate(dF,x1);
        x1:=x1+Delta;
      end while;
      
      //and store result.
      Append(~Result,<x1+O(pi^AbsolutePrecision(Delta)),1>);
     else
    
      //otherwise we have to look a bit closer. We take x0 as an approximation
      //and perturb with a polynomial variable. This is our new poly.
      G:=Evaluate(F,x0+UniformizingElement(R)*Parent(F).1);
      
      //of course, this polynomial has all of its coefficients 0 in reduction.
      //scalar multiplication does not change the roots, so just
      //scale down until things are visible in the finite field again.
      v:=MinPrec(G);
      assert v gt 0;
      //we determine the integral roots of that G and we transform them
      //back into roots for F. (Primitive Part of G is taken upon recursion
      //anyway, so we don't have to do that here.)
      Result cat:= [<x0+UniformizingElement(R)*z[1],1>:
                            z in IntegralSquarefreeRoots(G)];
    end if;
  end for;
  return Result;
end function;

intrinsic SquarefreeRoots(F::RngUPolElt)->SeqEnum
  {Depricated. Use Roots(F:IsSquarefree) instead.}
  K:=BaseRing(F);
  require ISA(Type(K),FldPad):
      "Base ring must be a local field";
  return Roots(F:IsSquarefree);
/*******************
  K:=BaseRing(F);
  require ISA(Type(K),FldPad):
      "Base ring must be a local field";
  //for the new ones, let's use the new code ...
  if true and ISA(Type(K),FldPad) then
    return Roots(F:IsSquarefree);
  end if;
  if Degree(F) eq 0 then
    return [];
  elif Degree(F) eq -1 then
    require F ne 0: "roots not well-defined for a zero polynomial";
    return [];
  end if;
  O:=IntegerRing(K);
  f:=Eltseq(F);
  L:=[v eq Infinity() select 10000 else v where v:=Valuation(fi):fi in f];
  n:=#f;
  //we transform x=u*z, so that F has only zeros for integral z.
  u:=UniformizingElement(K)^Minimum([Floor((L[i]-L[n])/(n-i)):i in [1..n-1]]);
  f:=Parent(F)![f[i]*u^(i-1):i in [1..n]];
  f:=PolynomialRing(O)!MyPrimitivePart(f);
  //How do we know when to stop lifting if our poly is precise?
  //We just set the precision on f to be the default precision.
  //This does not yield optimal results.
  if MinPrec(f) eq Infinity() then
    f:=FlattenPrecision(f+BigO(UniformizingElement(O)^O`DefaultPrecision));
  end if;
  //transform back
  return [<x[1]*u,x[2]> : x in IntegralSquarefreeRoots(f)];
********************/
end intrinsic;


intrinsic MyIsSquare(d::.)->BoolElt,.
    {More robust IsSquare function}
  R:=Parent(d);
  if (ISA(Type(R),RngPad) or ISA(Type(R),FldPad)) then
    return IsSquare(d);
  else  
    L:=SquarefreeRoots(ext<Parent(d)|>.1^2-d);
  end if;
  if #L eq 0 then
    return false,_;
  else
    return true,Parent(d)!L[1][1];
  end if;
end intrinsic;
