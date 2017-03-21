freeze;
declare verbose NEWTON, 4;
//NEWTON =4 turns on many checks which are expensive, but good for debugging purposes...


PolyMod:=function(f,M)
local M2, l;

  M2:=M div 2;
  l:=[x mod M: x in Coefficients(f)];
  l:=[(x gt M2) select x-M else x: x in l];
  return Parent(f) ! l;
end function;  

ComputeDenBound:=function(o)
/*Compute multiple of possisble denominators in Z[z] (including Z!!!)*/
local   L, d;

  d:=Discriminant(o);
  d:=PolynomialRing(Integers()) ! (PolynomialRing(Rationals()) ! d);
  L:=Factorization(d);
  L:=[x: x in L |x[2] gt 1];
  L:=[<x[1],x[2] div 2>: x in L];
  L:=[x[1]^x[2]: x in L];
  if #L eq 0 then return PolynomialRing(Integers()) ! 1;end if;
  return &*L;
end function;

TestResult1:=function(g, a, den)

  Z:=Integers();
  Zx:=RationalFunctionField(Rationals());
  Zxy:=PolynomialAlgebra(Zx);
  f:=Zxy ! DefiningPolynomial(Parent(a));
  R:=quo<Zxy|f>;
  b:=R ! Eltseq(a);
  b:=b/den;
  print Evaluate(g, b);
  return true;
end function;

TestResult:=function(g, a, M, limit, den)
local  ZM, b, gg, Qx, Qxy, res, L, nofrac;
  nofrac:=false; //Choose Algo
if nofrac then
  Qx:=RationalFunctionField(Rationals());
  Qxy:=PolynomialAlgebra(Qx);
  gg:=Qxy ! g;
  gg:=Evaluate(gg, Qxy.1/den)*den^Degree(g);
  gg:=Parent(g) ! gg;

  b:=a*den;
  res:=Evaluate(gg,b);
else
  res:=Evaluate(g,a);
end if;
  if res eq 0 then return true;end if;
  L:=Eltseq(res);
if nofrac then
  L:=[x*den: x in L];
end if; 
  L:=[FieldOfFractions(PolynomialAlgebra(Rationals())) ! x: x in L];
vprint NEWTON,2:"den ", [Denominator(x): x in L];
  L:=[Numerator(x):x in L];  
  ZM:=Integers(M);
  L:=[Polynomial(ZM,x):x in L];  
vprint NEWTON,2: "Zm-pol",L;
  L:=[Degree(x): x in L];

  vprint NEWTON,1:"Degrees of test: ",L;
  if Maximum(L) ge limit then return false; end if;
  
  return L;
end function;

/*b, w are alffo elts*/
intrinsic InternalNewtonLiftPowerSeries(g::RngUPolElt, b::RngFunOrdElt, w::RngFunOrdElt, limit::RngIntElt) -> BoolElt, FldFunElt
{Newton lifting}

local  eval2, exp,bound, test,tim, ev, Q, R, S, lim, f, lb, lw, Ztx, M, lden, p, ZM, gg, bb, ww, tmp, gd, M2, Zt, den2, den;


/*Init part*/
  Q:=Rationals();
  R:=Parent(g);
  S:=Parent(b);
  den:=PolynomialRing(Q) !ComputeDenBound(S);
  assert S cmpeq Parent(w);
  f:=DefiningPolynomial(S);
  f:=PolynomialRing(PolynomialRing(CoefficientRing(CoefficientRing(Parent(f))))) ! f;
  Ztx:=PolynomialRing(PolynomialRing(Integers()));
  f:=Ztx !f;

  lb:=Eltseq(b);
  lb:=[Q ! x: x in lb];
  bound:=Maximum([Abs(Numerator(x)): x in lb]);
  bound:=bound*Maximum([Abs(Denominator(x)): x in lb]);
  bound:=bound*10^20;
  lw:=Eltseq(w);
  lw:=[Q ! x: x in lw];
  lden:=Lcm([Denominator(x): x in (lb cat lw)]);
  p:=41;
  while lden mod p eq 0 do
    p:=NextPrime(p);
  end while;
  exp:=Round(Log(bound)/Log(p));
  M:=p^exp;  
  vprint NEWTON,1: "M= ", M,"  p=",p;

  while true do
   lb:=Eltseq(b);
   lb:=[Q ! x: x in lb];
   lw:=Eltseq(w);
   lw:=[Q ! x: x in lw];
   ZM:=Integers(M);
   lb := [ZM ! x: x in lb];
   lw := [ZM ! x: x in lw];

   ZMt<t>:=PuiseuxSeriesRing(ZM);
   ZMtx := PolynomialRing(ZMt); x := ZMtx.1;
   ff:=ZMtx ! f;
   gg:=PolynomialRing(PolynomialRing(CoefficientRing(CoefficientRing(Parent(g))))) ! g;
    gg:=Ztx !gg;

   gg:=ZMtx ! gg; 
   gd:=Derivative(gg);
   lb:=[elt<ZMt|0,[x],2>: x in lb];
   lw:=[elt<ZMt|0,[x],2>: x in lw];

   S<X>:=quo<ZMtx | ff>;
   bb:=S ! lb;
   ww:=S ! lw;
   lim :=1;

   while lim lt limit do
    lim:=Minimum(limit,lim*2);
    tim:=Cputime();
    vprint NEWTON,1:"Limit= ",lim;
    /*Update precision*/
    if lim gt 2 then
      vprint NEWTON,4: bb,"\n",[[Valuation(x),lim-Valuation(x)]: x in Eltseq(ww)];
      ww:= S ! [elt<ZMt|Valuation(x), Eltseq(x), lim-Valuation(x)> : x in Eltseq(ww)];
      bb:= S ! [elt<ZMt|Valuation(x), Eltseq(x), lim-Valuation(x)> : x in Eltseq(bb)];
    end if;
    vprint NEWTON,4: "beta =", bb;

    ev:=Evaluate(gg, bb);
    if GetVerbose("NEWTON") ge 4 then
       eval2:=[Valuation(y):  y in Coefficients(ev)];
       print eval2;
       if Minimum(eval2) lt (lim div 2) then
          error  "Wrong eval";
       end if; 
    end if;
    bb:= bb-ev*ww;

    vprint NEWTON,3: "beta =", bb;
    if lim eq limit then 
        vprint NEWTON,1: "Time: ",Cputime(tim);
        break; 
    end if;

    ev:=Evaluate(gd, bb);
    vprint NEWTON,4: "eval = ", ev*ww-1;
    ww:=ww*(( S ! 2)-ev*ww);
    vprint NEWTON,1: "Time: ",Cputime(tim);
    vprint NEWTON,3: "h =", ww;
   end while;
   Zt:=PolynomialRing(Integers());

   l:=[(Zt ! Eltseq(Truncate(x)))*Zt.1^Valuation(x): x in Eltseq(bb)];
   l:=[(x*(Zt! den)) mod Zt.1^limit: x in l];
   l:=[PolyMod(x,M): x in l];
   bb:=(Parent(b) ! l);

   bb:=FieldOfFractions(Parent(bb)) ! bb;
   bb:=bb/den;

vtime NEWTON,1:   test:=TestResult(g, bb, M, limit, den);
   if test cmpeq true then
     return true, bb;
   else if test cmpeq false then
    return false, _;
    end if;
   end if;
   M:=M*M;
   vprint NEWTON,1: "Update Precision: ", M;
  end while;
end intrinsic;
