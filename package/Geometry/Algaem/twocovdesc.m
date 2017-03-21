freeze;

/******************************************************************************
Code to compute fake two-selmer sets of hyperelliptic curves.

See Two-Cover descent on Hyperelliptic Curves by Nils Bruin and Michael Stoll
for a description of the algorithm.

 ******************************************************************************/

import "selmer.m" : IsFactorizationPrecisionError;


//intrinsic MakeSquareTest(Op::RngPad)->Map
//  {Create a square test returning -1 for non-square, 0 for possible square
//    and 1 for square (depending on available precision)}

function MakeSquareTest(Op)

  pi:=UniformizingElement(Op);
  resfld,toresfld:=ResidueClassField(Op);
 
  if (Prime(Op) eq 2) then
    sqr:={
      (&+[pi^(i-1)*(u[i]@@toresfld)+O(pi^(#u)) : i in [1..#u]])^2
      +O(pi^(Valuation(Op!4)+1))  :
           u in Flat(car<{u : u in resfld | u ne 0},
                      CartesianPower(resfld,Valuation(Op!2))>)};
    v4p1:=Valuation(Op!4)+1;
    pi:=pi+O(pi^(v4p1+1));
    function test(a)
      v:=Valuation(a);
      if v ge AbsolutePrecision(a) then
        return 0;
      elif (v mod 2) eq 0 then
        ar:=(a div (pi^v))+O(pi^(v4p1));
        if exists{sq: sq in sqr | RelativePrecision(ar-sq) eq 0} then
          if AbsolutePrecision(ar) ge v4p1 then
	    return 1;
	  else
	    return 0;
	  end if;
	else
	  return -1;
	end if;
      else
        return -1;
      end if;
    end function;
  else
    pi:=pi+O(pi^2);
    function test(a)
      v:=Valuation(a);
      if v ge AbsolutePrecision(a) then
        return 0;
      elif ((v mod 2) eq 0) and IsSquare(toresfld(a div (pi^v))) then
        return 1;
      else
        return -1;
      end if;
    end function;
  end if;    
  return map<Op->Integers()|a:->test(a)>;
end function;

function SqrComponents(f,sqrmap:Neighbourhood:=false,TargetSet:=false,R:={},slack:=0)

  if TargetSet cmpne false and TargetSet subset R then
    return R;
  end if;

  vprintf Selmer, 2: "SqrComponents for\n%o\n", f;

  Op:=BaseRing(Parent(f));
  fct,lc:=Factorisation(f:IsSquarefree);
  okay:=forall{g: g in fct | g[2] eq 1};
  fct:=[g[1]:g in fct];
  fct[1]:=lc*fct[1];
  fct:=[g: g in fct | Degree(g) eq 1] cat [g: g in fct | Degree(g) ne 1];

  okay and:=forall{a: a in Eltseq((&*fct)-f) | Valuation(a) gt Op`DefaultPrecision div 2};
  error if not okay, "Factorization is not accurate enough"; 
  // this error message must not be changed -- it is checked in try/catch in calling function(s)

  vprintf Selmer, 2: "Local factorization:\n%o\n", fct;
  
  pi:=UniformizingElement(Op);
  pi:=pi+O(pi);
  v4:=Valuation(Op!4)+slack;
  resfld,toresfld:=ResidueClassField(Op);
  resfldreps:={ u@@toresfld+O(pi): u in resfld };

  SquareTest:=MakeSquareTest(Op);

  // It is completely wrong to use Evaluate(f, x0+O(p^n)) when one wants
  // "the finest congruence class containing all the images f(x) for 
  // x in the congruence class x0+O(p^n)"
  // Evaluate1 does this, more or less.
  // Before this fix, the code traversed a massively-too-large portion
  // of the search tree.
  // -- SRD, October 2011
  y := PolynomialRing(Op).1;
  _pi:=UniformizingElement(Op);
  function Evaluate1(f, x);
    pr := Precision(x);
    xy := ChangePrecision(x, Precision(x) + Op`DefaultPrecision) + y*_pi^pr;
    ans := Evaluate(Evaluate(f, xy), O(Op!1));
    return ans;
  end function;

  function test(origin,gs,count,Rin)
    prc:=Precision(origin);
    origin:=elt<Op|origin,prc+1>;
    R:=Rin;
    for perturb in resfldreps do
      x:=origin+elt<Op|prc,perturb,prc+1>;
      fx:=Evaluate1(f,x);
      t:=SquareTest(fx);
      newcount:=count-1;
      if t ge 0 then
        gsn:=[g:g in gs | RelativePrecision(Evaluate1(g,x)) eq 0];
	if #gsn lt #gs then
	  newcount:=v4;
	end if;
        if #gsn eq 1 and 
	     Degree(gsn[1]) eq 1 and
	     newcount le 0 then
        elif #gsn eq 0 and t eq 1 and newcount le 0 then
	  img:=sqrmap(x);
	  Include(~R, img);
	  if TargetSet cmpne false and TargetSet subset R then
	    return R;
	  end if;
        else
	  R join:= $$(x,gsn,newcount,R);
	  if TargetSet cmpne false and TargetSet subset R then
	    return R;
	  end if;
	end if;
      else
      end if;
    end for;
    return R;
  end function;

  if Neighbourhood cmpeq false then
    Neighbourhood:= O(Op!1);
  else
    t:=SquareTest(Evaluate1(f,Neighbourhood));
    if t lt 0 then
      return R;
    end if;  
  end if;
  return test(Neighbourhood,fct,0,R);
end function;

intrinsic TwoCoverDescentInternal(
                          F::RngUPolElt:Bound:=-1,
                          Fields:=false,Algebra:=false,
			  PrimeBound:=0,PrimeCutoff:=0)
  -> SetEnum, Map, Map, SeqEnum
  {Performs a 2-cover descent on the given hyperelliptic curve}
  vprint Selmer:"Entering TwoCovWork with F =",F;
  x:=Parent(F).1;
  K:=BaseRing(Parent(F));
  if Algebra cmpne false then
    error if not(F/LeadingCoefficient(F) cmpeq Modulus(Algebra)),
      "Algebra must have modulus equal to F";
    A:=Algebra;theta:=A.1;
  else
    A<theta>:=quo<Parent(F)|F>;
  end if;

  if Type(K) eq FldRat then
    vprint Selmer:"Base change to Q as a numberfield";
    if not(assigned A`BaseChanged) then
      QNF:=NumberField(PolynomialRing(Rationals()).1-1:DoLinearExtension);
      FQ:=Polynomial(QNF,F);
      AQ<theta>:=quo<Parent(FQ)|FQ>;
      A`BaseChanged:=AQ;
    else
      AQ:=A`BaseChanged;
      QNF:=BaseRing(AQ);
      FQ:=Polynomial(QNF,F);
    end if;
    Deltas,toH1S,toVec,bU:=TwoCoverDescentInternal(FQ:
      Bound:=Bound,Fields:=Fields,Algebra:=A`BaseChanged,PrimeBound:=PrimeBound,
       PrimeCutoff:=PrimeCutoff);
    AtoAQ:=hom<A->AQ|AQ.1>;
    AQtoA:=hom<AQ->A|Coercion(QNF,Rationals())*Coercion(Rationals(),A),A.1>;
    iso:=map<A->AQ|a:->AtoAQ(a),b:->AQtoA(b)>;
    bU:=[a@@iso:a in bU];
    H1S:=Codomain(toH1S);
    
    if IsEven(Degree(F)) then
      function sqn(a)
	A:=Parent(a);
	Aa,toAa:=AbsoluteAlgebra(A);
	b:=toAa(a);
	N:=&*[&*[Integers()|Norm(P[1]): P in Factorisation(b[i]*IntegerRing(Aa[i]))| IsOdd(P[2])]:
	   i in [1..#b]];  
	return &*{Integers()|l[1]:l in Factorisation(N)}*a;
      end function;

      toH1S:=map<A->H1S|a:->toH1S(sqn(iso(a))),s:->PowerProduct(bU,Eltseq(toVec(s)))>;
    end if;
    return Deltas,toH1S,toVec,bU;
  end if;

  error if not(ISA(Type(K),FldAlg)),"Base ring must be a number field";
  OK:=IntegerRing(K);
  
  Dsc:=Discriminant(F);
  S:={LookupPrime(P):P in Support(Dsc*OK)|Valuation(Dsc,P) gt 1} join
     {LookupPrime(P): P in Support(2*LeadingCoefficient(F)*OK)} join
     {LookupPrime(P): P in Support(&*[Denominator(a):a in Eltseq(F)]*OK)};
  vprint Selmer:"Set of bad primes:",S;
  vprint Selmer:"Computing field decomposition of algebra";
  if Fields cmpne false then
    Aa,toAa:=AbsoluteAlgebra(A:Fields:=Fields);
  else
    Aa,toAa:=AbsoluteAlgebra(A);
  end if;

  univ:=cop<PowerStructure(FldOrd),
          PowerStructure(FldNum),
          PowerStructure(RngOrd)>;
  RelevantRings:=[univ|K];
  RelevantRings cat:=[univ|
                     Aa[i]: i in [1..NumberOfComponents(Aa)]];
  RelevantRings cat:=[univ|
                     IntegerRing(L): L in RelevantRings];

  if Bound ne -1 then
    vprint Selmer:"Computing class groups using Bound =",Bound;
    _:=[ClassGroup(IntegerRing(Aa[i]):Bound:=Bound):i in [1..NumberOfComponents(Aa)]];
  end if;

  vprint Selmer:"Computing A(2,S)";      
  H,toH1S,toVec,bU:=pSelmerGroup(A,2,S:Raw);
  vprintf Selmer:"A(2,S)=(Z/2Z)^%m\n",Ngens(H);
  bU:=Eltseq(bU);
  slmK,toslmK:=pSelmerGroup(2,S);
  
  if IsEven(Degree(F)) then
    H1S,qm:=quo<H|[toH1S(A!(a@@toslmK)):a in OrderedGenerators(slmK)]>;
    toH1S:=toH1S*qm;
    toVec:=Inverse(qm)*toVec;
  else
    H1S:=H;
  end if;
  
  NbU:=[Norm(b):b in bU];
  H1norm:=hom<H1S->slmK|
    [toslmK(PowerProduct(NbU,[c mod 2:c in Eltseq(toVec(g))])):
                                   g in OrderedGenerators(H1S)]>;
  lc:=toslmK(LeadingCoefficient(F));
  if lc in Image(H1norm) then
    LC:=lc@@H1norm;
    deltas:={LC+delta:delta in Kernel(H1norm)};
    vprint Selmer:"After Norm criterion, #deltas <=",#deltas;
  else
    deltas:={};
    vprint Selmer:"Norm criterion rules out any deltas";
    return deltas,toH1S,toVec,bU;
  end if;

/*****************
The following piece of code warrants some explanation. We let lp loop through
the real embeddings e:K->RealField, i.e., the different ways in which we can
consider f(x) in RealField[x]. Let's denote this embedding by F(x).

For each such embedding we compute the real extensions of pl to A.
Each such extension ei corresponds to a real root ri of F(x).

We can now say something about the image of C(k) under the map

(x,y) :-> x-theta :-> (...,Sign(ei(x-theta)),...)=(...,e(x)-

We know that the map is constant away from ei(x-theta)=0 . Therefore, we sample
the map (...,Sign(ei(u)),...) by computing
(...,Sign(rj+eps-ri),...) for j=1,2,... Implicitly, this works out the
ordering between the roots ri, and therefore captures the dependencies between
the signs: if r1>r2, then x-r1 can never be positive if x-r2 is negative.

For even degree f, note that our map is only defined up to multiplication by -1,
i.e., the sign vector (+1,...,+1) is really the same as the sign vector
(-1,...,-1).

For odd degree f, this is not the case. The description above never gives the
sign vector (-1,...,-1) because we sample in rj+eps, for a positive eps.
However, this vector can occur and in this case is not equivalent to a vector
we have already encountered elsewhere. Hence, we add this vector separately.

Finally, the leading coefficient of F determines which sign vector we need. If
it is positive, we need an even number of -1's. If it is negative, we need an
odd number.

Note that in the code below, signs are written additively, so 1 for negative and
0 for positive.
******************/

  for pl in [p: p in InfinitePlaces(K) | IsReal(p)] do
    vprint Selmer:"Looking at",pl;

    emb:=RealExtensions(A,pl);
    rts:=[e(A.1):e in emb];

    RH1:=AbelianGroup([2:i in rts]);
    AtoRH1:=map<A->RH1|
      a:->RH1![Real(cnj(a)) gt 0 select 0 else 1: cnj in emb]>;
    if #rts eq 0 then
      L:=sub<RH1|Identity(RH1)>;
    else
      if #rts eq 1 then
        L:=[[0],[1]];  // can only happen if Degree(f) is odd. only 2 possibilities
      else
        eps:=Minimum([Abs(rts[i]-rts[j]): i,j in [1..#rts] | i lt j])/1000;
        L:=[[ rt+eps gt r select 0 else 1 :r in rts]:rt in rts];
	if IsOdd(Degree(F)) then
	  Append(~L,[1:rt in rts]);
	end if;
      end if;
      if Evaluate(LeadingCoefficient(F),pl) gt 0 then
        L:={RH1!l: l in L| IsEven(#[c: c in l | c eq 1])};
      else
        L:={RH1!l: l in L| IsOdd(#[c: c in l | c eq 1])};
      end if;
      if IsEven(Degree(F)) then
        quot,toquot:=quo<RH1|AtoRH1(A!-1)>;
        L:={toquot(l):l in L};
	RH1:=quot;
	AtoRH1:=AtoRH1*toquot;
      end if;
    end if;

    embU:=[AtoRH1(u):u in bU];
    H1StoRH1:=hom<H1S->RH1|
       [&+[(v[i] mod 2)*embU[i]: i in [1..#v]]
              where v:=Eltseq(toVec(a)):a in OrderedGenerators(H1S)]>;
    deltas:={delta:delta in deltas| H1StoRH1(delta) in L};
    vprint Selmer:"Now, #deltas <=",#deltas;
    if #deltas eq 0 then
      vprint Selmer:"No deltas left. Shortcut return.";
      return deltas,toH1S,toVec,bU;
    end if;
  end for;
  
  if PrimeCutoff gt 0 then
    PrimeBound:=Minimum(PrimeBound,PrimeCutoff);
  end if;
  GoodPrimes:=&join[{P:P in Support(p*OK)| Norm(P) le PrimeBound}:
                               p in [1..PrimeBound]| IsPrime(p)];
  Primes:=Sort(Setseq(
                      (PrimeCutoff gt 0 select 
	                {P: P in S| Norm(P) lt PrimeCutoff} else S) join
                       GoodPrimes),
	       func<a,b|Norm(a)-Norm(b)>);
    
  for P in Primes do

    vprint Selmer:"Considering prime",P;

    epsilon:=1/5;

    prc:=(IsEven(Norm(P))) select 50 else 20;

    degF := Degree(F) + (IsEven(Degree(F)) select 0 else 1);
    Fr := Parent(F)![Coefficient(F,degF-i) : i in [0..degF]];

    repeat
      if prc ge 10000 then
        print "WARNING: very large p-adic precision seems to be needed (or there is a bug)";
      end if;

      KP,toKP:=MyCompletion(P:Precision:=prc);
      FP:=Polynomial([toKP(a):a in Coefficients(F)]);

      okay:=true;
      try
        vprintf Selmer, 3: "Factoring f with precision %o...\n", prc;
        fct:=[f[1]/LeadingCoefficient(f[1]):f in Factorization(FP:IsSquarefree)];
        vprintf Selmer, 3: "Factoring reverse f with precision %o...\n", prc;
        FPr := Polynomial([toKP(a):a in Coefficients(Fr)]);
        fctr := [f[1]/LeadingCoefficient(f[1]):f in Factorization(FPr:IsSquarefree)];
      catch ERR
        assert "Insufficient precision" in ERR`Object;
        okay:=false;
      end try;
      if okay then
        fct:=[Polynomial([K|c@@toKP:c in Coefficients(f)]):f in fct];
        okay := forall{c : c in Coefficients(LeadingCoefficient(F)*&*fct - F) | 
                           Valuation(c,P) gt prc-100};
      end if;
      if okay then
        fctr:=[Polynomial([K|c@@toKP:c in Coefficients(f)]):f in fctr];
        okay := forall{c : c in Coefficients(LeadingCoefficient(Fr)*&*fctr - Fr) |
                           Valuation(c,P) gt prc-100};
      end if;
      if not okay then
        prc*:=2;
        continue;
      end if;

      trueimgs:={};

      tolslm,recs:=LocalTwoSelmerMap(A,P);
      assert #fct eq #recs;
      //the tentative image under mu of these factors ...
      imgs:=[toAa((-1)^Degree(h)*Evaluate(h,theta)): h in fct];
      trueimgs:={};
      for l in [1..#recs] do
        im:=imgs[l];
        vls:=[ExtendedReals()|Valuation(im[recs[j]`i],recs[j]`p):j in [1..#recs]];
        okay:=forall{v:v in vls|v lt epsilon*prc or v gt (1-epsilon)*prc}
              and #{v: v in vls| v gt (1-epsilon)*prc} eq 1;
        if not okay then
          prc*:=2;
          break l;
        end if;
        _:=exists(j){j: j in [1..#recs]| vls[j] gt (1-epsilon)*prc};
        if Degree(fct[l]) eq 1 then
          Include(~trueimgs,
             Codomain(tolslm)!&cat[
               Eltseq(recs[k]`map(
                    (k eq j) select ((-1)^(Degree(F)-1)*toAa(LeadingCoefficient(F))[recs[j]`i])^1*
                         &*[Aa[recs[j]`i]|imgs[m][recs[j]`i]:m in [1..#recs]|m ne l]
                    else
                       im[recs[k]`i])):
               k in [1..#recs]]);
        end if;
      end for;
      if not okay then
        prc*:=2;
        continue;
      end if;

      if IsEven(Degree(F)) then
        mp:=LocalTwoSelmerMap(P);
        _,qm:=quo<Codomain(tolslm)|
           [tolslm(A!(g@@mp)): g in OrderedGenerators(Codomain(mp))]>;
        tolslm:=tolslm*qm;
        trueimgs:={qm(a):a in trueimgs};
      end if;
      if IsOdd(Degree(F)) then
        Include(~trueimgs, tolslm(A!LeadingCoefficient(F)));
      end if; 

      OP:=IntegerRing(KP);
      L:=[toKP(a): a in Eltseq(F)];
      m:=Minimum([Valuation(c):c in L]);
      L:=[OP|s*c:c in L] where s:=UniformizingElement(KP)^(-(m div 2)*2);
      fp:=Polynomial(L);

      lbU:=[tolslm(b):b in bU];
      Lmap:=hom<H1S->Codomain(tolslm)| [
           &+[v[i]*lbU[i]: i in [1..#v]]
         where v:=Eltseq(toVec(a)): a in OrderedGenerators(H1S)]>;

      target:={Lmap(delta):delta in deltas};
      sqrmap:=func<x|tolslm(K!(x@@toKP)-theta)>;

      try
        LocalDeltas:=SqrComponents(Polynomial(L),sqrmap:TargetSet:=target,R:=trueimgs);
        L:=L cat [OP|0 : i in [1..(Degree(F) mod 2)]];
        if RelativePrecision(L[1]) eq 0 then
          L:=L[2..#L];
        end if;
        sqrmap:=func<x|RelativePrecision(x) eq 0 select 
                                       tolslm(A!LeadingCoefficient(F)) else
                                       tolslm((K!(1/x)@@toKP)-theta)>;
        LocalDeltas join:=SqrComponents(Polynomial(Reverse(L)),sqrmap:
                     Neighbourhood:=O(UniformizingElement(OP)),
                     TargetSet:=target,
                     R:=LocalDeltas);
      catch ERR
        if IsFactorizationPrecisionError(ERR) then
          okay:=false;
        else
          error ERR;
        end if;
      end try;
      if not okay then
        prc*:=2;
        continue;
      end if;

    until true;

    deltas:={delta:delta in deltas| Lmap(delta) in LocalDeltas};

    vprint Selmer:"Now, #deltas <=",#deltas;
    if #deltas eq 0 then
      vprint Selmer:"No deltas left. Shortcut return.";
      return deltas,toH1S,toVec,bU;
    end if;
  end for;
  vprint Selmer:"Returning from TwoCovWork";
  return deltas,toH1S,toVec,bU;
end intrinsic;  

intrinsic TwoCoverDescent(C::CrvHyp:
     Bound:=-1,Fields:=false,Raw:=false,PrimeBound:=0,PrimeCutoff:=0)
  -> SetEnum, Map, Map, SeqEnum
  {"} // "
  require ISA(Type(BaseRing(C)),FldAlg) or Type(BaseRing(C)) eq FldRat:
    "Curve must be defined over Q or a number field";
  f,h:=HyperellipticPolynomials(C);
  F:=f+h^2/4;

  if assigned C`Algebra then
    Algebra:=C`Algebra;
  else
    Algebra:=false;
  end if;
  if PrimeBound eq 0 then
    g:=Genus(C);
    gD:=2^(2*g)*(g-1)+1;
    PrimeBound:=(4*gD^2-2);
  end if;
  deltas,toH1S,toVec,bU:=TwoCoverDescentInternal(F:
        Bound:=Bound,Fields:=Fields,Algebra:=Algebra,PrimeBound:=PrimeBound,
	PrimeCutoff:=PrimeCutoff);
  C`Algebra:=Domain(toH1S);
  if Raw then
    return deltas,toH1S,toVec,bU;
  else
    return deltas,toH1S;
  end if;
end intrinsic;
