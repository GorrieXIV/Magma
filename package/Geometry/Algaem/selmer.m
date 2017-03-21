freeze;

/******************************************************************************
 *
 * selmer.m
 *
 * date:   23/12/2003
 * author: Nils Bruin
 *
 * Fast routines to compute 2-Selmer groups of elliptic curves and hyperelliptic
 * jacobians and 2-isogeny Selmer groups of elliptic curves.
 *
 ******************************************************************************/

 /************************************

     CHANGE LOG
     ----------    


     2011-06, Brendan:
	+ Fixed computation of the local dimensions of J[2] in the case of 
	  odd genus and even degree.
	+ Increased default precision for local image computations (depending
	  on the valuation of the leading coefficient). Still not neccessarily
	  rigorous though...

     2011-06, Steve:

          Some revisions to the search for local points.  In particular,
          implemented some of my tricks for number fields as well as Q.
          Switched on IOD2 for all curves over Q (was only monic degree 3;
          incidentally, in the previous version, if IOD2 had been used for
          non-monic F, it have produced wrong local images because oddimg 
          was not used).

          I'm doing substantial testing (of correctness) after these revisions.

     2010-11, Nils:
     
        + Major rewrite of TwoSelmWork.

     2008-02, Mark: change Hints (GetHints2DescentNils became GetHintsEC)

     2007-10, Steve:
        
        + Store E`TwoSelmerGroup = <S,StoE,blah,blah,blah>

     2006-12, Steve:

        + Altered MuMap so that it will increase its p-adic precision when necessary 
          (to deal with Christian Wuthrich's examples with fields highly ramified at 2).
          Eg: E := EllipticCurve(CremonaDatabase(),14,1,1);
              F := NumberField(x^8 + 14*x^7 + 70*x^6 + 182*x^5 + 476*x^4 + 1050*x^3 
                               + 546*x^2 + 134*x + 7);

        + Reduced the precision used for GetHints2DescentNils, since evaluating toKP 
          when K has degree 8 seems very slow for precision above 100 or so.
          
          Comment from Nils: The Hints infrastructure is really only there so that
          a user can employ smart p-adic search techniques and provide hard to find
          local points (once you're over, say, a degree 12 field, you'll start to notice
          that this is quite valuable). The fact that hints found at one prime get used
          at other primes as well is only a side-effect from the implementation and
          not very likely to be of much value. On the other hand, it's still a reasonable
          random try, so it shouldn't really hurt much.
          
     2006-1, Steve:

        Changes to the search for local points on the Jacobian:
         + Changed MakeTry to avoid errors from HasRoots ("not enough precision").
         + Reinstated the degree 2 case, which is needed, even for y^2 = x^5 - 2.
         + Added my usual safety check: find a few extra points, 
           and check that the dimension is still not larger than it should be.
         + If the Selmer group is found to be trivial after imposing only
           some of the local conditions, don't bother working out the others.
           Also, leave the condition at 2 until later, since this is sometimes
           troublesome.
        Comment: 
           Better local point finding is on the agenda.
           At the moment, the aim is to succeed eventually 
           (although sometimes not efficiently) for every curve of genus 2 
           given by a minimal model.
           This seems to be the case over Q, according to the testing I've done.

                                         ****************************************/

declare verbose Selmer, 4;

declare attributes RngUPolRes:Helpful,BaseChanged;
declare attributes Map:Algebra,SelmerTuple;
declare attributes CrvEll:Algebra,TwoSelmerGroup; // TwoSelmerGroup = <S,StoE> = <GrpAb,Map>
declare attributes JacHyp:Algebra;
declare attributes CrvHyp:Algebra;

import "../CrvEll/FourDesc/hints.m":GetHintsEC;
import "resolvent.m":degnres;
import "../Arith/loctools.m":pAdicEvaluate;

import "twocovdesc.m":SqrComponents;

/***********************************************************************************
 Processing precision errors from p-adic Roots and Factorization
 ***********************************************************************************/

//Since the returned string has unpredictable linebreaks and spaces in it,
//remove all non-alphabetic characters from either string and compare those.

alphabetic_characters:={CodeToString(c): c in {StringToCode("A")..StringToCode("Z")} 
                                         join {StringToCode("a")..StringToCode("z")}};
function squash(s)
   return &cat[a : a in Eltseq(s) | a in alphabetic_characters];
end function;

FactorizationErrorMessages:={
   squash("Runtime error in 'LocalFactorization': Factorization: "*
          "Insufficient precision in factorization of a non-squarefree polynomial"),
   squash("Factorization: Something went wrong when trying to factor a non-monic Polynomial"),
   squash("Factorization is not accurate enough")
};

RootFindingErrorMessage:=
   squash("Runtime error in 'Roots': Insufficient precision to find roots");

function IsFactorizationPrecisionError(ERR)
   return squash(ERR`Object) in FactorizationErrorMessages;
end function;

function IsRootFindingPrecisionError(ERR)
   return squash(ERR`Object) eq RootFindingErrorMessage;
end function;

/******************************************************************************
 Predicate to test if an isogeny is multiplication by 2.
 ******************************************************************************/

function IsogenyIsMultiplicationByTwo(phi)
//  {tests if an isogeny of elliptic curves is multiplication by 2}
  return (Domain(phi) cmpeq Codomain(phi)) and
         (IsogenyMapPsi(phi) eq f+h^2/4 where
                f,h:=HyperellipticPolynomials(Codomain(phi)));
end function;

/******************************************************************************
 Workhorse for 2-isogeny descent. F and Fd should be monic quadratics. Hints
 should contain a list for x-coordinates that give rise to useful (local)
 points.

 return values:
 
 SF      - 2-isogeny Selmer group of isogeny to y^2=x*F
 SFd     - 2-isogeny Selmer group of isogeny to y^2=x*Fd
 toK2S   - Map K -> K(2,S), to the ambient group of SF and SFd
 Helpful - Complete set of hints
 toVec   - Map K(2,S) -> {exponent vectors}
 bU      - Basis in K^* for exponent vectors.

 ******************************************************************************/

function TwoIsogWork(F,Fd,Hints)
  //Does a 2-isogeny descent on y^2=x*F and y^2=x*Fd;
  //these curves should be 2-isogenous.
  vprint Selmer:"Entering TwoIsogWork with [F,Fd] =",[F,Fd];

  K:=BaseRing(F);

  assert BaseRing(F) eq BaseRing(Fd);
  assert IsMonic(F) and IsMonic(Fd) and Degree(F) eq 2 and Degree(Fd) eq 2;

  if Type(K) eq FldRat then
    vprint Selmer:"Base change to Q as a number field";
    QNF:=NumberField(PolynomialRing(Rationals()).1-1:DoLinearExtension);
    F:=Polynomial(QNF,F);
    Fd:=Polynomial(QNF,Fd);
    Hints:=ChangeUniverse(Hints,QNF);
    SF, SFd,toK2S,Useful,toVec,bU:=TwoIsogWork(F,Fd,Hints);
    bU:=[Rationals()!a:a in bU];
    toK2S:=map<Rationals()->Codomain(toK2S)|a:->toK2S(QNF!a),
                                       s:->PowerProduct(bU,Eltseq(toVec(s)))>;
    Useful:={Rationals()|Rationals()!a:a in Useful};
    return SF, SFd,toK2S,Useful,toVec,bU;
  end if;

  OK:=IntegerRing(K);

  x:=Parent(F).1;
  B,A:=Explode(Eltseq(F));
  Bd,Ad:=Explode(Eltseq(Fd));
  Dsc:=Discriminant(x*F)*Discriminant(x*Fd);
  S:={LookupPrime(P):P in Support(Dsc*OK)|Valuation(Dsc,P) gt 1} join
     {LookupPrime(P): P in Support(2*OK)} join
     {LookupPrime(P): P in Support(&*[Denominator(a):
                               a in Eltseq(F)cat Eltseq(Fd)]*OK)};
  vprint Selmer:"Bad primes:",S;
  vprint Selmer:"Computing K(2,S)";
  K2S,toK2S,toVec,bU:=pSelmerGroup(2,S:Raw);
  vprintf Selmer:"Found K(2,S)=(Z/2Z)^%o\n",Ngens(K2S);
  bU:=Eltseq(bU);
  SF:=K2S;SFd:=K2S;
  vprint Selmer:
    "A priori rank bounds on Selmer groups",[Ngens(SF),Ngens(SFd)];
  for i in [1..Signature(OK)] do
    C:=Sign(Real(Conjugate(A^2-4*B,i))) lt 0 or
        ( Sign(Real(Conjugate(A,i))) lt 0 and
	  Sign(Real(Conjugate(A^2-(A^2-4*B),i))) gt 0);
    Cd:=Sign(Real(Conjugate(Ad^2-4*Bd,i))) lt 0 or
        ( Sign(Real(Conjugate(Ad,i))) lt 0 and
	  Sign(Real(Conjugate(Ad^2-(Ad^2-4*Bd),i))) gt 0);
    if C or Cd then
      gp:=AbelianGroup([2]);
      w:=[Real(Conjugate(b,i)) lt 0 select gp.1 else gp!0: b in bU];
      Krn:=Kernel(hom<K2S->gp|[&+[v[i]*w[i]: i in [1..#w]] where v:=toVec(g):
                                       g in OrderedGenerators(K2S)]>);
      if C then
        SF:=SF meet Krn;
      end if;
      if Cd then
        SFd:=SFd meet Krn;
      end if;
    end if;
    vprint Selmer:
      "After real embedding",i,"rank bounds are:",[Ngens(SF),Ngens(SFd)];
  end for;
  Helpful:={K|};
  for P in S do
    vprint Selmer:"Determining local Selmer groups at",P;
    toKp2:=LocalTwoSelmerMap(P);
    Kp2:=Codomain(toKp2);
    TotalExpectedRank:=(2+InertiaDegree(P)*Valuation(K!2,P));
    vprint Selmer:"  Total local rank:",TotalExpectedRank;
    KP,toKP:=MyCompletion(P);
    KPDP:=KP`DefaultPrecision;
    while true do
      try 
        FP:=[K|(r[1])@@toKP:r in Roots(Polynomial(KP,[toKP(a):a in Eltseq(F)]))];
        FPd:=[K|(r[1])@@toKP:r in Roots(Polynomial(KP,[toKP(a):a in Eltseq(Fd)]))];
        no_error:=true;
      catch ERR
        if IsRootFindingPrecisionError(ERR) then
          no_error:=false;
        else
          error ERR;
        end if;
      end try;
      if no_error then break; end if; //break from while if no error was raised
      KP`DefaultPrecision +:= 10;
      vprint Selmer, 3: "TwoIsogWork: increasing precision to", KP`DefaultPrecision;
    end while;
    KP`DefaultPrecision:=KPDP;
    SFp:=sub<Kp2|[toKp2(b): b in [B] cat FP]>;
    SFpd:=sub<Kp2|[toKp2(b): b in [Bd] cat FPd]>;
    vprint Selmer:"  Ranks due to 2-torsion:",[Ngens(SFp),Ngens(SFpd)];
    KP,toKP:=MyCompletion(P);
    pi:=SafeUniformiser(P);
    for h in Hints do
      C:=h ne 0 and IsSquare(toKP(h*Evaluate(F,h)));
      Cd:=h ne 0 and IsSquare(toKP(h*Evaluate(Fd,h)));
      if Cd or C then
        u:=toKp2(h);
        if C and u notin SFp then
          SFp:=sub<Kp2|[u] cat OrderedGenerators(SFp)>;
          vprint Selmer,2:"Adding hint",h,"to local selmer group. Ranks:",
               [Ngens(SFp),Ngens(SFpd)];
          Helpful join:={h};
        end if;
        if Cd and u notin SFpd then
          SFpd:=sub<Kp2|[u] cat OrderedGenerators(SFpd)>;
          vprint Selmer,2:"Adding hint",h,"to dual local selmer group. Ranks:",
               [Ngens(SFp),Ngens(SFpd)];          
          Helpful join:={h};
        end if;
      end if;
    end for;
    vprint Selmer:"Ranks due to hints:",[Ngens(SFp),Ngens(SFpd)];

    Bnd:=Minimum(P)^(4*Valuation(K!4,P)+2);      
    Bnd+:=100; // SRD, April 2008 -- not sure why one would take such a precisely computed 
               // value for the Bnd; anyway it seems the argument here must have been wrong, 
               // since this failed to find points for EllipticCurve([0,164,0,1,0])
    while Ngens(SFp)+Ngens(SFpd) lt TotalExpectedRank do
      h:=K!(Random(OK,Bnd)*pi^Random([-8..8]));
      C:=h ne 0 and IsSquare(toKP(h*Evaluate(F,h)));
      Cd:=h ne 0 and IsSquare(toKP(h*Evaluate(Fd,h)));
      if Cd or C then
        u:=toKp2(h);
        if C and u notin SFp then
          SFp:=sub<Kp2|[u] cat OrderedGenerators(SFp)>;
          vprint Selmer,2:"Adding ",h,"to local selmer group. Ranks:",
               [Ngens(SFp),Ngens(SFpd)];
          Helpful join:={h};          
        end if;
        if Cd and u notin SFpd then
          SFpd:=sub<Kp2|[u] cat OrderedGenerators(SFpd)>;
          vprint Selmer,2:"Adding ",h,"to dual local selmer group. Ranks:",
               [Ngens(SFp),Ngens(SFpd)];          
          Helpful join:={h};
        end if;
      end if;
    end while;
    vprint Selmer:"Found local ranks:",[Ngens(SFp),Ngens(SFpd)];
    
    w:=[toKp2(u): u in bU];
    hm:=hom<K2S->Kp2|[&+[v[i]*w[i]: i in [1..#w]] where v:=toVec(g):
                                       g in OrderedGenerators(K2S)]>;
    qt,quomap:=quo<Kp2|SFp>;
    Krn:=Kernel(hom<K2S->qt|[quomap(hm(g)):g in OrderedGenerators(K2S)]>);
    SF:=SF meet Krn;
    qt,quomap:=quo<Kp2|SFpd>;
    Krn:=Kernel(hom<K2S->qt|[quomap(hm(g)):g in OrderedGenerators(K2S)]>);
    SFd:=SFd meet Krn;
    vprint Selmer:"Ranks for global Selmer groups:",[Ngens(SF),Ngens(SFd)];
  end for;
  vprint Selmer:"Returning from TwoIsogWork";
  return SF, SFd,toK2S,Helpful,toVec,bU;
end function;

/******************************************************************************
 Workhorse for full 2 descent. F should be monic of odd degree.

 Bound   - If positive, used instead of Minkowski bound
 Fields  - Set of fields to be used in AbsoluteAlgebra
 Hints   - Set of possibly useful points in local computations
 Algebra - If given, should be quo<Parent(F)|F>. Then used.

 return values:

 H1S
 toH1S
 toVec
 bU
 Helpful
 
 SF      - 2-isogeny Selmer group of isogeny to y^2=x*F
 SFd     - 2-isogeny Selmer group of isogeny to y^2=x*Fd
 toK2S   - Map K -> K(2,S), to the ambient group of SF and SFd
 Helpful - Complete set of hints
 toVec   - Map K(2,S) -> {exponent vectors}
 bU      - Basis in K^* for exponent vectors.

 ******************************************************************************/

//function that does the actual two selmer group computation

function TwoSelmWork(F:Bound:=-1,Fields:=false,Hints:={},Algebra:=false,
                                                                  res:=false)
// F: the polynomial of the hyperelliptic curve y^2=F(x) for the Jacobian
// Bound: Class group bound to be used
// Fields: A set of fields used by Absolute Algebra. Mainly useful if
//         they already contain class group information. FldOrd is also
//	   an allowed type!
// Hints: An optional list of hints (polynomials in x describing
//         x-support of divisors over local fields.)
// Algebra: Optionally the algebra to be used in the descent
// res:   The resultant to check if F is the product of two conjugate poly-
//        nomials. Currently, the resolvent can be computed
//        if the base ring is Q. Otherwise, a resolvent should be precomputed.
							  
  vprint Selmer:"Entering TwoSelmWork with F =",F;
  x:=Parent(F).1;
  K:=BaseRing(Parent(F));
  fctF:=[f[1]: f in Factorisation(F)];
  dscF:=Discriminant(F);
  lcF:=LeadingCoefficient(F);
  F_is_elliptic_curve:=(Degree(F) eq 3) and (lcF eq 1);
  
//Parsing of optional parameters
 
  if Algebra cmpne false then
    error if not(F/lcF cmpeq Modulus(Algebra)),
      "Algebra must have modulus equal to F";
    A:=Algebra;theta:=A.1;
  else
    A<theta>:=quo<Parent(F)|F/lcF>;
  end if;

  if #Hints gt 0 and Universe(Hints) cmpne PolynomialRing(K) then
    Hints:={x-a:a in Hints};
  end if;

  //error if not(ISA(Type(K),FldAlg)),"Base ring must be a number field";
  OK:=IntegerRing(K);

//Compute the set of bad primes
//*NOTE* Primes are sent through "LookupPrime", which looks up cached
//prime ideals on their order, so that we have access to possible
//attributes on the ideals. IS THIS STILL A GOOD IDEA??

  if Type(BaseRing(F)) eq FldRat then
    S:={c[1] : c in Factorisation(4*Numerator(dscF))| c[2] ge 2} join
       {c[1] : c in Factorisation(&*[Denominator(a): a in Eltseq(F)])} join
       //BMC: Leading Coefficient is pretty important too!
       // e.g.
       // f := -10*T^5 + 3*T^3 - 4*T^2 - 9*T;
       // g := T^5 - 30*T^3 - 400*T^2 + 9000*T;
       // define isomorphic hyperelliptic curves, and omitting the lcf
       // leads to different answers for the Selmer group
       {c[1] : c in Factorisation(Numerator(LeadingCoefficient(F)))};
  else
    S:={LookupPrime(P[1]):P in Factorisation(4*dscF*OK)| P[2] ge 2} join
       {LookupPrime(P): P in Support(&*[Denominator(a):a in Eltseq(F)]*OK)} join
       {LookupPrime(P): P in Support(LeadingCoefficient(F)*OK)};
  end if;
  vprint Selmer:"Set of bad primes:",S;

//Decomposition of algebra.

  vprint Selmer:"Computing field decomposition of algebra";
  if Fields cmpne false then
    Aa,toAa:=AbsoluteAlgebra(A:Fields:=Fields);
  else
    Aa,toAa:=AbsoluteAlgebra(A);
  end if;

//Make sure class group information is available to the desired level.
//Given the new infrastructure for controlling the desired level of
//rigour in class group computations globally, it is conceivable to
//delete the Bound parameter altogether.

  if Bound ne -1 then
    vprint Selmer:"Computing class groups using Bound =",Bound;
    vtime Selmer:
    _:=[ClassGroup(IntegerRing(Aa[i]):Bound:=Bound):i in [1..NumberOfComponents(Aa)]];
  end if;

//Compute the appropriate ambient group for the selmer group.
//this is the p-selmer group of the algebra, modulo some case-dependent
//modifications.

  vprint Selmer:"Computing A(2,S)";      
  vtime Selmer:
  H,toH1S,toVec,bU:=pSelmerGroup(A,2,S:Raw);
  vprintf Selmer:"A(2,S)=(Z/2Z)^%m\n",Ngens(H);
  bU:=Eltseq(bU);
  H1S:=H;

//In the even degree case, we need to quotient out by scalars, so we quotient
//out the p-selmer group by the image of the scalars.
//Note that we currently neglect to use "pselmergroup" on the ground field
//in "raw" mode, so we work with actual representatives rather than the factor basis.
//(for one, the factor basis would not necessarily get mapped into H1S)

  vprint Selmer:"Computing K(2,S)";      
  vtime Selmer:
  slmK,toslmK:=pSelmerGroup(2,S);
  if IsEven(Degree(F)) then
    H1S,qm:=quo<H|[toH1S(A!(a@@toslmK)):a in OrderedGenerators(slmK)]>;
    toH1S:=toH1S*qm;
    toVec:=Inverse(qm)*toVec;
  else
    H1S:=H;
  end if;

//Compute the norm map on the 2-selmer group. Currently we do this by
//computing norms of the factor basis and take the appropriate product
//according to the exponent vectors. Since we can reduce the exponent vectors
//mod 2, this will not be terrible. However, using Tom's really small representatives
//might even be better.

  NbU:=[Norm(b):b in bU];
  H1norm:=hom<H1S->slmK|
    [toslmK(PowerProduct(NbU,[c mod 2:c in Eltseq(toVec(g))])):
                                   g in OrderedGenerators(H1S)]>;
  H1S:=Kernel(H1norm);
  vprint Selmer:"Bound on Selmer group after Norm criterion:",Ngens(H1S);

//Deal with the real places of K one by one.

  for pl in [p: p in InfinitePlaces(K) | Type(p) eq Infty or IsReal(p)] do
    vprint Selmer:"Looking at",pl;

    emb:=RealExtensions(A,pl);
    rts:=[e(A.1):e in emb];

    RH1:=AbelianGroup([2:i in rts]);
    AtoRH1:=map<A->RH1|
      a:->RH1![Real(cnj(a)) gt 0 select 0 else 1: cnj in emb]>;
    if #rts eq 0 then
      Rimg:=sub<RH1|Identity(RH1)>;
    else
      if #rts eq 1 then
        L:=[[1]];
      else
	eps:=Minimum([Abs(rts[i]-rts[j]): i,j in [1..#rts] | i lt j])/1000;
	L:=[[ rt+eps gt r select 0 else 1 :r in rts]:rt in rts];
      end if;
      if Real(emb[1](A!lcF)) gt 0 then
        L:=[RH1!l: l in L| IsEven(#[c: c in l | c eq 1])];
      else
        L:=[RH1!l: l in L| IsOdd(#[c: c in l | c eq 1])];
      end if;
      if IsOdd(Degree(F)) then
        Append(~L,AtoRH1(lcF));
      end if;
      L:=[l-L[1]:l in L];
      if IsEven(Degree(F)) then
        Append(~L,RH1![1:i in [1..#rts]]);
      end if;

      Rimg:=sub<RH1| [l:l in L]>;
      
    end if;

    quot,toquot:=quo<RH1|Rimg>;
    embU:=[toquot(AtoRH1(u)):u in bU];
    H1Stoquot:=hom<H1S->quot|
       [&+[(v[i] mod 2)*embU[i]: i in [1..#v]]
              where v:=Eltseq(toVec(a)):a in OrderedGenerators(H1S)]>;
    H1S:=Kernel(H1Stoquot);
    vprint Selmer:"Bound on Selmer group now:",Ngens(H1S);
  end for;

//Preparation to deal with finite places. We first define some helper functions that
//generate the appropriate maps.
  
  //produces the map A^* -> A^*/A^*2 tensor K_P
  // return values:
  // mumap    - the map
  // trueimgs - images of the 2-torsion
  // rnk      - 2-rank of local Selmer group

  function reasonable_precision(P)
  //gives back a reasonable starting precision to do computations with. Things weighed are:
  // * Discriminant of F
  // * Valuation of denominator of F (to make formula independent of scaling)
  // * Valuation of 2
    return Valuation(K!8,P)+3*Abs(Valuation(dscF,P))+Abs(Valuation(LeadingCoefficient(F),P))+
           2*(Degree(F)-1)*Valuation(K!LCM([Denominator(c):c in Eltseq(F)]),P);
  end function;

  //res:=degnres(F,deg(F)/2) is computed once, if needed, otherwise not at all
  res:=false;

  function MuMap(A,P:res:=res)
    Aa,toAa:=AbsoluteAlgebra(A);
    thetaAa:=toAa(theta);
    tolslm,recs:=LocalTwoSelmerMap(A,P);
    //this formula is not exact, but it does have most elements in it that should matter:
    // * At even places we probably need a bit more precision because we're looking mod squares
    // * The discriminant plays a role
    // * we should weigh the denominator as well.
    prc0:=reasonable_precision(P);
    KP,toKP:=MyCompletion(P);
    KP`DefaultPrecision:=prc0;
    while true do 
      KP`DefaultPrecision+:=50;
      error if KP`DefaultPrecision gt prc0+1000, "Factorization of polynomial over p-adic field failed yet again...";
      vprintf Selmer,2: "Computing MuMap with precision %o\n", KP`DefaultPrecision;
      //compute p-adic factorization of F
      FP:=[Polynomial([toKP(a):a in Coefficients(f)]):f in fctF];
      try  
        fct:=&cat[[f[1]:f in Factorization(l:IsSquarefree)]:l in FP];
      catch ERR
        if IsFactorizationPrecisionError(ERR) then
           fct=[]; //this will trigger a continue below.
         else
           error ERR;
         end if;
      end try;
      if #fct ne #recs then
        continue;
      end if; 

      // TO DO: this is highly nonrigorous, and *will* lead to incorrect answers sometimes!!
      // Factorization makes no guarantees about the precision of the factors, which might
      // not be sufficient to determine the image of tolslm for the weierstrass places below.
      // Example:
      //    J := Jacobian(HyperellipticCurve(32*x^4 - 49*x^3 + 83*x^2 - 49*x + 32));
      // the assertion below about trueimgs fails for certain "reasonable" values 
      // of KP`DefaultPrecision, for instance 20 or 25.
      
      fct:=[Polynomial([K|c@@toKP:c in Coefficients(f)]):f in fct];
      // BMC: Factorization of non integral polys
      // over local fields doesn't always give monic factors
      // ???
      // one needs to deal with this:
      fct:=[ LeadingCoefficient(h)^-1*h : h in fct ];
      
      //compute the images of the weierstrass places    
      trueimgs:=[];
      for l in [1..#fct] do
        h:=fct[l];
        htilde:=lcF*&*[Universe(fct)|fct[m]:m in [1..#fct]| m ne l]; 
        if IsEven(Degree(F)) then
          Append(~trueimgs,tolslm((-1)^(Degree(h) mod 2)*h-
             (-1)^(Degree(htilde) mod 2)*htilde));
        else
          Append(~trueimgs,tolslm((-1)^(Degree(h) mod 2)*h+
             (-1)^(Degree(htilde))*htilde));
        end if;
      end for;
      break;
    end while;
        
    //muP(h): computes the image of a divisor (h(x),y-g(x))
    function muP(h)
      muh:=(-1)^(Degree(h) mod 2)*pAdicEvaluate(h,theta);
      return tolslm(muh);
    end function;
 
    //Build mumap according to whether F is of even degree or not  
    if IsOdd(Degree(F)) then
      mumap:=map<Parent(F)->Codomain(tolslm)|h:->muP(h)>;
      g:=(Degree(F)-1) div 2;
      dim:=(#fct-1)+g*InertiaDegree(P)*Valuation(KP!2);
      oddimg:=tolslm(A!lcF);
    else
      g:=(Degree(F)-2) div 2;
      dim:=g*InertiaDegree(P)*Valuation(KP!2);
      //We divide out by scalars again and map over what we already have computed
      mp:=LocalTwoSelmerMap(P);
      _,qm:=quo<Codomain(tolslm)|
	 [tolslm(A!(g@@mp)): g in OrderedGenerators(Codomain(mp))]>;
      mumap:=map<Parent(F)->Codomain(tolslm)|h:->muP(h)>*qm;
      tolslm:=tolslm*qm;
      trueimgs:=[qm(a):a in trueimgs]; 
      //If there is an odd degree Weierstrass place, things are straightforward
      if exists(i){i: i in [1..#fct] | IsOdd(Degree(fct[i]))} then
        vprint Selmer: "Odd degree local factor";
        dim+:=(#fct-2);
        oddimg:=trueimgs[i];
      else
        //otherwise, we have to check for a cassels kernel (even genus) or extra
	//2-torsion points (odd genus)
        vprint Selmer:"No odd degree local factor";
        dim+:=(#fct-2);
        //if g even, this is dim J[2] - 1
	//if g odd there may be more 2-torsion coming 
	//from factorizations over quadratic extensions

	//get the global resolvent
        if res cmpeq false then
          res:=degnres(F, Degree(F) div 2);
	end if;
        //we may have to increase precision for determining if the resolvent for testing
        //if F is a product of two conjugate factors, has a root. However, the precision
        //needed in this computation has little to do with the rest, so we reset the
        //precision afterwards again.
        KP_stored_precision:=KP`DefaultPrecision;
        while true do
          resP:=Polynomial([toKP(a):a in Coefficients(res)]);
          try
            roots:=Roots(resP);
            no_error:=true;
          catch ERR
            if IsRootFindingPrecisionError(ERR) then
              no_error:=false;
            else
              error ERR;
            end if;          
          end try;
          if no_error then
            break;
          end if;
          KP`DefaultPrecision +:= 10;
          vprint Selmer, 3: "MuMap resolvent root finding: increasing precision to", KP`DefaultPrecision;
        end while;
        KP`DefaultPrecision:=KP_stored_precision;

        if #roots eq 0 then
          if IsEven(g) then
            //dim -:= 1;
	    vprint Selmer:"Local cassels kernel non-trivial";
          else
            vprint Selmer:"No extra 2-torsion points coming from factorizations";
          end if;
        else
          if IsEven(g) then
            vprint Selmer:"No local Cassels kernel.";
            dim +:= 1;
	  else
            //each root in roots corresponds to a rational 2-torsion point.
            //We need to count how many of these are 'new'.
            DegreesOfFactors := [ Degree(g) : g in fct ];
            //degrees := [ Degree(g) : g in fct ];
            degree := &+DegreesOfFactors;
            Pd := Partitions(Integers()!(degree/2));
            PartitionsOfRoots2 := 0;
            //twotors2 := 0;
            for P in Pd do
              vals := Set(P);
              ct := 1;
              for v in vals do
                v1 := #[ w : w in P | w eq v ];
                v2 := #[ w : w in DegreesOfFactors | w eq v];
                ct *:= Binomial(v2,v1);
                if ct eq 0 then break; end if;
              end for;
              PartitionsOfRoots2 +:= ct;               
            end for;
            PartitionsOfRoots2 := Integers()!(PartitionsOfRoots2/2);
            //PartionsOfRoots2 is the number of distinct partitions 
            //of the roots of f into Galois stable subsets of equal size.
            // These correspond to roots of the resolvent which are 
            // accounted for by the factorization of f.
            if Ilog(2,#roots - PartitionsOfRoots2 + 1) gt 0 then
              //there are 2-torsion points coming from a proper 
              //factorization over a quadratic extension.
              //if f has factors of degree 2, some of these may lead to the torsion points.
              dblct := Max([0,#[ g : g in fct ] - 2]);
            else
              dblct := 0;
            end if;
            dimn := Ilog(2,#roots - PartitionsOfRoots2 + 1) - dblct;
            vprintf Selmer, 2: "Factorizations over quadratic extensions ==>",
                               " %o extra dimensions of 2-torsion.\n", dimn;
            dim +:= dimn;
          end if;//IsEven(g)
        end if;
      end if;
    end if;

    //a consistency check on the images of the weierstrass places
    if IsEven(Degree(F)) then 
      assert Order(&+trueimgs) eq 1;
    else
      assert Order(&+trueimgs+oddimg) eq 1;
    end if;
    
    //if there are odd degree weierstrass places then oddimg is set
    //We should build an even degree divisor out of them, so we
    //add "oddimg" (the image of some odd degree weier
    if assigned oddimg then
      trueimgs:=[IsOdd(Degree(fct[i])) select 
                         trueimgs[i]+oddimg else trueimgs[i]:
                                            i in [1..#trueimgs]];
      return mumap,tolslm,trueimgs,dim,oddimg,KP,toKP,res;
    else
      return mumap,tolslm,trueimgs,dim,_,KP,toKP,res;
    end if;
  end function; // MuMap

  //produces a test-map that tests if {g(x)=0} splits in Div(y^2=F)(Q_P).
  //if g(x) comes close to {F(x)=0}, false is returned.
  function MakeTestH(F,P,toKP)
    pi:=SafeUniformiser(P);
    KP:=Codomain(toKP);
    KP`DefaultPrecision+:=50;
    FP:=Polynomial([toKP(a):a in Coefficients(F)]);
    RP:=Parent(FP);
    R:=Parent(F);
    RR:=PolynomialRing(R);
    toRR:=hom<R->RR|RR.1>;
    required_significant_digits:=1+Valuation(KP!4);
    function testH(h)
      assert IsMonic(h);
      if Degree(h) eq 1 then
        vl:=pAdicEvaluate(FP,toKP(-Eltseq(h)[1]));
        if RelativePrecision(vl) lt required_significant_digits then
          return false;
        else
          return IsSquare(vl);
        end if;
      elif Degree(h) eq 2 then
        Ysqrrel:=Resultant(R.1-toRR(F),toRR(h));
        assert Degree(Ysqrrel) eq 2 and IsMonic(Ysqrrel);
        B,A:=Explode(Eltseq(Ysqrrel));
        //eliminating x from {y^2-f(x),h(x)}, we get
        //y^4+A*y^2+B
        //which factors as (y^2+a*y+b)*(y^2-a*y+b) exactly if
        //A=2*b-a^2, B=b^2, i.e., if
        //(A+a^2)^2-4*B has a root.
        if A eq 0 and B eq 0 then
          return false;
        end if;
        v:=Floor(Minimum(Valuation(A,P)/2,Valuation(B,P)/4));
        AKP:=toKP(A/pi^(2*v));BKP:=toKP(B/pi^(4*v));
        gg:=(AKP+RP.1^2)^2-4*BKP;
        if 2*Valuation(Discriminant(gg)) gt AbsolutePrecision(BKP) then
          return false;
        end if;        
        cc:=Eltseq(gg)[1];
        bl:=HasRoot(gg);
	if not(bl) then
	end if;
        return bl;
      else
        print "Degree not supported yet";
      end if;
    end function; // testH
    return map<R->Booleans()|h:->testH(h)>;
  end function; // MakeTestH

//We keep track of the information that comes in handy in determining the local
//images.

  Helpful:= assigned(A`Helpful) select A`Helpful else {};

//loop through all primes in S

  for P in S do
  
    vprint Selmer:"Considering prime",P;
    IndentPush();

    //construct the local cassels map and initialize several parameters:
    muP,toslP,twoP,dim,oddimg,KP,toKP,res:=MuMap(A,P:res:=res);
    vprint Selmer:"Dimension of local selmer group:",dim;
    slP:=Codomain(toslP);
    imgP:=sub<slP|twoP>;

    vprint Selmer:"Dimension generated by 2-torsion:",Ngens(imgP);
    assert Ngens(imgP) le dim;
    foundall := Ngens(imgP) eq dim;
    
    if foundall then
      vprint Selmer:"Found local selmer group from 2-torsion";
    else
      test:=MakeTestH(F,P,toKP);

      // We still haven't succeeded in generating the local image,
      // so now try any prestored or given hints.
      // 'MarksHints' are the 2-power torsion on an elliptic curve; 
      // we use them at odd primes.  For even primes we do IOD2 below.

      use_IOD2 := Degree(K) eq 1 and Minimum(P) eq 2 and
                  forall{c: c in Coefficients(F) | Denominator(c) eq 1};

      if F_is_elliptic_curve and not use_IOD2 then
        val:=Abs(Valuation(2^4*dscF,P));
        a6,a4,a2:=Explode(Eltseq(Coefficients(F)));
        MarksHints:= (Ngens(imgP) lt 2) select
	  GetHintsEC(EllipticCurve([0,a2,0,a4,a6]),P,3*val+50) else []; 
        HINTS:=Hints join {x-(K!v): v in MarksHints};
      else 
        HINTS:=Hints;
      end if;
    
      for h in Helpful join HINTS do
        if test(h) then
          muPh:=muP(h);
          if IsOdd(Degree(h)) then
            if not assigned oddimg then
              vprint Selmer,2:"Found first odd degree divisor",h;
              Helpful join:={h};
              oddimg:=muPh;
            end if;
            muPh+:=oddimg;
          end if;
          if muPh notin imgP then
            vprint Selmer,2:"Adding hint",h;
            Helpful join:={h};
            imgP:=sub<slP|imgP,muPh>;
          else
            vprint Selmer,2:"Hint",h,"already in.";
          end if;
        end if;
      end for;
    end if;
    foundall := Ngens(imgP) ge dim;

    /* 
     [Mark's comment]
     This is the IOD2 (ImageOfDelta at 2) function. It finds 2-adic
     neighborhoods of y^2=f(x)=quartic. 

     The idea is to keep iterating with x-values of more precision until you
     get something that it definitely yes/no for whether it is a 2-adic square.
     This is in Stoll's Acta Arithmetica paper (he states it for all primes,
     and at 2 you need to additionally consider the K-valuation of 4 I think).

     One version of this is in CrvEll/FourDesc/local_quartic.m, and another
     in CrvEll/twodesc.m, and maybe CrvG2/selmer.m?
     I think the version in Michael's stuff (maybe CrvG2?) had some problems
     with scaling [which is why I first switch f(x) to 4^d*f(x/4)].

     TO DO: previously, this code was only used when F is monic of degree 3;
            are those assumptions used in it somehow?  (of course, if anything
            is wrong here, it just means we might not find the full image yet)
     TO DO: when do we need to use both f(x) and f(1/x) ?
    */
    if not foundall and use_IOD2 then
     Z:=Integers();
     Z4:=Integers(4);
     Z8:=Integers(8);
     PZ:=PolynomialRing(Z);
     PQ:=PolynomialRing(Rationals());
     EQ:=ExactQuotient; 
     f:=PQ!F; y:=Parent(f).1; f:=PZ!f; X:=PZ.1;
     U:=[<PZ!(4^Degree(f)*Evaluate(f,y/4)),0,1/4,0>];

     while not foundall and not IsEmpty(U) do 
      last:=U[#U]; 
      Prune(~U); 
      f,xi0,a,d:=Explode(last); 
      df:=Derivative(f);
      for xi in GF(2) do 
       fx:=Evaluate(f,xi); 
       xi1:=Z!xi;
       if fx eq 0 then 
        fx1:=Evaluate(df,xi);
        if fx1 eq 0 then
         if Evaluate(f,Z4!xi1) eq 0 then
          U cat:=[<EQ(Evaluate(f,xi1+2*X),4),xi0+a*xi1,2*a,d+1>]; 
         end if;
        else //fx1 ne 0
         xi1+:=Z!Evaluate(f,Z4!xi1);
         xi1+:=Z!(4+Evaluate(f,Z8!xi1));
         U cat:=[<EQ(Evaluate(f,xi1+8*X),4),xi0+a*xi1,8*a,d+1>]; 
        end if;
       else // fx ne 0
        for xi2 in [Z8 | xi1+i : i in [0,2,4,6]] do
         if Evaluate(f,xi2) eq 1 then
          h:=x-K!(xi0+a*Z!xi2);
          if test(h) then
            muPh:=muP(h);
            if IsOdd(Degree(h)) then
              if not assigned oddimg then
                vprint Selmer,2:"Found first odd degree divisor",h;
                Helpful join:={h};
                oddimg:=muPh;
              end if;
              muPh+:=oddimg;
            end if;
            if muPh notin imgP then
              vprint Selmer,2:"Adding hint:",h;
              Helpful join:={h};
              imgP:=sub<slP|imgP,muPh>;
              foundall := Ngens(imgP) ge dim;
              if foundall then
                 break xi; 
              end if; 
            end if;
          end if; 
         end if;
        end for; // xi2
       end if; 
      end for; // xi
     end while; 
    end if;
    foundall := Ngens(imgP) ge dim;

if Degree(K) eq 1 and F_is_elliptic_curve and (Minimum(P) ne 2 or use_IOD2) then 
  assert foundall; // the 2-power torsion plus IOD2 should find everything
end if;

    DoDegreeOneSearch := not foundall and not use_IOD2 and Norm(P) lt 100; 

    if DoDegreeOneSearch then

      // General version of the systematic search.
      // For small P we use the same code as for two-cover descent
      // to determine the subgroup generated by degree 1 points.

      // TO DO: this often tends to be very slow, even over Q,
      // and especially when K has large ramification degree.
      // It's certainly better to use the above techniques before
      // resorting to this; in fact, it would often be better to
      // also try a bit of the targetted search (below) before this.

      vprint Selmer:"Looking for local points on the curve (systematic search)";
      time_deg1 := Cputime();
    
      OP:=IntegerRing(KP);

      function sqrmap(x)
        xK:=K!(x@@toKP);
        return toslP((xK-theta));
      end function;

      cfF:=Coefficients(F);

      while true do
        cfs:=[toKP(a):a in cfF];
        // normalize cfs
        m:=Minimum([Valuation(c):c in cfs]);
        if m in {0,1} then
          cfs:=[OP|c:c in cfs];
        else
          ss:=UniformizingElement(KP)^(-2*(m div 2));
          cfs:=[OP|ss*c:c in cfs];
        end if;
        try
          LocalDeltas:=SqrComponents(Polynomial(cfs),sqrmap);
          no_error:=true;
        catch ERR
          if IsFactorizationPrecisionError(ERR) then
            no_error:=false;
          else
            error ERR;
          end if;          
        end try;
        if no_error then 
          break; 
        end if;
        KP`DefaultPrecision +:= 10;
        vprint Selmer, 3: "MuMap LocalDeltas: increasing precision to", KP`DefaultPrecision;
      end while;
      
      //Reverse the coefficients here, to swap x=0 and x=infty.
      
      cfF:=Reverse(cfF cat [0 : i in [1..(Degree(F) mod 2)]]);
      if cfF[#cfF] eq 0 then
        cfF:=cfF[1..#cfF-1];
      end if;

      function sqrmap(x)
        if RelativePrecision(x) eq 0 then
          return toslP(A!lcF);
        else
          xK:=K!(1/(x@@toKP));
          return toslP((xK-theta));
        end if;
      end function;

      while true do
        cfs:=[toKP(a):a in cfF];
        m:=Minimum([Valuation(c):c in cfs]);
        cfs:=[OP|s*c:c in cfs] where s:=UniformizingElement(KP)^(-(m div 2)*2);
        try
          RevLocalDeltas:=SqrComponents(Polynomial(cfs),sqrmap:
                   Neighbourhood:=O(UniformizingElement(OP)));
          no_error:=true;
        catch ERR
          if IsFactorizationPrecisionError(ERR) then
            no_error:=false;
          else
            error ERR;
          end if;          
        end try;
        if no_error then break; end if; //break from while if no error was raised
        KP`DefaultPrecision +:= 10;
        vprint Selmer, 3: "MuMap LocalDeltas: increasing precision to", KP`DefaultPrecision;
      end while;

      LocalDeltas join:=RevLocalDeltas;
      
      if #LocalDeltas ne 0 then
        if not assigned oddimg then
          oddimg:=Rep(LocalDeltas);
        end if;
        imgP:=sub<slP|imgP,[d-oddimg:d in LocalDeltas]>;
      end if;

      foundall := Ngens(imgP) ge dim;

      vprintf Selmer: "Systematic search for local points on curve took %os\n", Cputime(time_deg1);
      vprint Selmer: "Dimension generated by 2-torsion plus points on curve:", Ngens(imgP);
      if foundall then
        vprint Selmer: "Found local selmer group from 2-torsion and points on curve";
      end if;

    end if; // DoDegreeOnSearch
    
    if not foundall then

      // SET UP TARGETED SEARCH
      // Random search for points with x-values near zeros mod P^i of F(x).
      // We use two slightly different ways of producing near-zeros of F.
      // (TO DO: the 'try_near_roots' method should be redundant.)

      // TO DO: something similar for divisors of degree > 1
      // TO DO: another idea was to plug in y-values near Weierstrass points 
      //        (guessing y-values is less complicated than x-values here)

      // TO DO: on second thoughts, instead we should do a new
      // implementation of the general search, which will be fast
      // if done the right way

      vprint Selmer: "Trying random points.";
      time_random := Cputime();

      try_near_bad := Minimum(P) eq 2;
      try_near_roots := false;
try_near_bad := false;

      pi:=SafeUniformiser(P);
      discval := Abs(Valuation(Discriminant(F), P));
      prec1 := discval + 20;
      prec2 := 2*discval;
      prec3 := 3*discval + 20; // hopefully enough for Factorization

      if try_near_roots then
         if Type(K) eq FldRat then
            KP := pAdicField(2, prec3);
            rootsF := Roots(ChangeRing(F,K), KP);
            err := O(KP.1^prec1);
            approxrootsF := [K! (r[1] + err) : r in rootsF]; 
         else
            KP, mKP := Completion(K, P : Precision:=prec3);
            rootsF := Roots(Polynomial([c@mKP : c in Coefficients(F)]));
            err := O(KP.1^prec1);
            approxrootsF := [(r[1] + err) @@ mKP : r in rootsF]; 
         end if;
         try_near_roots := not IsEmpty(approxrootsF);
       end if;

       if try_near_bad then
         // make a P-integral rescaling of F
         eP := Valuation(K!2,P); // e > 0
         s := 1;
         Fs := F * pi^-Valuation(LeadingCoefficient(F),P);
         while not forall{c: c in Coefficients(Fs) | Valuation(c,P) ge 0} do
            Fs := pi^Degree(F) * Evaluate(Fs, 1/pi*Parent(Fs).1);
            s /:= pi;
         end while;
assert IsMonic(F);
         // Now collect common zeros of F and F' modulo pi^i by successive lifting
         DFs := Derivative(Fs);
         cDFs := Min([Valuation(c,P) : c in Coefficients(DFs)]); // content of DFs
         zerosFs := [ [K|1] ];
         zerosF := [ [K|s] ];
         for i := 1 to Valuation(Discriminant(Fs),P) + 2*eP do
            // define zeros[i+1]
            liftsPi := &cat[[zz,zz+pi^(i-1)] : zz in zerosFs[i]];
            zerosPi := [zz : zz in liftsPi | Valuation(Evaluate(Fs,zz), P) ge i
                                         and Valuation(Evaluate(DFs,zz), P) ge i+cDFs];
            if #zerosPi eq 0 or #zerosPi gt 10^4 then
              break;
            end if;
            Append(~zerosFs, zerosPi);
            Append(~zerosF, [s*zz : zz in zerosPi]);
         end for;
       end if;

       if Degree(F) le 4 then
         degs := [1];
       elif DoDegreeOneSearch then
         // we have done the systematic degree one search, so should now only
	 // try quadratic points (and higher degree, when that is implemented)
         degs := [2];
       else
         degs := [1,1,1,2]; // more often try degree 1
       end if;
       vb := 2;
       vc := Min(discval, Valuation(ConstantCoefficient(F), P) );
       B := Minimum(P)^6*2^Valuation(K!8,P);
       counter := 0;
       while not foundall do
         repeat
           counter +:= 1;
           if counter mod 1000 eq 0 and vb lt prec2 then // TO DO: how negative can it get?
              vb +:= 1;
           end if;
           if try_near_bad and counter mod 3 eq 0 then
             i := Random([1..#zerosF]);
             h := x - Random(zerosF[i]) + Random(OK,B)*pi^(i+Random([-3..3]));
           elif try_near_roots and counter mod 3 le 1 then
             h := x - Random(approxrootsF) + Random(OK,B)*pi^Random(prec2);
           else 
             // completely naive random x-value
             if Random(degs) eq 1 then
               // use vb*B here just to avoid looping infinitely over a small fixed set
               h := x - Random(OK,vb*B)*pi^Random([-vb..vc]);
             else
               // TO DO: choose more wisely
               val := Random([-8..8]);
               h := x^2 + K!Random(OK,B)*pi^val*x + K!Random(OK,B)*pi^(2*val);
             end if;
           end if; 
         until test(h);
         muPh:=muP(h);
         if IsOdd(Degree(h)) then
           if not assigned oddimg then
             vprint Selmer,2:"Found first odd degree divisor",h;
             Helpful join:={h};
             oddimg:=muPh;
           end if;
           muPh+:=oddimg;
         end if;
         if muPh notin imgP then
           vprint Selmer,2:"Adding hint",h;
           Helpful join:={h};
           imgP:=sub<slP|imgP,muPh>;
           foundall := Ngens(imgP) ge dim;
         end if;
       end while;
       vprintf Selmer: "Search for random points took %os\n", Cputime(time_random);
    end if;

    vprint Selmer:"Found local Selmer group.";
    assert Ngens(imgP) eq dim;
    quot,toquot:=quo<slP|imgP>;

    //We compute the localization map by determining the images of the factor basis.
    //it is conceivable that more direct methods might be faster in smaller cases.
    //note that we determine the images in the group modulo the local image
    //so we are interested in the kernel.
    lbU:=[toquot(toslP(u)):u in bU];
    Lmap:=hom<H1S->quot| [
         &+[v[i]*lbU[i]: i in [1..#v]]
       where v:=Eltseq(toVec(a)): a in OrderedGenerators(H1S)]>;
    H1S:=Kernel(Lmap);
    
    IndentPop();
    vprint Selmer:
      "After intersection, bound on global selmer group:",Ngens(H1S);
  end for;
  
  //store information that turned out to be useful
  A`Helpful:=Helpful;
  
  //now we should determine if there can be a global cassels kernel.
  vprint Selmer:"Returning from TwoSelmWork";
  if forall{f: f in fctF | IsEven(Degree(f))} then
    if Degree(F) mod 4 eq 2 and res cmpeq false then
      res:=degnres(F, Degree(F) div 2);
    end if;
    if Degree(F) mod 4 eq 0 or #Roots(res) eq 0 then
      vprint Selmer:"Cassels Kernel may be non-trivial";
      G:=AbelianGroup([2: i in [1..Ngens(Codomain(toH1S))+1] ]);
      GtoH1S:=hom<G->Codomain(toH1S)|OrderedGenerators(Codomain(toH1S)) cat [H1S!0]>;
      toH1S:=toH1S*Inverse(GtoH1S);
      toVec:=GtoH1S*toVec;
      H1S:=H1S@@GtoH1S;
    else
      vprint Selmer:"Cassels kernel is trivial due to resolvent";
    end if;
  else
    vprint Selmer:"Cassels kernel is trivial due to odd degree factor";
  end if;
  return H1S,toH1S,Helpful,toVec,bU;
end function;

/******************************************************************************
Compute 2-Selmer group of an elliptic curve isogeny.
 ******************************************************************************/

intrinsic SelmerGroup(phi::Map:
      Bound:=-1,Fields:=false,Hints:={},Raw:=false)->GrpAb,Map
  {Given an isogeny between elliptic curves defined over a number field,
   computes the Selmer group of the isogeny. Currently implemented for
   2-isogenies, and for "multiplication by 2". Give integral models 
   for the curves.}
  
  require Type(BR) eq FldRat or ISA(Type(BR),FldAlg) and BaseRing(BR) cmpeq Rationals()
          where BR is BaseRing(Domain(phi)) :
    "The given isogeny must be defined over Q or a number field (which must be an absolute extension of Q)";

  if Degree(phi) eq 2 then
    if not assigned(phi`SelmerTuple) then
      phid:=DualIsogeny(phi);
      E:=Codomain(phi);
      Ed:=Codomain(phid);
      f,h:=HyperellipticPolynomials(E);
      x:=Parent(f).1;
      x0:=Roots(IsogenyMapPsi(phid))[1][1];
      F:=ExactQuotient(Evaluate(f+h^2/4,x+x0),x);
      fd,hd:=HyperellipticPolynomials(Ed);
      x0d:=Roots(IsogenyMapPsi(phi))[1][1];
      Fd:=ExactQuotient(Evaluate(fd+hd^2/4,x+x0d),x);
      S,Sd,toS,Hints,toVec,bU:=TwoIsogWork(F,Fd,Hints);
      phi`SelmerTuple:=<S,toS,Hints,toVec,bU>;
      phid`SelmerTuple:=<Sd,toS,Hints,toVec,bU>;
    end if;
    S,toS,Hints,toVec,bU:=Explode(phi`SelmerTuple);
    if Raw then
      return S,toS,Hints,toVec,bU;
    else
      return S,toS,Hints;
    end if;

  elif IsogenyIsMultiplicationByTwo(phi) then
    // Call TwoSelmerGroup(E) for caching, and to use the fast code over Q 
    E:=Domain(phi); 
    if assigned phi`Algebra then
      E`Algebra:=phi`Algebra;
    end if;
    S2, mS2 := TwoSelmerGroup(E:Bound:=Bound,Fields:=Fields,Hints:=Hints,Raw:=Raw);
    E`Algebra:=Domain(mS2);
    phi`Algebra:=Domain(mS2);
    return S2, mS2;
  end if;

  require false: "Selmer group not implemented for this kind of isogeny";
end intrinsic;

/******************************************************************************
Compute 2-Selmer group of an elliptic curve.
 ******************************************************************************/

// TO DO: work out the "really bad primes" (those with c_p even)

// Note: there is a separate signature for CrvEll[FldRat]

intrinsic TwoSelmerGroup(E::CrvEll:
     Bound:=-1,Fields:=false,Hints:={},Raw:=false)->GrpAb,Map
{The 2-Selmer group of an elliptic curve defined over a number field}

  BR := BaseRing(E);
  require ISA(Type(BR),FldAlg) and BaseRing(BR) cmpeq Rationals():
    "Elliptic curve must be defined over Q or a number field (which must be an absolute extension of Q)";
   
  if assigned E`TwoSelmerGroup then 
    if Raw and #E`TwoSelmerGroup ge 5 then 
      return Explode(E`TwoSelmerGroup);
    elif not Raw then 
      return Explode([*tup[i] : i in [1..Min(3,#tup)]*]) where tup is E`TwoSelmerGroup;
    end if;
  end if;

  // Use an integral modulus F 
  // TO DO: use a nice (reduced) minimal model
  E1:=IntegralModel(E);
  f,h:=HyperellipticPolynomials(E1);
  F:=f+h^2/4;
  assert Degree(F) eq 3 and IsMonic(F);
  x:=Parent(F).1;
  while not forall{c: c in Coefficients(F) | IsIntegral(c)} do
    F:=Evaluate(F,x/4)*64;
  end while;
  assert IsMonic(F);

  H1S,toH1S,NewHints,toVec,bU:=TwoSelmWork(F :
        Bound:=Bound, Fields:=Fields, Hints:=Hints,
        Algebra:= (assigned E`Algebra) select E`Algebra else false
        );
  E`Algebra:=Domain(toH1S);

  if Raw then
    E`TwoSelmerGroup := <H1S,toH1S,NewHints,toVec,bU>;
  else
    E`TwoSelmerGroup := <H1S,toH1S,NewHints>;
  end if;

  return Explode(E`TwoSelmerGroup);
end intrinsic;

/******************************************************************************
Compute 2-Selmer group of the Jacobian of a hyperelliptic curve
 ******************************************************************************/

intrinsic TwoSelmerGroupOld(J::JacHyp:
     Bound:=-1,Fields:=false,Hints:={},Raw:=false,res:=false)->GrpAb,Map
  {Computes the 2-Selmer group of J}
  require ISA(Type(BaseRing(J)),FldAlg) or Type(BaseRing(J)) eq FldRat:
    "Curve must be defined over Q or a number field";
  f,h:=HyperellipticPolynomials(Curve(J));
  F:=f+h^2/4; // TO DO: make a nice integral rescaling here
  d:=Degree(F);

  if assigned J`Algebra then
    Algebra:=J`Algebra;
  else
    Algebra:=false;
  end if;
  H1S,toH1S,NewHints,toVec,bU:=TwoSelmWork(F:
        Bound:=Bound,Fields:=Fields,Hints:=Hints,Algebra:=Algebra,res:=res);
  J`Algebra:=Domain(toH1S);
  if Raw then
    return H1S,toH1S,NewHints,toVec,bU;
  else
    return H1S,toH1S,NewHints;
  end if;
end intrinsic;
