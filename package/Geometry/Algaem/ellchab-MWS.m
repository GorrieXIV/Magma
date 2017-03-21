freeze;

import "newell.m":ProjectiveReduction;

//intrinsic NewRelevantCosets(MWmap::Map,Ecov::MapSch,p::RngIntElt:
//                            InertiaDegreeBound:=3,SmoothBound:=50,IndexBound:=-1)->Tup,RngIntElt
function NewRelevantCosets(MWmap,Ecov,p:
                            InertiaDegreeBound:=3,SmoothBound:=50,IndexBound:=-1)

  if IndexBound cmpne -1 and ISA(Type(IndexBound),RngIntElt) then
    IndexBound:=PrimeBasis(IndexBound);
  end if;
  MWgrp:=Domain(MWmap);
  E:=Domain(Ecov);
  //require Codomain(MWmap) eq E:"MWmap should correspond to cover";
  //require ISA(Type(Codomain(Ecov)),Prj) and Dimension(Codomain(Ecov)) eq 1:
  //  "Cover Ecov should be to a projective line";
  //require BaseRing(Codomain(Ecov)) eq Rationals():
  //  "The cover Ecov should map to a projective line defined over the rationals.";
  //require IsPrime(p): "Parameter p should be a prime";
  vprintf EllChab,2: "-"^40*"\nCollecting coset data at %o\n",p;
  Prs:=[LookupPrime(P): P in Support(p*IntegerRing(BaseRing(E)))| 
                        InertiaDegree(P) le InertiaDegreeBound];
  if #Prs eq 0 then
    vprint EllChab,2: "-"^40;
    vprintf EllChab,1: "Summary at %o: No suitable places. NO DATA.\n",p;
    return false,_,_;
  end if;
    
  Ep,toEp:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
               V:=[<a,b>where a,b:=Reduction(E,P):P in Prs];
  nEp:=[#e: e in Ep];
  vprint EllChab,2: "Group orders:",nEp;
  idx:=[i: i in [1..#Ep] | Max(PrimeBasis(nEp[i])) le SmoothBound];
  if #idx eq 0 then
    vprint EllChab,2: "-"^40;
    vprintf EllChab,1: "Summary at %o: No smooth group orders. NO DATA.\n",p;
    return false,_,_;
  end if;
  Prs:=Prs[idx];
  Ep:=Ep[idx]; toEp:=toEp[idx];
  
  k,tok:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
               V:=[<a,b>where a,b:=ResidueClassField(p):p in Prs];
  GFp:=GF(p);
  P1p:=ProjectiveSpace(GF(p),1);
  Ecovp:=[map<Ep[i]->P1p|
     [ProjectiveReduction(l,Prs[i],CoordinateRing(Ambient(Ep[i]))):
       l in AllDefiningPolynomials(Ecov)]>:i in [1..#Prs]];
  MWred,EpGrpMap:=Explode(<[v[1]:v in V],[v[2]:v in V]>) where
                        V:=[<a,b>where a,b:=Reduction(MWmap,P):P in Prs];
  IDXs:=[];
  fibs:=[PowerStructure(Assoc)|];
  V:=RationalPoints(P1p);
  idx:=[];
  for i in [1..#Prs] do
    vprintf EllChab,2:"Considering prime #%o with <f,e>=%o\n",i,<InertiaDegree(Prs[i]),RamificationDegree(Prs[i])>;
    P1k:=P1p(k[i]);
    if Multiplicity(Invariants(MWgrp), 0) le 1 then   // rank 1
      Append(~IDXs,#(Codomain(MWred[i])/Image(MWred[i])));
    else
      Append(~IDXs,#Codomain(MWred[i]));
    end if;
    if ISA(Type(IndexBound),SeqEnum) and not(PrimeBasis(IDXs[i]) subset IndexBound) then
      vprint EllChab,2:"Skipping prime because of index";
      continue i;
    end if;
    generic_image:=Ecovp[i](GenericPoint(Ep[i]));
    if generic_image[2] eq 0 or Degree(generic_image[1]/generic_image[2]) le 0 then
      vprint EllChab,2:"Skipping prime because of bad reduction of cover";
      continue i;
    end if;
    //If the image of the Mordell-Weil map is much bigger than p+1
    //then it's probably worth it to use discrete logarithms to lift the points
    //back into Image(MWred[i]). Otherwise, we may as well just enumerate
    //Image(MWred[i]) and see which images we get.
    //(if p is totally split, then the latter is the case, otherwise
    //discrete logarithms are probably less costly, provided the group order is
    //sufficiently smooth.

    if #Image(MWred[i]) gt 2*#V then
      vprint EllChab,2:"Using discrete log";
      //first build an associative array that allows quick lookup of
      //the images of rational points in the base locus of the map
      Images:=AssociativeArray(V);
      BadLocus:={Ep[i]!p:p in RationalPoints(BaseScheme(Ecovp[i]))};
      for v in V do
        Images[v]:={p: p in RationalPoints(v@@Ecovp[i])|p notin BadLocus};
      end for;
      for p in BadLocus do
        //we extend the map locally to get the value
        v:=EvaluateByPowerSeries(Ecovp[i],p);
        if v in V then
          Include(~Images[v],p);
        end if;
      end for;
      for v in V do
        Images[v]:={a:p in Images[v]|a in Image(MWred[i]) where a:=p@@EpGrpMap[i]};
      end for;
    else
      vprint EllChab,2:"Using enumeration";
      Images:=AssociativeArray(V);
      for p in Image(MWred[i]) do
        v:=EvaluateByPowerSeries(Ecovp[i],EpGrpMap[i](p));
        if v in V then
          if IsDefined(Images,v) then
            Include(~Images[v],p);
          else
            Images[v]:={p};
          end if;
        end if;
      end for;
    end if;
    fibs[i]:=Images;
    Append(~idx,i);
    vprintf EllChab,2:"IDX, Number of productive fibers: %o, %o\n",IDXs[i],#{v: v in Keys(fibs[i]) | #fibs[i][v] ge 1};
  end for;

  if IsEmpty(idx) then
    return false,_,_;
  end if;

  fibs:=[*fibs[i]: i in idx*];
  MWred:=MWred[idx];
  Prs:=Prs[idx];
  IDXs:=IDXs[idx];
  
  fib1:=fibs[1];
  m1:=MWred[1];
  G:=FreeAbelianGroup(Ngens(MWgrp));
  m1:=hom<G->Image(m1)|[m1(g):g in OrderedGenerators(Domain(m1))]>;

  for i in [2..#Prs] do
    fib2:=fibs[i];
    m2:=MWred[i];
    m2:=hom<G->Image(m2)|[m2(g):g in OrderedGenerators(Domain(m2))]>;

    gcd,togcd:=quo<G|Generators(Kernel(m1))join Generators(Kernel(m2))>;
    lcm,tolcm:=quo<G|Kernel(m1) meet Kernel(m2)>;
    lcmto1:=hom<lcm->Codomain(m1)|[m1(a@@tolcm):a in OrderedGenerators(lcm)]>;
    lcmto2:=hom<lcm->Codomain(m2)|[m2(a@@tolcm):a in OrderedGenerators(lcm)]>;
    m1togcd:=hom<Codomain(m1)->gcd|
        [togcd(a@@m1):a in OrderedGenerators(Codomain(m1))]>;
    m2togcd:=hom<Codomain(m2)->gcd|
        [togcd(a@@m2):a in OrderedGenerators(Codomain(m2))]>;
    function CRT(e1,e2)
      if m1togcd(e1) eq m2togcd(e2) then
        v:=Eltseq(e1@@m1-e2@@m2);
        A1:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m1))];
        A2:=[Eltseq(G!a):a in OrderedGenerators(Kernel(m2))];
        w:=Solution(Matrix(A1 cat A2),Vector(v));
        crt:=tolcm(e1@@m1-Kernel(m1)![w[i]:i in [1..Ngens(Kernel(m1))]]);
        return {crt+a:a in Kernel(lcmto1)meet Kernel(lcmto2)};
      else
        return {lcm|};
      end if;
    end function;
    for v in V do
      if IsDefined(fib1,v) and IsDefined(fib2,v) then
        fib1[v]:=&join[CRT(e1,e2):e1 in fib1[v],e2 in fib2[v]];
      else
        fib1[v]:={lcm|};
      end if;
    end for;
    m1:=tolcm;
  end for;
  quomap:=hom<MWgrp->Codomain(m1)|[m1(g):g in OrderedGenerators(G)]>;
  fibers:=ChangeUniverse(&join[fib1[v]:v in Keys(fib1)],Codomain(m1));
  
  if #Codomain(quomap) eq #fibers then
    vprint EllChab,2: "-"^40;
    vprintf EllChab,1: "Summary at %o: #points/#image = %o/%o. NO DATA\n",
                    p,#fibers,#Codomain(quomap);
    return false,_,_;
  end if;
  
  vprint EllChab,2: "-"^40;
  vprintf EllChab,1:"Summary at %o: #points/#image = %o/%o = %4o\n",
                    p,#fibers,#Codomain(quomap),RealField(2)!#fibers/#Codomain(quomap);
  return Prs,<quomap,fibers>,LCM(IDXs);
end function;
//end intrinsic;

// The following two functions are adapted from Chabauty-MWS.m by Michael Stoll.
// The changes made are:
//  - The reduction data is passed in as "filters" rather than "GI"
//    (different data structure)
//  - There is an additional parameter "r" for the rank of the group
//    (Michael Stoll's implementation is specialized for r=1)

function CheckInvariant(filters, r, tors)
  rep := 10;
  function frac(B, entry)
    I := Invariants(Codomain(entry[1]));
    Is := [Integers() | GCD(i,B) : i in I];
    n := &*Is;
    if Is eq I then return 1.0*#entry[2]/n; end if;
    cs := {};
    for cc in entry[2] do
      Include(~cs, [c[i] mod Is[i] : i in [1..#Is]] where c := Eltseq(cc));
      if #cs eq n then return 1.0; end if;
    end for;
    return 1.0*#cs/n;
  end function;
  //
  Gs := [Codomain(filters[l][1]) : l in Keys(filters)];
  primes := &join[Seqset(PrimeDivisors(#G)) : G in Gs];
  // for each prime, find largest exponents in invariants of product
  Bs := [1 : j in [1..rep]];
  for p in primes do
    vals := &join[{* Valuation(i, p) : i in Invariants(G) *} : G in Gs];
    m := Max(vals);
    Exclude(~vals, m);
    for j := 1 to rep do
      Bs[j] *:= p^m;
      if m ne 0 then
        if IsEmpty(vals) then
          m := 0;
        else
          m := Max(vals);
          Exclude(~vals, m);
        end if;
      end if;
    end for;
  end for;
  // compute estimated number of candidates for B
  rs := [1.0*B^r*tors : B in Bs];
  for l in Keys(filters) do 
    rs := [rs[j]*frac(Bs[j], filters[l]) : j in [1..rep]]; 
  end for;
  return Min(rs);
end function;

function dryRun(filters, r, Bound, eps, tors, Bs)
  vprintf EllChab, 1: "dryRun: Bound = %o, eps = %o\n", Bound, eps;
  function frac(B, entry)
    I := Invariants(Codomain(entry[1]));
    Is := [Integers() | GCD(i,B) : i in I];
    n := &*Is;
    if Is eq I then return 1.0*#entry[2]/n; end if;
    cs := {};
    for cc in entry[2] do
      Include(~cs, [c[i] mod Is[i] : i in [1..#Is]] where c := Eltseq(cc));
      if #cs eq n then return 1.0; end if;
    end for;
    return 1.0*#cs/n;
  end function;
  red := func<B | B^r*tors*&*[frac(B, filters[l]) : l in Keys(filters)]>;
  prl := [2] cat [p : p in [3..Bound by 2] | IsPrime(p)];
  max := &*[p^Max(&cat[[Valuation(i,p) : i in Invariants(Codomain(filters[l][1]))]
                         : l in Keys(filters)])
             : p in prl];
  vprintf EllChab, 2: "        max = %o\n", max;
  pl := [p : p in prl | IsDivisibleBy(max, p)];
  // optimze according to max red(B_i)
  // if B_0 = 1, B_{i+1} = B_i*p_i
  agendas := [[<1, 1, 1.0>]]; // entries <p, B, s>
  agendav :=[1.0]; 
  reached := {1}; // lists the values of B that have been seen so far
  while true do
    v, pos := Min(agendav); // try to extend cheapest path so far
    l := agendas[pos];
    vprintf EllChab, 2: "  dryRun: l = %o,\n   v = %o\n",
                   [l[i,1] : i in [2..#l]], v;
    Remove(~agendas, pos);
    Remove(~agendav, pos);
    B := l[#l,2];
    s := l[#l,3];
    if B eq max or (s lt eps and exists{b : b in Bs | IsDivisibleBy(B,b)}) then 
      break;  // reached success criterion
    end if;
    // list possible extensions
    new := [<p, Bp, red(Bp)> : p in pl 
                             | Bp notin reached and IsDivisibleBy(max, Bp)
                               where Bp := B*p];
    // and update agenda
    agendas cat:= [Append(l, n) : n in new];
    agendav cat:= [n[3] : n in new];
    reached join:= {n[2] : n in new};
  end while;
  vprintf EllChab, 1: "dryRun:\n Multipliers: %o\n",
                [l[i,1] : i in [2..#l]];
  vprintf EllChab, 1: " Predicted sizes: %o\n", [Round(l[i,3]) : i in [2..#l]];
  return [<l[i,1], l[i,3]> : i in [2..#l]], s lt eps;
end function;

//intrinsic Keys(L::SeqEnum)->SetEnum
//{Returns indices i for which L[i] is defined}
//  return {i: i in [1..#L] | IsDefined(L,i)};
//end intrinsic;

intrinsic Chabauty(MWmap::Map, Ecov::MapSch:
                      InertiaDegreeBound:=20,
                      SmoothBound:=50,
                      PrimeBound:=30,
                      IndexBound:=-1,InitialPrimes:=50)-> BoolElt, SetEnum
{Computes the points in the image of MWmap that map to a rational point under Ecov.
 using a combination of Mordell-Weil sieving and Chabauty's method. Several parameters
 are available to influence the performance.
   InertiaDegreeBound: The routine considers many reductions of the elliptic curve.
     The size of the residue field is an important factor in the cost. No primes with
     an inertia degree exceeding this bound will be considered.
   SmoothBound: Only primes at which the elliptic curve has a smooth group order are considered
   PrimeBound: In the Mordell-Weil sieving stage, only prime factors below this bound
     will be added to the group order.
   IndexBound: The routine finds all points in the Mordell-Weil group with rational image
     provided the image of MWmap is saturated at certain primes. Setting this bound
     ensures that the routine will only use information that depends on the image being
     p-saturated for p dividing IndexBound. Setting this bound can make it impossible
     for the routine to complete.
   InitialPrimes: Information at all good primes below this bound will be used initially.}

  if ISA(Type(IndexBound),RngIntElt) and IndexBound ne -1 then
     IndexBound:=PrimeBasis(IndexBound);
  end if;
  
  E:=Codomain(MWmap);
  BadPrimes:=Seqset(PrimeBasis(&*[Denominator(a): a in aInvariants(E)]) cat
             PrimeBasis(Discriminant(IntegerRing(BaseRing(E)))) cat
             PrimeBasis(Numerator(Norm(Discriminant(E)))));
  pbound:=0;
  MWgrp:=Domain(MWmap);
  T:=TorsionSubgroup(MWgrp);
  G:=TorsionFreeSubgroup(MWgrp);
  cands:={t: t in T};
  kernel:=OrderedGenerators(G);
  B:=1;    
  Epsilon:=0.1;est:=2*Epsilon;

  filters:=AssociativeArray(Integers());
  Prs:=AssociativeArray(Integers());

  IDX:=1;
  
  found:={};
  BadChabautyPrimes:={};
  ChabauteedPrimes:={};
  oldB:=1;
  
  while true do
    while est ge Epsilon do
      if IsZero(pbound) then //first iteration
        pbound:=InitialPrimes;
        PrimeRange:=[p: p in [2] cat [3..pbound by 2]| IsPrime(p) and p notin BadPrimes];
      else
        PrimeRange:=[p: p in [pbound..2*pbound+1 by 2]| IsPrime(p) and p notin BadPrimes];
        pbound:=2*pbound+3;
      end if;

      vprintf EllChab,1:"Gathering information at primes: %o\n",PrimeRange;
      for p in PrimeRange do
        prs,rcs,NewIDX:=NewRelevantCosets(MWmap,Ecov,p:SmoothBound:=SmoothBound,
                                      IndexBound:=IndexBound,InertiaDegreeBound:=InertiaDegreeBound);
        if prs cmpne false then
          filters[p]:=rcs;
          Prs[p]:=prs;
          IDX:=LCM(IDX,NewIDX);
        end if;
      end for;
      est := CheckInvariant(filters, #kernel, #T);
      Bs:=[Exponent(Codomain(f[1])): p in Keys(filters) | p notin BadChabautyPrimes and Max(PrimeBasis(#Universe(filters[p][2]))) le PrimeBound where f:=filters[p]];
    end while;
    ChabauteedPrimes:={};
    if IsEmpty(Bs) then
      Epsilon *:=0.5;
      continue;
    end if;
    run, flag:=dryRun(filters, #kernel, PrimeBound, 5*Epsilon, #T, Bs);
    if not flag then
      // expected size goal not reached: need more information
      vprintf EllChab, 1:
              "No good run found  ==>  reduce Epsilon and start over.\n";
      Epsilon *:= 0.5;
      continue;
    end if;
    
    B:=1;
    kernel:=OrderedGenerators(G);
   
    for l in [1] cat [r[1]: r in run] do
      vprintf EllChab,1:"Next step in run: Adding %o to B=%o\n",l,B;
      if l eq 1 then
        RelevantPs:=Keys(filters);
      else
        vB:=Valuation(B,l);
        RelevantPs:={p: p in Keys(filters)| Valuation(Exponent(Universe(filters[p][2])),l) gt vB};
      end if;

      kernel:=[l*g: g in kernel];
      conds:=[PowerStructure(Tup)|];
      for p in RelevantPs do
        Q,quomap:=quo<Universe(filters[p][2])| [filters[p][1](g): g in kernel]>;
        Append(~conds,< hom<MWgrp->Q|[quomap(filters[p][1](g)): g in OrderedGenerators(MWgrp)]>,
                      {quomap(g):g in filters[p][2]}>);
      end for;

      reps:=[ G![i: i in v] : v in CartesianPower([0..B*(l-1) by B],#kernel)];
      cands:={c: a in cands, b in reps | forall{1: f in conds|f[1](c) in f[2]} where c:=a+b};
      cands:={ShortLift(pi,pi(a)): a in cands} where _,pi:=quo<MWgrp|kernel>;
      B:=B*l;
      vprintf EllChab,1:"We now have %o candidates in a group of size %o\n",#cands,B^#kernel*#T;
    
      if IsEmpty(cands) then
        vprint EllChab,1:"No more candidates left. Returning found points.";
        return found,IDX;
      end if;
    
      newfound:={};

      nonrat:=0;
      largecoords:=0;
      for C in cands do
        if C in found then continue; end if;
        if forall{i: i in Eltseq(C) | Abs(i) le Sqrt(B)} then
          b:=EvaluateByPowerSeries(Ecov,MWmap(C));
          if b[1] in Rationals() and b[2] in Rationals() then
            vprintf EllChab,1:"Found point %o with image %o.\n",Eltseq(C),b;
            Include(~newfound,C);
          else
            nonrat+:=1;
          end if;
        else
          largecoords+:=1;
        end if;
      end for;
      vprintf EllChab,1:"Point search: Found %o new points with rational image,\n"*
                        "              %o cosets with non-rational image,\n"*
                        "              %o cosets untested due to size of representative.\n",
                        #newfound,nonrat,largecoords;
    
      found join:=newfound;
    
      ChabPrimes:=[<p,e div GCD(e,B)>: p in Keys(filters)|
                     &+[InertiaDegree(P): P in Prs[p]] gt #kernel and p notin BadChabautyPrimes
                     where e:=Exponent(Universe(filters[p][2]))];
      Sort(~ChabPrimes,func<a,b|a[2]-b[2]>);
      for ppair in ChabPrimes do
        p:=ppair[1];
        if p in ChabauteedPrimes then
          W:=newfound;
        else
          W:=found;
          Include(~ChabauteedPrimes,p);
        end if;
        for g in W do
          //if this point does not occur in in the list of points in reduction, then it
          //obviously has been removed already.
          if filters[p][1](g) notin filters[p][2] then
            continue g;
          end if;
          P0:=MWmap(g);
          Eqs,order,IDXq:=ChabautyEquations(P0,Ecov,MWmap,Seqset(Prs[p]):
                                    Centred);
          if IDXq eq 1 then
            //we have just proved that MWmap is saturated at p, so we can
            //remove p from IDX
            IDX:= IDX div p^Valuation(IDX,p);
          end if;
          if IndexBound cmpne -1 and IDXq ne 1 and IDXq notin IndexBound then
            vprintf EllChab,1:"Saturation at %o not proved but required. Discarding prime.",p;
            Include(~BadChabautyPrimes,p);
            continue ppair;
          end if;
          IDX:=LCM(IDX,IDXq);
          bl:=TestEquations(Eqs,order);
          if bl then
            vprintf EllChab,1:"Chabauty at %o proves that %o is unique in coset.\n",p,Eltseq(g);
            Exclude(~filters[p][2],filters[p][1](g));
          else
            vprintf EllChab,1:"Chabauty at %o leaves %o undecided.\n",p,Eltseq(g);
          end if;
        end for;
        //reapply the sieves
        conds:=[PowerStructure(Tup)|];
        for p in Keys(filters) do
          Q,quomap:=quo<Universe(filters[p][2])| [filters[p][1](g): g in kernel]>;
          Append(~conds,< hom<MWgrp->Q|[quomap(filters[p][1](g)): g in OrderedGenerators(MWgrp)]>,
                        {quomap(g):g in filters[p][2]}>);
        end for;
        cands:={c: a in cands | forall{1: f in conds|f[1](c) in f[2]} where c:=a};
        if IsEmpty(cands) then
          vprint EllChab,1:"No more candidates left. Returning found points.";
          return found,IDX;
        end if;
      end for;
    end for;
    vprintf EllChab,1:"Run exhausted. Reducing Epsilon and starting again.\n";
    Epsilon*:=0.5;
    Bs:=[LCM(b,B): b in Bs | not(IsDivisibleBy(B,b))];
   end while;
end intrinsic;
