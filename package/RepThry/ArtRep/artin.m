freeze;

/*******************************************************************
Artin representations and Frobenius elements in Galois groups

implements ArtRep type and all related functionality

version 1: Tim Dokchitser, Sep 2008
  compute full splitting field: works well for Galois groups of size <70,
  possibly up to <150 or so.
version 2: Tim and Vladimir Dokchitser, Sep 2010
  implemented identification by cycle type, Serre's trick for A_n and
  general machinery from `Identifying conjugacy classes in Galois groups'
  to handle arbitrary Galois groups plus improved p-adic computations
  can usually handle Galois groups of size <10000 (acting on a small number
  of points) easily, and much larger special groups such as A_n and S_n.
version 3: TD Oct 2014
  redo ComputeSplittingField, AutomorphismGroup, ramification filtration
  speeds up local computations by a factor of 5.
  Moved ComputeSplittingField into splittingfield.m
*******************************************************************/

// pass precomputed local data at bad primes?
// Remove `//!' in the text that refer to bugs
// Use Method:=Artin in Dedekind zeta functions more often
//  (always? for all extensions except Galois ones?)
// Eventually replace ZptoZ by standard coercion (Claus fixed this)



declare verbose ArtRep,3;     // Verbose printing

// Attributes

declare attributes FldNum: artinrepdata;

declare type ArtRep;
declare attributes ArtRep: K, character, conductor;

artinrec:=recformat<K,f,G,Frob,p0,r,C,CC,ramified,badprimes,localdata,
                    cycs,disc,disc_unfactored,Inv,complexconjugation,
                    galoisdata>;

/*
local data at a prime p
in the format <rts, D, Frob, ramgps, classmap, prec>
  rts  = roots of f in its splitting field F over Q_p
  D    = local Galois group as a subgroup of S_n (via action on rts)
  Frob = Frobenius, an element of D
  ramgps = data for higher ramification groups, in the form of a list
              [<H1,i1>,<H2,i2>,...],
           where for H,i in each entry, H is the subgroup of DSn consisting
           of inertia automorphisms for which v=valuation(sigma(pi)-pi) >= i,
           and i runs over all v's that can occur like that;
           ramgps[1][1] is the inertia group
  classmap = indexing map ConjugacyClasses(DSn)->ConjugacyClasses(G)
           from an embedding D->G as a decomposition group
  prec = precision of Q_p, prime ring of F
*/


// Default settings for factoring the discriminant of the defining
// polynomial of K

DefaultDiscFactor:=<10000,65535,10,0,false>;

// import: computing p-adic splitting fields


import "../../Ring/RngLoc/splitfield.m": 
  GaloisToPermutation,ComputeSplittingField,pAdicChangePrecision;


function fixedQasNF() return CyclotomicField(1); end function;

// mmylib functions

Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
Count:=func<S,x|#[z: z in S | z eq x]>;   // count occurences of x in a list
CycleType:=func<g|Sort([#x: x in CycleDecomposition(g)])>;     // incr order
DelCRs:=func<s|&cat([x: x in Eltseq(Sprint(s)) | x ne "\n"])>; // delete \n's
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;

// Hackobj: creation functions, in, coercion


intrinsic IsCoercible(x::ArtRep, y::.) -> BoolElt, .
{Coerce an Artin representation}
  return false, _;
end intrinsic;


intrinsic 'in'(x::ArtRep, y::.) -> BoolElt
{"in" function for an Artin representation}
  return false;
end intrinsic;


intrinsic '&+'(S::SeqEnum[ArtRep]) -> ArtRep
{Sum a sequence of Artin representations (needed as zero does not exist)}
  return IsEmpty(S) select fixedQasNF()!![0]
                    else   InternalAdd(S);
end intrinsic;


intrinsic '&*'(S::SeqEnum[ArtRep]) -> ArtRep
{Times a sequence of Artin representations (needed as one does not exist)}
  return IsEmpty(S) select fixedQasNF()!![1]
                    else   InternalMult(S);
end intrinsic;


intrinsic ArtRepCreate() -> ArtRep
{Create an Artin representation (internal function)}
  return New(ArtRep);
end intrinsic;


// Printing


function PrintField(F)
  if AbsoluteDegree(F) eq 1 then 
    return "Q"; 
  elif Type(F) eq FldQuad then 
    return "Q(sqrt("*Sprint(F.1^2)*"))";
  elif Type(F) eq FldCyc then 
    return "Q(zeta_"*Sprint(CyclotomicOrder(F))*"))";
  end if;
  B:=BaseField(F);
  R<x>:=PR(B);
  defpol:=DefiningPolynomial(F);
  if Type(defpol) eq SeqEnum 
  then defpol:=[R|x: x in defpol];
   else defpol:=R!defpol;
  end if;
  return Sprintf("ext<%o|%o>",PrintField(B),DelSpaces(defpol));
end function;


intrinsic Print(A::ArtRep, level::MonStgElt)
{Print an Artin representation}
  if level eq "Magma" then
    printf "%o !! %o",Sprint(A`K,"Magma"), DelCRs(Eltseq(Character(A)));
  else
    if not IsCharacter(Character(A)) or (not assigned A`K`artinrepdata`ramified)
      then condstr:="";
      else condstr:=", conductor " cat Sprint(Conductor(A)) cat
        (A`K`artinrepdata`disc_unfactored cmpeq 1 select "" else "(?)");
    end if;
    printf "Artin representation %o: %o of %o%o",
      GroupName(Group(A)),DelSpaces(Sprint(A`character,"Minimal")),
      PrintField(A`K),condstr;
  end if;
end intrinsic;


// Degrees of the irreducible factors of f defined over F_p

function CycleTypeFp(f)

  //! Bug in DistinctDegreeFactorization for p=2
  if Characteristic(BaseRing(Parent(f))) eq 2 then
    fct:=[u[1]: u in Factorisation(f)];
    degs:=Sort([Degree(u): u in fct]);
    sdegs:=Sort(SetToSequence(Set(degs)));
    fct:=[<d,&*[u: u in fct | Degree(u) eq d]> : d in degs];
    return degs,fct;
  end if;

  fct:=DistinctDegreeFactorization(f);
  return Sort(&cat[ [d[1]: i in [1..Degree(d[2])/d[1]]]: d in fct]),fct;
end function;


// Find an unramified prime with smallest residue degree >=mindeg
// in a given number of attempts, and starting with a given p

function GoodGaloisPrime(f: p:=100, attempts:=200, mindeg:=1)
  dsc:=Z!Abs(Discriminant(f));
  assert dsc ne 0;
  success:=0;
  minextdeg:=0;
  minp:=0;
  repeat
    p:=NextPrime(p);
    if dsc mod p eq 0 then continue; end if;
    success+:=1;
    extdeg:=LCM(CycleTypeFp(PR(GF(p))!f));
    if (extdeg ge mindeg) and ((minp eq 0) or (extdeg lt minextdeg)) then
      minextdeg:=extdeg; minp:=p;
    end if;
  until success gt attempts;
  return minp,minextdeg;
end function;


// Galois group of a polynomial f in Q[x]; returns p, G, roots in Z_p
//   parameter p is either a fixed prime (e.g. 17)
//     or "galois" (default in GaloisGroup)
//     or [startp,attempts,mindeg] (use GoodGaloisPrime)

function ComputeGaloisGroup(f,p)
  if Type(p) cmpeq RngIntElt then
    G,r,data:=GaloisGroup(f: Prime:=p); return p,G,r,data;
  end if;
  if p cmpeq "galois" then
    G,r,data:=GaloisGroup(f);
    return Prime(Universe(r)),G,r,data;
  end if;
  startp,attempts,mindeg:=Explode(p);
  p,deg:=GoodGaloisPrime(f:
    p:=startp, attempts:=attempts, mindeg:=Min(Degree(f),mindeg));
  if p eq 0 then
    vprint ArtRep,1: "Failed to find a good Galois prime, data:",Sprint([startp,attempts,mindeg]);
  else
    try
      vprint ArtRep,1: Sprintf("Attempting Galois group with p=%o deg=%o",p,deg);
      G,r,data:=GaloisGroup(f: Prime:=p);
      return p,G,r,data;
    catch e;
    end try;
  end if;
  "Galois group failed, choosing default prime";
  G,r,data:=GaloisGroup(f);
  return Prime(Universe(r)),G,r,data;
end function;


/*
// Compute splitting field of a polynomial, by repeatedly increasing
// precision until SplittingField(f,Zp) works

// very slow for some unknown reason

function ComputeSplittingField1(f,p : prec:=20)
  for tries:=1 to 10 do
    try
      vprint ArtRep, 2: "spl> Splitting field, precision =",prec;
      Zp:=pAdicRing(p,prec);
      R:=SplittingField(f,Zp);
      rts:=Roots(f,R);
      assert #rts eq Degree(f);
      return R,Zp,[r[1]: r in rts];
    catch e; 
      prec:=2*prec;
      vprint ArtRep,2: "spl> Failed (",DelCRs(e`Object),"); increasing precision to",prec;
    end try;
  end for;
  return false,_,_;
end function;
*/


/*
function ComputeSplittingField2(f,p: prec:=20)
  prec0 := prec;

  for attempt:=1 to 10 do
  try
    Qp:=pAdicField(p,prec);
    K:=Qp;
    F:=f;
    rts:=[];
    for i:=1 to Degree(f) do
      R<x>:=PR(K);
      F:=R!F;
      vprint ArtRep,2: "loc> Finding roots (prec",prec,")";
      rtsF:=[r[1]: r in Roots(F)];
      rts:=[K!r: r in rts] cat rtsF;
      if #rts eq Degree(f) then
        OK:=IntegerRing(K);
        vprint ArtRep,2: "loc> Converting to an absolute extension";
        R:=AbsoluteTotallyRamifiedExtension(OK);
        rts:=[r[1]: r in Roots(f,FieldOfFractions(R))];
        error if #rts ne Degree(f), "Found only",#rts,"out of",Degree(f),"roots in the splitting field";
        return R,IntegerRing(Qp),rts;
      end if;
      F:=f div &*[R| x-r: r in rts];
      _,_,e:=Factorisation(F: Extensions:=true);
      _,indx:=Max([AbsoluteDegree(d`Extension): d in e]);
      K:=e[indx]`Extension;
      vprint ArtRep,2: "loc> Adjoining root -> [K:Q_p] =",AbsoluteDegree(K);
    end for;
    error "Should exit before";
  catch e;
    prec:=2*prec;
    vprint ArtRep,2: "Failed (",DelCRs(e`Object),"); increasing precision to",prec;
  end try;
  end for;
  
  // [SRD, Dec 2011]
  vprint ArtRep,2: "loc> Plan B: call (slow?) SplittingField";
  OK:=ComputeSplittingField1(f, p : prec:=prec0);
  if R cmpne false then
    vprint ArtRep,2: "loc> Converting to an absolute extension";
    R:=AbsoluteTotallyRamifiedExtension(OK);
    rts:=[r[1]: r in Roots(f,FieldOfFractions(R))];
    error if #rts ne Degree(f), "Found only",#rts,"out of",Degree(f),"roots in the splitting field";
    Zp:=BaseRing(BaseRing(R));
    return R,Zp,rts;
  end if;

  error "Failed to compute the splitting field for f = ",f," at p =",p;
end function;
*/


// Make roots of f in Z_p accurate to at least a given precision

procedure Henselize(f,~rts,prec);
  if Precision(rts[1]) ge prec then return; end if;
  vprint ArtRep,2: "Henselizing roots to precision "*Sprint(prec);
  Qp:=ChangePrecision(Universe(rts),prec);
  f:=PR(Qp)!f;
  assert LeadingCoefficient(f) eq 1;    //! Otherwise HenselLift fails
  rts:=[HenselLift(f,Qp!r): r in rts];
  vprint ArtRep,2: "Henselized successfully";
end procedure;


// Which powers of c in G are conjugate to c?

ConjugatePowers:=func<G,c|[j: j in [1..Max(1,o-1)] |
  (GCD(j,o) eq 1) and IsConjugate(G,c,c^j)] where o is Order(c)>;


// Our main ST polynomial: roots are sums
//    evalpol(r[i]) * (r[g[i]]+r[g^u[i]]+...), u in pow
// indexed by elements g in a conjugacy class (modulo pow),
// and evalpol is x^2 or some other polynomial (if x^2 fails)

// Note: STInvariant only works for monic f's


function ZpToZ(n)
  a:=Z!n;
  b:=-(Z!(-n));
  if Abs(a) lt Abs(b) then return a; else return b; end if;
end function;


// Set of representatives of the conjugacy classes of an element classrep
// in G modulo a specified list of powers (#(classrep^G)/#pow of them)

function ClassRepsModPowers(G,classrep,pow)
  c:=[c: c in classrep^G];
  O:=[];
  while not IsEmpty(c) do
    x:=c[1];
    for j in pow do Remove(~c,Position(c,x^j)); end for;
    Append(~O,x);
  end while;
  return O;
end function;


/*
function STInvariantPoly(G,rts,classrep,pow,evalpol);
  C:=ClassRepsModPowers(G,classrep,pow);
  Rp<z>:=PR(Universe(rts));
  erts:=[Evaluate(evalpol,r): r in rts];
  f:=&*[z - &+[ erts[i]* &+[rts[i^(g^j)]: j in pow]
    : i in [1..#rts]]: g in C];
  return PR(Q)![ZpToZ(c): c in Eltseq(f)];
end function;
*/


function STInvariantPoly(G,rts,classrep,pow,evalpol);
  C:=ClassRepsModPowers(G,classrep,pow);
  Rp<z>:=PR(Universe(rts));
  erts:=[Evaluate(evalpol,r): r in rts];

  K:=Universe(rts);
  Zp:=PrimeRing(K);
  RZp:=PR(Zp);
  k:=ResidueClassField(K);
  p:=Characteristic(k);
  Fp:=PrimeField(k);
  f:=Degree(k,Fp);
  n:=#rts;
  // Find Frobenius in G
  frob:=[[j: j in [1..n] | Valuation(r-rts[j]) gt 0] where r is rts[i]^p:
          i in [1..n]];
  frob:=Sym(n)!Flat(frob);
  assert frob in G;
  ftots:=[RZp|];
  c:=[c: c in classrep^G];   // split the conjugacy class into groups
                             // both by powers in pow and by Frobenius action
                             // to minimize the computation and make
                             // intermediate polys (stored in ftots)
                             // defined over Zp rather than K
                             // (big speed improvement)
  while not IsEmpty(c) do
    x:=c[1];
    f:=1;
    repeat
      for j in pow do Remove(~c,Position(c,x^j)); end for;
      froot:=&+[ erts[i] * &+[rts[i^(x^j)]: j in pow]: i in [1..#rts]];
      f*:=(z-froot);
      x:=x^frob;
    until not (x in c);
    f:=RZp!f;
    Append(~ftots,f);
  end while;
  return PR(Q)![ZpToZ(c): c in Eltseq(&*ftots)];
end function;


function STInvariantGen(rts,F,data)
  pow,evalpol:=Explode(data);
  return &+[Evaluate(evalpol,rts[i]) * &+[rts[i^(F^j)]: j in pow]: i in [1..#rts]];
end function;


function STInvariantFp(f,fct,data)
  pow,evalpol:=Explode(data);
  R:=Parent(f);
  p:=Characteristic(R);
  Q<x>:=quo<R|R!f>;
  u:=Evaluate(evalpol,x) * &+[x^(p^j): j in pow];
  // compute its trace
  trace:=0;
  deg:=Degree(f)-1;
  for j:=0 to deg do
    trace+:=Coefficient(u,j);
    if j ne deg then u*:=x; end if;
  end for;
  return trace;
end function;


// For an irreducible f in F_p[t], compute the `alternating' invariant
// (Serre's trick), which is one of the square roots of the discriminant of f

function SqrtDiscIrrPoly(f)
  d:=Degree(f);
  R:=Parent(f);
  p:=Characteristic(R);
  Q<x>:=quo<R|f>;
  rts:=[];
  r:=x;
  for i:=1 to d do
    Append(~rts,r);
    if i ne d then r:=r^p; end if;
  end for;
  return GF(p)!&*[rts[i]-rts[j]: i,j in [1..#rts] | i gt j];
end function;

// Same, but for a general f in F_p[t], using resultants between the
// irreducible factors and SqrtDiscIrrPoly for the irreducible ones

function SqrtDiscInvariantFp(f,fct,dontcare)
  k:=BaseRing(Parent(f));
  degs:=[f[1]: f in fct];
  Sort(~degs,~perm);
  fct:=PermuteSequence([f[2]: f in fct],perm);
  return &*[k|Resultant(fct[i],fct[j]): i,j in [1..#fct] | i gt j] *
    &*[k|SqrtDiscIrrPoly(u): u in fct | Degree(u) gt 1];
end function;

// Same, but over Q_p

function SqrtDiscInvariantGen(r,F,can)
  _,c:=IsConjugate(Sym(#r),F,can);
  sgn:=IsOdd(c) select -1 else +1;
  return sgn * &*[r[i]-r[j]: i,j in [1..#r] | i gt j];
end function;


function IdentifyFrobClassFp(data,p)
  R:=PR(GF(p));
  f:=data`f;
  cyc,fct:=CycleTypeFp(R!f);
  inv:=data`Inv[Position(data`cycs,cyc)];
  if Type(inv) eq RngIntElt then return inv; end if;   // by cycle type
  funFp,funQp,par,list:=Explode(inv);
  sinv:=funFp(R!f,fct,par);
  vals:=[Evaluate(R!m[1],sinv): m in list];
  if Count(vals,0) eq 1 then         // by an invariant computation over F_p
    frob:=list[Position(vals,0),2];
    return frob;
  else                               // several invariants are roots ->
    return 0;                        // failed, need to work over Q_p
  end if;
end function;


function IdentifyConjugacyClassQp(data,F,r)
  cyc:=CycleType(F);
  inv:=data`Inv[Position(data`cycs,cyc)];
  if Type(inv) eq RngIntElt then return inv; end if;  // by cycle type
  funFp,funQp,par,list:=Explode(inv);                 // using an invariant

  sinv:=Universe(r)!funQp(r,F,par);
  vals:=[Valuation(Evaluate(m[1],sinv)): m in list];
  v,max:=Max(vals);
  vnext:=Max(Remove(vals,max));     // next closest

  assert v gt 0;  // at least one zero must occur; and precision 
                  // must be sufficient to be certain, otherwise fail

  prec:=Precision(Universe(r)) div 2;
  if v-vnext lt prec then return 0; end if;

  frob:=list[max][2];
  return frob;
end function;


function LocalData(K,p: prec:=20)
  A:=K`artinrepdata;
  badpos:=Position(A`badprimes,p);
  if (badpos ne 0) and (A`localdata[badpos][6] ge prec)
		   then return Explode(A`localdata[badpos]);
  end if;
  f:=A`f;

  try
    vprint ArtRep,1: Sprintf("Local data at p=%o; vdisc=%o; prec=%o",
      p,Valuation(A`disc,p),prec);
    R,Zp,rts,D,I,ramgps,frob,act:=ComputeSplittingField(f,p: prec:=prec, Gal:=true);
    prec:=Precision(Zp);
    n:=#rts;

    vprint ArtRep,2: "loc> Class map D->G";
    CCD:=ConjugacyClasses(D);
    CD:=CharacterTable(D);
    CC:=A`CC;
    
    rtsclassmap:=rts;                  // may need higher precision 
    prec:=1;                           // for the class map
    repeat  
      classmap:=[IdentifyConjugacyClassQp(A,c[3],rtsclassmap): c in CCD];
      if (0 notin classmap) and forall{rho: rho in A`C | 
        IsCharacter(Universe(CD)![rho(CC[classmap[i]]): i in [1..#CCD]])} then break; end if;
      prec*:=3;
      vprint ArtRep,2: "Class map: prec -> *"*Sprint(prec);
      error if prec gt 81, "Not enough precision to construct the class map";
      R2,m:=pAdicChangePrecision(R,prec*Precision(R));
      rtsclassmap:=[HenselLift(PR(R2)!f,m(r)): r in rts];
    until false;
    vprintf ArtRep,2: "classmap=%o\n",classmap;
  catch e
    vprint ArtRep,2: e`Object;
    vprint ArtRep,3: e`Position;
    prec:=2*prec;
    if prec gt 6000 then
      error "Local data failed at "*Sprint(p)*"; not enough precision";
    end if;
    return LocalData(K,p: prec:=prec);
  end try;     

  data:=<rts, D, frob, ramgps, classmap, Precision(Zp), act>;
  if badpos eq 0 then
    Append(~K`artinrepdata`badprimes,p);
    Append(~K`artinrepdata`localdata,data);
  else
    K`artinrepdata`localdata[badpos]:=data;
  end if;

  return Explode(data);

end function;


// Pull back a character rho of G to a local decomposition group at p

function LocalRepresentation(K,rho,p)
  r,DSn,FPerm,ramgps,DtoG,prec:=LocalData(K,p);
  a:=K`artinrepdata;
  CD:=CharacterTable(DSn);
  CC:=a`CC;
  chi:=Universe(CD)![rho(CC[DtoG[i]]): i in [1..#ConjugacyClasses(DSn)]];
  //assert IsCharacter(chi); // added MW, moved TD  17 Apr 2012
  return chi;
end function;


function RamifiedPrimes(K)
  if assigned K`artinrepdata`ramified then
    return K`artinrepdata`ramified;
  end if;
  vprint ArtRep, 2: "Factoring the discriminant of f";
  disc:=K`artinrepdata`disc;
  fct:=K`artinrepdata`disc_unfactored;
  if fct cmpeq true then
    vprint ArtRep, 1: "Factoring the discriminant";
    P:=PrimeDivisors(disc);
  else
    if fct cmpeq false then fct:=DefaultDiscFactor; end if;
    TL,PL,EL,ML,PF:=Explode(fct);
    P:={f[1]: f in Factorisation(disc: TrialDivisionLimit:=TL,
      PollardRhoLimit:=PL, MPQSLimit:=ML, ECMLimit:=EL, Proof:=PF)};
    P:=Sort([p: p in P]);
    U:=disc div &*[Z|p^Valuation(disc,p): p in P];
    if U ne 1 then
      vprint ArtRep,1: "Unfactored part",U;
    end if;
    K`artinrepdata`disc_unfactored:=U;
  end if;
  vprint ArtRep, 1: "Primes dividing the discriminant",DelSpaces(P);
  vprint ArtRep, 2: "Computing ramified primes";
  K`artinrepdata`ramified:=[p: p in P | #ramgps[1][1] ne 1
    where _,_,_,ramgps,_,_ is LocalData(K,p)];
  return K`artinrepdata`ramified;
end function;


intrinsic Conductor(A::ArtRep) -> RngIntElt
{Conductor of an Artin representation}
  if assigned A`conductor then return A`conductor; end if;
  require IsCharacter(A`character):
   "Conductor is not defined for virtual representations";
  cond:=1;
  if IsOne(A`character) then return 1; end if;
  for p in RamifiedPrimes(A`K) do
    _,_,_,ramgps,_,_:=LocalData(A`K,p);
    ch:=LocalRepresentation(A`K,A`character,p); // pullback of A to
                                                // the local Galois group
    first:=true;
    delta:=0;                                   // conductor exponent
    lastindex:=0;
    g0:=#ramgps[1][1];
    for I in ramgps do
      coinvdim:=Degree(ch)-InnerProduct(Restriction(ch,I[1]),
                PrincipalCharacter(I[1]));
      if coinvdim eq 0 then break; end if;
      delta +:= coinvdim * (I[2]-lastindex) * #(I[1]) / g0;
      lastindex:=I[2];
    end for;
    cond*:=p^(Z!delta);

  end for;

  A`conductor:=cond;
  return cond;
end intrinsic;


// Conjugacy class of Frobenius at infinity (complex conjugation)

function ComplexConjugation(K)

  A:=K`artinrepdata;
  if assigned A`complexconjugation then return A`complexconjugation; end if;

  vprint ArtRep,2: "Class of complex conjugation";

  r1:=#Roots(A`f,RealField());       // was r1,r2:=Signature(K);
  r2:=(Degree(A`f)-r1) div 2;        // but this should feel f instead

  cyc:=[1: i in [1..r1]] cat [2: i in [1..r2]];
  inv:=A`Inv[Position(A`cycs,cyc)];
  if Type(inv) eq RngIntElt then           // by cycle type
    K`artinrepdata`complexconjugation:=inv;
    return inv;
  end if;
  funFp,funQp,par,list:=Explode(inv);     // using an invariant

  maxdeg:=Max([Degree(u[1]): u in list]);
  maxcf:=Max([Max([Abs(c): c in Coefficients(u[1])]): u in list])+1;
  prec:=2*Round(Log(10,maxcf))+30;   //!

  vprint ArtRep,1: "Identifying complex conjugation, complex precision", prec;
  C:=ComplexField(prec);

  r:=[z[1]: z in Roots(A`f,C)];    // real roots followed by complex roots
  r:=[x: x in r | IsReal(x)] cat [x: x in r | not IsReal(x)];
  F:=&*[Sym(r1+2*r2)|(r1+2*i-1,r1+2*i): i in [1..r2]];      // permutation
  sinv:=C!funQp(r,F,par);

  vals:=[Abs(Evaluate(m[1],sinv)): m in list];
  v,min:=Min(vals);

  assert v lt 1E-15;                         // at least one zero must occur
  assert #[x: x in vals | x lt 10^4*v ] le 1;  // and only once

  frob:=list[min][2];
  K`artinrepdata`complexconjugation:=frob;
  return frob;
end function;


function Frobenius(K,p)
  if p cmpeq Infinity() then return ComplexConjugation(K); end if;

  data:=K`artinrepdata;
  if data`disc mod p ne 0 then
    frob:=IdentifyFrobClassFp(data,p);
    if frob ne 0 then return frob; end if;
  end if;

  prec:=20;
  repeat
    r,_,FPerm,_,_,prec:=LocalData(K,p: prec:=prec);
    frob:=IdentifyConjugacyClassQp(data,FPerm,r);
    if frob ne 0 then return frob; end if;
    prec:=2*prec;
    vprint ArtRep,2: "Frobenius failed, increasing local precision to",prec;
  until prec gt 1280;
  error "Failed to compute local data at "*Sprint(p);

end function;



// Ordered by cycles in increasing size, e.g. for t=[1,2,3] gives (2,3)(4,5,6)
function CanonicalElementOfCycleType(t)
  l:=[n+1: n in [1..&+t]];
  n:=0;
  for c in t do
    l[n+c]:=n+1; n+:=c;
  end for;
  return Sym(&+t)!l;
end function;


// Ramification: false, true
// FactorDiscriminant: false, true, <Trlim, Plim, Elim, Mlim, Proof>
// p0: p0:=17, p0:="galois", p0:=[minp, attempts, mindeg]
// f: monic minimal integral poly of some primitive element of K/Q


procedure ComputeArtinRepresentations(~K:
  Ramification:=false, FactorDiscriminant:=false, p0:="default", f:="default");

  if assigned K`artinrepdata then
    if Ramification then P:=RamifiedPrimes(K); end if;
    return;
  end if;

  vprint ArtRep,1: "Artin representations of",PrintField(K);

  if f cmpeq "default" then
    f:=MinimalPolynomial(PrimitiveElement(AbsoluteField(K)));
    P:=&join {Set(PrimeDivisors(Denominator(a))): a in Eltseq(f)};
    for p in P do
      repeat                                    // make it monic integral
        f:=p^Degree(f)*Evaluate(f,Parent(f).1/p);
      until forall{a: a in Eltseq(f) | Valuation(a,p) ge 0};
    end for;
  end if;
  f:=PR(Z)!f;

  vprint ArtRep,2: "f =",DelSpaces(f);

  n:=Degree(f);

  // Upper bound on the size of coefficients of the ST_invariants m_c
  // if they have degree d and are symmetrized over j powers

  crts:=[r[1]: r in Roots(f,ComplexField())];
  rabs:=Reverse(Sort([Abs(r): r in crts]));
  mbnd:=func<evp|n*Max([Abs(x): x in Eltseq(evp)])*rabs[1]^Degree(evp)*rabs[2]>;
  mcfbound:=func<d,evp,j|Max([Binomial(Z!d,i)*(mbnd(evp)*j)^i: i in [0..d]])>;

  if p0 cmpeq "default" then
    p0:="galois";  //!
    //p0:=[100,200,2+(n div 10)];
  end if;

  p0,G,r,galdata:=ComputeGaloisGroup(f,p0);
  vprint ArtRep,1: Sprintf("deg(f)=%o Gal=%o over Z_%o^%o",
    n,GroupName(G),p0,AbsoluteDegree(Universe(r)));

  CC:=[c: c in ConjugacyClasses(G)];
  order:=[c[1]: c in CC];
  csizes:=[c[2]: c in CC];
  cc:=[c[3]: c in CC];
  cyc:=[CycleType(c): c in cc];

  cycs:=Sort(SetToSequence(Set(cyc)));
  disc:=Z!Discriminant(f);
  sqrtdsc:=0;
  R<x>:=PR(Z);
  StdEvalPolyList:=[x^2, x^2-3*x+1, x^3-7*x^2+11*x-5, x^4-7*x^3-2*x^2+5*x+2,
                    x^2, &+[(n-i)*x^i: i in [0..n-1]] ];

  Inv:=[* "?": i in [1..#cycs] *];
  vprint ArtRep,2: "Cycle types -> Conjugacy classes";
  for j:=1 to #cycs do
    c:=cycs[j];
    classes:=[i: i in [1..#cc] | cyc[i] eq c ];

    // Distinguishable by cycle type
    if #classes eq 1 then
      Inv[j]:=classes[1];
      vprint ArtRep,2: DelSpaces(c),"->",Inv[j];
      continue;
    end if;

    // Sqrt(discriminant): cycle types with distinct odd cycles for G in A_n
    if (#Set(c) eq #c) and forall{x: x in c | IsOdd(x)} and (#classes eq 2)
       and (G subset Alt(n)) then

       can:=CanonicalElementOfCycleType(c);
       // can:=cc[classes[1]];  // does not always work

      _,c1:=IsConjugate(Sym(n),cc[classes[1]],can);
      _,c2:=IsConjugate(Sym(n),cc[classes[2]],can);
      if IsOdd(c1) ne IsOdd(c2) then                  // Distinct in A_n
        vprint ArtRep,1: DelSpaces(c),"is alternating";
        if sqrtdsc cmpeq 0 then
          sqrtZ:=Sqrt(Discriminant(f));
          prec:=Round(Log(p0,sqrtZ))+2;
          Henselize(f,~r,prec);
          sqrtdsc:=ZpToZ(&*[r[i]-r[j]: i,j in [1..n] | i gt j]);
          vprint ArtRep,2: "Sqrt discriminant =",sqrtdsc;
        end if;
        Inv[j]:=<SqrtDiscInvariantFp,SqrtDiscInvariantGen,can,
                [<x-sqrtdsc,IsEven(c1) select classes[1] else classes[2]>,
                 <x+sqrtdsc,IsEven(c1) select classes[2] else classes[1]>]>;
        continue;
      end if;
    end if;

    pow:=Sort(SetToSequence(&meet{Set(ConjugatePowers(G,cc[c])): c in classes}));
    // powers of elts in all our conjugacy classes that lie in the same class
    invdeg:=Max(csizes[classes])/#pow;
    vprint ArtRep,1: DelSpaces(c),"deg",invdeg,"->",DelSpaces(classes);

    for m:=1 to 30 do              // MaxInvAttempts:=30 once and for all
      if m le #StdEvalPolyList
        then evalpol:=StdEvalPolyList[m];
             if m eq #StdEvalPolyList-1 then
               pow:=[1]; invdeg:=Max(csizes[classes]);
             end if;
        else evalpol:=R![Random(-m,m): i in [0..Random(1,n-1)]];
      end if;

      // Compute the degree of the ST invariant and ensure sufficient p0-adic
      // precision for the roots of f to compute the polynomial itself
      prec:=Round(Log(p0,mcfbound(invdeg,evalpol,#pow)))+2;
      Henselize(f,~r,prec);

      // ST invariant

      //! Check they are powers of irr polys and replace by constituents?
      ST:=[STInvariantPoly(G,r,cc[i],pow,evalpol): i in classes];

      // Check they are coprime
      if not exists{i: i in [2..#ST], j in [1..#ST-1] |
        (i gt j) and (Degree(GCD(ST[i],ST[j])) ne 0)}
      then    // found a good invariant
        Inv[j]:=<STInvariantFp,STInvariantGen,<pow,evalpol>,
          [<ST[i],classes[i]>: i in [1..#classes]]>;
        break;
      end if;
      vprint ArtRep,2: DelSpaces(evalpol), "ST didn't work";
    end for;
    error if Inv[j] cmpeq "?", "Could not find distinct ST polynomials";
  end for;

  K`artinrepdata:=rec<artinrec|
    f:=f,K:=K,G:=G,
    Frob:=func<p|Frobenius(K,p)>,
    p0:=p0,r:=r,C:=CharacterTable(G),CC:=cc,galoisdata:=galdata,
    badprimes:=[],localdata:=[* *],cycs:=cycs,disc:=Abs(disc),
    disc_unfactored:=FactorDiscriminant,
    Inv:=Inv
    // ramified, complexconjugation initially undefined
  >;

  if Ramification then P:=RamifiedPrimes(K); end if;

end procedure;


intrinsic DefiningPolynomial(A:: ArtRep) -> RngUPolElt
{The polynomial whose roots Group(A) permutes}
  return Field(A)`artinrepdata`f;
end intrinsic;


intrinsic FrobeniusElement(K::FldNum, p::RngIntElt) -> GrpPermElt
{Compute a Frobenius element at p in the Galois group of the Galois closure
of K. This is a permutation on the roots of a polynomial defining K,
which can be recovered as DefiningPolynomial(A) for any Artin
representation of K; the Frobenius element is well-defined up to conjugacy
and modulo inertia.}
  error if not IsPrime(p),
    "p must be a rational prime or Infinity()";
  ComputeArtinRepresentations(~K);
  Frob:=Frobenius(K,p);
  return K`artinrepdata`CC[Frob];
end intrinsic;


intrinsic FrobeniusElement(K::FldNum, p::Infty) -> GrpPermElt {"}//"
  ComputeArtinRepresentations(~K);
  Frob:=Frobenius(K,p);
  return K`artinrepdata`CC[Frob];
end intrinsic;


// Standard representation functions copied for Artin representations

intrinsic Group(A::ArtRep) -> GrpPerm
{Returns the Galois group of the field K=Field(A) through
which A factors.} //, and phi specifies the action of G on K.}
  return A`K`artinrepdata`G;
end intrinsic;

intrinsic Character(A::ArtRep) -> AlgChtrElt
{Character of an Artin representation}
  return A`character;
end intrinsic;

intrinsic Degree(A::ArtRep) -> RngIntElt
{Degree (=dimension) of an Artin representation}
  d:=Degree(Character(A));
  if IsCoercible(Integers(),d) then return Integers()!d; end if;
 return d;
end intrinsic;

intrinsic Dimension(A::ArtRep) -> RngIntElt
{Degree (=dimension) of an Artin representation}
  return Degree(Character(A));
end intrinsic;

intrinsic IsIrreducible(A::ArtRep) -> BoolElt
{True if the Artin representation A is irreducible}
  return IsCharacter(ch) and IsIrreducible(ch) where ch is Character(A);
end intrinsic;


intrinsic Decomposition(A::ArtRep) -> SeqEnum[Tup]
{Decompose A into irreducible consituents. Returns a sequence [...<A_i,n_i>...]
  with A_i irreducible and n_i their exponents in A (possibly negative)}
  ch:=Character(A);
  K:=Field(A);
  C:=K`artinrepdata`C;
  return [<K!!c,InnerProduct(ch,c)>: c in C | InnerProduct(ch,c) ne 0];
end intrinsic;


function ArtinRepIsRamified(A,p,wild)
// check whether A is ramified (wild=false) or wildly ramified (wild=true)

  d:=A`K`artinrepdata;
  if (d`disc mod p ne 0) or (assigned d`ramified and not (p in d`ramified))
    then return false; end if;
  if wild and (#d`G mod p ne 0) then return false; end if;
  _,_,_,ramgps,_,_:=LocalData(A`K,p);
  I:=ramgps[1][1];                              // inertia at p
  if #I eq 1 then return false; end if;
  if wild then I:=SylowSubgroup(I,p); end if;   // wild inertia (wild=true)
  if #I eq 1 then return false; end if;
  ch:=LocalRepresentation(A`K,A`character,p); // pullback of A to
                                              // the local Galois group
  invdim:=InnerProduct(Restriction(ch,I),PrincipalCharacter(I));
  return invdim ne Dimension(A);
end function;


intrinsic IsRamified(A::ArtRep, p::RngIntElt) -> BoolElt
{True if the Artin representation A is ramified at p}
  require IsPrime(p): "p must be a prime number";
  require IsCharacter(Character(A)): "Artin representation may not be virtual";
  return ArtinRepIsRamified(A,p,false);
end intrinsic;


intrinsic IsWildlyRamified(A::ArtRep, p::RngIntElt) -> BoolElt
{True if the Artin representation A is wildly ramified at p}
  require IsPrime(p): "p must be a prime number";
  require IsCharacter(Character(A)): "Artin representation may not be virtual";
  return ArtinRepIsRamified(A,p,true);
end intrinsic;


intrinsic Field(A::ArtRep) -> FldNum
{Number field K such that A factors through the Galois closure of K}
  return AbsoluteDegree(A`K) eq AbsoluteDegree(A`K`artinrepdata`K)
    select A`K else A`K`artinrepdata`K;
end intrinsic;


intrinsic IsZero(A::ArtRep) -> BoolElt
{Whether an Artin representation is zero} 
  return IsZero(Character(A)); 
end intrinsic;


intrinsic '!!'(F:: FldNum, A:: ArtRep: MinPrimes:=20) -> ArtRep, BoolElt
{Given an Artin representation A of some number field, recognize it
if possible as an Artin representation of F and return F!!A,true.
If not possible, return 0,false}

  if A`K cmpeq F then return A; end if;
  if IsZero(A) then return 0*ArtinRepresentations(F)[1],true; end if;

  K:=Field(A);
  AF:=ArtinRepresentations(F);
  Kdata:=K`artinrepdata;
  Fdata:=F`artinrepdata;
  CCK:=Kdata`CC;
  CCF:=Fdata`CC;

  decA:=Decomposition(A);
  Alist:=[Character(data[1]): data in decA];
  Amult:=[data[2]: data in decA];

  matches:=[[c: c in Fdata`C | (Degree(c) eq Degree(a))
       and (Set(Eltseq(c)) eq Set(Eltseq(a)))]: a in Alist];

  p:=100;
  finished:=0;
  repeat
    p:=NextPrime(p);
    if (Kdata`disc mod p eq 0) or (Fdata`disc mod p eq 0) then continue; end if;

    frobK:=CCK[Kdata`Frob(p)];
    frobF:=CCF[Fdata`Frob(p)];

    finished+:=1;
    for i:=1 to #Alist do
      n:=#matches[i];
      if n eq 0 then return 0, false; end if;
      if n ne 1 then finished:=0; end if;
      //p,Alist[i],finished;
      matches[i]:=[m: m in matches[i] | Alist[i](frobK) eq m(frobF)];
    end for;
  until finished eq MinPrimes;

  return F!! &+[Amult[i]*matches[i][1]: i in [1..#Alist]],true;

end intrinsic;


intrinsic ChangeField(A:: ArtRep, F:: FldNum: MinPrimes:=20) -> ArtRep, BoolElt
{Given an Artin representation A of some number field, recognize it
if possible as an Artin representation of F and return F!!A,true.
If not possible, return 0,false}
  return '!!'(F,A: MinPrimes:=MinPrimes);
end intrinsic;


function VirtualCharacterKernel(a)
  if a eq 0
    then return Group(Parent(a)); end if;
  if not IsCharacter(a) then
    a:=&+[ch: ch in Basis(Parent(a)) | InnerProduct(ch,a) ne 0];
  end if;
  return Kernel(a);
end function;


intrinsic Minimize(A::ArtRep: Optimize:=true) -> ArtRep
{A restricted to the smallest number field K such that A factors through the
      its Galois closure. If Optimize=true (default), attempt to
      minimize the defining polynomial of K using OptimizedRepresentation}

  ch:=Character(A);
  H:=VirtualCharacterKernel(ch);

  F:=A`K;
  d:=AbsoluteDegree(F);
  a:=F`artinrepdata;
  G:=a`G;
  galdata:=a`galoisdata;
  GQ,m:=quo<G|H>;

  prevlimit:=0;
  limits:=[a:a in [3,5,10,20,30,40,60] | a lt d-1] cat 
    (#H eq 1 select [d-1] else [d]);

  ok:=false;
  for indexlimit in limits do
    S:=[H`subgroup: H in Subgroups(GQ: IndexLimit:=indexlimit) |
        Index(GQ,H`subgroup) gt prevlimit];
    for i:=prevlimit+1 to indexlimit do
      ok:=exists(H){H: H in S | (Index(GQ,H) eq i) and
          IsFaithful(PermutationCharacter(GQ,H))};
      if ok then break; end if;
    end for;
    if ok then break; end if;
    prevlimit:=indexlimit;
  end for;

  if not ok then
    if not Optimize then return false; end if;
    K:=OptimizedRepresentation(F);
    if K eq F then return A; end if;
    if not assigned K`artinrepdata then
      K`artinrepdata:=a;
      K`artinrepdata`K:=K;
    end if;
    AMin:=K!!A;
    return A;
  end if;

  K:=NumberField(GaloisSubgroup(galdata,H@@m)); 
  if Type(K) eq FldRat then K:=fixedQasNF(); end if;
  if Optimize then K:=OptimizedRepresentation(K); end if;
  AMin:=K!!A;
  return AMin;

end intrinsic;


intrinsic Kernel(A::ArtRep) -> FldNum
{The smallest Galois extension K/Q such that A factors through Gal(K/Q).
Note that this field may be enormous and uncomputable.}
  K:=SplittingField(DefiningPolynomial(Minimize(A)));
  return K;
end intrinsic;


function GenArtinCompose(A1,opfun,A2: charsonly:=false)

  /*
  //! Minimize?
  A1:=Minimize(A1);
  A2:=Minimize(A2);
  */

  F1A:=A1`K`artinrepdata`K;
  F2A:=A2`K`artinrepdata`K;
  vprint ArtRep,1: "Composing the fields";

  if   IsCoercible(F2A,F1A.1) then F:=F2A;
  elif IsCoercible(F1A,F2A.1) then F:=F1A;
  else
    F:=CompositeFields(AbsoluteField(F1A),AbsoluteField(F2A));
                                        //! use reducible f when it works?
      d,i:=Min([Degree(K): K in F]);
      if   d eq Degree(F1A,Q) then F:=F1A;
      elif d eq Degree(F2A,Q) then F:=F2A;
      else
        F:=F[i];
    end if;
  end if;
  vprint ArtRep,1: "Compositum:",DelSpaces(DefiningPolynomial(F)),
    "; now composing the representations";

  if charsonly
    then return F,F!!A1,F!!A2;
    else return opfun(F!!A1,F!!A2);
  end if;

end function;


intrinsic '+'(A1::ArtRep,A2:: ArtRep) -> ArtRep
{Direct sum of two Artin representations}
  if A1`K cmpeq A2`K
    then return A1`K!!(Character(A1)+Character(A2));
    else return GenArtinCompose(A1,'+',A2);
  end if;
end intrinsic;


intrinsic '-'(A1::ArtRep,A2:: ArtRep) -> ArtRep
{Direct difference of two Artin representations}
  if A1`K cmpeq A2`K
    then return A1`K!!(Character(A1)-Character(A2));
    else return GenArtinCompose(A1,'-',A2);
  end if;
end intrinsic;

intrinsic '-'(A::ArtRep) -> ArtRep {Negation of an Artin representation}
 return A`K!!(-Character(A)); end intrinsic;

intrinsic '*'(A1::ArtRep,A2:: ArtRep) -> ArtRep
{Tensor product of two Artin representations}
  if A1`K cmpeq A2`K
    then return A1`K!!(Character(A1)*Character(A2));
    else return GenArtinCompose(A1,'*',A2);
  end if;
end intrinsic;


intrinsic 'eq'(A1::ArtRep,A2:: ArtRep) -> BoolElt
{Test whether the two Artin representations are equal}
  c1:=Character(A1);
  c2:=Character(A2);
  if A1`K cmpeq A2`K then 
    return c1 eq c2; end if;
  if (IsZero(c1) ne IsZero(c2)) or (IsOne(c1) ne IsOne(c2)) or
     (Degree(c1) ne Degree(c2)) then return false; end if;
  if (IsZero(c1) and IsZero(c2)) or (IsOne(c1) and IsOne(c2))
    then return true; end if;
  D1:=A1`K`artinrepdata`disc;
  D2:=A2`K`artinrepdata`disc;
  C:=ComplexField();
  p:=100;
  for step:=1 to 20 do
    repeat p:=NextPrime(p); until (D1 mod p ne 0) and (D2 mod p ne 0);
    e:=EulerFactor(A1,p)-EulerFactor(A2,p);
    dif:=[Abs(C!c): c in Coefficients(e)];
    if not IsEmpty(dif) and (Max(dif) gt 0.01) then return false; end if;
  end for;
  _,C1,C2:=GenArtinCompose(A1,'eq',A2: charsonly:=true);
  return C1 eq C2;
end intrinsic;


intrinsic '!!'(K:: FldNum, ch:: AlgChtrElt) -> ArtRep
{The Artin representation of K with character ch}
  ComputeArtinRepresentations(~K);
  A:=ArtRepCreate();
  A`K:=K;
  CR:=Universe(K`artinrepdata`C);
  require IsCoercible(CR,ch): Sprintf("%o is not in %o",ch,CR);
  A`character:=CR!ch;
  return A;
end intrinsic;


intrinsic '!!'(K:: FldNum, ch:: SeqEnum) -> ArtRep
{The Artin representation of K with character ch}
  ComputeArtinRepresentations(~K);
  A:=ArtRepCreate();
  A`K:=K;
  CR:=Universe(K`artinrepdata`C);
  require IsCoercible(CR,ch): Sprintf("%o is not in %o",ch,CR);
  A`character:=CR!ch;
  return A;
end intrinsic;


intrinsic ArtinRepresentations(K::FldRat: Ramification:=false,
  FactorDiscriminant:=false, p0:="default", f:="default") -> SeqEnum
{Artin representations that factor through Q, i.e. just the principal character of Gal(Qbar/Q)}
  return ArtinRepresentations(RationalsAsNumberField(): Ramification:=Ramification,
      FactorDiscriminant:=FactorDiscriminant, p0:=p0, f:=f);
end intrinsic;

/*
Ramification (default false)
specifies whether to compute the ramification data at all the bad primes.
FactorDiscriminant (default false)
specifies whether
*/

intrinsic ArtinRepresentations(K::FldNum: Ramification:=false,
  FactorDiscriminant:=false, p0:="default", f:="default") -> SeqEnum
{All irreducible Artin representations that factor through the normal closure of K.}

  require Type(Ramification) eq BoolElt
    : "Ramification must be boolean";
  require (Type(F) eq BoolElt) or
    (Type(F) eq Tup) and (#F eq 5) and (Type(F[5]) eq BoolElt) and
    forall{j: j in [1..4] | IsCoercible(Z,F[j])}
    where F is FactorDiscriminant
    : "FactorDiscriminant must be boolean or a list <Trlim, Plim, Elim, Mlim, Proof>";
  require (p0 cmpeq "default") or                           // "default"
    (p0 cmpeq "galois") or                                  // "galois"
    IsCoercible(Z,p0) and (Z!p0 ge 2) and IsPrime(Z!p0) or  // 37
    (Type(p0) eq SeqEnum) and (#p0 eq 3) and                // [101,200,1]
    forall{x: x in p0 | IsCoercible(Z,x) and (x ge 0)}
    : "p0 must be \"default\", \"galois\", a prime number or a sequence [minp, attempts, mindeg]";
  require (f cmpeq "default") or
    (Type(f) eq RngUPolElt) and IsCoercible(PR(Z),f) and
    (LeadingCoefficient(f) eq 1) /* and IsIrreducible(f) */
    : "f must be \"default\" or a monic polynomial over the integers";

  ComputeArtinRepresentations(~K: Ramification:=Ramification,
      FactorDiscriminant:=FactorDiscriminant, p0:=p0, f:=f);
  return [K!!ch: ch in K`artinrepdata`C];
end intrinsic;


CharacterCharPoly:=func<c,g|
  CharacteristicPolynomialFromTraces([c(g^i): i in [1..c[1]]])>;


intrinsic LSeries(A:: ArtRep: Precision:=0) -> LSer
{L-series of an Artin representation}
  ch:=Character(A);
  if IsZero(ch) then
    L:=LSeries(1: Precision:=Precision);
    L`parent:=A;
    return L;
  end if;
  require IsCharacter(ch): "Artin representation may not be virtual";
  if not IsIrreducible(ch) then
    dec:=Decomposition(A);
    dec:=&cat([[d[1]: i in [1..d[2]]]: d in dec]);
    L:=&*[LSeries(a: Precision:=Precision): a in dec];
    LSetPrecision(L,Precision);
    L`parent:=A;
    L`name:=A;
    return L;
  end if;
  data:=A`K`artinrepdata;
  G:=data`G;
  if ch eq PrincipalCharacter(G) then
    return RiemannZeta(:Precision:=Precision);
  end if;
  F:=data`Frob;
  bad:=RamifiedPrimes(A`K);

  C:=data`C;
  CC:=data`CC;
  charpolys:=[Eltseq(CharacterCharPoly(ch,g)): g in CC];

  TARGET:=Universe(Eltseq(ch));

  function loc(p,d: Precision:=GetPrecision(0.5)) // target ring?
    CF:=ComplexField(Precision);
    if Type(TARGET) in {RngInt,FldRat} then CF:=Integers(); end if;
    if CyclotomicOrder(TARGET) le 2 then CF:=Integers(); end if; // pleugh
    if not (p in bad) then return PR(CF)!charpolys[F(p)];
    else return EulerFactor(A,p: R:=CF); end if;
  end function;

  // gamma factors depend on the action of complex conjugation
  cctrace:=Z!ch[ComplexConjugation(A`K)];
  gammazeroes:=(Degree(ch)+cctrace)/2;   // dim of +1 eigenspace
  gammaones:=(Degree(ch)-cctrace)/2;     // dim of -1 eigenspace
  gamma:=[0: i in [1..gammazeroes]] cat [1: i in [1..gammaones]];

  // not going to compute the sign (root number)
  // except for orthogonal characters where it is 1 (Frohlich-Queyrut's thm)
  sign:=Schur(ch,2) eq 1 select 1 else 0;
  return LSeries(1,gamma,Conductor(A),loc: Parent:=A, Precision:=Precision, Sign:=sign);

end intrinsic;


intrinsic HodgeStructure(A::ArtRep) -> HodgeStruc
{The Hodge structure of an Artin representation}
  ch:=Character(A); 
  if IsZero(ch) then return HodgeStructure([]); end if;
  cctrace:=Z!ch[ComplexConjugation(A`K)];
  gammazeroes:=(Degree(ch)+cctrace)/2;   // dim of +1 eigenspace
  gammaones:=(Degree(ch)-cctrace)/2;     // dim of -1 eigenspace
  ARR:=[<0,0,0> : i in [1..gammazeroes]] cat [<0,0,1> : i in [1..gammaones]];
  return HodgeStructure(ARR); 
end intrinsic;


intrinsic PermutationCharacter(K::FldNum) -> ArtRep
{For a number field K with Galois closure F, compute the character of
C[Gal(Qbar/Q)/Gal(Qbar/K)] as an Artin representation. It is of degree [K:Q]
and is the character of the permutation representation of the absolute
Galois group on the embeddings of K in C}
  ComputeArtinRepresentations(~K);
  G:=K`artinrepdata`G;
  H:=Stabiliser(G,1);    //! assumes transitive
  return K!!PermutationCharacter(G,H);
end intrinsic;


intrinsic PermutationCharacter(K::FldRat) -> ArtRep
{The principal character of Gal(Qbar/Q) as an Artin representation}
  return ArtinRepresentations(Q)[1];
end intrinsic;


function RationalArg(x)
  C:=ComplexField();
  x:=C!x;
  if Abs(x) lt 10^(-Precision(C) div 2) then return 9; end if;
  a:=Arg(x)/2/Pi(C);
  n:=BestApproximation(a,10^(Precision(C) div 2));
  if n eq -1/2 then n:=1/2; end if;
  return n;
end function;


function test_same(A,chi) 
  ch:=Character(A);
  P:=[p : p in PrimesUpTo(1000) | Valuation(2*Conductor(chi),p) eq 0];
  K:=Field(A); 
  N:=Conductor(chi); 
  CC:=K`artinrepdata`CC;
  F:=K`artinrepdata`Frob; 
  FClass:=Group(A)!1;
  o:=Order(chi); 
  CF:=CyclotomicField(IsOdd(o) select 2*o else o);
  for p in P do 
    if CF!ch(CC[F(p)]) ne CF!chi(p) then return false; end if;
  end for; 
  return true; 
end function;


// should go elsewhere
intrinsic EulerFactor(chi::GrpDrchElt,p::RngIntElt : R:=ComplexField()) -> RngUPolElt
{The Euler factor of a Dirichlet character at a prime}
  require IsPrime(p): "p must be prime"; 
  P<t>:=PolynomialRing(R);
  return P!Polynomial([1,-chi(p)]); 
end intrinsic;


intrinsic ArtinRepresentation(chi::GrpDrchElt: field:="undefined") -> ArtRep
{Convert a Dirichlet character chi to an Artin representation A.
 To avoid recomputation, the minimal field through which A factors may be
 specified by the field parameter.}
  if IsTrivial(chi) then return ArtinRepresentations(Q)[1]; end if; // MW
  if field cmpeq "undefined" then
    K:=OptimisedRepresentation(AbsoluteField(NumberField(AbelianExtension(chi))));
  else
    K:=field;
  end if;
  error if Degree(K,Q) ne Order(chi),
    "The specified field is not the minimal field for chi";
  A:=ArtinRepresentations(K);
  p:=1;
  dK:=K`artinrepdata`disc;
  N:=Conductor(chi);
  o:=Order(chi); CF:=CyclotomicField(IsOdd(o) select 2*o else o);
  repeat
    p:=NextPrime(p);
    if (dK mod p eq 0) or (N mod p eq 0) then continue; end if;
    //vprint ArtRep,1: RationalArg(chi(p)),Denominator(RationalArg(chi(p))),Order(chi);
  until Denominator(RationalArg(chi(p))) eq Order(chi);
  F:=K`artinrepdata`Frob(p);
  F:=K`artinrepdata`CC[F];
  reps:=[a: a in A | CF!Character(a)(F) eq CF!chi(p)];
  error if #reps ne 1, "Failed to convert",chi,"to an Artin representation";
  return reps[1];
end intrinsic;


intrinsic ArtinRepresentation(chi::GrpDrchNFElt: field:="undefined") -> ArtRep
{Convert a Dirichlet character chi to an Artin representation A.
 To avoid recomputation, the minimal field through which A factors
 may be specified by the field parameter.} // copy of above, for GrpDrchNFElt
  require Degree(Parent(chi)`NF) eq 1: "Must be a Dirichlet character over Q";
  if IsTrivial(chi) then return ArtinRepresentations(Q)[1]; end if;
  return ArtinRepresentation(DirichletCharacterOverQ(chi) : field:=field);
end intrinsic;


intrinsic EulerFactor(A:: ArtRep, p::RngIntElt: 
  R:=Universe(Eltseq(Character(A)))) -> RngUPolElt
{Euler factor of A at p. The coefficient field (cyclotomic field or some
complex field) may be specified with the optional parameter R.}
  ch:=Character(A);
  data:=A`K`artinrepdata;
  G:=data`G;
  CC:=data`CC;
  if Type(R) eq FldCyc and CyclotomicOrder(R) le 2 then R:=Integers(); end if;
  PolR:=PR(R);

  // A unramified
  if not IsRamified(A,p) then
    return PolR!CharacterCharPoly(ch,CC[data`Frob(p)]);
  end if;

  // A ramified
  _,DSn,FPerm,ramgps,DtoG,_:=LocalData(A`K,p);
  chD:=LocalRepresentation(A`K,ch,p);
  frob:=DtoG[ClassMap(DSn)(FPerm)];

  I:=ramgps[1][1];  // inertia group as a permutation sgp of D
  if #I eq 1 then return PolR!CharacterCharPoly(ch,CC[frob]); end if;
  // pick up characters of D that enter ch|D and with full inertia
  // invariants (irreducible rep of D -> inertia invariants are
  // either trivial or the whole representation; we want char poly
  // of Frobenius just on inertia invariants)
  ichars:=[c: c in CharacterTable(DSn) | (InnerProduct(chD,c) ne 0) and
    (InnerProduct(Restriction(c,I),PrincipalCharacter(I)) ne 0)];
  return IsEmpty(ichars) select PolR!1 else     // do NOT coerce individual terms
    PolR!(&*[CharacterCharPoly(c,FPerm)^(Z!InnerProduct(chD,c)): c in ichars]);  
end intrinsic;


////////////////////////////////////////////////////////////////////////
// Mark's additions


function DeterminantCharacter(c) 
  R:=Parent(c);
  G:=Group(R);
  d:=Integers()!c[1];
  ccgens:=[x[3]:x in ConjugacyClasses(G)];
  return R![(-1)^d*Coefficient(CharacterCharPoly(c,g),d): g in ccgens];
end function;


intrinsic Determinant(A::ArtRep) -> ArtRep
{Given an Artin representation, return its determinant as an Artin rep}
  if Degree(A) eq 1 then return A; end if; // turn off, for testing
  return Field(A)!!DeterminantCharacter(Character(A)); 
end intrinsic;


intrinsic '^'(A::ArtRep,n::RngIntElt) -> ArtRep
{Tensor power of an Artin representation} 
  require n ge 0 or Degree(A) eq 1: "Negative power of nonlinear ArtRep";
  if n eq 0 then return Field(A)!![1 : i in [1..#Eltseq(Character(A))]]; end if;
  if n eq 1 then return A; end if;
  if Degree(A) eq 1 then return Field(A)!!(Character(A)^n); end if;
  B:=A; R:=IsOdd(n) select B else B^0;
  while n gt 0 do n:=n div 2; B:=B*B;
  if IsOdd(n) then R:=R*B; end if; end while; 
  return R; 
end intrinsic;


intrinsic '*'(n::RngIntElt,A::ArtRep) -> ArtRep 
{Direct sum of an Artin representation n times}
  return Field(A)!!(n*Character(A)); 
end intrinsic;


intrinsic '*'(A::ArtRep,n::RngIntElt) -> ArtRep 
{Direct sum of an Artin representation n times}
  return Field(A)!!(n*Character(A)); 
end intrinsic;


function artrep_to_dirchar(A) ch:=Character(A); assert IsLinear(ch);
 K:=Field(A); N:=Conductor(A); NZ:=N*Integers(fixedQasNF());
 CC:=K`artinrepdata`CC; p:=100; dK:=K`artinrepdata`disc;
 F:=K`artinrepdata`Frob; DATA:=[* *];
 o:=Order(ch); CF:=CyclotomicField(IsOdd(o) select 2*o else o);
 while true do p:=NextPrime(p);
  if (dK mod p eq 0) or (N mod p eq 0) then continue; end if;
  DATA:=DATA cat [* <p,CF!ch(CC[F(p)])> *];
  chi,K:=DirichletCharacter(NZ,<d :d in DATA> : RequireGenerators:=false);
  if #K eq 1 then break; end if; end while; return chi; end function;


intrinsic DirichletCharacter(A::ArtRep) -> GrpDrchElt
{Convert a linear Artin representation to a Dirichlet character (over Q)}
 ch:=Character(A); error if not IsLinear(ch), "Character of A must be linear";
 chi:=artrep_to_dirchar(A); return DirichletCharacterOverQ(chi); end intrinsic;


function sign_character()
 return DirichletGroup(1*Integers(fixedQasNF()),[1]).1; end function;


intrinsic HeckeCharacter(A::ArtRep) -> GrpHeckeElt
{Convert a linear Artin representation to a Dirichlet character (over Q)}
 ch:=Character(A); error if not IsLinear(ch), "Character of A must be linear";
 chi:=artrep_to_dirchar(A);
 if not IsTrivialOnUnits(chi) then chi:=chi*sign_character(); end if;
 psi:=HeckeLift(chi); return AssociatedPrimitiveCharacter(psi); end intrinsic;


intrinsic Symmetrization(A::ArtRep,S::SeqEnum) -> ArtRep
{Given an Artin representation A and a partition S, return the symmetrization
 of A corresponding to S}
 require &and[p ge 1 : p in S] and #S gt 0: "Partition must be positive";
 require Reverse(S) eq Sort(Reverse(S)): "Partition must be non-increasing";
 return Field(A)!!Symmetrization(Character(A),S); end intrinsic;


////////////////////////////////////////////////////////////////////////
/* Everything below should be moved eventually */

function char_symm(chi,S) if #S gt 0 then n:=&+S; else n:=0; end if;
    lambda:=SymmetricCharacter(S);
    ans:=[CyclotomicField(chi)|];
    R := Parent(chi);
    numcl := #ClassesData(R);
    pm := PowerMap(R);
    Sn:=Group(Parent(lambda));
    nfact := Factorial(n);
    for g in [1..numcl] do
	a:=0;
	for rho in ConjugacyClasses(Sn) do
	    cst:=CycleStructure(rho[3]);
	    cst:={* i[1]^^i[2] : i in cst *};
	    a +:= rho[2] * lambda(rho[3]) *
		&*[chi[pm(g,k)]^Multiplicity(cst,k) : k in [1..n]];
	end for;
	Append(~ans, a/nfact);
    end for;
    return Parent(chi)!ans;
end function;

/*
function char_symm(chi,S) if #S gt 0 then n:=&+S; else n:=0; end if;
 lambda:=SymmetricCharacter(S); ans:=[];
 G:=Group(Parent(chi)); Sn:=Group(Parent(lambda));
 repsG:=[c[3] : c in ConjugacyClasses(G)];
 for g in repsG do a:=0; for rho in ConjugacyClasses(Sn) do
  cst:=CycleStructure(rho[3]); cst:=&cat[[i[1] : j in [1..i[2]]] : i in cst];
  a:=a+rho[2]*lambda(rho[3])*&*[chi(g^k)^Multiplicity(cst,k) : k in [1..n]];
  end for; ans cat:=[a/Factorial(n)]; end for;
 return Parent(chi)!ans; end function;
*/

intrinsic Symmetrization(chi::AlgChtrElt,P::SeqEnum) -> AlgChtrElt
{Given a character chi and a partition P, return the symmetrization}
 require IsCharacter(chi): "chi must be a character (not just a class func)";
 while 0 in P do Exclude(~P,0); end while;
 require &and[p ge 1 : p in P]: "Partition must be positive";
 require Reverse(P) eq Sort(Reverse(P)): "Partition must be non-increasing";
 if #P eq 0 then return chi^0; end if;
 return char_symm(chi,P); end intrinsic;

intrinsic IsOrthogonalCharacter(chi::AlgChtrElt) -> BoolElt
{Given a character of a finite group, determine whether it is orthogonal}
 require IsCharacter(chi): "chi must be a character";
 if not IsReal(chi) then return false; end if;
 CT:=CharacterTable(Group(Parent(chi)));
 for ct in CT do ip:=Integers()!InnerProduct(ct,chi);
  if not IsReal(ct) then
   if ip eq InnerProduct(chi,ComplexConjugate(ct)) then continue; end if;
   return false; end if; if ip mod 2 eq 0 then continue; end if;
 if Schur(ct,2) ne +1 then return false; end if; end for;
 return true; end intrinsic;

S:=SFA(Integers());

function is_frob_one(q)
 if #q eq 0 then return true; end if; q:=Reverse(Sort(q));
 if #q eq 1 then return q eq [2]; end if;
 if 1+#q ne q[1] then return false; end if;
 q:=[r-1 : r in Remove(q,1)]; while 0 in q do Exclude(~q,0); end while;
 return is_frob_one(q); end function;

function ortho_to_sym(p)
 if #p eq 0 then n:=0; else n:=&+p; end if; A:=[<p,1>];
 for u in [2..n by 2] do
  P:=[q : q in Partitions(u) | is_frob_one(q)];
  for q in P,s in Partitions(n-&+q) do
   c:=Coefficient(S.q*S.s,p)*(-1)^(u div 2);
   if c ne 0 then A cat:=[<s,c>]; end if;
   end for; end for; return A; end function;

function sym_to_ortho(p)
 if #p eq 0 then n:=0; else n:=&+p; end if; A:=[<p,1>];
 for u in [2..n by 2] do
  P:=[q : q in Partitions(u) | &and[IsEven(e) : e in q]];
  for q in P,s in Partitions(n-&+q) do
   c:=Coefficient(S.q*S.s,p); if c ne 0 then A cat:=[<s,c>]; end if;
   end for; end for; return A; end function;

/*
for p in Partitions(10) do
 A:=&+[o[2]*&+[u[2]*S.u[1] : u in ortho_to_sym(o[1])] : o in sym_to_ortho(p)];
 assert A eq S.p; end for;
*/

intrinsic OrthogonalSymmetrization(chi::AlgChtrElt,P::SeqEnum) -> AlgChtrElt
{Given a (hereditarily) orthogonal character chi and a partition P,
 return the orthogonal symmetrization}
 require IsOrthogonalCharacter(chi): "Character must be orthogonal";
 while 0 in P do Exclude(~P,0); end while;
 require IsPartition(P): "P must be a partition";
 return &+[u[2]*Symmetrization(chi,u[1]) : u in ortho_to_sym(P)];end intrinsic;

function symp_to_sym(p)
 if #p eq 0 then n:=0; else n:=&+p; end if; A:=[<p,1>];
 for u in [2..n by 2] do
  P:=[q : q in Partitions(u) | is_frob_one(ConjugatePartition(q))];
  for q in P,s in Partitions(n-&+q) do
   c:=Coefficient(S.q*S.s,p)*(-1)^(u div 2);
   if c ne 0 then A cat:=[<s,c>]; end if;
   end for; end for; return A; end function;

function sym_to_symp(p)
 if #p eq 0 then n:=0; else n:=&+p; end if; A:=[<p,1>];
 for u in [2..n by 2] do
  P:=[q : q in Partitions(u) | &and[IsEven(e) : e in ConjugatePartition(q)]];
  for q in P,s in Partitions(n-&+q) do
   c:=Coefficient(S.q*S.s,p); if c ne 0 then A cat:=[<s,c>]; end if;
   end for; end for; return A; end function;

/*
for p in Partitions(10) do
 A:=&+[s[2]*&+[u[2]*S.u[1] : u in symp_to_sym(s[1])] : s in sym_to_symp(p)];
 assert A eq S.p; end for;
*/

intrinsic IsSymplecticCharacter(chi::AlgChtrElt) -> BoolElt
{Given a character of a finite group, determine whether it is symplectic}
 require IsCharacter(chi): "chi must be a character";
 if not IsReal(chi) then return false; end if;
 CT:=CharacterTable(Group(Parent(chi)));
 for ct in CT do ip:=Integers()!InnerProduct(ct,chi);
  if not IsReal(ct) then
   if ip eq InnerProduct(chi,ComplexConjugate(ct)) then continue; end if;
   return false; end if; if ip mod 2 eq 0 then continue; end if;
 if Schur(ct,2) ne -1 then return false; end if; end for;
 return true; end intrinsic;

intrinsic SymplecticSymmetrization(chi::AlgChtrElt,P::SeqEnum) -> AlgChtrElt
{Given a (hereditarily) symplectic character chi and a partition P,
 return the symplectic symmetrization}
 require IsSymplecticCharacter(chi): "Character must be symplectic";
 while 0 in P do Exclude(~P,0); end while;
 require IsPartition(P): "P must be a partition";
 return &+[u[2]*Symmetrization(chi,u[1]) : u in symp_to_sym(P)];end intrinsic;

