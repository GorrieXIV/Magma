freeze;

/* 08.05.00: Series[3] removed from structure */
/* 14.08.02: Bugfix in Module List */

/*
 * Intrinsics for the calculations of soluble quotients of finite groups.
 * A soluble quotient is represented by the category `SQProc`.
 * In this version the category has no functions by itself, it just holds the
 * attributes attached to it.
 * The first attributes store the information given at the start of the
 * calculation, plus some main information about the current quotient.
 * they are:
 *
 * SQ    : < Map: F -> G, initial prime specification, limit for new primes>
 * Series: <id_num, weights>
 * Data  : <order, {relevant primes}, steps_to_complete>
 * Modi  : [modus_identifiers];
 * Limits: [limits given at start]
 * ModulCandidates : lists of G-modules, sorted by primes and limits.
 * Relat : Parent and children.
 * Collect: Set of Collectors
 * SplitExt: List of solution spaces for split extensions
 * NonsplitExt: List of solution spaces for nonsplit extensions
 */

/*
 * 10.05.2000 modification of the organisation of processes belonging to the same session.
 * With the first initialisation of a process a root process will be created. It keeps a list of all processes
 * belonging to that session and organizes the relations of the quotients. Each process quotient refers
 * to it.
 * It is !NOT! intended to give access to this root process to the user, it is for internal use only.
 * Attributes for the root:
 * Root   : <true, 1,F>  : The process is the root, SQP is the root process itself. In this case
 * Data:    [ <IsActive, SQP> ] complete list of SQProcs, IsActive eq true iff not deleted.
 * Relat: [{i_1,i_2}, ...] Sets of indices of the children of the i-th process.
 * Attributes for other SQProcs
 * Root  : <false, i, Root> : The process is not a root, i is the index in the list, Root is the root SQP.
 */

declare type SQProc;

declare attributes SQProc : Root,SQ, Series, Data, Modi, Limits, ModulCandidates, SplitExt, NonsplitExt,
Relat, Collect;

GaloisOrbit := function (L, r, K)

return { [(e*t) mod r : e in L] : t in K };

end function;

SetupGaloisAuts := function(r)

K := {i : i in [1..r-1] | GCD(i,r) eq 1};

return K;
end function;

SetupActMatrices := function(G, k)

mats := [];
n := NPCgens(G);
pt := PCPrimes(G);
P := [pt[i] : i in [1..k-1]];

for i := 1 to k-1 do
matsi := [];
for j := k to n do
s := Eltseq(G.j^G.i);
Append(~matsi, [s[l] : l in [k..n] ]);
end for;
Append(~mats, matsi);
end for;

return mats, P;
end function;

ExpvecAction := function(L, mm, r)

O := [];
n := #L;

for i := 1 to n do
t := 0;
for j := 1 to n do
t +:= L[j] * mm[i,j];
end for;
Append(~O, (t mod r));
end for;

return O;

end function;

CalcOrbitNew := function(L, mm, P, r)

OO := {L};
d := #mm;

for i := 1 to d do
OOT := {};
MT := mm[i];
for L in OO do
LO := ExpvecAction (L, MT, r);
if LO ne L then
Include(~OOT, LO);
for k := 2 to P[i] do
LO := ExpvecAction (LO, MT, r);
Include(~OOT, LO);
end for;
end if;
end for;
OO join:= OOT;
end for;
return OO;
end function;

NextOrbitsMinimum := function(G, LL, r)

n := NPCgens(G);
k := n - #Min(LL) + 1;

mm, P := SetupActMatrices (G, k);
LOO := {L : L in LL};
K := SetupGaloisAuts(r);

L := Min(LOO);
OT := CalcOrbitNew(L, mm, P, r);
GO := {};
for L in OT do
gtt := GaloisOrbit(L, r, K);
GO join:= gtt;
end for;
LOO diff:= GO;

return L, LOO;
end function;

CodeToRep := function(G, L, r)

g := GCD(r, GCD(L));
if r div g le 2 then
K := Rationals();
else
K := CyclotomicField(r div g);
end if;
GM := GL(1, K);
GMM := MatrixAlgebra(K, 1);

if r div g le 2 then
R := hom<G -> GM | [GM!(GMM!-1^(e div g)) : e in L]>;
else
R := hom<G -> GM | [GM!(GMM!K.1^(e div g)) : e in L]>;
end if;

return R;
end function;

SQProcCreateRoot := function(F)

/*
 * Create a new root process
 */
SQP := New(SQProc);

SQP`Root := <true, 1, F >;
SQP`Data := [<true, SQP>];
SQP`Relat := [ {Integers() | 0 } ];

return SQP;
end function;

SQProcCreateproc:= procedure(~SQRoot, epi, primes, p_limit, SQ_series, weights,
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  RatRepDegreeLimit, SQTimeLimit)

/*
 * Basic setup function, create a new SQProc and store the given values.
 * Write it to its root process SQRoot.
 */

SQP := New(SQProc);
SQP`SQ        := <epi, primes, p_limit>;
G := Codomain(epi);
ng := NPCgens(G);
if ng eq 0 then
ng := 1;
end if;
if SQTimeLimit gt 0 then
SQTimeLimit +:= Cputime();
end if;

SQP`Data   := <#G,{Integers()|t[1]:t in primes |t[1] ne 0}, ng>;
SQP`Series := <SQ_series, weights>;
SQP`Modi      := [SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus];
SQP`Limits    := [SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
                  Integers() ! RatRepDegreeLimit, SQTimeLimit];
SQP`ModulCandidates  := < [Integers() | ],[* *], [* *] >;
SQP`SplitExt  := [* *];
SQP`NonsplitExt  := [* *];
SQP`Relat     := <{Integers()| },{Integers()| }>;
SQP`Collect   := <[* *],[* *]>;

Append(~SQRoot`Data, <true, SQP>);
Append(~SQRoot`Relat, {Integers()| });
SQP`Root := <false, #SQRoot`Data, SQRoot>;

end procedure;

GetNewSQ := function (SQRoot);

k := #SQRoot`Data;

return SQRoot`Data[k,2];

end function;


ChangeQuotient := function(SQP, epi, primes, weights)

/*
 * Create a copy of the given SQProc and change the epimorphism/weights.
 */

G:= Codomain(epi);
SQN := New(SQProc);
SQN`SQ     := <epi, primes, SQP`SQ[3]>;
ng := NPCgens(G);
if ng eq 0 then
ng := 1;
end if;
SQN`Data   := <#G,SQP`Data[2] join {t[1]: t in primes | t[1] ne 0}, ng>;
SQN`Series := <SQP`Series[1], weights>;
SQN`Modi   := SQP`Modi;
SQN`Limits := SQP`Limits;
SQN`ModulCandidates  := < [Integers() |],[* *], [* *] >;
SQN`SplitExt  := [* *];
SQN`NonsplitExt  := [* *];
SQN`Relat  := <{Integers()| }, {Integers()| }>;
SQN`Collect   := <[* *],[* *]>;

SQR := SQP`Root[3];
Append(~SQR`Data, <true, SQN>);
Append(~SQR`Relat, {Integers()| });
SQN`Root := <false, #SQR`Data, SQR>;

return SQN;
end function;

InsertRelatives := procedure(~SQP, ~SQR)

// Tell SQR that it is a son of SQP, transfer information about relavant primes from SQP to SQR.

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);
if #GP gt 1 then
images := [GP.i : i in [1..np]] cat [Id(GP) : i in [np+1..nr]];
else
images := [Id(GP) : i in [1..nr]];
end if;

sq_epi := hom<GR -> GP | images>;
SQRoot := SQR`Root[3];
SQRi  := SQR`Root[2];
SQPi  := SQP`Root[2];

SQR`Data[2] join:= SQP`Data[2];

if 0 in SQP`Data[2] then
SQR`Data[3] := 0;
else
nt := SQP`Data[3] + nr - np;
if nt lt SQR`Data[3] then
SQR`Data[3] := nt;
end if;
end if;

Include(~(SQP`Relat[2]), SQRi);
Include(~(SQR`Relat[1]), SQPi);

// tell SQR it has a new child ...
Include(~SQRoot`Relat[SQRi], SQPi);
end procedure;

intrinsic Initialize(F::GrpFP:
          SQ_series := 1, RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc
{Initialize a SQProc for a finitely presented group F without any information
 about the relevant primes.}

SQR := SQProcCreateRoot(F);
G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
SQProcCreateproc (~SQR, epi, [], 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);

SQP := GetNewSQ(SQR);
return SQP;
end intrinsic;

intrinsic Initialize(epi::Map:
          SQ_series := 1, RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc
{Initialize a SQProc for a given quotient epi:F -> G without any information
 about the relevant primes.}
SQR := SQProcCreateRoot (Domain(epi));
SQProcCreateproc (~SQR, epi, [], 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQR);

return SQP;
end intrinsic;

intrinsic Initialize(F::GrpFP, n::RngIntElt:
          SQ_series := 1, RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc
{Initialize a SQProc for a finitely presented group F with expected order n. }

require n ge 0 : "n must be a nonnegative integer.";

SQR := SQProcCreateRoot(F);
G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
SQProcCreateproc (~SQR, epi, Factorization(n), 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);

SQP := GetNewSQ(SQR);
return SQP;
end intrinsic;

intrinsic Initialize(epi::Map, n::RngIntElt:
          SQ_series := 1, RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc
{Initialize a SQProc for a given quotient epi:F -> G with expected order n.}

require n ge 0 : "n must be a nonnegative integer.";

SQR := SQProcCreateRoot (Domain(epi));
SQProcCreateproc (~SQR, epi, Factorization(n), 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQR);

return SQP;
end intrinsic;

// ===========================================================================
// Copy of the last version, transscripted to use the SQProc stuff
// ===========================================================================
/*
 * The Verbose_ modes are organized as bitmap flags, so one can
 * combine print options by adding the given values.
 * Names, Values and Meanings:
 *
 * MSQ_TraceFunc:  (0 - 2)
 *     Give messages about the current function called.
 *     0:  No messages (Default)
 *     1:  Important functions
 *     2:  almost all (except some tiny and trivial functions
 *
 * MSQ_Collector (0 - 1)
 *    If 1, the timing for the setup of the collector is printed.
 *
 * MSQ_RepsCalc (0 - 3)
 *     1:  timing for calculating representations/modules on each level
 *     2:  some statistics on each level
 *
 * MSQ_RepsCheck   (0 - 3)
 *     1:  Timing information for checking extensions of modules
 *     2:  Statistics of the number of modules to be checked.
 *
 * MSQ_PrimeSearch (0 - 15)
 *     Information about different part in the algorithm for determine
 *     the relevant primes.
 *     1:  Timings and statistics about the calculation of rational
 *         representations (in combination with MSQ_RepsCalc).
 *     2:  Timings of the transformation into integral representations.
 *     4:  Calculation of the relevant primes determination step
 *     8:  Printing of new relevant primes
 *
 * MSQ_Messages (0 - 1)
 *     Given information about the size of the soluble quotients
 *     calculated so far.
 */

// Default levels of Print statements
// SetVerbose("MSQ_PrimeSearch" , 0);
// SetVerbose("MSQ_RepsCalc"    , 0);
// SetVerbose("MSQ_RepsCheck"   , 0);
// SetVerbose("MSQ_Collector"   , 0);
// SetVerbose("MSQ_TraceFunc"   , 0);
// SetVerbose("MSQ_Messages"    , 0);

/*
 * Definitions of variables giving different strategies.
 * These are optional arguments of the main function MSQ.
 *
 * SQ_CollectorModus :
 *     defines the setup modus for the symbolic collector:
 *     0:  complete precalculation of the tables
 *     1:  Partial precalculations, depending on the size of the tables,
 *     2:  Dynamic setup during normalisation (default)
 *
 * SQ_ModulCalcModus :
 *     defines how the modules for nonsplit extensions are determined
 *     CAUTION: a change of this parameter can lead to wrong results if
 *               a series other than the SAG is chosen.
 *     0:   Calculate and check all modules (default)
 *     1:   Take constituents of tensor products, plus further
 *          candidates (faster, but need some checks)
 *     2:   Restrict to constituents tensor products.
 *          (better only for big quotients.)
 *         
 * SQ_PrimeSearchModus :
 *     Defines the strategy of finding new relevant primes
 *
 *     0:   No prime search. (Default, if not explicitly requested)
 *     1:   Prime search after SQ calculation and quit.
 *          (suitable for checking the maximality of an SQ of known
 *           order/prime divisors)
 *     2:   Prime search after SQ calculation; continue if new primes
 *          occure.
 *     3:   Prime search end beginning of a new nilpotent section.
 *          (Default for explicite primesearch request)
 *     4:   Prime search at beginning of e new layer in the LCS
 *     5:   Prime search after each extension of the SQ.
 */

/*
 * A collection of help functions to set/read theses variables.
 */

MSQVerboseIsSet := function(NN, i)
// checks whether the i-th bit is set in A

A := GetVerbose(NN);
if A lt i then
return false;
else
A := A mod (2*i);
if A lt i then
return false;
else
return true;
end if;
end if;

end function;

SQ_TraceFunction := procedure(A, l);
// print message if MSQ_TraceFunc has given value

x := GetVerbose("MSQ_TraceFunc") mod (2*l);
if x ge l then
if l eq 1 then
print "   Enter:", A;
else
print "     Enter:", A;
end if;
end if;

end procedure;

ChangeDefaultVerbose := function(NN, i)

if not IsVerbose(NN) then
SetVerbose(NN, i);
return true;
else
return false;
end if;

end function;

MSQsetVerboseForOption := procedure(~pr)
case pr:
    when -1:
        pr := 0;
    when 0:
        SetVerbose("MSQ_PrimeSearch", 0);
        SetVerbose("MSQ_RepsCalc"   , 0);
        SetVerbose("MSQ_RepsCheck"  , 0);
        SetVerbose("MSQ_Collector"  , 0);
        SetVerbose("MSQ_TraceFunc"  , 0);
SetVerbose("MSQ_Messages"   , 0);
    when 1:
t := ChangeDefaultVerbose("MSQ_PrimeSearch", 8);
t := ChangeDefaultVerbose("MSQ_Messages"   , 1);
    when 2:
t := ChangeDefaultVerbose("MSQ_PrimeSearch", 10);
t := ChangeDefaultVerbose("MSQ_RepsCalc"   , 1);
t := ChangeDefaultVerbose("MSQ_RepsCheck"  , 1);
t := ChangeDefaultVerbose("MSQ_Collector"  , 1);
t := ChangeDefaultVerbose("MSQ_Messages"   , 1);
    when 3:
t := ChangeDefaultVerbose("MSQ_PrimeSearch", 11);
t := ChangeDefaultVerbose("MSQ_RepsCalc"   , 2);
t := ChangeDefaultVerbose("MSQ_RepsCheck"  , 2);
t := ChangeDefaultVerbose("MSQ_Collector"  , 1);
t := ChangeDefaultVerbose("MSQ_Messages"   , 1);
    when 4:
t := ChangeDefaultVerbose("MSQ_PrimeSearch", 15);
t := ChangeDefaultVerbose("MSQ_RepsCalc"   , 3);
t := ChangeDefaultVerbose("MSQ_RepsCheck"  , 3);
t := ChangeDefaultVerbose("MSQ_Collector"  , 1);
t := ChangeDefaultVerbose("MSQ_Messages"   , 1);
t := ChangeDefaultVerbose("MSQ_TraceFunc"  , 1);
    when 5:
t := ChangeDefaultVerbose("MSQ_PrimeSearch", 15);
t := ChangeDefaultVerbose("MSQ_RepsCalc"   , 3);
t := ChangeDefaultVerbose("MSQ_RepsCheck"  , 3);
t := ChangeDefaultVerbose("MSQ_Collector"  , 1);
t := ChangeDefaultVerbose("MSQ_Messages"   , 1);
t := ChangeDefaultVerbose("MSQ_TraceFunc"  , 2);
end case;
end procedure;

MSQGetCollectorModus := function( SQ_CollectorModus  );

CollectorModi := ["Complete", "Partial", "Dynamic"];
return CollectorModi[SQ_CollectorModus+1];
end function;

MSQGetRepsOption := function(flag)
// return the value for the optional arg `Print` in the calculation of
// Reps/Modules

if flag eq true then  // rational representation calculation
if MSQVerboseIsSet("MSQ_PrimeSearch", 1) then
if MSQVerboseIsSet("MSQ_RepsCalc", 1) then
if MSQVerboseIsSet("MSQ_RepsCalc", 2) then
return 11;
else
return 7;
end if;
else
if MSQVerboseIsSet("MSQ_RepsCalc", 2) then
return 8;
else
return 4;
end if;
end if;
else
return 2*GetVerbose("MSQ_RepsCalc");
end if;

else             // finite modules calculation
return 2*GetVerbose("MSQ_RepsCalc");
end if;
end function;

Message_SQ_return_comment := function(flag)

comm_seq := [
"Soluble quotient stops when no extension with this specification was found.",
"Soluble quotient with this specification successfully completed.",
"Soluble quotient terminates when hitting a given bound.",
"Soluble quotient terminates when free abelian section found.",
"Soluble quotient reached quotient size limit",
"(with respect to limited prime search)",
"Soluble quotient reached time limit."
];

return comm_seq[flag+1];
end function;

/*
 * Help function for various situations
 */

find_nontrivial_length := function(weights, SQ_PrimeSearchModus);

SQ_TraceFunction("find_nontrivial_length", 2);

if #weights eq 0 then
return 0;
end if;

nt := 0;
if SQ_PrimeSearchModus le 2 then
for lw in weights do /* nilpotent section */
for lwl in lw do /* sequence of head/layers */
for lwi in lwl do /* sequence of prime plus dimension */
for i := 2 to #lwi do /* add up the dimensions */
nt +:= Dimension(lwi[i]);
end for;
end for;
end for;
end for;
else
lw := weights[#weights]; /* last nilpotent section */
if SQ_PrimeSearchModus eq 3 then
for lwl in lw do /* sequence of head/layers */
for lwi in lwl do /* sequence of prime plus dimension */
for i := 2 to #lwi do /* add up the dimensions */
nt +:= Dimension(lwi[i]);
end for;
end for;
end for;
else
lwl := lw[#lw]; /* last head/layer */
if SQ_PrimeSearchModus eq 4 then
for lwi in lwl do /* sequence of prime plus dimension */
for i := 2 to #lwi do /* add up the dimensions */
nt +:= Dimension(lwi[i]);
end for;
end for;
elif SQ_PrimeSearchModus eq 5 then
lwi:= lwl[#lwl];         /* last module in layer   */
nt := Dimension(lwi[#lwi]);
end if;
end if;
end if;

return nt;
end function;

// Given matrix X over Z and sequence ignore_primes of primes to ignore

ElementaryPrimeDivisors := function(X, ignore_primes)
SQ_TraceFunction("ElementaryPrimeDivisors", 2);

c := Ncols(X);
if c eq 0 then return []; end if;

Z := Integers();
r := Nrows(X);
L := [];

p := 1;
ii := 0;

while ii eq 0 do
    p := NextPrime(p);
    while p in ignore_primes do
	p := NextPrime(p);
    end while;
    K := GF(p);
    V := VectorSpace(K, c);
    S := sub<V|>;

    rows := [];
    for i := 1 to r do
        v := V ! X[i];
        Include(~S, v, ~new);
        if new then
            Append(~rows, X[i]);
            if #rows eq c then
		ii := i;
                break;
            end if;
        end if;
    end for;

    if Rank(X) lt c then
        return [0];
    elif ii eq 0 then
	Append(~L, p);
    end if;
end while;

MR := MatrixRing(Z, c);
Y := MR ! rows;
D := Abs(Determinant(Y));

if D eq 0 then
print "BUG, determinant zero!!!";
end if;
for pt in ignore_primes join Seqset(L) do
while D mod pt eq 0 do
D div:= pt;
end while;
end for;
if D eq 1 then
return L;
end if;

if D gt 10^50 or Max(PrimeDivisors(D)) gt 100000 then
S := {j : j in [1..c]};
tD := 1;
fl := true;
k := Random(S);
i := ii+1 ;
while i le r do
Rt := rows[k];
rows[k] := X[i];
Y := MR ! rows;
tD := Determinant(Y);
if tD ne 0 then
D := GCD(tD, D);
if D eq 1 then
return [];
elif D lt 10^20 and Max(PrimeDivisors(D)) lt 100000 then
break;
end if;
fl := true;
else
rows[k] := Rt;
if fl eq true then
i -:= 1;
fl := false;
end if;
end if;
k := Random(S);
i +:= 1;
end while;
end if;

for p in PrimeDivisors(D) do
    if p gt 2^30 then
    // New approach: hopefully handles big primes
	K := GF(p);
	V := VectorSpace(K, c);
	S := sub<V|>;

	for i := 1 to r do
	    v := V ! X[i];
	    Include(~S, v, ~new);
	    if #rows eq c then
		break;
	    end if;
	end for;

	if #rows lt c then
	    Append(~L, p);
	end if;
    // end of new approach
    else
	MS := RMatrixSpace(GF(p), r, c);
	MSX := MS ! X;
	if Rank(MSX) lt c then
	    Append(~L, p);
	end if;
    end if;
end for;

return L;

end function;

IntegralRepresentation := function (DD)
SQ_TraceFunction("IntegralRepresentation", 2);

t := Cputime();
Q := Rationals();
Z := Integers();
G := Domain(DD);
ng := NPCgens(G);
GLM := Codomain(DD);
d := Degree(GLM);

LS := StandardLattice(d);
RS := RSpace(Q, d);
AM := MatrixRing(Z, d);

Mats := [DD(G.i) : i in {1 .. ng}];

IntMat := [CanChangeUniverse(Eltseq(M), Z) : M in Mats];
flag := false in IntMat;
DDO := DD;
tries := 0;

while flag eq true do
    flag := false;
    tries +:= 1;
    MatR := [Mats[i] : i in {1..#Mats} | IntMat[i] eq false];
ST := [Eltseq(M[i]): i in {1..Nrows(M)}, M in MatR];
S := [t : t in ST | CanChangeUniverse(t, Z) eq false];
    // S := [Eltseq((RS!l)*M) : l in Basis(LS), M in MatR];
    LL := ext<LS| S>;
BB := Basis(LL);
BBT := [(RS!bb) : bb in BB | bb notin LS];
BB := 0;
    T := {l*M : l in BBT, M in Mats};
    LLe := ext<LL| T>;

    if LLe eq LL then
        BM := LLL(BasisMatrix(LL));
        BMi := BM^-1;
        Mats := [BM*M*BMi : M in Mats];
        DDO := hom< G -> GLM | Mats > ;
    else
        BM := LLL(BasisMatrix(LLe));
        BMi := BM^-1;
        Mats := [BM*M*BMi : M in Mats];
        IntMat := [CanChangeUniverse(Eltseq(M), Z) : M in Mats];
        flag := false in IntMat;
        if flag eq false then
            DDO := hom< G -> GLM | Mats > ;
        end if;
    end if;
end while;

if MSQVerboseIsSet("MSQ_PrimeSearch", 4) then
print "   Transform to integral representation:", Cputime(t);
end if;

return DDO, tries;
end function;

FindBaseToStandard := function(A);
Z := Integers();
ns := Nrows(A);
nc := Ncols(A);
rA := Rank(A);
S := [];
k := 1;
count_minus := 0;
for i := 1 to rA do
while A[i,k] eq 0 do
k +:= 1;
end while;
if A[i,k]^2 eq 1 then
Append(~S, k);
else
Append(~S, -k);
count_minus +:= 1;
end if;
end for;

Sc := [i : i in [1..nc] | i notin S];
nSc := #Sc;
T2 := RMatrixSpace(Z, nc, nSc) ! 0;
for i := 1 to nSc do
T2[Sc[i], i] := 1;
end for;

if count_minus eq 0 then
A3 := Transpose(T2);
else
T1 := RMatrixSpace(Z, count_minus,ns) ! 0;
k := 1;                                      
for i := 1 to ns do
if S[i] lt 0 then
T1[k,i] := 1;
k +:= 1;
if k gt count_minus then
break;
end if;
end if;
end for;
A2 := T1 * A * T2;
D, RT, CT := SmithForm(A2);        
rD := Rank(D);
CTI := CT^-1;
T3 := RMatrixSpace(Z, nSc - rD, nSc) ! 0;
for i := 1 to nSc - rD do
T3[i,i+rD] := 1;
end for;
A3 := T3 * CTI * Transpose(T2);
end if;

/* Test of the correctness of this algorithm.
Lu := PureLattice(Lattice(A));
Lc := Lattice(A3);
BL := Basis(Lc) cat Basis(Lu);
LS := StandardLattice(nc);
LL := sub<LS| BL>;
ITest := Index(LS, LL);
print ITest;
if ITest ne 1 then
print "ERROR!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
print "Echelon"; time UH2, T := EchelonForm(Transpose(A));
print "Smith:";   time D, TB := SmithForm(UH2);
print "Inverse";  time Bi := Transpose(TB*T)^-1;
rD := Rank(D);
Bz := [Bi[i] : i in {rD+1..Nrows(Bi)}];
AA := [];
for b in Bz do
AA cat:= Eltseq(b);
end for;
L := Lattice(Ncols(A), AA);
UBR := RMatrixSpace(Z, Nrows(Bi)-rD, Ncols(A));
tmp := UBR!0;
for i in {rD+1..Nrows(Bi)} do
tmp[i-rD, i] := 1;
end for;
AA := tmp*Bi;
print A, A3, AA;
end if;
 */

return A3;
end function;

Coboundmats := function(FG, DD, epi)

t := Cputime();
Q := Rationals();
Z := Integers();
G := Domain(DD);
k := Ngens(FG);
g := Codomain(DD);
d := Degree(g);

UM := RMatrixSpace(Z, d, d*k);
HM := RMatrixSpace(Z, d, d);

TM := [Transpose(DD(epi(FG.i))) : i in {1..k}];

MM := [UM ! 0 :  i in {1..k}];
for i := 1 to k do
for j := 1 to d do
MM[i,j, j+(i-1)*d] := 1;
end for;
end for;
U := (HM ! TM[1])*MM[1] - MM[1];
for i := 2 to k do
U +:= (HM ! TM[i]) * MM[i] - MM[i];
end for;

UH := HermiteForm(U: Integral := true);
Bi := FindBaseToStandard(UH);

CR := RMatrixSpace(Integers(), d, Nrows(Bi));
Cobounds := [];
for i := 1 to k do
M := CR ! 0;
for j := 1 to Nrows(Bi) do
LBI := Bi[j];
for jj := 1 to d do
M[jj,j] := LBI[jj + d*(i-1)];
end for;
end for;
Append(~Cobounds, M);
end for;

AM := MatrixAlgebra(Integers(), d);
DDG := [AM ! DD(epi(FG.i)) : i in {1..k}];
DDGi := [DDG[i]^-1 : i in {1..k}];
CoboundInvs := [-1*DDGi[i] * Cobounds[i]: i in {1..k}];

if MSQVerboseIsSet("MSQ_PrimeSearch", 2) then
print "   Setup of the coboundary matrices took:", Cputime(t);
end if;
return DDG, DDGi, Cobounds, CoboundInvs, 1;
end function;

RelationsImage := function(r, DDG, DDGi, Cobounds, CoboundInvs)
SQ_TraceFunction("RelationsImage", 2);

if Eltseq(r[2]) eq [] then
    El := Eltseq(r[1]);
else
    El := Eltseq(r[1] * r[2]^-1);
end if;

if El[1] gt 0 then
    A := DDG[El[1]];
    C := Cobounds[El[1]];
else
    A := DDGi[-El[1]];
    C := CoboundInvs[-El[1]];
end if;

for j := 2 to #El do
    e := El[j];
    if e gt 0 then
        C := C + A*Cobounds[e];
        A := A*DDG[e];
    else
        e := -e;
        C := C + A*CoboundInvs[e];
        A := A*DDGi[e];
    end if;
end for;

return C;

end function;

FirstCohomPrimes := function (FG, DDQ, epi, PP_known)
SQ_TraceFunction("FirstCohomPrimes", 1);

t := Cputime();
DD := IntegralRepresentation(DDQ);

R := Relations(FG);
Z := Integers();

DDG, DDGi, Cobounds, CoboundInvs, LIndex := Coboundmats(FG, DD, epi);

RC := [];

for r in R do
    RC cat:= Eltseq(RelationsImage(r,DDG,DDGi, Cobounds, CoboundInvs));
end for;
U := RMatrixSpace(Integers(),#R*Nrows(Cobounds[1]), Ncols(Cobounds[1]));
M := U!RC;
PD := ElementaryPrimeDivisors (M, PP_known);
return PD;

end function;

MSQfindprimes := function(epi, nt, RatRepDegreeLimit, SQTimeLimit)
SQ_TraceFunction("MSQfindprimes", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * nt : Number of generators on which the rep must not be completely
 *      trivial.
 */

FG := Domain(epi);
 G := Codomain(epi);
 R := Rationals();

// take care of the free group!
if #Relations(FG) eq 0 then
return {0};
end if;

if #G eq 1 then
AI := AbelianQuotientInvariants(FG);
if 0 in AI then
return {0};
end if;
P := {};
for q in AI do
P join:= {p : p in PrimeDivisors(q)};
end for;
return P;
end if;

t := Cputime();

if nt ne 0 then

D := AbsolutelyIrreducibleRepresentationsSchur(G, R, nt : GaloisAction:="Yes",Process:=true, MaxDimension := RatRepDegreeLimit,
Print := MSQGetRepsOption(true));
F := [* D[1] *];
E := Remove(D, 1);
AbsolutelyIrreducibleModulesDelete(~F);
D := IrreducibleRepresentationsSchur(G, R, E : MaxDimension := RatRepDegreeLimit,
Print := MSQGetRepsOption(true));
AbsolutelyIrreducibleModulesDelete(~E);
else
D := IrreducibleRepresentationsSchur(G, R: MaxDimension := RatRepDegreeLimit,
Print := MSQGetRepsOption(true));
end if;
if MSQVerboseIsSet("MSQ_PrimeSearch", 1) then
dD := [];
for i := 1 to #D do
Append(~dD, Degree(Codomain(D[i])));
end for;
print "   Needed", Cputime(t) ,"sec to calculate",
#D, "rational representations with degrees:";
print "    ", dD;
end if;

PP_known := {p: p in PCPrimes(G)};
PP := {};
for delta in D do
t := Cputime();
if RatRepDegreeLimit gt 0 and Degree(Codomain(delta)) gt RatRepDegreeLimit then
print "degree of rational representation violates the limit.";
continue;
end if;
S := FirstCohomPrimes(FG, delta, epi, PP_known);
if S eq [0] then
AbsolutelyIrreducibleModulesDelete(~D);
return {0};
end if;
if SQTimeLimit gt 0 and Cputime() gt SQTimeLimit then
return PP;
end if;

if MSQVerboseIsSet("MSQ_PrimeSearch", 2) then
print "   ", Cputime(t) ,"sec to check", delta;
if #S ne 0 then
vprint MSQ_PrimeSearch,8: "   Occuring primes:", S;
end if;
elif #S ne 0 then
vprint MSQ_PrimeSearch,8: "   Occuring primes for :", delta, S;
end if;

PP := PP join Seqset(S);

end for;
// AbsolutelyIrreducibleModulesDelete(~D);

return PP;
end function;

MSQfindprimesStepwise := function(epi, nt, RatRepDegreeLimit, SQTimeLimit)

/* epi: epimorphism FG --> G, FG and G are read from it.
 * nt : Number of generators on which the rep must not be completely
 *      trivial.
 */

FG := Domain(epi);
 G := Codomain(epi);
 R := Rationals();

// take care of the free group!
if #Relations(FG) eq 0 then
return {0};
end if;

if #G eq 1 then
AI := AbelianQuotientInvariants(FG);
if 0 in AI then
return {0};
end if;
P := {};
for q in AI do
P join:= {p : p in PrimeDivisors(q)};
end for;
return P;
end if;

t := Cputime();

// Prepare the stepwise prime calculation, check wether it is worth it.

SG := CompositionSeries(G);
nn := 1;
while nn le #SG and IsAbelian(SG[nn]) eq false do
nn +:= 1;
end while;
while nn le #SG and IsNormal(G, SG[nn]) eq false do
nn +:= 1;
end while;
if nn ge #SG -1 then
P := MSQfindprimes(epi, nt, RatRepDegreeLimit, SQTimeLimit);
return P;
end if;

LMt, r := LinearRepresentations(SG[nn], 0);

print "Number of linear reps up to galois:", #LMt;

PP_known := {p: p in PCPrimes(G)};
PP := {};
while #LMt ne 0 do
time L, LMt := NextOrbitsMinimum(G, LMt, r);

dD := [];
Rep := CodeToRep(SG[nn], L, r);
RD := [* < AbsIrrFromMap(Rep), Rep > *];
D := IrreducibleRepresentationsSchur(G, R, RD: MaxDimension := RatRepDegreeLimit,Print := MSQGetRepsOption(true));
if MSQVerboseIsSet("MSQ_PrimeSearch", 1) then
for i := 1 to #D do
Append(~dD, Degree(Codomain(D[i])));
end for;
print "   Needed", Cputime(t) ,"sec to calculate",
#D, "rational representations from", L , "with degrees:";
print "    ", dD;
end if;
AbsolutelyIrreducibleRepresentationsDelete(~RD);
RD := 0;

for delta in D do
t := Cputime();
S := FirstCohomPrimes(FG, delta, epi, PP_known join PP);
if S eq [0] then
return {0};
end if;

if MSQVerboseIsSet("MSQ_PrimeSearch", 2) then
print "   ", Cputime(t) ,"sec to check", delta;
if #S ne 0 then
vprint MSQ_PrimeSearch,8: "   Occuring primes:", S;
end if;
elif #S ne 0 then
vprint MSQ_PrimeSearch,8: "   Occuring primes for :", delta, S;
else
vprint MSQ_PrimeSearch,8: "   No primes for :", delta;
end if;

PP := PP join Seqset(S);
if SQTimeLimit gt 0 and Cputime() gt SQTimeLimit then
return PP;
end if;

end for;
end while;

return PP;
end function;

intrinsic Primes(SQP::SQProc)
{Calculate the set of relevant primes for SQP.}

nt := SQP`Data[3];
if nt eq 0 then
return;
end if;

epi := SQP`SQ[1];

PP := MSQfindprimesStepwise(epi, nt, Integers() ! SQP`Limits[5], SQP`Limits[6]);
SQP`Data[2] join:= PP;
SQP`Data[3] := 0;

end intrinsic;

intrinsic AddPrimes(SQP::SQProc, p::RngIntElt: IsComplete := -1)
{Add the given prime to the set of relevant primes.}

if p eq 0 then
SQP`Data[2] := {0};
SQP`Data[3] := 0;
else
SQP`Data[2] join:= {p};
if Type(IsComplete) eq BoolElt then
if IsComplete eq true then
SQP`Data[3] := 0;
end if;
end if;
end if;

end intrinsic;

intrinsic AddPrimes(SQP::SQProc, mp::SetEnum: IsComplete := -1)
{mp is a set of primes which are added to the relevant primes for SQP.}

if 0 in mp then
SQP`Data[2] := {0};
SQP`Data[3] := 0;
else
SQP`Data[2] join:= mp;
if Type(IsComplete) eq BoolElt then
if IsComplete eq true then
SQP`Data[3] := 0;
end if;
end if;
end if;

end intrinsic;

intrinsic ReplacePrimes(SQP::SQProc, mp::SetEnum: IsComplete := -1)
{Replace the set of relevant primes in SQP by the given set.}

if 0 in mp then
SQP`Data[2] := {0};
SQP`Data[3] := 0;
else
SQP`Data[2] := mp;
if Type(IsComplete) eq BoolElt then
if IsComplete eq true then
SQP`Data[3] := 0;
else
SQP`Data[3] := NPCgens(Codomain(SQP`SQ[1]));
end if;
elif IsComplete ge 0 then
SQP`Data[3] := IsComplete;
end if;
end if;

end intrinsic;

find_weight_right := function(wseq, limit, offset)

if limit eq 0 then
    for k := 2 to #wseq do
        offset +:= Dimension(wseq[k]);
    end for;
    return [offset];
end if;

mw := [offset];
pp := wseq[1];
d := 0;
for i := 2 to #wseq do
    if pp^(d+Dimension(wseq[i])) gt limit then
        if d eq 0 then
            Append(~mw, mw[#mw] + Dimension(wseq[i]));
        else
            Append(~mw, mw[#mw] + d);
            d := Dimension(wseq[i]);
        end if;
    else
        d +:= Dimension(wseq[i]);
    end if;
end for;
if d ne 0 then
    Append(~mw, mw[#mw] + d);
end if;
Remove(~mw, 1);

return mw;

end function;

find_my_weights := function(weights, limit)
SQ_TraceFunction("find_my_weights", 2);

if #weights eq 0 then
    return [];
end if;

out := [];
for i := 1 to #weights do
    NS := weights[i];
    for j := 1 to #NS do
        layer := NS[j];
        for k := 1 to #layer do
            p_layer := layer[k];
            if out eq [] then
                pd := find_weight_right(p_layer, limit, 0);
            else
                pd := find_weight_right(p_layer, limit, out[#out]);
            end if;
            out cat:= pd;
        end for;
    end for;
end for;

return out;
end function;

RepsListDelete := procedure(~DL)

for ip := 1 to #DL do
    D := DL[ip];
    if #D ne 0 then
        AbsolutelyIrreducibleModulesDelete(~D);
    end if;
end for;

end procedure;

RepsListFind := function(DL, p)

for ip := 1 to #DL do
    D := DL[ip];
    if #D ne 0 then
        delta := D[1];
        if p eq Characteristic(CoefficientRing(delta[2])) then
            return true, D;
        end if;
    end if;
end for;

return false, _;
end function;

ModuleListe := function(G, primes, ng, agsflag, ags_last_prime)
SQ_TraceFunction("ModuleListe", 2);

/*
 * create the list of representations interesting for relevant primes.
 * the reps are ordered s.t. those which are nontrivial on the last
 * nilpotent section appear first, their number is stored in DLnum.
 * the lists are modified s.t. the handle is still a module over its
 * splitting field whils the explicit module is given over GF(p).
 * (this part might be obsolete soon)
 */

NewPrimes := [];
np := #primes;
DL := [* *];
DLnum := [];

for ip := 1 to np do
    if ags_last_prime eq primes[ip,1] then
        Append(~NewPrimes, primes[ip]);
        Append(~DL, [* *]);
        Append(~DLnum, 0);
        continue;
    end if;
DLstat := []; /* sequence for statistics */
    R := GF(primes[ip,1]);
    e := primes[ip,2];
    NWi := [ primes[ip,1] ];
    if agsflag eq true and ng ne 0 then
        E := AbsolutelyIrreducibleModulesSchur(G, R, ng :
                GaloisAction:="Yes",Process := true, MaxDimension := e,
Print := MSQGetRepsOption(false));
        F := [* E[1] *];
        Remove(~E, 1);
D := AbsolutelyIrreducibleModulesSchur(G, R, F :
                GaloisAction:="Yes",Process := true, MaxDimension := e,
Print := MSQGetRepsOption(false));
AbsolutelyIrreducibleModulesDelete(~F);
Append(~DLnum, #D);
F := 0;
if #E gt 0 then
F := AbsolutelyIrreducibleModulesSchur(G, R, E :
                GaloisAction:="Yes",Process := true, MaxDimension := e,
Print := MSQGetRepsOption(false));
AbsolutelyIrreducibleModulesDelete(~E);
D cat:= F;
F := 0;
end if;
    else
        D := AbsolutelyIrreducibleModulesSchur(G, R : GaloisAction := "Yes",
                          Process := true, MaxDimension := e,
  Print := MSQGetRepsOption(false));
        Append(~DLnum, #D);
    end if;
// get the corresponding Fp-moduls
    DD := IrreducibleModulesSchur(G, R, D:
Sort := false, Print := MSQGetRepsOption(false));
    for i := 1 to #D do
Append(~DLstat, <Dimension(D[i,2]),
Degree(CoefficientRing(D[i,2]))>);
        D[i,2] := DD[1];
Remove(~DD, 1);
    end for;
DD := 0;
    if e eq 0 then
        Append(~NewPrimes, primes[ip]);
    end if;
    Append(~DL, D);
vprint MSQ_RepsCalc, 2: "   ",#DLstat,"modules in characteristic",
primes[ip,1], "<dim, degree(R)>:\n", "   ", DLstat;
end for;

return NewPrimes, DL, DLnum;
end function;


MSQallsplit := function(SQP);

SQ_TraceFunction("MSQallsplit", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * Primes: sequence of tuples <p_i, e_i>, where e_i is 0 or an
 *         upper bound for the extension size.
 * weights: Sequences describing the ags structure of G.
 * agsflag: function is called in ags-context, i.e. we can exclude
 * some modules from the list.
 */

epi     := SQP`SQ[1];
primes  := SQP`SQ[2];
weights := SQP`Series[2];
agsflag := SQP`Series[1] eq 1;

SQ_PrimeSearchModus := SQP`Modi[1];

FG := Domain(epi);
 G := Codomain(epi);

if #G eq 1 and SQ_PrimeSearchModus ge 3 then
nt := find_nontrivial_length(weights, SQ_PrimeSearchModus);
new_primes := MSQfindprimes(epi, nt, Integers() ! SQP`Limits[5], SQP`Limits[6]);
if 0 in new_primes then
return 3, SQP, [* *];
end if;
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
if #new_primes ne 0 then
if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print "+++ New primes have been found:", new_primes;
end if;
for p in new_primes do
Append(~primes, <p, SQP`SQ[3]>);
end for;
SQP`Data[2] join:= new_primes;
SQP`Data[3] := 0;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQP, [* *];
end if;
else
new_primes := {};
end if;

np := #primes;
if np eq 1 then
R := GF(primes[1,1]);
else
R := Integers();
end if;

t := Cputime();
if #weights eq 0 then
VS := MSQLettersplit(G, R: Setup := MSQGetCollectorModus(SQP`Modi[3]));
else
mw := find_my_weights(weights, 65);
VS := MSQLettersplit(G, R, mw: Setup := MSQGetCollectorModus(SQP`Modi[3]));
lw := weights[#weights]; /* last nilpotent section */
end if;

vprint MSQ_Collector: "   Symbolic collector setup:", Cputime(t), "sec";

NW := [];   /* Sequence for the new weights */
NewPrimes := []; /* sequence of the remaining primes */

nt := 0;
nt := find_nontrivial_length(weights, SQ_PrimeSearchModus);

if agsflag eq true and nt ne 0 and #lw[1] eq 1 then
ags_last_prime := lw[1,1,1];
// last nilpotent section was p-group, so this p need no check
else
ags_last_prime := -1;
end if;

NewPrimes, DL, DLnum := ModuleListe(G,primes,nt,agsflag,ags_last_prime);

for ip := 1 to np do
D := DL[ip];
if #D eq 0 then
continue;
end if;

e := primes[ip,2];

vprint MSQ_RepsCheck,2: "   Check split extensions for",
#D, "modules for prime", primes[ip,1];

NWi := [* primes[ip,1] *];

    for dn := #D to 1 by -1 do
        delta := D[dn];
Remove (~D, dn);
/* check that delta is nontrivial on last nilpotent section */
Fp_dim := Dimension(delta[2]) * Degree(CoefficientRing(delta[2]));
if e gt 0 and e lt Fp_dim then
continue;
end if;

t := Cputime();
dd, new_epi := MSQsplit(VS, epi, delta);
ndd := Integers()!(dd / Fp_dim);

if MSQVerboseIsSet("MSQ_RepsCheck",1) then
if ndd eq 0 then
print "   Needed", Cputime(t) ,"sec to check ",delta[2];
else
print "   Needed", Cputime(t) ,"sec to check ",delta[2],
"found multiplicity", ndd;
end if;
elif ndd ne 0 then
vprint MSQ_Messages:
"   found multiplicity", ndd, "for module", delta[2];
end if;

if dd ne 0 then /* step was successfull */
            for i := 1 to ndd do
                Append(~NWi, delta[2] );
            end for;
delta := 0;
epi := new_epi;
if e gt 0 then
e -:= dd;
if e le 0 then
break;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR, DL;
end if;

if SQ_PrimeSearchModus eq 5 then
new_primes join:= MSQfindprimes(epi, dd, Integers() ! SQP`Limits[5], SQP`Limits[6]);
if 0 in new_primes then
if e gt 0 then
Append(~NewPrimes, <primes[ip,1], e>);
end if;
if #NWi gt 1 then
Append(~NW, NWi);
Append(~weights, [NW]);
end if;
                    Append(~NewPrimes, <primes[ip,1], e>);
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
 return 3, SQR, DL;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR, DL;
end if;
end if;

end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR, DL;
end if;
end for;
if e gt 0 then
Append(~NewPrimes, <primes[ip,1], e>);
end if;
if #NWi gt 1 then
Append(~NW, NWi);
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR, DL;
end if;
end for;
ttt := LetterVarDelete(VS);

if #NW gt 0 then
Append(~weights, [NW]);
if SQ_PrimeSearchModus eq 4 then
nt := find_nontrivial_length(weights, SQ_PrimeSearchModus);
new_primes join:= MSQfindprimes(epi,nt, Integers() ! SQP`Limits[5],SQP`Limits[6]);
if 0 in new_primes then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 3, SQR, DL;
end if;
end if;
if SQ_PrimeSearchModus gt 3 then
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print " New primes has been found:", new_primes;
end if;
for p in new_primes do
Append(~NewPrimes, <p, SQP`SQ[3]>);
end for;
SQP`Data[2] join:= new_primes;
SQP`Data[3] := 0;
end if;
end if;

SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 1, SQR, DL;
else
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 0, SQR, DL;
end if;

end function;

checktrivial := function(G, weights, primerest)
SQ_TraceFunction("checktrivial", 2);

/*
 * returns a sequence of pairs [i,i] or [i,j] for which one can
 * require that the tail at the relation G.i^p resp. G.i^G.j
 * is trivial.
 */

PO := PCPrimes(G);
T1 := [];

/* First step: take all pairs of generators where both indices do not
 * occur in PO
 */
Ind := {i : i in [1..#PO] | PO[i] notin primerest};
if #Ind eq 0 then
    T1 := [];
else
    T1 := [[a,b] : a in Ind, b in Ind | a ge b];
end if;

NS := weights[#weights]; /* last section, count gens belonging to it */
ng := 0;
nd := 0;
ld := [0];  /* dimension of the layers */
for NSL in NS do /* loop on the layers in the descending series */
    for NSLP in NSL do /* loop over the primes in layers */
        for i := 2 to #NSLP do /* loop over module dimensions */
            ng +:= Dimension(NSLP[i]);
        end for;
    end for;
    Append(~ld, ng-nd);
    nd := ng;
end for;

Ind := {#PO- ng+1..#PO};
ldw := [0 : i in {1..#PO- ng}];
wt := 1;
for i := 2 to #ld do
    ttt := [wt : j in {1..ld[i]}];
    ldw := ldw cat ttt;
    wt +:= 1;
end for;

/* Second step: look at the actual nilpotent section, take all pairs of
 * generators with different indices.
 * i.e. use the fact that a nilpotent group is the direct product of
 * p-groups.
 */

T2 := [[a,b] : a in Ind, b in Ind | a ge b and PO[a] ne PO[b]];

/* Third step: look at each p-group in the nilpotent section and
 * use the weights given by the lower descending series.
 * collect those pairs where the sum of the weights is bigger then
 * the expected weight of the new layer.
 */
T3 := [[a,b] : a in Ind, b in Ind | a gt b and PO[a] eq PO[b] and
                                    ldw[a]+ldw[b] gt wt ];

/*
 * fourth step: only need reps which are trivial on the last nilpotent
 * section, add this to the group operation.
 */
if #weights gt 1 then
    a := #PO+1;
    T4 := [[a,b] : b in {a-ng..a-1}];
else
    T4 := [];
end if;
TC := T1 cat T2 cat T3 cat T4;
return TC, ng;
end function;

elemabel_layer := function(G, weights, split_flag)
SQ_TraceFunction("elemabel_layer", 2);

/*
 * returns a sequence of pairs [i,j] or [i,j] (as above) in order
 * to require that the module together with the last layer is still
 * elementary abelian.
 */

PO := PCPrimes(G);

NS := weights[#weights]; /* last section, count gens belonging to it */
ng := 0;
nd := 0;
ld := [0];  /* dimension of the layers */
for NSL in NS do /* loop on the layers in the descending series */
    for NSLP in NSL do /* loop over the primes in layers */
        for i := 2 to #NSLP do /* loop over module dimensions */
            ng +:= Dimension(NSLP[i]);
        end for;
    end for;
    Append(~ld, ng-nd);
    nd := ng;
end for;

Ind := {#PO- ld[#ld]+1..#PO};
  
T1 := [[a,b] : a in Ind, b in Ind | a ge b ];
if split_flag eq false then
    T2 := [];
else
    /* force the extension to split with the quotient with the last
       nilpotent section. */
    Ind := {1 .. #PO-ng};
    T2 := [[a,b] : a in Ind, b in Ind | a ge b ];
end if;

return T1 cat T2;
end function;


QuotientAction := function(G, primerest, DL)
SQ_TraceFunction("QuotientAction", 1);

S := {1..#PCGenerators(G)};
for pp in primerest do
    flag, D := RepsListFind (DL, pp);
if #D eq 0 then
continue;
end if;
MG := Group(D[1,2]);
MS := {s : s in S | s le NPCgens(MG)};
if IsEmpty(MS) then
continue;
end if;
for dd in D do
M := dd[2];
MS := { g : g in MS | ActionGenerator(M, g) eq 1};
if #MS eq 0 then
S := {s : s in S | s gt NPCgens(MG)};
if IsEmpty(S) then
return [];
end if;
break;
end if;
end for;
S := MS join {s : s in S | s gt NPCgens(MG)};
end for;

return [[NPCgens(G)+1, s]: s in S];
end function;

FindTensorConstituents := function(LL, FL, DD, SQ_ModulCalcModus )

SQ_TraceFunction("FindTensorConstituents", 2);

if SQ_ModulCalcModus eq 2 then // `strict` module search
CL := [* *];
else
CL := LL;
end if;

for i := 1 to #LL do
    M := LL[i];
    CI := [];
    if #FL eq 0 then
        for j := i to #LL do
            N := LL[j];
            Append(~CI, TensorProduct(M, N));
        end for;
    else
        for j := 1 to #FL do
            N := FL[j];
            Append(~CI, TensorProduct(M, N));
        end for;
    end if;
    for M in CI do
        C := Constituents(M);
        for c in C do
            flag := false;
            for k := 1 to #CL do
                flag := IsIsomorphic(c, CL[k]);
                if flag eq true then
                    break;
                end if;
            end for;
            if flag eq false then
                Append(~CL, c);
            end if;
        end for;
    end for;
end for;

if #CL eq #DD then
    DDO := DD;
else
    DDO := [* *];
    for i := 1 to #DD do
        D := DD[i,2];
        for j := 1 to #CL do
            if IsIsomorphic(CL[j], D) then
                Append(~DDO, DD[i]);
                Remove(~CL, j);
                break;
            end if;
        end for;
    end for;
end if;

return DDO;
end function;

ExtractPossibleModules := function(weights, DL, SQ_ModulCalcModus)
SQ_TraceFunction("ExtractPossibleModules", 2);

/*
 * realization of Charles` idea: create a sublist of DL of modules
 * which are constituents of the tensor products of modules in the
 * first and the last layer of the nilpotent section.
 */

NS := weights[#weights];
LL := NS[#NS]; /* last layer == bottom */
FL := NS[  1]; /* first layer == head */
t := Cputime();

DLout := [* *];

primes := {l[1] : l in LL}; // Primes still relevant
for p in primes do // main loop
    ff, DT := RepsListFind(DL, p);
    if #DT eq 1 or SQ_ModulCalcModus eq 0 then
        Append(~DLout, DT);
        continue;
    end if;
    LLmodules := [* *];
    for ll in LL do
        if ll[1] ne p then
            continue;
        end if;
        for i := 2 to #ll do
            M := ll[i];
            flag := true;
            for j := 1 to #LLmodules do
                if IsIsomorphic(M, LLmodules[j]) then
                    flag := false;
                    break;
                end if;
            end for;
            if flag eq true then
                Append(~LLmodules, M);
            end if;
        end for;
    end for;
    FLmodules := [* *];
    if #NS ne 1 then
        for ll in FL do
            if ll[1] ne p then
                continue;
            end if;
            for i := 2 to #ll do
                M := ll[i];
                flag := true;
                for j := 1 to #FLmodules do
                    if IsIsomorphic(M, FLmodules[j]) then
                        flag := false;
                        break;
                    end if;
                end for;
                if flag eq true then
                    Append(~FLmodules, M);
                end if;
            end for;
        end for;
    end if;
    DLP := FindTensorConstituents(LLmodules, FLmodules, DT, SQ_ModulCalcModus);
       vprint MSQ_RepsCalc: "   Compare:", #DLP, "Modules out of",
#DT, "are candidates," , Cputime(t), "secs to check";
    Append(~DLout, DLP);
end for;

return DLout;
end function;

MSQallnonsplit := function(SQP, firstflag, DLT)

SQ_TraceFunction("MSQallnonsplit", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * Primes: sequence of tuples <p_i, e_i>, where e_i is 0 or an
 *         upper bound for the extension size.
 * weights: Sequences describing the ags structure of G.
 * firstflag: if true, only extension are checked which are elementary
 *            abelian with the last layer.
 */

epi     := SQP`SQ[1];
primes  := SQP`SQ[2];
weights := SQP`Series[2];
agsflag := SQP`Series[1] eq 1;
DL := ExtractPossibleModules(weights, DLT, SQP`Modi[2]);

FG := Domain(epi);
 G := Codomain(epi);

np := #primes;
if np eq 1 then
R := GF(primes[1,1]);
else
R := Integers();
end if;

nnf := #weights;
if nnf le 0 then
return 0, _,_;
end if;

lastsection := weights[nnf];               /* last nilpotent section */
lastlayer   := lastsection[#lastsection];  /* head or layer */
primerest   := {l[1] : l in lastlayer};    /* remaining primes for this sec */
new_primes := {};

trivseq, ng := checktrivial(G, weights, primerest);
if firstflag eq true then
    if #lastsection eq 1 then
        trivelemseq := elemabel_layer(G, weights, true);
    else
        trivelemseq := elemabel_layer(G, weights, false);
    end if;
    trivseq cat:= trivelemseq;
end if;

trivseq cat:= QuotientAction(G, primerest, DL);
t := Cputime();
mw := find_my_weights(weights, 65);
setarg := MSQGetCollectorModus(SQP`Modi[3]);
VS := MSQLetternonsplit(G, R, trivseq, mw: Setup := setarg);
vprint MSQ_Collector:
"   Symbolic collector setup:", Cputime(t), "sec";

NL := [];        /* Sequence for the new layer */
NewPrimes := []; /* sequence of the remaining primes */

for ip := 1 to np do
pp := primes[ip,1];
if pp notin primerest then
Append(~NewPrimes, primes[ip]);
continue;
end if;

    flag, D := RepsListFind (DL, pp);
vprint MSQ_RepsCheck, 2:
"   Check nonsplit extensions for",#D, "modules for prime", pp;

R := GF(pp);
e := primes[ip,2];
old_e := e;
NWi := [* pp *];

for delta in D do
dB := #Basis(delta[2]) * Degree(CoefficientRing(delta[2]));
if e gt 0 and e lt dB then
continue;
end if;

t := Cputime();
dd, new_epi := MSQnonsplit(VS, epi, delta);

ndd := Integers()!(dd / dB);

if MSQVerboseIsSet("MSQ_RepsCheck",1) then
if ndd ne 0 and IsVerbose("MSQ_Messages") then
print "   Needed", Cputime(t) ,"sec to check ", delta[2],
"    found multiplicity", ndd;
else
print "   Needed", Cputime(t) ,"sec to check ";/* , delta[2] */
end if;
else
if ndd ne 0 then
vprint MSQ_Messages:
"   found multiplicity",ndd,"for module",delta[2];
end if;
end if;

if dd ne 0 then /* step was successfull */
            for i := 1 to ndd do
                Append(~NWi, delta[2]);
            end for;
epi := new_epi;
new_epi := 0;
if e gt 0 then
e -:= dd;
if e le 0 then
break;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR;
end if;
if SQP`Modi[1] eq 5 then
new_primes join:= MSQfindprimes(epi,dd, Integers() ! SQP`Limits[5], SQP`Limits[6]);
if 0 in new_primes then
if old_e eq 0 then
Append(~NewPrimes, <pp, old_e>);
elif e gt 0 then
Append(~NewPrimes, <pp, e>);
end if;
if #NWi gt 1 then
Append(~NL, NWi);
if firstflag eq true then
k := #weights[nnf];
weights[nnf,k] cat:= NL;
else
Append(~weights[nnf], NL);
end if;
end if;
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 3, SQR;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 6, SQR;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQP;
end if;
end for;
if old_e eq 0 then
Append(~NewPrimes, <pp, old_e>);
elif e gt 0 then
Append(~NewPrimes, <pp, e>);
end if;
if #NWi gt 1 then
Append(~NL, NWi);
end if;
end for;
ttt := LetterVarDelete(VS);

if #NL gt 0 then
    if firstflag eq true then
        k := #weights[nnf];
        weights[nnf,k] cat:= NL;
    else
        Append(~weights[nnf], NL);
    end if;
if SQP`Modi[1] eq 4 then
nt := find_nontrivial_length(weights, SQP`Modi[1]);
new_primes join:= MSQfindprimes(epi,nt, Integers() ! SQP`Limits[5],SQP`Limits[6]);
if 0 in new_primes then
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 3, SQR;
end if;
end if;
if SQP`Modi[1] gt 3 then
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print "    New primes has been found:", new_primes;
end if;
for p in new_primes do
Append(~NewPrimes, <p, SQP`SQ[3]>);
end for;
SQP`Data[2] join:= new_primes;
SQP`Data[3] := 0;
end if;
end if;
SQR := ChangeQuotient(SQP, epi, NewPrimes, weights);
InsertRelatives(~SQP, ~SQR);
return 1, SQR;
else
return 0, _ , _;
end if;

end function;

CheckReturnValue := function( flag, SQR)

weights := SQR`Series[2];
if flag eq 0 then
return true, 0;
elif flag eq 3 then
return true, 3;
elif flag eq 6 then
vprint MSQ_Messages:
"<<<Algorithm reached time limit.";
return true, 6;
elif SQR`SQ[2] eq [] then
vprint MSQ_Messages: ">>>Found soluble quotient of size",
#Codomain(SQR`SQ[1]);
return true, 1;
elif SQR`Limits[2] eq #weights[#weights]  then
vprint MSQ_Messages:
"<<<Algorithm reached limit given for LCS length.";
return true, 2;
elif 0 lt SQR`Limits[3]  and SQR`Limits[3] le SQR`Data[1]  then
vprint MSQ_Messages:
"<<<Algorithm reached additive bound on the image order.";
PrintProcess(SQR);
return true, 4;
elif 0 lt SQR`Limits[4] then
lw := weights[#weights]; /* last nilpotent section */
t := 1;
for lwl in lw do /* sequence of head/layers */
for lwi in lwl do /* sequence of prime plus dimension */
nt := 0;
for i := 2 to #lwi do /* add up the dimensions */
nt +:= Dimension(lwi[i]);
end for;
t *:= lwi[1]^nt;
end for;
end for;
if SQR`Limits[4] le t then
vprint MSQ_Messages:
"<<<Algorithm reached additive bound on the image section order.";
PrintProcess(SQR);
return true, 5;
end if;
end if;

return false, 1;
end function;

MSQnilpotent := function(SQP)
SQ_TraceFunction("MSQnilpotent", 1);

SQ_PrimeSearchModus := SQP`Modi[1];
LCSbound            := SQP`Limits[2];
NpClass := SQP`Limits[1];

flag, SQR, DL := MSQallsplit(SQP);

ret_flag, flag := CheckReturnValue ( flag, SQR);
if ret_flag eq true then
RepsListDelete(~DL);
return flag, SQR;
end if;

vprint MSQ_Messages: ">>>Found soluble quotient of size",
#Codomain(SQR`SQ[1]);

while flag eq 1 do
SQP := SQR;
flag, SQR := MSQallnonsplit(SQP, false, DL);
if flag ne 0 then
vprint MSQ_Messages:
">>>Found soluble quotient of size", #Codomain(SQR`SQ[1]);
ret_flag, flag := CheckReturnValue ( flag, SQR);
if ret_flag eq true then
RepsListDelete(~DL);
return flag, SQR;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
RepsListDelete(~DL);
return 6, SQR;
end if;
end while;

RepsListDelete(~DL);
if SQ_PrimeSearchModus eq 3 then
nt := find_nontrivial_length(SQP`Series[2], SQ_PrimeSearchModus);
new_primes := MSQfindprimes(SQP`SQ[1], nt, Integers() ! SQP`Limits[5],SQP`Limits[6]);
if 0 in new_primes then
return 3, SQP;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQP;
end if;
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print "+++ New primes have been found:", new_primes;
end if;
for p in new_primes do
Append(~SQP`SQ[2], <p, SQP`SQ[3]>);
end for;
SQP`Data[2] join:= new_primes;
SQP`Data[3] := 0;
end if;
end if;

return 1, SQP;

end function;

MSQall_ags := function(SQP)

SQ_TraceFunction("MSQall_ags", 1);

epi     := SQP`SQ[1];
T       := SQP`SQ[2];
weights := SQP`Series[2];

if SQP`Modi[1] eq 0 and <0,0> in T then
SQP`Modi[1] := 3;
end if;

SQ_PrimeSearchModus := SQP`Modi[1];
NpClass     := SQP`Limits[1];

/* calculating the quotient using a ags system.
 */

Null_T := {t : t in T | t[1] eq 0};
if #Null_T eq 0 then
primes := T;
else
primes := [t : t in T | t[1] ne 0];
a := Random(Null_T); // just to get the elt.
end if;

flag := 1;
first_primes := {t[1] : t in primes};
weightst := weights;

while flag eq 1 do

lw := #weights;
flag,SQR:= MSQnilpotent(SQP);
weightst := SQR`Series[2];

if flag eq 0 then
if SQ_PrimeSearchModus in {1,2} then
nt := find_nontrivial_length(weights, SQ_PrimeSearchModus);
new_primes := MSQfindprimes(SQP`SQ[1], nt, Integers() ! SQP`Limits[5], SQP`Limits[6]);
if 0 in new_primes then
print "<<<Found free abelian module in final primesearch.";
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
print "+++Found new relevant primes in final primesearch:",
new_primes;
for p in new_primes do
Append(~SQR`SQ[2], <p, SQR`SQ[3]>);
end for;
end if;
return 3, SQR;
end if;
new_primes := new_primes diff SQP`Data[2];
if #new_primes ne 0 then
print"+++New primes found in the final prime search:",
new_primes;
for p in new_primes do
Append(~SQR`SQ[2], <p, SQR`SQ[3]>);
end for;
SQR`Data[2] join:= new_primes;
SQP`Data[3] := 0;
if SQ_PrimeSearchModus eq 1 then
return 1, SQR;
else
flag := 1;
end if;
else
return 1, SQR;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQR;
end if;
else
return 1, SQR;
end if;
elif flag eq 1 then
vprint MSQ_Messages:
">>> Nilpotent section completed, size of Quotient:",
#Codomain(SQR`SQ[1]);
if NpClass gt 0 and #weightst ge NpClass then
vprint MSQ_Messages:
"<<< Algorithm reached limit given on Nilpotency Class";
return 2, SQR;
elif SQP`Limits[2] eq #weightst[#weightst]  then
return 2, SQR;
end if;

if SQR`SQ[2] eq [] and Null_T eq {} then
if SQ_PrimeSearchModus in {1,2} then
nt := find_nontrivial_length(weights, SQ_PrimeSearchModus);
new_primes := MSQfindprimes(SQR`SQ[1], nt, Integers() ! SQR`Limits[5], SQR`Limits[6]);
if 0 in new_primes then
if IsVerbose("MSQ_Messages") or
MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print "<<< Found free abelian module in the final prime search.";
end if;
new_primes := new_primes diff SQR`Data[2];
if #new_primes ne 1 then
if IsVerbose("MSQ_Messages") or
MSQVerboseIsSet("MSQ_PrimeSearch", 8)
then
print "+++New primes found in the final prime search:",
new_primes;
end if;
end if;
for p in new_primes do
Append(~SQR`SQ[2], <p, SQR`SQ[3]>);
end for;
return 3, SQR;
end if;
new_primes := new_primes diff SQR`Data[2];
if #new_primes ne 0 then
if IsVerbose("MSQ_Messages") or
MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
print "+++New primes found in the final prime search:",
new_primes;
end if;
for p in new_primes do
Append(~SQR`SQ[2], <p, SQR`SQ[3]>);
end for;
SQR`Data[2] join:= new_primes;
SQP`Data[3] := 0;
if SQ_PrimeSearchModus eq 1 then
return 1, SQR;
end if;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQR;
end if;
else
return 1, SQR;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQR;
end if;
end if;

else
return flag, SQR;
end if;
if SQP`Limits[6] gt 0 and Cputime() gt SQP`Limits[6] then
return 6, SQR;
end if;
SQP := SQR;
weights := SQP`Series[2];
end while;

end function;

SQ_main := function(SQP)

flag, SQR := MSQall_ags(SQP);

return SQR, flag;

end function;

intrinsic SQ_check(SQP::SQProc) -> BoolElt
{Check the correctness of the soluble quotient.};
require assigned SQP`SQ : "empty SQ Process.";

epi := SQP`SQ[1];
FG := Domain(epi);
R := {r[1] * r[2]^-1: r in Relations(FG)};
S := {epi(r) : r in R};

if #S ne 1 then
    flag1 := false;
else
flag1 := true;
end if;

G := Codomain(epi);
GS := sub< G | {epi(f) : f in Generators(FG)}>;

if GS ne G then
    return flag1, false;
else
    return flag1, true;
end if;

end intrinsic;

intrinsic EquivalentQuotients(SQP::SQProc, SQR::SQProc : Construct := false) -> BoolElt, SQProc
{Checks whether two soluble quotients have the same kernel. If not and Construct
is true, then a bigger quotient will be constructed, where the
kernel is the intersection of both kernels.}

E1 := SQP`SQ[1];
E2 := SQR`SQ[1];
G1 := Codomain(E1);
G2 := Codomain(E2);
FG := Domain(E1);

require  FG eq Domain(E2) : "Quotients from different groups.";

if #G1 ne #G2 and Construct eq false then
return false, _;
end if;

H, p1, p2 := DirectProduct(G1, G2);
EE := hom<FG -> H | [p1[1](E1(FG.i))*p1[2](E2(FG.i)): i in [1..Ngens(FG)]]>;
S := sub<H | [EE(FG.i) : i in [1..Ngens(FG)]]>;

if #S eq #G1 then
if #S eq #G2 then
// Quotient are equivalent
return true, _;
else
// G1 is a kind of lift of G2
return false, SQP;
end if;
elif #S eq #G2 then
// G2 is a kind of lift of G1
return false, SQR;
else
// kernels have new intersection
if Construct eq false then
return false, _;
else
EES := hom<FG -> S | [S!(EE(FG.i)) : i in [1..Ngens(FG)]]>;
SQRoot := SQP`Root[3];
SQProcCreateproc (~SQRoot, EES, [], 0, 1, [], 0, 0, 0, 0,0,0,0);
SQN := GetNewSQ(SQRoot);
AddPrimes(SQN, SQP`Data[2]);
AddPrimes(SQN, SQR`Data[2]);
InsertRelatives(~SQP, ~SQN);
InsertRelatives(~SQR, ~SQN);
return false, SQN;
end if;
end if;

end intrinsic;

intrinsic IntersectKernels(SQP::SQProc, SQR::SQProc) -> SQProc, Map, Map
{Construct a bigger soluble quotient by intersecting the kernels of the given
quotient. The return values are a new soluble quotient process and maps from
the new to the given soluble groups.}

E1 := SQP`SQ[1];
E2 := SQR`SQ[1];
G1 := Codomain(E1);
G2 := Codomain(E2);
FG := Domain(E1);

H, p1, p2 := DirectProduct(G1, G2);
EE := hom<FG -> H | [p1[1](E1(FG.i))*p1[2](E2(FG.i)): i in [1..Ngens(FG)]]>;
S := sub<H | [EE(FG.i) : i in [1..Ngens(FG)]]>;

if #S eq #G1 then
print "IntersectKernels: Warning: Intersection is equal to kernel of the first argument quotient.";
return SQP, _,_;
elif #S eq #G2 then
print "IntersectKernels: Warning: Intersection is equal to kernel of the second argument quotient.";
return SQR, _, _;
end if;

se1 := hom<S -> G1 | [p2[1](H!S.i) : i in [1..NPCgens(S)]]>;
se2 := hom<S -> G2 | [p2[2](H!S.i) : i in [1..NPCgens(S)]]>;
EES := hom<FG -> S | [S!(EE(FG.i)) : i in [1..Ngens(FG)]]>;

SQRoot := SQP`Root[3];
SQProcCreateproc (~SQRoot, EES, [], 0, 1, [], 0, 0, 0, 0,0,0,0);
SQN := GetNewSQ(SQRoot);

AddPrimes(SQN, SQP`Data[2]);
AddPrimes(SQN, SQR`Data[2]);
InsertRelatives(~SQP, ~SQN);
InsertRelatives(~SQR, ~SQN);
return SQN, se1, se2;

end intrinsic;

ExtendQuotientGroups := function(GG, G1, G2)

if #GG eq 1 then
return DirectProduct(G1, G2);
end if;

ngg := NPCgens(GG);
ng1 := NPCgens(G1);
ng2 := NPCgens(G2);
S2 := sub<G2 | [G2.i : i in [ngg+1..ng2]]>; 
m := [[Eltseq(G2.j^G2.i): j in [ngg+1..ng2]]: i in [1..ngg]];
mm := [[[mii[i] : i in [ngg+1..ng2]]:mii in mi] :mi in m];   
idhom := hom<S2 -> S2 | [S2.i : i in [1..NPCgens(S2)]]>;
f := [hom<S2 -> S2| [S2!mii : mii in mi] > : mi in mm] cat
 [idhom : i in [ngg+1..ng1]];

m := [[Eltseq(G2.j^G2.i): j in [i..ngg]]: i in [1..ngg]];
mm := [[[mii[i] : i in [ngg+1..ng2]]:mii in mi] :mi in m];   
t := [];
for i := 1 to ngg do
mi := mm[i];
for j := 1 to #mi do
e := S2 ! mi[j];
if e ne Id(S2) then
Append(~t, <i+j-1, i, e>);
end if;
end for;
end for;

if #t eq 0 then
GB := Extension(S2, G1, f);
else
GB := Extension(S2, G1, f, t);
end if;

return GB;
end function;

ExtendQuotientEpis := function(ee, e1, e2)

GG := Codomain(ee);
G1 := Codomain(e1);
G2 := Codomain(e2);
ngg := NPCgens(GG);
ng1 := NPCgens(G1);
ng2 := NPCgens(G2);

GB := ExtendQuotientGroups (GG, G1, G2);
FF := Domain(ee);
n  := Ngens(FF);
s2 := [Eltseq(e2(FF.i)) : i in [1..n]];
s2m := [[sm[i] : i in [ngg+1..ng2]] :sm in s2];
sb := [GB! (Eltseq(e1(FF.i)) cat s2m[i]) : i in [1..n]];

eb := hom<FF -> GB | sb >;

return eb;
end function;

intrinsic ComposeQuotients(SQP::SQProc, SQ1::SQProc, SQ2::SQProc:
Check := true) -> BoolElt, SQProc
{Compose the lifts SQ1 and SQ2 of SQP to a new bigger quotient. If the optional
 parameter Check is set to true, it will be tested whether the intersection of
 the kernels has maximal index.}

if Check eq true then
SQR, t1, t2 := IntersectKernels(SQ1, SQ2);
if SQP`Data[1]*SQR`Data[1] ne SQ1`Data[1] * SQ2`Data[1] then
return false, SQR;
end if;
DeleteProcess(~SQR);
end if;

ee := SQP`SQ[1];
e1 := SQ1`SQ[1];
e2 := SQ2`SQ[1];
er := ExtendQuotientEpis (ee, e1, e2);
SQRoot := SQP`Root[3];
SQProcCreateproc (~SQRoot, er, [], 0, 1, [], 0, 0, 0, 0,0,0,0);

SQN := GetNewSQ(SQRoot);
AddPrimes(SQN, SQ1`Data[2]);
AddPrimes(SQN, SQ2`Data[2]);
InsertRelatives(~SQ1, ~SQN);
InsertRelatives(~SQ2, ~SQN);
return Check, SQN;

end intrinsic;

//=======================================================================
// Main intrinsics for soluble quotients using the sag system
//=======================================================================

intrinsic SolubleQuotientProcess(F::GrpFP:
          Print := -1, SQ_series := 1,
  RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=4, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc, RngIntElt
{Start the soluble quotient algorithm for a finitely presented group F without
any information about the relevant primes.}

MSQsetVerboseForOption(~Print);
SQ_TraceFunction("Soluble Quotient Algorithm arg 1", 1);
if SQ_PrimeSearchModus eq 0 then
SQ_PrimeSearchModus := 4;
end if;
G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
SQRoot := SQProcCreateRoot(F);
SQProcCreateproc (~SQRoot, epi, [], 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQRoot);
SQR, success_flag := SQ_main(SQP);
epi := SQR`SQ[1];
return SQR, success_flag;
end intrinsic;

intrinsic SolubleQuotientProcess(F::GrpFP, n::RngIntElt:
          Print := -1, SQ_series := 1,
  RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc, RngIntElt
{Start the soluble quotient algorithm for a finitely presented group F with
expected order of the quotient being n.}

require n ge 0 : "n must be a nonnegative integer.";

MSQsetVerboseForOption(~Print);
SQ_TraceFunction("Soluble Quotient Algorithm arg 2", 1);
G := PCGroup(CyclicGroup(1));
if n eq 0 then
T := [];
SQ_PrimeSearchModus := 3;
else
T := Factorization(n);
end if;

epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
SQRoot := SQProcCreateRoot(F);
SQProcCreateproc (~SQRoot, epi, T, 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQRoot);
SQR, success_flag := SQ_main(SQP);
epi := SQR`SQ[1];
return SQR, success_flag;
end intrinsic;

intrinsic SolubleQuotientProcess(F::GrpFP, f::RngIntEltFact:
          Print := -1, SQ_series := 1,
  RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc, RngIntElt
{Start the soluble quotient algorithm for a finitely presented group F with
expected order of the quotient being the factorized integer f.}

MSQsetVerboseForOption(~Print);
SQ_TraceFunction("Soluble Quotient Algorithm arg 3", 1);
G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
SQRoot := SQProcCreateRoot(F);
SQProcCreateproc (~SQRoot, epi, f, 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQRoot);

SQR, success_flag := SQ_main(SQP);
epi := SQR`SQ[1];
return SQR, success_flag;
end intrinsic;


/*
intrinsic SolubleQuotientProcess(F::GrpFP, f::SeqEnum:
          Print := -1, SQ_series := 1,
  RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc, RngIntElt
{Start the soluble quotient algorithm for a finitely presented group F with
relevant primes restricted by the sequence of tuples f.}

require Type(f[1]) eq Tup :
"2nd argument must be a sequence of tuples of integers.";

MSQsetVerboseForOption(~Print);
SQ_TraceFunction("Soluble Quotient Algorithm arg 4", 1);
G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
T := [s[2] : s in f | s[1] eq 0];
require #T le 1 : "Two or more tuples with first entry 0";
if T ne [] then
f := [s : s in f | s[1] ne 0];
if SQ_PrimeSearchModus eq 0 then
SQ_PrimeSearchModus := 3;
end if;
else
T[1] := 0;
end if;

SQRoot := SQProcCreateRoot(F);
SQProcCreateproc (~SQRoot, epi, f, T, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQRoot);

SQR, success_flag := SQ_main(SQP);
epi := SQR`SQ[1];
return SQR, success_flag;
end intrinsic;
*/


intrinsic SolubleQuotientProcess(F::GrpFP, s::SetEnum:
          Print := -1, SQ_series := 1,
  RatRepDegreeLimit:=0, SQTimeLimit:=0,
  SQ_PrimeSearchModus:=0, SQ_ModulCalcModus:=0, SQ_CollectorModus:= 2,
  SeriesLength:=0,SubSeriesLength:=0,QuotientSize:=0,SectionSize:=0)
          -> SQProc, RngIntElt
{Start the soluble quotient algorithm for a finitely presented group F with
relevant primes restricted by the set s.}

require s eq {g : g in s | g gt 0} :
"2nd argument must be a set of positive integers.";

MSQsetVerboseForOption(~Print);
SQ_TraceFunction("Soluble Quotient Algorithm arg 5", 1);

G := PCGroup(CyclicGroup(1));
epi := hom<F -> G | [Id(G) : g in Generators(F)]>;
if 0 in s then
f := [];
if SQ_PrimeSearchModus eq 0 then
SQ_PrimeSearchModus := 3;
end if;
else
f := [<e,0> : e in s];
end if;
SQRoot := SQProcCreateRoot(F);
SQProcCreateproc (~SQRoot, epi, f, 0, SQ_series, [],
  SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus,
  SeriesLength,SubSeriesLength,QuotientSize,SectionSize,
  Integers() ! RatRepDegreeLimit, SQTimeLimit);
SQP := GetNewSQ(SQRoot);

SQR, success_flag := SQ_main(SQP);
epi := SQR`SQ[1];
return SQR, success_flag;
end intrinsic;

intrinsic NonsplitCollector(SQP::SQProc, p::RngIntElt: Setup := "Dynamic")
{Set up the collector for a nonsplit extension of SQP with algebra RG,
R the prime ring in characteristic p.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";

C := SQP`Collect[1];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
if  #C[I[1]] eq 2 then
return;
else
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[1], I[1]);
end if;
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
V := MSQLetternonsplit(G, R: Setup := Setup);
Append(~SQP`Collect[1], <V, p>);

return;
end intrinsic;

intrinsic NonsplitCollector(SQP::SQProc, p::RngIntElt, tr::SeqEnum: Setup := "Dynamic")
{Set up the collector for a nonsplit extension of SQP with algebra RG,
R the prime ring in characteristic p. The pairs in tr indicates trivial tails.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";

C := SQP`Collect[1];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
if  #C[I[1]] eq 3 and C[I[1], 3] eq tr then
return;
else
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[1], I[1]);
end if;
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
V := MSQLetternonsplit(G, R, tr: Setup := Setup);
Append(~SQP`Collect[1], <V, p, tr>);

return;
end intrinsic;

intrinsic NonsplitCollector(SQP::SQProc, p::RngIntElt, tr::SeqEnum,
ws::SeqEnum: Setup := "Dynamic")
{Set up the collector for a nonsplit extension of SQP with algebra RG,
R the prime ring in characteristic p. The pairs in tr indicates trivial tails.
ws defines the weights of a series.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";

C := SQP`Collect[1];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
if  #C[I[1]] eq 4 and C[I[1],3] eq tr and C[I[1],4] eq ws then
return;
else
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[1], I[1]);
end if;
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
V := MSQLetternonsplit(G, R, tr, ws: Setup := Setup);
Append(~SQP`Collect[1], <V, p, tr, ws>);

return;
end intrinsic;

intrinsic NonsplitCollector(SQP::SQProc, p::RngIntElt, tr::SeqEnum,
ws::SeqEnum, epi::Map : Setup := "Dynamic")
{Set up the collector for a nonsplit extension of SQP with algebra RG,
R the prime ring in characteristic p. The pairs in tr indicates trivial tails.
ws defines the weights of a series. epi is an epimorphism onto another
soluble group.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";
require Type(Codomain(epi)) eq GrpPC : "Epimorphism must be onto a GrpPC.";

C := SQP`Collect[1];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[1], I[1]);
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
Q := Codomain(epi);
V := MSQLetternonsplit(G, R, tr, ws, Q, epi: Setup := Setup);
Append(~SQP`Collect[1], <V, p, tr, ws, epi>);

return;
end intrinsic;

intrinsic SplitCollector(SQP::SQProc, p::RngIntElt: Setup := "Dynamic")
{Set up the collector for a standard split extension of SQP with algebra RG
R the prime ring in characteristic p.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";

C := SQP`Collect[2];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
if  #C[I[1]] eq 2 then
return;
else
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[2], I[1]);
end if;
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
V := MSQLettersplit(G, R: Setup := Setup);
Append(~SQP`Collect[2], <V, p>);

return;
end intrinsic;

intrinsic SplitCollector(SQP::SQProc, p::RngIntElt,
ws::SeqEnum: Setup := "Dynamic")
{Setup the collector for a standard ssplit extension of SQP with algebra RG
R the prime ring in characteristic p. ws defines the weights of a series.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";

C := SQP`Collect[2];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
if  #C[I[1]] eq 3 and C[I[1],3] eq ws then
return;
else
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[2], I[1]);
end if;
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
V := MSQLettersplit(G, R, ws: Setup := Setup);
Append(~SQP`Collect[2], <V, p, ws>);

return;
end intrinsic;

intrinsic SplitCollector(SQP::SQProc, p::RngIntElt,
ws::SeqEnum, epi::Map : Setup := "Dynamic")
{Set up the collector for a nonsplit extension of SQP with algebra RG, R the
 prime ring in characteristic p. ws defines the weights of a series. epi is
 an epimorphism onto another soluble group.}

require p eq 0 or IsPrime(p) : "Coefficient ring must be integers or GF(p)";
require Type(Codomain(epi)) eq GrpPC : "Epimorphism must be onto a GrpPC.";

C := SQP`Collect[2];

if #C ne 0 then
I := [i : i in {1..#C} | C[i,2] eq p];
if #I ne 0 then
V := C[I[1],1];
LetterVarDelete(V);
Remove(~SQP`Collect[2], I[1]);
end if;
end if;

if p eq 0 then
R := Integers();
else
R := GF(p);
end if;
G := Codomain(SQP`SQ[1]);
Q := Codomain(epi);
V := MSQLettersplit(G, R, ws, Q, epi: Setup := Setup);
Append(~SQP`Collect[2], <V, p, ws, epi>);

return;
end intrinsic;

ExtractModulesFromSQPlist := function(list, ll)

if Type(ll) eq SetEnum then
ExactDimension := ll;
elif Type(ll) eq RngIntElt then
ExactDimension := {1..ll};
end if;

if ExactDimension eq {} then
m := 0;
else
m := Max(ExactDimension);
end if;

newlist := <m, ExactDimension, [* *]>;
for M in list do
if Dimension(M[2]) * Degree(CoefficientRing(M[2])) in ExactDimension then
Append(~newlist[3], M);
end if;
end for;

return newlist;
end function;

SelectNewModules := function(L1, Lo)
// Returns a list of modules from L1 which are inequivalent to all modules
// from Lo. (This is a easy check, so don`t use it for long lists!)
// We assume that each two modules from the same list are inequivalent.

So := {1..#Lo};

outlist := [* *];
outlistindex := [];
for i := 1 to #L1 do
M := L1[i,2];
for j in So do
N := Lo[j,2];
flag := IsEquivalent(M,N);
if flag eq true then
Exclude(~So, j);
break;
end if;
end for;
if flag eq false then
Append(~outlist, L1[i]);
Append(~outlistindex, i);
end if;
end for;

return outlist, outlistindex;
end function;

intrinsic Modules(SQP::SQProc, p::RngIntElt :
          ExactDimension := {Integers()| }, MaxDimension := 0) -> RngIntElt

{Calculates the G-modules in characteristic p with respect to the given options.
The return value is 0 iff no such module exists, otherwise it is the index of
the list of modules in SQP.}

modlist := SQP`ModulCandidates;

// Normalize the input options
if #ExactDimension ne 0 then
if MaxDimension ne 0 then
ExactDimension := {d : d in ExactDimension | d le MaxDimension};
end if;
MaxDimension := Max(ExactDimension);
elif MaxDimension ne 0 then
ExactDimension := {1..MaxDimension};
end if;

G := Codomain(SQP`SQ[1]);
n := Index(modlist[1], p);
if n eq 0 then // no list for this prime exists, create it.
if MaxDimension eq 0 then
outlist := AbsolutelyIrreducibleModulesSchur(G,GF(p):
Process:= true, GaloisAction:= "Yes");
else
outlist := AbsolutelyIrreducibleModulesSchur(G, GF(p):
Process:= true, GaloisAction:="Yes",
ExactDimension := ExactDimension);
end if;
NL := <MaxDimension, ExactDimension, outlist, 0>;
CL := <MaxDimension, ExactDimension, [1..#outlist]>;
Append(~SQP`ModulCandidates[1], p);
n := #SQP`ModulCandidates;
Append(~SQP`ModulCandidates[2], NL);
Append(~SQP`ModulCandidates[3], [* CL *]);
TT := [ 0 : i in [1..#outlist] ];
Append(~SQP`SplitExt    , Seqlist(TT));
if #G gt 1 then
Append(~SQP`NonsplitExt , Seqlist(TT));
else
TT := [ false : i in [1..#outlist] ];
Append(~SQP`NonsplitExt , Seqlist(TT));
end if;
return 1;
end if;

/* Check wether the modul list can be extracted from existing list */
modspec := modlist[2,n];
md := modspec[1];
ed := modspec[2];
tf := modspec[4] eq 0;
mn := modlist[3,n];
if tf then
if md eq 0 then
flag := true;
if MaxDimension eq 0 then // Bingo!
tt := [i : i in [1..#mn] | mn[i,1] eq 0];
if #tt ne 0 then
return tt[1];
else
Append(~SQP`ModulCandidates[3,n], <0, {}, [1..#modspec[3]]>);
SQP`SplitExt[n] cat:= Seqlist([ 0 : i in [1..#modspec[3]] ]);
SQP`NonsplitExt[n] cat:= Seqlist([ 0 : i in [1..#modspec[3]] ]);
return #SQP`ModulCandidates[3,n];
end if;
end if;
elif md lt 0 or MaxDimension eq 0 or tf eq false then
flag := false;
elif ExactDimension subset ed then
flag := true;
if ExactDimension eq ed then
return 1;
end if;
end if;

if flag eq true then
/* Check whether there is a list with exact the same specifications */
li := [i : i in [1.. #mn] | mn[i,2] eq ExactDimension];
if #li ne 0 then // Bingo!
return li[1];
end if;
end if;

if MaxDimension eq 0 then
tmplist := AbsolutelyIrreducibleModules(G,GF(p): Process:= true, GaloisAction:= "Yes");
tt := ExtractModulesFromSQPlist(tmplist, ExactDimension);
tt := tt[3];
dellist := [* *];
complist := SQP`ModulCandidates[2,n,3];
for i := 1 to #tmplist do
h := tmplist[i];
if i in tt then
Append(~dellist, h);
else
for i := 1 to #complist do
flag := IsEquivalent(h[2], complist[i,2]);
if flag eq true then
Append(~dellist, h);
Remove(~complist, i);
break;
end if;
end for;
if flag eq false then
Append(~SQP`ModulCandidates[2,n, 3], h);
Append(~SQP`SplitExt[n] , 0);
Append(~SQP`NonsplitExt[n], 0);
end if;
end if;
end for;
RepsListDelete(~dellist);
CL := <MaxDimension, ExactDimension, [1..#SQP`ModulCandidates[2,3]]>;
Append(~SQP`ModulCandidates[3,n], CL);
return #SQP`ModulCandidates[3,n];
end if;
end if;

if tf then
outlist := AbsolutelyIrreducibleModules(G, GF(p): Process:= true,
GaloisAction:="Yes", ExactDimension := ExactDimension diff ed,
MaxDimension := MaxDimension);
else
tr := modspec[4];
if MaxDimension eq 0 then
tmplist := AbsolutelyIrreducibleModules(G,GF(p),tr:
Process:= true,GaloisAction:="Yes");
else
tmplist := AbsolutelyIrreducibleModules(G, GF(p), tr: Process:= true,
GaloisAction:="Yes", ExactDimension := ExactDimension diff ed,
MaxDimension := MaxDimension);
end if;
tl1 := [* tmplist[1] *];
Remove(~tmplist, 1);
if MaxDimension eq 0 then
outlist := AbsolutelyIrreducibleModules(G,GF(p),tl1:
Process:= true,GaloisAction:="Yes");
tl, tli := SelectNewModules (outlist, modlist[2,n,3]);
for k := #tli to 1 by -1 do
Remove(~outlist, tli[k]);
end for;
AbsolutelyIrreducibleModulesDelete(~outlist);
outlist := 0;
if #tmplist eq 0 then
outlist := tl;
else
outlist := tl cat AbsolutelyIrreducibleModules(G, GF(p), tmplist:
Process:= true, GaloisAction:= "Yes");
end if;
else
if #tl1 eq 0 then
outlist := [* *];
else
outlist := AbsolutelyIrreducibleModules(G, GF(p), tl1:
Process:= true, ExactDimension := ExactDimension diff ed,
GaloisAction := "Yes", MaxDimension := MaxDimension);
end if;
if #tmplist ne 0 then
outlist cat:= AbsolutelyIrreducibleModules(G, GF(p), tmplist:
Process:= true, ExactDimension := ExactDimension join ed,
GaloisAction:= "Yes", MaxDimension := MaxDimension);
end if;
end if;
AbsolutelyIrreducibleModulesDelete(~tmplist);
tmplist := 0;
AbsolutelyIrreducibleModulesDelete(~tl1);
tl1 := 0;
end if;
SQP`ModulCandidates[2,n,1] := Max(MaxDimension, md);
SQP`ModulCandidates[2,n,2] := ExactDimension join ed;
SQP`ModulCandidates[2,n,3] cat:= outlist;
SQP`ModulCandidates[2,n,4] := 0;
SQP`SplitExt[n]    cat:= Seqlist([ 0 : i in [1..#outlist] ]);
SQP`NonsplitExt[n] cat:= Seqlist([ 0 : i in [1..#outlist] ]);
nl := ExtractModulesFromSQPlist(SQP`ModulCandidates[2,n,3], ExactDimension);
Append(~SQP`ModulCandidates[3,n], nl);
return #SQP`ModulCandidates[3,n];

end intrinsic;

intrinsic Modules(SQP::SQProc:
          ExactDimension := {Integers()| }, MaxDimension := 0) -> SeqEnum
{Calculates the modules for all (known) relevant primes.}

S := [];
for p in SQP`Data[2] do
Append(~S, <p, Modules(SQP, p:
          ExactDimension := ExactDimension, MaxDimension := MaxDimension)>);
end for;

return S;
end intrinsic;

intrinsic AppendModule(SQP::SQProc, M::Tup) -> RngIntElt, BoolElt

{Append/Find the module M in the list of modules in SQP.
The first return value is the index of the module in the char p list in SQP.
The second return value is false iff the index belongs to an isomophic module.
(It might happen that the isomorphism is the identity; relevant is the internal
data structure.)}

modlist := SQP`ModulCandidates;
p := Characteristic(CoefficientRing(M[2]));

G := Codomain(SQP`SQ[1]);
n := Index(modlist[1], p);
if n eq 0 then // no list for this prime exists, create it.
NL := <-1, {}, [* M *], 0>;
CL := <-1, {}, [1]>;
Append(~SQP`ModulCandidates[1], p);
Append(~SQP`ModulCandidates[2], NL);
Append(~SQP`ModulCandidates[3], [* CL *]);
Append(~SQP`SplitExt, [* 0*]);
Append(~SQP`NonsplitExt, [* 0*]);
return 1;
end if;

/* Check wether the modul list can be extracted from existing list */
modspec := modlist[2,n];
mn := modspec[3];
li := [i : i in [1.. #mn] | mn[i,1] eq M[1]];
if #li ne 0 then // Bingo!
return li[1], true;
else
if modspec[1] eq 0 or
   Dimension(M[2]) * Degree(CoefficientRing(M[2])) in modspec[2] then
for k := 1 to #mn do
N := mn[k,2];
f, C := IsEquivalent(N, M[2]);
if f eq true then
return k, false;
end if;
end for;
end if;
Append(~SQP`ModulCandidates[2,n,3], M);
Append(~SQP`SplitExt[n], 0);
Append(~SQP`NonsplitExt[n], 0);
modlist[2,n,1] := -1;
return #SQP`ModulCandidates[2,n,3], true;
end if;

end intrinsic;

FindActualCollector := function(SQP, p, split, exact)

if split eq true then
Collectors := SQP`Collect[2];
else
Collectors := SQP`Collect[1];
end if;

if #Collectors ne 0 then
I := [i : i in {1..#Collectors} | Collectors[i,2] eq p];
if #I ne 0 then
CN := Collectors[I[1]];
else
if exact eq true then
return false, _;
end if;
I := [i : i in {1..#Collectors} | Collectors[i,2] eq 0];
if #I ne 0 then
CN := Collectors[I[1]];
else
return false, _;
end if;
end if;
else
return false, _;
end if;

return true, CN;
end function;

intrinsic SolutionSpace (SQP::SQProc, p::RngIntElt, i::RngIntElt, split::BoolElt, explicit::BoolElt) -> BoolElt, RngIntElt
{ internal };

// Calculate the solution space for the i-th madule in characteristic p
// if split eq true, the split solution is taken, otherwise the nonsplit
// if explicit eq true, the calculation is done anyway, otherwise the function
// searches for previous results.


modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
moduls := modlist[2,n];
epi := SQP`SQ[1];

M := moduls[3,i]; // modul to be checked
flag, CN := FindActualCollector(SQP, p, split, false);
if flag eq false then
if split eq true then
SplitCollector   (SQP, 0: Setup := "Dynamic");
else
NonsplitCollector(SQP, 0: Setup := "Dynamic");
end if;
flag, CN := FindActualCollector(SQP, p, split, false);
end if;

if split eq true then
SolSpace := SQP`SplitExt[n];
else
SolSpace := SQP`NonsplitExt[n];
end if;

case Type(SolSpace[i]):
when BoolElt:
if SolSpace[i] eq false then // no extension possible at all
return false, _;
end if;
when RngIntElt:
// assume yet that it is 0, might be more possible values later.
if split eq true then
f, S  := MSQsplitBase(CN[1], epi, M);
else
f, S  := MSQnonsplitBase(CN[1], epi, M);
end if;
if f in {0,2} then
if #CN eq 2 then // sufficient to be a general collector
if split eq true then
SQP`SplitExt[n,i] := false;
else
SQP`NonsplitExt[n,i] := false;
end if;
return false, _;
else // no solution, so store that
if split eq true then
SQP`SplitExt[n,i] := [*2, < CN, f>*];
else
SQP`NonsplitExt[n,i] := [*2, < CN, f>*];
end if;
return true, 2;
end if;
else
if split eq true then
SQP`SplitExt[n,i] := [*2, < CN, f, S>*];
else
SQP`NonsplitExt[n,i] := [*2, < CN, f, S>*];
end if;
return true, 2;
end if;
when List:
Sols := SolSpace[i];
I := [k : k in [2..#Sols] | Sols[k,1,1] eq CN[1]];
if #I eq 0 then
if split eq true then
f, S  := MSQsplitBase(CN[1], epi, M);
else
f, S  := MSQnonsplitBase(CN[1], epi, M);
end if;
if f in {0,2} then
if #CN eq 2 then // sufficient to be a general collector
if split eq true then
SQP`SplitExt[n,i] := false;
else
SQP`NonsplitExt[n,i] := false;
end if;
return false, _;
else // no solution, so store that
if split eq true then
Append(~SQP`SplitExt[n,i], < CN, f>);
SQP`SplitExt[n,i,1] := #SQP`SplitExt[n,i];
else
Append(~SQP`NonsplitExt[n,i] , < CN, f>);
SQP`NonsplitExt[n,i,1] := #SQP`NonsplitExt[n,i];
end if;
end if;
else
if split eq true then
Append(~SQP`SplitExt[n,i], < CN, f, S>);
SQP`SplitExt[n,i,1] := #SQP`SplitExt[n,i];
else
Append(~SQP`NonsplitExt[n,i] , < CN, f, S>);
SQP`NonsplitExt[n,i,1] := #SQP`NonsplitExt[n,i];
end if;
end if;
return true, #SolSpace[i]+1;
elif explicit eq true then
if split eq true then
f, S  := MSQsplitBase(CN[1], epi, M);
else
f, S  := MSQnonsplitBase(CN[1], epi, M);
end if;
act := I[1];
if f in {0,2} then
if split eq true then
SQP`SplitExt[n,i,act] := < CN, f>;
SQP`SplitExt[n,i,1] := act;
else
SQP`NonsplitExt[n,i,act] := < CN, f>;
SQP`NonsplitExt[n,i,1] := act;
end if;
else
if split eq true then
SQP`SplitExt[n,i,act] := < CN, f, S>;
SQP`SplitExt[n,i,1] := act;
else
SQP`NonsplitExt[n,i,act] := < CN, f, S>;
SQP`NonsplitExt[n,i,1] := act;
end if;
end if;
return true, act;
else
if split eq true then
SQP`SplitExt[n,i,1] := I[1];
else
SQP`NonsplitExt[n,i,1] := I[1];
end if;
return true, I[1];
end if;
end case;

return false, _;
end intrinsic;

intrinsic SplitExtensionSpace(SQP::SQProc, M::Tup) -> RngIntElt

{ Calculates the split extension lift for the module M. The return is -1 iff
  the solution space does not exist in general,otherwise it is the Fq-dimension
  of the space (could be 0).}

p := Characteristic(CoefficientRing(M[1]));
n, flag := AppendModule(SQP, M);
flag, k := SolutionSpace(SQP, p, n, true, true);

if flag eq false then
return -1;
end if;

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
SolSpace := SQP`SplitExt[n, k];
if SolSpace[2] in {0,2} then
return 0;
else
return Nrows(SolSpace[3,1,3]);
end if;

end intrinsic;

intrinsic SplitExtensionSpace(SQP::SQProc, L::List) -> SeqEnum

{ Calculates the split extension lift for the modules in the list. Returned is
a sequence of: -1 iff the solution space does not exist in general,
otherwise it is the Fq-dimension of the space (could be 0).}

RL := [];

for i := 1 to #L do
RL[i] := SplitExtensionSpace(SQP, L[i]);
end for;
return RL;

end intrinsic;

intrinsic SplitExtensionSpace(SQP::SQProc, p::RngIntElt,
l::RngIntElt) -> SeqEnum

{ Calculates the split extension lift for the modules in the l-th list in SQP.
The return is a sequence of: -1 iff the solution space does not exist in
general,otherwise it is the Fq-dimension of the space (could be 0).}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
indices := modlist[3,n,l,3];
RL := [];

for i := 1 to #indices do
flag, k := SolutionSpace (SQP, p, indices[i], true, false);
if flag eq false then
RL[i] := -1;
else
SolSpace := SQP`SplitExt[n, indices[i], k];
if SolSpace[2] in {0,2} then
RL[i] := 0;
else
RL[i] := Nrows(SolSpace[3,1,3]);
end if;
end if;
end for;
return RL;

end intrinsic;

intrinsic SplitExtensionSpace(SQP::SQProc, p::RngIntElt) -> SeqEnum

{ Calculates the split extension lift for the p-modules stored in SQP.
The return is a sequence of: -1 iff the solution space does not exist in
general, otherwise it is the Fq-dimension of the space (could be 0).}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);

require n gt 0 : "No modules for characteristic p calculated.";

l := #modlist[2,n,3];
RL := [];

for i := 1 to l do
flag, k := SolutionSpace(SQP, p, i, true, false);
if flag eq false then
RL[i] := -1;
else
SolSpace := SQP`SplitExt[n, i, k];
if SolSpace[2] in {0,2} then
RL[i] := 0;
else
RL[i] := Nrows(SolSpace[3,1,3]);
end if;
end if;
end for;
return RL;

end intrinsic;

intrinsic SplitExtensionSpace(SQP::SQProc) -> SeqEnum

{ Calculates the split extension lift for all modules stored in SQP.
The return are sequences for each prime of: -1 iff the solution space does
not exist in general, otherwise it is the Fq-dimension of the space
(could be 0).}

modlist := SQP`ModulCandidates;
l := #modlist[1];
RLL := [];

for i := 1 to l do
p := modlist[1,i];
if p ne 0 then
Append(~RLL, <p, SplitExtensionSpace(SQP, p)>);
end if;
end for;
return RLL;

end intrinsic;

intrinsic NonsplitExtensionSpace(SQP::SQProc, M::Tup) -> RngIntElt

{ Calculates the nonsplit extension lift for the module M. The return is -1 iff
the solution space does not exist in general, otherwise it is the Fq-dimension
of the space (could be 0).}

p := Characteristic(CoefficientRing(M[1]));
n, flag := AppendModule(SQP, M);
flag, k := SolutionSpace(SQP, p, n, false, true);

if flag eq false then
return -1;
end if;

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
SolSpace := SQP`SplitExt[n, k];
if SolSpace[2] in {0,2} then
return 0;
else
return Nrows(SolSpace[3,1,3]);
end if;

end intrinsic;

intrinsic NonsplitExtensionSpace(SQP::SQProc, L::List) -> SeqEnum

{Calculates the nonsplit extension lift for the modules in the list. The return
is a sequence of: -1 iff the solution space does not exist in general,
otherwise it is the Fq-dimension of the space (could be 0).}

RL := [];

for i := 1 to #L do
RL[i] := NonsplitExtensionSpace(SQP, L[i]);
end for;
return RL;

end intrinsic;

intrinsic NonsplitExtensionSpace(SQP::SQProc, p::RngIntElt,
l::RngIntElt) -> SeqEnum

{Calculates the nonsplit extension lift for the modules in the l-th list
in SQP. The return is a sequence of: -1 iff the solution space does not exist
in general, otherwise it is the Fq-dimension of the space (could be 0).}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
indices := modlist[3,n,l,3];
RL := [];

for i := 1 to #indices do
flag, k := SolutionSpace(SQP, p, indices[i], false, false);
if flag eq false then
RL[i] := -1;
else
SolSpace := SQP`NonsplitExt[n, indices[i], k];
if SolSpace[2] in {0,2} then
RL[i] := 0;
else
RL[i] := Nrows(SolSpace[3,1,3]);
end if;
end if;
end for;
return RL;

end intrinsic;

intrinsic NonsplitExtensionSpace(SQP::SQProc, p::RngIntElt) -> SeqEnum

{ Calculates the split extension lift for the p-modules stored in SQP.
The return is a sequence of: -1 iff the solution space does not exist in
general, otherwise it is the Fq-dimension of the space (could be 0).}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
l := #modlist[2,n,3];
RL := [];

for i := 1 to l do
flag, k := SolutionSpace(SQP, p, i, false, false);
if flag eq false then
RL[i] := -1;
else
SolSpace := SQP`NonsplitExt[n, i, k];
if SolSpace[2] in {0,2} then
RL[i] := 0;
else
RL[i] := Nrows(SolSpace[3,1,3]);
end if;
end if;
end for;
return RL;

end intrinsic;

intrinsic NonsplitExtensionSpace(SQP::SQProc) -> SeqEnum

{ Calculates the nonsplit extension lift for all modules stored in SQP.
The return are sequences for each prime of: -1 iff the solution space does
not exist in general, otherwise it is the Fq-dimension of the space
(could be 0).}

modlist := SQP`ModulCandidates;
l := #modlist[1];
RLL := [];

for i := 1 to l do
p := modlist[1,i];
if p ne 0 then
Append(~RLL, <p, NonsplitExtensionSpace(SQP, p)>);
end if;
end for;
return RLL;

end intrinsic;

CoerceModulElement := function(M, e, phi, MM)

d := Dimension(M);
es := [];
for i := 1 to d do
es cat:= Eltseq(phi(e[i]));
end for;

ee := MM!es;
return ee;
end function;

CreateLift := function(epi, M, T, L)

// Let epi: F ->> G be a soluble quotient and M a G-module, T a solution
// space and L be a sequence, giving the coefficients for a cocycle from T.
// Calculate the linear combination and build the lift of the quotient.

t_epi := [];
t_grp := [];
Z := Integers();

if Type(M) eq Tup then
K := CoefficientRing(M[2]);
p := Characteristic(K);
if K eq GF(p) then
flag := true;
MM := M[2];
//M := M[2];
else
flag := false;
MML := IrreducibleModules(Group(M[2]), GF(p), [* M *]);
MM := MML[1];
A, phi := Algebra(K, GF(p));
end if;
M := M[2];
else
K := CoefficientRing(M);
p := Characteristic(K);
if K eq GF(p) then
flag := true;
MM := M;
else
flag := false;
hhh := [* <AbsIrrFromModul(M), M> *];
MML := IrreducibleModules(Group(M), GF(p), hhh );
AbsolutelyIrreducibleModulesDelete(~hhh);
hhh := 0;
MM := MML[1];
A, phi := Algebra(K, GF(p));
end if;
end if;

d := Nrows(T[1,3]);
r := [c : c in {1..d}| L[c] ne 0];
if #T[1] eq 4 then
b := [c : c in {1+d.. Nrows(T[1,4])+d} | L[c] ne 0];
else
b := [];
end if;

for t in T do

e := MM!0;
for i in r do
if flag eq true then
e +:= MM ! (L[i]*t[3,i]);
else
e +:= CoerceModulElement(M, (L[i]*t[3,i]), phi, MM);
end if;
end for;
for i in b do
if flag eq true then
e +:= MM ! (L[i]*t[4,i-d]);
else
e +:= CoerceModulElement(M, (L[i]*t[4,i-d]), phi, MM);
end if;
end for;
if t[2] eq 0 then
Append(~t_epi, <t[1], e>);
else
Append(~t_grp, <t[1], t[2], e>);
end if;
end for;

// Create the new group:
if #t_grp eq 0 then
GG := Extension(MM, Group(MM));
else
GG := Extension(MM, Group(MM), Seqset(t_grp));
end if;

// Create the new epimorphism
F := Domain(epi);
im := [Eltseq(epi(F.i)) : i in [1..Ngens(F)]];
for t in t_epi do
if #Codomain(epi) eq 1 then
im[t[1]] := [Z! tt : tt in Eltseq(t[2])];
else
im[t[1]] cat:= [Z! tt : tt in Eltseq(t[2])];
end if;
end for;

ngg := NPCgens(GG);
for i := 1 to #im do
e := im[i];
if #e ne ngg then
f := ngg - #e;
im[i] cat:= [0 : j in [1..f]];
end if;
end for;
new_epi := hom<F -> GG | [GG!e : e in im]>;

return new_epi;
end function;

ModulFromQuotientGroup := function(MM, G)
// Let H = Group(M) and G a group t.s. G == < H.1...H.k,G.k+1..G.n >
// Return M as a G-module.

M := MM[2];
H := Group(M);
A := Action(M);
r := NPCgens(H);
n := NPCgens(G) - r;

if #H eq 1 then
Q := [A ! 1: j in [1..NPCgens(G)]];
else
Q := [ActionGenerator(M, i) : i in [1..r]] cat [A ! 1: j in [1..n]];
end if;

MG := GModule(G, Q);

return MG;
end function;

ModulCandidatesFromParent := function(SQP, SQR, p)
// Rewrite the p-modules of SQP as modules of SQR

modlist := SQP`ModulCandidates;
H := Codomain(SQP`SQ[1]);
G := Codomain(SQR`SQ[1]);
n := Index(modlist[1], p);

if n eq 0 then
return false, _, _;
end if;

modules := modlist[2,n];
ML := modules[3];
NL := [* *];
for i := 1 to #ML do
help := ModulFromQuotientGroup(ML[i], G);
NL[i] := <AbsIrrFromModul(help), help>;
end for;

if #modules eq 3 then
outmodules := <modules[1], modules[2], NL, NPCgens(G) - NPCgens(H)>;
else
outmodules := <modules[1],modules[2],NL,modules[4]+NPCgens(G)-NPCgens(H)>;
end if;
return true, outmodules, modlist[3,n];
end function;


ExtensionSpacesFromParent := function(SQP, SQR, p)
// Rewrite the extensions spaces for the p-modules of SQP for SQR

modlist := SQP`ModulCandidates;
H := Codomain(SQP`SQ[1]);
G := Codomain(SQR`SQ[1]);
n := Index(modlist[1], p);

gn := NPCgens(G);
hn := NPCgens(H);
tr := [[i,j] : i in [1..j], j in [hn+1..gn]];

if n eq 0 then
return false, _, _;
end if;

SE := SQP`SplitExt[n];
NSE := SE;

NE := SQP`NonsplitExt[n];
NNE := [* *];
r := #NE;

for i := 1 to r do
if Type(NE[i]) ne List then
NNE[i] := 0;
else
T:= NE[i];
TT := [* T[1] *];
for j := 2 to #T do
S := T[j,1];
case #S:
when 2:
OS := <S[1], S[2], tr>;
when 3:
OS := <S[1], S[2], S[3] cat tr>;
when 4:
OS := <S[1], S[2], S[3] cat tr, S[4]>;
when 5:
OS := <S[1], S[2], S[3] cat tr, S[4], S[5]>;
end case;
if #T[j] eq 2 then
Append(~TT, <S, T[j,2]>);
else
Append(~TT, <S, T[j,2], T[j,3]>);
end if;
end for;
NNE[i] := TT;
end if;
end for;

return  true, NSE, NNE;
end function;

intrinsic DeleteSplitSolutionspace(SQP::SQProc, p::RngIntElt, i::RngIntElt,
k::RngIntElt)
{Delete the k-th split solution space of the i-th p-module as the actual
solution space.  }

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
require Type(SQP`SplitExt[n,i]) ne BoolElt : "Split extension impossible for this module.";
require Type(SQP`SplitExt[n,i]) ne RngIntElt : "Split extension for this module not calculated yet.";

if #SQP`SplitExt[n,i] eq 2 then
SQP`SplitExt[n,i] := 0;
else
Remove(~SQP`SplitExt[n,i], k+1);
if SQP`SplitExt[n,i,1] eq k+1 then
SQP`SplitExt[n,i,1] := 0;
elif SQP`SplitExt[n,i,1] gt k+1 then
SQP`SplitExt[n,i,1] -:= 1;
end if;
end if;

end intrinsic;

intrinsic DeleteNonsplitSolutionspace(SQP::SQProc, p::RngIntElt, i::RngIntElt,
k::RngIntElt)
{Delete the k-th split solution space of the i-th p-module as the actual
solution space.  }

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
require Type(SQP`NonsplitExt[n,i]) ne BoolElt : "Nonsplit extension impossible for this module.";
require Type(SQP`NonsplitExt[n,i]) ne RngIntElt : "Nonsplit extension for the is module not calculated yet.";

if #SQP`NonsplitExt[n,i] eq 2 then
SQP`NonsplitExt[n,i] := 0;
else
Remove(~SQP`NonsplitExt[n,i], k+1);
if SQP`NonsplitExt[n,i,1] eq k+1 then
SQP`NonsplitExt[n,i,1] := 0;
elif SQP`NonsplitExt[n,i,1] gt k+1 then
SQP`NonsplitExt[n,i,1] -:= 1;
end if;
end if;

end intrinsic;

intrinsic LiftSplitExtension(SQP::SQProc, p::RngIntElt, i::RngIntElt,
k::RngIntElt : LinComb := []) -> SQProc
{Build the split extension of the i-th p-module for the k-th solution space.
 A set of linear combinations can be specified.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
M := modlist[2,n,3,i];
require Type(SQP`SplitExt[n,i]) ne BoolElt : "Split extension impossible for this module.";
require Type(SQP`SplitExt[n,i]) ne RngIntElt : "Split extension for this module not calculated yet.";

T := SQP`SplitExt[n,i,k+1, 3]; /* Index shift ! */

if LinComb eq [] then
r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
zero := GF(p) ! 0;
one  := GF(p) ! 1;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;
else
L := LinComb;
end if;

epi := SQP`SQ[1];
NWT := [* p *];
primes := SQP`SQ[2];
epi := CreateLift(epi, M, T, L[i]);
Append(~NWT, M[2] );
for i := 2 to #L do
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[i]);
    Append(~NWT, M[2] );
end for;
SQR := ChangeQuotient (SQP, epi, primes, SQP`Series[2] cat [[[NWT]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;

for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
SE[i] := false; // THIS IS NOT ALWAYS CORRECT!!!!
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;

return SQR;
end intrinsic;

intrinsic LiftSplitExtension(SQP::SQProc, p::RngIntElt, l::RngIntElt) -> RngIntElt, SQProc

{Build the split extension of the l-th list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
L := modlist[3,n,l,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
epi := SQP`SQ[1];
NWT := [* p *];
primes := SQP`SQ[2];
flag := 0;

for tu in L do
TS := SQP`SplitExt[n,tu];
M := modlist[2,n,3,tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;

r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
epi := CreateLift(epi, M, T, L[1]);
Append(~NW, M );
for i := 2 to #L do
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[i]);
Append(~NWT, M[2] );
end for;
end for;

if flag ne 0 then
SQR := ChangeQuotient (SQP, epi, primes, SQP`Series[2]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
Append(~SQR`Series[2],  [[NWT]]);
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
for tu in L do
if Type(SE[tu]) ne RngIntElt then
SE[tu] := false; // THIS IS NOT ALWAYS CORRECT!!!!
end if;
end for;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
else
SQR := SQP;
end if;
return flag, SQR;
end intrinsic;

intrinsic LiftSplitExtension(SQP::SQProc, p::RngIntElt) -> RngIntElt, SQProc

{Build the split extension of the list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
ML := modlist[2,n,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
epi := SQP`SQ[1];
primes := SQP`SQ[2];
flag := 0;

NWT := [* p *];
for tu := 1 to #ML do
TS := SQP`SplitExt[n,tu];
M := ML[tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;

r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
for i := 1 to #L do
G := Codomain(epi);
if NPCgens(Group(M[2])) ne NPCgens(G) then
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[i]);
else
epi := CreateLift(epi, M, T, L[i]);
end if;
Append(~NWT, M[2] );
end for;
end for;

if flag ne 0 then
SQR := ChangeQuotient(SQP,epi,primes,SQP`Series[2] cat [[[ NWT ]]]);
SQR`Series[1] := 0;
InsertRelatives(~SQP, ~SQR);
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
for tu in [1..#SE] do
if Type(SE[tu]) ne RngIntElt then
SE[tu] := false; // THIS IS NOT ALWAYS CORRECT!!!!
end if;
end for;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
else
SQR := SQP;
end if;
return flag, SQR;
end intrinsic;

intrinsic LiftSplitExtension(SQP::SQProc) -> RngIntElt, SQProc

{Build the split extension of the list of modules for their actual solution
space.}

require SQP`Data[2] ne {} : "relevant primes unknown";
ef := 0;
for p in SQP`Data[2] do
flag, SQR := LiftSplitExtension(SQP, p);
if flag ne 0 then
ef +:= flag;
SQP := SQR;
end if;
end for;

return ef, SQR;
end intrinsic;

intrinsic LiftSplitExtensionRow(SQP::SQProc, p::RngIntElt, l::RngIntElt) ->RngIntElt, SQProc

{Build the split extensions of SQP for the p-modules in the l-th list for their
actual solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
L := modlist[3,n,l,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
primes := SQP`SQ[2];
flag := 0;

for tu in L do
NWT := [* p *];
TS := SQP`SplitExt[n,tu];
M := modlist[2,n,3,tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;

epi := SQP`SQ[1];
r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
for i := 1 to #L do
epi := CreateLift(epi, M, T, L[i]);
Append(~NWT, M[2] );
end for;
SQR := ChangeQuotient (SQP,epi,primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
SE[tu] := false; // THIS IS NOT ALWAYS CORRECT!!!!
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
end for;

return flag, SQP;
end intrinsic;

intrinsic LiftSplitExtensionRow(SQP::SQProc, p::RngIntElt) -> RngIntElt, SQProc

{Build the split extensions of SQP for the list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
ML := modlist[2,n,3];
zero := GF(p) ! 0;
primes := SQP`SQ[2];
flag := 0;

for tu := 1 to #ML do
TS := SQP`SplitExt[n,tu];
NWT := [* p *];
M := ML[tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;

one  := GF(p) ! 1;
epi := SQP`SQ[1];
r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..d]];
for i := 1 to d do
L[i,i] := one;
end for;

flag +:= 1;
for i := 1 to #L do
epi := CreateLift(epi, M, T, L[i]);
Append(~NW, M );
end for;
SQR := ChangeQuotient(SQP,epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
SE[tu] := false; // THIS IS NOT ALWAYS CORRECT!!!!
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
end for;

return flag, SQP;
end intrinsic;

intrinsic LiftSplitExtensionRow(SQP::SQProc) -> RngIntElt, SQProc

{Build the split extension of the list of modules for their actual solution space.}

ef := 0;
for p in SQP`Data[2] do
flag, SQP := LiftSplitExtensionRow(SQP, p);
if flag ne 0 then
ef +:= flag;
end if;
end for;

return ef, SQP;
end intrinsic;

intrinsic LiftNonsplitExtension(SQP::SQProc, p::RngIntElt, i::RngIntElt,
k::RngIntElt : LinComb := []) -> SQProc
{Build the non-split extension of the i-th p-module for the k-th solution space.
 A set of linear combinations can be specified.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
M := modlist[2,n,3,i];
T := SQP`NonsplitExt[n,i,k+1,3];
r := Nrows(T[1,3]);

if LinComb eq [] then
r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
zero := GF(p) ! 0;
one  := GF(p) ! 1;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;
else
L := LinComb;
end if;

epi := SQP`SQ[1];
primes := SQP`SQ[2];
epi := CreateLift(epi, M, T, L[1]);
NWT := [* p, M[2] *];
for j := 2 to #L do
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[j]);
    Append(~NW, M[2] );
end for;
SQR := ChangeQuotient (SQP, epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
NE[i] := 0;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;

return SQR;
end intrinsic;

intrinsic LiftNonsplitExtension(SQP::SQProc, p::RngIntElt, l::RngIntElt) ->RngIntElt, SQProc

{Build the non-split extension of the l-th list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
L := modlist[3,n,l,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
epi := SQP`SQ[1];
NWT := [* p *];
primes := SQP`SQ[2];
flag := 0;

for tu in L do
TS := SQP`NonsplitExt[n,tu];
M := modlist[2,n,3,tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;

r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
epi := CreateLift(epi, M, T, L[1]);
Append(~NWT, M[2] );
for i := 2 to #L do
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[i]);
Append(~NW, M );
end for;
end for;

if flag ne 0 then
SQR := ChangeQuotient(SQP,epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
for tu in L do
NE[tu] := 0;
end for;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
else
SQR := SQP;
end if;
return flag, SQR;
end intrinsic;

intrinsic LiftNonsplitExtension(SQP::SQProc, p::RngIntElt) -> RngIntElt, SQProc

{Build the non-split extension of the list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
ML := modlist[2,n,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
epi := SQP`SQ[1];
NWT := [* p *];
primes := SQP`SQ[2];
flag := 0;

for tu := 1 to #ML do
TS := SQP`NonsplitExt[n,tu];
M := ML[tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
elif TS[TS[1],2] in {0,2} then
continue;
else
T := TS[TS[1],3];
end if;

r := Nrows(T[1,3]);
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[1]);
Append(~NWT, M[2] );
for i := 2 to #L do
G := Codomain(epi);
MM := ModulFromQuotientGroup(M,G);
epi := CreateLift(epi, MM, T, L[i]);
Append(~NWT, M[2] );
end for;
end for;

if flag ne 0 then
SQR := ChangeQuotient(SQP,epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
NE := Seqlist([0 : k in [1..#MM1[3]]]);
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
else
SQR := SQP;
end if;
return flag, SQR;
end intrinsic;

intrinsic LiftNonsplitExtension(SQP::SQProc) -> RngIntElt, SQProc

{Build the non-split extension of the list of modules for their actual solution space.}

ef := 0;
for p in SQP`Data[2] do
flag, SQR := LiftNonsplitExtension(SQP, p);
if flag ne 0 then
ef +:= flag;
SQP := SQR;
end if;
end for;

return ef, SQR;
end intrinsic;

intrinsic LiftNonsplitExtensionRow(SQP::SQProc, p::RngIntElt, l::RngIntElt)-> RngIntElt, SQProc

{Build the non-split extensions of SQP for the p-modules in the l-th list for
their actual solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
L := modlist[3,n,l,3];
zero := GF(p) ! 0;
one  := GF(p) ! 1;
primes := SQP`SQ[2];
flag := 0;

for tu in L do
TS := SQP`NonsplitExt[n,tu];
M := modlist[2,n,3,tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;
r := Nrows(T[1,3]);

epi := SQP`SQ[1];
NWT := [* p *];
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
for i := 1 to #L do
epi := CreateLift(epi, M, T, L[i]);
Append(~NWT, M[2] );
end for;
SQR := ChangeQuotient(SQP,epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
NE[tu] := 0;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
end for;

return flag, SQP;
end intrinsic;

intrinsic LiftNonsplitExtensionRow(SQP::SQProc, p::RngIntElt) -> RngIntElt,SQProc

{Build the non-split extensions of SQP for the list of p-modules for their actual
solution space.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);
ML := modlist[2,n,3];
zero := GF(p) ! 0;
primes := SQP`SQ[2];
flag := 0;

for tu := 1 to #ML do
TS := SQP`NonsplitExt[n,tu];
NWT := [* p *];
M := ML[tu];
if Type(TS) ne List or TS[1] eq 0 then
continue;
else
T := TS[TS[1],3];
end if;
r := Nrows(T[1,3]);

one  := GF(p) ! 1;
epi := SQP`SQ[1];
if #T[1] eq 3 then
d := r;
else
d := r + Nrows(T[1,4]);
end if;
L := [[zero: i in [1..d]]: j in [1..r]];
for i := 1 to r do
L[i,i] := one;
end for;

flag +:= 1;
for i := 1 to #L do
epi := CreateLift(epi, M, T, L[i]);
Append(~NWT, M[2] );
end for;
SQR := ChangeQuotient(SQP,epi, primes, SQP`Series[2] cat [[[ NWT ]]]);
InsertRelatives(~SQP, ~SQR);
SQR`Series[1] := 0;
for pp in modlist[1] do
f1, MM1, MM2 := ModulCandidatesFromParent(SQP, SQR, pp);
f2, SE, NE   := ExtensionSpacesFromParent(SQP, SQR, pp);
if pp eq p then
NE[tu] := 0;
end if;
Append(~SQR`ModulCandidates[1], pp);
Append(~SQR`ModulCandidates[2], MM1);
Append(~SQR`ModulCandidates[3], MM2);
Append(~SQR`SplitExt, SE);
Append(~SQR`NonsplitExt, NE);
end for;
end for;

return flag, SQP;
end intrinsic;

intrinsic LiftNonsplitExtensionRow(SQP::SQProc) -> RngIntElt, SQProc

{Build the non-split extension of the list of modules for their actual solution space.}

ef := 0;
for p in SQP`Data[2] do
flag, SQP := LiftNonsplitExtensionRow(SQP, p);
if flag ne 0 then
ef +:= flag;
end if;
end for;

return ef, SQP;
end intrinsic;

/*
 * Description of the data structure of an SQ Process.
 * Let F be a finitely generated group and G a soluble group with epimorphism
 * epi: F ->> G;
 *
 * We have the following data:
 * SQ : <epi, [<p, e>], e_max>
 *       p a prime and e nonnegative integer, limits the exponent of p in |G|.
 *       e eq 0 means no limit, e_max gives a default limit for new primes.
 *       The second and third entry may be given when the quotient is init,
 *       the second entry is modified when new primes occur.
 * Series: <id, weights, [* <M, S,L >*]>
 *       The series used for the construction. id is an identification code:
 *       0:user, 1:sag-system. Weights is the list giving the series structure.
 *       the third arg is the list of moduls and solution spaces used for the
 *       construction of the SQ. If a special choice of coefficients has been
 *       used, it is stored in the third entry.
 * Data: <|G|, {relevant primes}, Num_to_complete>;
 *       the order, the set of known relevant primes. c_flag is true iff the
 *       completeness of the set has been proved.
 *       If a free abelian module occurs, the set is changed to {0} and c_flag
 *       is always true.
 * Modi: [SQ_PrimeSearchModus, SQ_ModulCalcModus, SQ_CollectorModus]
 *       The modi with the same meaning as in MSQ...
 * Limits: [SeriesLength, SubSeriesLength, QuotientSize, SectionSize]
 *       Limits as in MSQ...
 * Collect: <[* <V, p, tr, ws,  epi >*],[* <V, p, ws, epi >*]>
 *       Lists of Collectors and their specifications for the nonsplit and the
 *       split case. Only V and p are obligatory, the other entries are omitted
 *       from the right if trivial V is the collector (handle), p the
 *       characteristic of the coefficient ring. Each p appears only once per
 *       list, if a new collector with the same characteristic is set up, the
 *       existing one will be removed.
 *       tr is a sequence of tuples defining tails which are required to be 0.
 *       ws is a explicitly defined weight series
 *       epi is and epimorphism onto a quotient algebra of the group algebra.
 * Relat: <[* SQF1, SQF2,...*], [* SQE1, SQE2 ... *]>
 *       Lists of related quotients: SQF1 is the quotient lift where the actual
 *       quotient SQP is a direct lift from; for the later their exists an
 *       epimorphism SQP ->> SQFi. The second list holds direct lifts of SQP.
 * ModulCandidates: <[* p *], [* <max, {exact}, [* moduls *]> *],
 *                   [* <max, {exact}, [indices]> *]>
 *       lists of moduls calculated for the soluble group. The first list holds
 *       the characteristics of the calculated moduls. The i-th entry of the
 *       second list holds tuples, giving restrictions applied when the list has
 *       been calculated, and the list of moduls for the i-th prime. Note that
 *       any new p_i-module will be appended to that list, and all modules in
 *       the list are inequivalent.
 *       The third list holds index lists for subsets of the modul list.
 * SplitExt   : [* [* 0/false/ [* a, S1, S2...*] *] *]
 * NonsplitExt: [* [* 0/false/ [* a, S1, S2...*] *] *]
 *       Lists of solutions spaces for (non-)split extensions, the i-th list
 *       corresponds to the i-th list of modules.
 *       The list entries are either "0", indicating that no solutions space has
 *       been calculated yet, "false", indicating that no solution exists for
 *       that module, or a list [* a, S1, S2...*]. Here Si are solution spaces,
 *       and the integer a is the index of the `actual` solution space (last
 *       calculated or specified by user)
 */

SQProcPrint_p := procedure(SQP, p: Quotient := 1, Primes := 1, Series:= 0,
Collector := 1, Relat := 1, Modules := 1, Extensions:= 1)

epi := SQP`SQ[1];
case Quotient :
when 0:
print "Soluble Quotient: ";
print "Image of order ", SQP`Data[1];
when 1:
print "=============== Soluble quotient info ==========================";
print "Soluble Quotient of ", Domain(epi);
print "Image is:", Codomain(epi);
when 2:
print "=============== Soluble quotient info ==========================";
print "Soluble Quotient of ", Domain(epi);
print "Image is:", Codomain(epi);
F := Domain(epi);
print "The Generators are mapped to:", [epi(f) : f in Generators(F)];
else:
print "=============== Soluble quotient info =========================";
print "Soluble Quotient of ", Domain(SQP`SQ[1]);
print "Image is:", Codomain(SQP`SQ[1]);
epi := SQP`SQ[1];
F := Domain(epi);
print "The Generators are mapped to:", [epi(f) : f in Generators(F)];
print "The remaining prime guesses are:", SQP`SQ[2];
end case;

case Primes:
when 0:
Dummy := 0;
when 1:
print "=============== relevant primes ===============================";
if SQP`Data[3] ne 0 then
print "The known set of relevant primes is", SQP`Data[2],
      "Completenes has not been checked";
elif 0 in SQP`Data[2] then
print "A free abelian section exists, all primes are relevant.";
else
print "Complete set of relevant primes is", SQP`Data[2];
end if;
end case;

case Collector:

when 0:
Dummy := 0;
when 1:
print "=============== active Collectors=============================";
if #SQP`Collect[1] eq 0 then
print "No Collectors for nonsplit extensions active";
else
pt := {t[2] : t in SQP`Collect[1]};
if p in pt then
print "Characteristic",p,"Collector for nonsplit extensions active. ";
elif 0 in pt then
print "Characteristic 0 Collector for nonsplit extensions active.";
else
print "No Collectors for characteristic",p, "nonsplit extensions active";
end if;
end if;
if #SQP`Collect[2] eq 0 then
print "No Collectors for split extensions active";
else
pt := {t[2] : t in SQP`Collect[2]};
if p in pt then
print "Characteristic",p,"Collector for split extensions active.";
elif 0 in pt then
print "Characteristic 0 Collector for split extensions active.";
else
print "No Collectors for characteristic",p, "split extensions active";
end if;
end if;

else :
print "=============== active Collectors=============================";
if #SQP`Collect[1] eq 0 then
print "No Collectors for nonsplit extensions active";
else
T := SQP`Collect[1];
k := {i : i in [2..#T] | T[i,2] in {0,p}};
print "Active Collectors for nonsplit extensions:", {T[i] : i in k};
end if;
if #SQP`Collect[2] eq 0 then
print "No Collectors for split extensions active";
else
T := SQP`Collect[2];
k := {i : i in [2..#T] | T[i,2] in {0,p}};
print "Active Collectors for nonsplit extensions:", {T[i] : i in k};
end if;
end case;

ML := SQP`ModulCandidates;
case Modules:

when 0:
Dummy := 0;
when 1:
print "=============== irreducible modules===========================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print #ML[2,i,3], "modules found in characteristic ", ML[1,i];
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
end if;
end if;
when 2:
print "=============== irreducible modules===========================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print"Modules found in characteristic",ML[1,i],":";
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
else
print "This list fulfills the specification:", ML[2,i,1], ML[2,i,1];
end if;
print ML[2,i,3];
end if;
else:
print "=============== irreducible modules===========================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print"Modules found in characteristic",ML[1,i],":";
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
else
print "This list fulfills the specification:",
ML[2,i,1], ML[2,i,2];
end if;
print ML[2,i,3];
if #ML[3,i] gt 1 then
print "The following sublists has been created:";
for j := 2 to #ML[3,i] do
print ML[3,i,j];
end for;
end if;
end if;
end case;

SE := SQP`SplitExt;
NE := SQP`NonsplitExt;

case Extensions:
when 0:
Dummy := 0;
when 1:
print "=============== Extension spaces==============================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
outlist := [Integers() |];
for k := 2 to #SE[i,j] do
if SE[i,j, k, 2]  in {0,2} then
Append(~outlist, 0);
else
Append(~outlist, Nrows(SE[i,j,k,3,1,3]));
end if;
end for;
print #SE[i,j]-1, "Solution spaces with split extensions calculated, multiplicity:", outlist;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
outlist := [Integers() |];
for k := 2 to #NE[i,j] do
if NE[i,j, k, 2]  in {0,2} then
Append(~outlist, 0);
else
Append(~outlist, Nrows(NE[i,j,k,3,1,3]));
end if;
end for;
print #NE[i,j]-1, "Solution spaces with nonsplit extensions calculated, multiplicity:", outlist;
end if;
end for;
end if;
when 2:
print "=============== Extension spaces==============================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
outlist := [<0,0>];
for k := 2 to #SE[i,j] do
case SE[i,j, k, 2]:
when 0:
Append(~outlist, <0,0>);
when 2:
Append(~outlist, <0,Nrows(SE[i,j,k,3,1,4])>);
when 1:
Append(~outlist, <Nrows(SE[i,j,k,3,1,3]),0>);
when 3:
Append(~outlist, <Nrows(SE[i,j,k,3,1,3]),
  Nrows(SE[i,j,k,3,1,4])>);
end case;
end for;
print #SE[i,j]-1, "Solution spaces with split extensions calculated, <multiplicity, #Coboundaries>:", outlist;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
outlist := [<0,0>];
for k := 2 to #NE[i,j] do
case NE[i,j, k, 2]:
when 0:
Append(~outlist, <0,0>);
when 2:
Append(~outlist, <0,Nrows(NE[i,j,k,3,1,4])>);
when 1:
Append(~outlist, <Nrows(NE[i,j,k,3,1,3]),0>);
when 3:
Append(~outlist, <Nrows(NE[i,j,k,3,1,3]),
  Nrows(NE[i,j,k,3,1,4])>);
end case;
end for;
print #NE[i,j]-1, "Solution spaces with nonsplit extensions calculated, <multiplicity, #Coboundaries>:", outlist;
end if;
end for;
end if;
else:
print "=============== Extension spaces==============================";
if p notin ML[1] then
print "No modules in characteristic", p, "have been calculated yet.";
else
i := Index(ML[1], p);
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
print "Solution spaces with split extensions:";
for k := 2 to #SE[i,j] do
print SE[i,j,k,3];
end for;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
print "Solution spaces with nonsplit extensions:";
for k := 2 to #NE[i,j] do
print NE[i,j,k,3];
end for;
end if;
end for;
end if;
end case;
print "===============================================================";

end procedure;

intrinsic PrintProcess(SQP::SQProc, p::RngIntElt: Quotient := 1, Primes := 1,
Series := 0, Collector := 1, Relat := 1, Modules := 1, Extensions:= 1)
{Print function for SQProc. Print prime specific information.};

require p in SQP`Data[2] : "Given prime is not relevant for this soluble quotient.";

SQProcPrint_p(SQP, p: Quotient := Quotient, Primes := Primes, Series := Series,
Collector := Collector, Relat := Relat, Modules := Modules,
Extensions := Extensions);

end intrinsic;

SQProcPrint := procedure(SQP: Quotient := 1, Primes := 1, Series :=0,
Collector := 1, Relat := 1, Modules := 1, Extensions:= 1)

epi := SQP`SQ[1];
case Quotient :
when 0:
print "Soluble Quotient: ";
print "Image of order ", SQP`Data[1];
when 1:
print "=============== Soluble quotient info =========================";
print "Soluble Quotient of ", Domain(epi);
print "Image is:", Codomain(epi);
when 2:
print "=============== Soluble quotient info =========================";
print "Soluble Quotient of ", Domain(epi);
print "Image is:", Codomain(epi);
F := Domain(epi);
print "The Generators are mapped to:", [epi(f) : f in Generators(F)];
else:
print "=============== Soluble quotient info =========================";
print "Soluble Quotient of ", Domain(epi);
print "Image is:", Codomain(epi);
F := Domain(epi);
print "The Generators are mapped to:", [epi(f) : f in Generators(F)];
print "The remaining prime guesses are:", SQP`SQ[2];
end case;

/* case Series:
when 0:
Dummy := 0;
when 1:
print SQP`Series[2];
end case;
*/

case Primes:
when 0:
Dummy := 0;
when 1:
print "=============== relevant primes ===============================";
if SQP`Data[3] ne 0 then
print "The known set of relevant primes is", SQP`Data[2],
      "Completenes has not been checked";
elif 0 in SQP`Data[2] then
print "A free abelian section exists, all primes are relevant.";
else
print "Complete set of relevant primes is", SQP`Data[2];
end if;
end case;

case Collector:

when 0:
Dummy := 0;
when 1:
print "=============== active Collectors=============================";
if #SQP`Collect[1] eq 0 then
print "No Collectors for nonsplit extensions active";
else
print "Collectors for nonsplit extensions active with coefficient ring characteristic:", {t[2] : t in SQP`Collect[1]};
end if;
if #SQP`Collect[2] eq 0 then
print "No Collectors for split extensions active";
else
print "Collectors for split extensions active with coefficient ring characteristic:", {t[2] : t in SQP`Collect[2]};
end if;

else :
print "=============== active Collectors=============================";
if #SQP`Collect[1] eq 0 then
print "No Collectors for nonsplit extensions active";
else
print "Active Collectors for nonsplit extensions:";
for t in SQP`Collect[1] do
print "Coefficient ring characteristic:", t[2];
for i := 3 to #t do
print t[i];
end for;
end for;
end if;
if #SQP`Collect[2] eq 0 then
print "No Collectors for split extensions active";
else
print "Active Collectors for split extensions:";
for t in SQP`Collect[2] do
print "Coefficient ring characteristic:", t[2];
for i := 3 to #t do
print t[i];
end for;
end for;
end if;
end case;

case Relat:
when 0:
Dummy := 0;
when 1:
print "=============== related quotients=============================";
print #SQP`Relat[1], "quotients found that lift to this quotient.";
print #SQP`Relat[2], "quotients found that are lifts of this quotient.";
end case;

ML := SQP`ModulCandidates;
case Modules:

when 0:
Dummy := 0;
when 1:

print "=============== irreducible modules===========================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print #ML[2,i,3], "found in characteristic ",
ML[1,i];
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
end if;
end for;
end if;
when 2:
print "=============== irreducible modules===========================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print"Modules found in characteristic",ML[1,i],":";
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
else
print "This list fulfills the specification:",
ML[2,i,1],
ML[2,i,1];
end if;
print ML[2,i,3];
end for;
end if;
else:
print "=============== irreducible modules===========================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print"Modules found in characteristic",ML[1,i],":";
if ML[2,i,1] eq 0 and ML[2,i,4] eq 0 then
print "This list is complete.";
else
print "This list fulfills the specification:",
ML[2,i,1], ML[2,i,2];
end if;
print ML[2,i,3];
if #ML[3,i] gt 1 then
print "The following sublists has been created:";
for j := 2 to #ML[3,i] do
print ML[3,i,j];
end for;
end if;
end for;
end if;
end case;

SE := SQP`SplitExt;
NE := SQP`NonsplitExt;

case Extensions:
when 0:
Dummy := 0;
when 1:
print "=============== Extension spaces==============================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
outlist := [Integers() |];
for k := 2 to #SE[i,j] do
if SE[i,j, k, 2]  in {0,2} then
Append(~outlist, 0);
else
Append(~outlist, Nrows(SE[i,j,k,3,1,3]));
end if;
end for;
print #SE[i,j]-1, "Solution spaces with split extensions calculated, multiplicity:", outlist;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
outlist := [Integers() |];
for k := 2 to #NE[i,j] do
if NE[i,j, k, 2]  in {0,2} then
Append(~outlist, 0);
else
Append(~outlist, Nrows(NE[i,j,k,3,1,3]));
end if;
end for;
print #NE[i,j]-1, "Solution spaces with nonsplit extensions calculated, multiplicity:", outlist;
end if;
end for;
end for;
end if;
when 2:
print "=============== Extension spaces==============================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
outlist := [<0,0>];
for k := 2 to #SE[i,j] do
case SE[i,j, k, 2]:
when 0:
Append(~outlist, <0,0>);
when 2:
Append(~outlist, <0,Nrows(SE[i,j,k,3,1,4])>);
when 1:
Append(~outlist, <Nrows(SE[i,j,k,3,1,3]),0>);
when 3:
Append(~outlist, <Nrows(SE[i,j,k,3,1,3]),
                  Nrows(SE[i,j,k,3,1,4])>);
end case;
end for;
print #SE[i,j]-1, "Solution spaces with split extensions calculated, <multiplicity, Coboundaries>:", outlist;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
outlist := [<0,0>];
for k := 2 to #NE[i,j] do
case NE[i,j, k, 2]:
when 0:
Append(~outlist, <0,0>);
when 2:
Append(~outlist, <0,Nrows(NE[i,j,k,3,1,4])>);
when 1:
Append(~outlist, <Nrows(NE[i,j,k,3,1,3]),0>);
when 3:
Append(~outlist, <Nrows(NE[i,j,k,3,1,3]),
                  Nrows(NE[i,j,k,3,1,4])>);
end case;
end for;
print #NE[i,j]-1, "Solution spaces with nonsplit extensions calculated, multiplicity:", outlist;
end if;
end for;
end for;
end if;
else:
print "=============== Extension spaces==============================";
if #ML[1] eq 0 then
print "No modules have been calculated yet.";
else
for i := 1 to #ML[1] do
print"Extensions in characteristic",ML[1,i],":";
for j := 1 to #ML[2,i,3] do
print "Modul", j, ":";
if Type(SE[i,j]) eq RngIntElt then
print "Split Extension Space unknown";
elif Type(SE[i,j]) eq BoolElt then
print "No split extensions possible";
else
print "Solution spaces with split extensions:";
for k := 2 to #SE[i,j] do
print SE[i,j,k,3];
end for;
end if;
if Type(NE[i,j]) eq RngIntElt then
print "Nonsplit Extension Space unknown";
elif Type(NE[i,j]) eq BoolElt then
print "No nonsplit extensions possible";
else
print "Solution spaces with nonsplit extensions:";
for k := 2 to #NE[i,j] do
if NE[i,j,k,2] eq 0 then
print "<0>";
else
print NE[i,j,k,3];
end if;
end for;
end if;
end for;
end for;
end if;
end case;
print "===============================================================";

end procedure;

intrinsic PrintProcess(SQP::SQProc: Quotient := 1, Primes := 1, Series := 0,
Collector := 1, Relat := 1, Modules := 1, Extensions:= 1)
{General print function for SQProc.};

SQProcPrint(SQP: Quotient := Quotient, Primes := Primes, Series := Series,
Collector := Collector, Relat := Relat, Modules := Modules,
Extensions := Extensions);

end intrinsic;

intrinsic PrintQuotient (SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := Print, Series := 0, Primes := 0,
Collector := 0, Relat := 0, Modules := 0, Extensions:= 0);
end intrinsic;

intrinsic PrintSeries (SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := 0, Series := Print, Primes := 0,
Collector := 0, Relat := 0, Modules := 0, Extensions:= 0);
end intrinsic;

intrinsic PrintPrimes (SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := 0, Series := 0, Primes := Print,
Collector := 0, Relat := 0, Modules := 0, Extensions:= 0);
end intrinsic;

intrinsic PrintCollector (SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := 0, Series := 0, Primes := 0,
Collector := Print, Relat := 0, Modules := 0, Extensions:= 0);
end intrinsic;

intrinsic PrintCollector (SQP::SQProc, p::RngIntElt: Print := 1)
{Print function};
PrintProcess(SQP, p: Quotient := 0, Series := 0, Primes := 0,
Collector := Print, Relat := 0, Modules := 0, Extensions:= 0);
end intrinsic;

intrinsic PrintRelat (SQP::SQProc: Print := 1)
{Print function};

SQRoot := SQP`Root[3];
case Print:
when 1:
PrintProcess(SQP: Quotient := 0, Series := 0, Primes := 0,
Collector := 0, Relat := Print, Modules := 0, Extensions:= 0);
when 2:
ParentList := SQP`Relat[1];
if #ParentList gt 0 then
print "Parent quotient:";
for i in ParentList do
RR := SQRoot`Data[i];
if RR[1] eq true then
PrintQuotient(RR[3]);
end if;
end for;
end if;
ChildList := SQP`Relat[2];
if #ChildList gt 0 then
print "Children quotients:";
for i in ChildList do
RR := SQRoot`Data[i];
if RR[1] eq true then
PrintQuotient(RR[3]);
end if;
end for;
end if;
else :
ParentList := SQP`Relat[1];
if #ParentList gt 0 then
for i in ParentList do
RR := SQRoot`Data[i];
if RR[1] eq true then
print "Parent quotient:";
PrintQuotient(RR[3]);
print"-------- its relatives ----------------";
PrintRelat(RR[3]: Print := 2);
print"---------------------------------------";
end if;
end for;
end if;
ChildList := SQP`Relat[2];
if #ChildList gt 0 then
for i in ChildList do
RR := SQRoot`Data[i];
if RR[1] eq true then
print "Child quotient:";
PrintQuotient(RR[3]);
print"-------- its relatives ----------------";
PrintRelat(RR[3]: Print := 2);
print"---------------------------------------";
end if;
end for;
end if;
end case;

end intrinsic;

intrinsic PrintModules (SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := 0, Series := 0, Primes := 0,
Collector := 0, Relat := 0, Modules := Print, Extensions:= 0);
end intrinsic;

intrinsic PrintModules (SQP::SQProc, p::RngIntElt: Print := 1)
{Print function};
PrintProcess(SQP, p: Quotient := 0, Series := 0, Primes := 0,
Collector := 0, Relat := 0, Modules := Print, Extensions:= 0);
end intrinsic;

intrinsic PrintExtensions(SQP::SQProc: Print := 1)
{Print function};
PrintProcess(SQP: Quotient := 0, Series := 0, Primes := 0,
Collector := 0, Relat := 0, Modules := 0, Extensions:= Print);
end intrinsic;

intrinsic PrintExtensions(SQP::SQProc, p::RngIntElt: Print := 1)
{Print function};
PrintProcess(SQP, p: Quotient := 0, Series := 0, Primes := 0,
Collector := 0, Relat := 0, Modules := 0, Extensions:= Print);
end intrinsic;

intrinsic GetQuotient(SQP::SQProc) -> GrpPC, Map
{Returns the soluble group and the epimorphism from SQP.}

epi := SQP`SQ[1];

return Codomain(epi), epi;
end intrinsic;

intrinsic GetPrimes(SQP::SQProc) -> SetEnum, BoolElt
{Return the relevant primes stored in SQP and a flag indicating the
completeness.}

return SQP`Data[2], SQP`Data[3];
end intrinsic;

intrinsic GetParent(SQP::SQProc) -> SQProc
{Returns the parent of SQP, i.e. the soluble Quotient which lifts to SQP}

RR := SQP`Relat[1];
require #RR ne 0 : "Process does not have a parent";

return (SQP`Root[3])`Data[Min(RR), 3];
end intrinsic;

intrinsic GetChildren(SQP::SQProc) -> List
{Returns a list of soluble quotients which are lifts of SQP.}

RR := [* *];
LL := (SQP`Root[3])`Data;
for t in SQP`Relat[2] do
if LL[t,1] eq true then
Append(~RR, LL[t,1]);
end if;
end for;

return RR;
end intrinsic;

intrinsic GetChild(SQP::SQProc, i::RngIntElt) -> List
{Returns the i-th soluble quotient which is a lift of SQP.}

RR := SQP`Relat[2];
require  i in RR: "Process does not have i as child";
SQRoot := SQP`Root[3];

DD := SQRoot`Data;
require DD[i,1] ne false: "i-th SQ Process has been deleted";
return DD[i,3];
end intrinsic;

intrinsic GetModule(SQP::SQProc, p::RngIntElt, i::RngIntElt) -> ModGrp
{Return the i-th p-module stored in SQP.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);

require n ne 0 : "No module for that prime stored.";
L := modlist[2,n,3];
require i le #L : "Index out of bound for module list.";

return L[i,2];

end intrinsic;

intrinsic GetModules(SQP::SQProc, p::RngIntElt: Process := false) -> List
{Return the list of all p-modules stored in SQP.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);

if n eq 0 then
return [* *];
elif Process eq true then
return modlist[2,n,3];
else
MM := modlist[2,n,3];
L := [* *];
for i := 1 to #MM do
L[i] := MM[i,2];
end for;
return L;
end if;

end intrinsic;

intrinsic GetModules(SQP::SQProc, p::RngIntElt, l::RngIntElt: Process := false) -> List
{Return the l-th list of p-modules stored in SQP.}

modlist := SQP`ModulCandidates;
n := Index(modlist[1], p);

require n ne 0 : "No modules for that prime stored.";
require l le #modlist[3,n] : "Index out of bound for list of modules.";
M := modlist[2,n,3];
I := modlist[3,n,l,3];
L := [* *];

for i := 1 to #I do
t := I[i];
if Process eq false then
L[i] := M[t,2];
else
L[i] := M[t];
end if;
end for;

return L;

end intrinsic;

intrinsic DeleteSplitCollector(SQP::SQProc, p::RngIntElt)
{Delete the collector for split extensions in characteristic p.}

CN := SQP`Collect[2];
for i := 1 to #CN do
if CN[i,2] eq p then
LetterVarDelete(CN[i,1]);
Remove(~SQP`Collect[2], i);
break;
end if;
end for;
end intrinsic;

intrinsic DeleteSplitCollector(SQP::SQProc)
{Delete all collectors for split extensions.}

CN := SQP`Collect[2];
for i := 1 to #CN do
LetterVarDelete(CN[i,1]);
end for;
SQP`Collect[2] := [* *];

end intrinsic;

intrinsic DeleteNonsplitCollector(SQP::SQProc, p::RngIntElt)
{Delete the collector for non-split extensions in characteristic p.}

CN := SQP`Collect[1];
for i := 1 to #CN do
if CN[i,2] eq p then
LetterVarDelete(CN[i,1]);
Remove(~SQP`Collect[1], i);
break;
end if;
end for;
end intrinsic;

intrinsic DeleteNonsplitCollector(SQP::SQProc)
{Delete all collectors for non-split extensions.}

CN := SQP`Collect[1];
for i := 1 to #CN do
LetterVarDelete(CN[i,1]);
end for;
SQP`Collect[1] := [* *];

end intrinsic;

intrinsic DeleteCollector(SQP::SQProc, p::RngIntElt)
{Delete the collectors in characteristic p.}

DeleteSplitCollector(SQP, p);
DeleteNonsplitCollector(SQP, p);

end intrinsic;

intrinsic DeleteCollector(SQP::SQProc)
{Delete all the collectors of SQP.}

DeleteSplitCollector(SQP);
DeleteNonsplitCollector(SQP);

end intrinsic;

intrinsic DeleteProcess(~SQP::SQProc)
{Delete the soluble quotient process variable.}

// Delete Collectors
DeleteSplitCollector(SQP);
DeleteNonsplitCollector(SQP);
SQP`Collect := 0;

// Delete Modules
modlist := SQP`ModulCandidates;
for i := 1 to #modlist[1] do
MM := modlist[2,i,3];
AbsolutelyIrreducibleModulesDelete(~MM);
MM := 0;
modlist[2,i,3] := 0;
end for;
SQP`ModulCandidates := 0;
flag := 0;

SQRoot := SQP`Root[3];
SQPi := SQP`Root[2];
for t in SQP`Relat[1] do
Exclude(~(SQRoot`Relat[t]), SQPi);
SQRoot`Relat[t] join:= SQP`Relat[2];
end for;
DD := SQRoot`Data;

for t in SQP`Relat[2] do
RR := DD[t,3];
Exclude(~(RR`Relat[1]), SQPi);
RR`Relat[1] join:= SQP`Relat[1];
end for;
SQP`Relat := 0;

SS := SQP`Series[2];
for i := 1 to #SS do
SSS := SS[i];
for j := 1 to #SSS do
SSSS := SSS[j];
for k := 1 to #SSSS do
SSSSS := SSSS[k];
while #SSSSS ne 0 do
Remove(~SSSSS, 1);
end while;
end for;
end for;
end for;
SQP`Series := 0;

SQP`SQ := 0;
SQP`Data := 0;
SQP`Modi := 0;
SQP`Limits := 0;
SQP`SplitExt := 0;
SQP`NonsplitExt := 0;
SQRoot`Data[SQPi, 1] := false;
//delete SQP;
end intrinsic;

intrinsic DeleteProcessDown(~SQP::SQProc)
{Delete the Process and all its child processes.}

CC := SQP`Relat[2];
DD := (SQP`Root[3])`Data;
for i in CC do
if DD[i,1] ne false then
DeleteProcess(~DD[i,3]);
CC := SQP`Relat[2];
end if;
end for;
DeleteProcess(~SQP);

end intrinsic;

intrinsic DeleteProcessComplete(~SQP::SQProc)
{Delete all soluble quotient processes which are related to SQP}

SQRoot := SQP`Root[3];
DD := SQRoot`Data;
for i := 2 to #DD do
if (DD[i,2])`Root[1] ne false then
DeleteProcessDown(~(DD[i,2]));
end if;
end for;

SQRoot`Data := 0;
SQRoot`Root := 0;
SQRoot`Relat := 0;

end intrinsic;

///////////////////////////////////////////////////////////////////
// Some tools related to the SQ Process.
///////////////////////////////////////////////////////////////////

intrinsic KeepGeneratorOrder(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the
order of the pc generators in SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[i,i] : i in {1..np}];
return S;
end intrinsic;

intrinsic KeepGeneratorAction(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the
conjugation action  of the pc generators in SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[j,i] : j in [i+1..np], i in {1..np}];
return S;
end intrinsic;

intrinsic KeepElementary(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the
order of the pc generators in SQR\SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[i,i] : i in {np+1..nr}];
return S;
end intrinsic;

intrinsic KeepAbelian(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the
conjugation action  of the pc generators in SQR \ SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[j,i] : j in [i+1..nr], i in {np+1..nr}];
return S;
end intrinsic;

intrinsic KeepGroupAction(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the
conjugation action  of the pc generators of SQP on those of SQR \ SQP is
kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[j,i] : j in [np+1..nr], i in {1..np}];
return S;
end intrinsic;

intrinsic KeepSplit(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the presentation of SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[j,i] : j in [i..np], i in {1..np}];
return S;
end intrinsic;

intrinsic KeepElementaryAbelian(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the order and the 
conjugation action  of the pc generators in SQR \ SQP is kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S := [[j,i] : j in [i..nr], i in {np+1..nr}];
return S;
end intrinsic;

intrinsic KeepSplitAbelian(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the presentation of SQP and the conjugation action in
SQR \ SQP are kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S :=     [[j,i] : j in [i..np], i in {1..np}]
     cat [[j,i] : j in [i+1..nr], i in {np+1..nr}];
return S;
end intrinsic;

intrinsic KeepSplitElementaryAbelian(SQP::SQProc, SQR::SQProc) -> SeqEnum
{Return the sequence useful for the Collector setup.
It determines that the presentation of SQP and of
SQR \ SQP are kept unchanged.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
GR := Codomain(SQR`SQ[1]);
nr := NPCgens(GR);

require np le nr : "Second argument is not a lift of the first argument.";

S :=     [[j,i] : j in [i..np], i in {1..np}]
     cat [[j,i] : j in [i..nr], i in {np+1..nr}];
return S;
end intrinsic;

intrinsic KeepPrimePower(SQP::SQProc, p::RngIntElt) -> SeqEnum
{Return a sequence of pairs [j,i] s.t. the order of both G.j and G.i is not p.}

GP := Codomain(SQP`SQ[1]);
np := NPCgens(GP);
pp := PCPrimes(GP);

I := {i : i in [1..np] | pp[i] ne p};
S := [[j,i] : j in I, i in I | j ge i];

return S;
end intrinsic;

intrinsic KeepPGroupWeights(SQseq::SeqEnum) -> SeqEnum
{Return a sequence of pairs [j,i] correspnding to the weight condition for the
 p-group. The weights are defined by the sequence of quotients.}

if #SQseq le 2 then
return []; // no condition derivable
end if;

SGP := [Codomain((SQseq[i])`SQ[1]): i in [1..#SQseq]];
snp := [NPCgens(SGP[i]) : i in [1..#SGP]];
gnp := snp[#SGP];

S := [[gnp+1, i] : i in [snp[1]+1..gnp-1]];
for nj := #snp -1 to 1 by -1 do
ni := #snp - nj+1;
if ni gt nj then
break;
end if;
S cat:= [[j,i] : i in [snp[ni]+1..j-1], j in [snp[nj]+1..snp[nj+1]] ];
end for;

return S;
end intrinsic;

//////////////////////////////////////////////////////////////////////
// Next step of tools
//////////////////////////////////////////////////////////////////////

intrinsic IsPureOrder(G::GrpPC) -> BoolElt, RngIntElt, RngIntElt
{Check the PC presentation of G for the Hall property.}

for i := 1 to NPCgens(G) do
oo := Order(G.i);
of := Factorization(oo);
if #of ne 1 then
return false, oo, _;
end if;
end for;

pp := PCPrimes(G);
pm := Seqset(pp);
ng := NPCgens(G);
index_pp := [<p, { i : i in {1.. #pp}| pp[i] eq p}>: p in pm];

for i := 1 to ng do
for j := i+1 to ng do
gs := Eltseq(G.j^G.i);
for ipp in index_pp do
if ipp[1] eq pp[j] then
tp := {i : i in {1..ng} | gs[i] ne 0};
if tp subset ipp[2] eq false then
return false, i, j;
end if;
end if;
end for;
end for;
end for;

return true, _,_;
end intrinsic;

SQProcNextSection := function(SQP, p, split, nonsplit, abelian, elementary, keeporder, modullist: tr_ext := [], semisimple := false, keepCollector:= [false, false])

/* general function for the calculation of a section with specified properties.
 * It is called with the apropriate args by the following intrinsics.
 * The arguments are:
 * SQP        SQProc : given process.
 * p          integer: prime characteristic of the modules.
 * split      boolean: if true, check split extensions (first step only)
 * nonsplit   boolean: if true, check nonsplit extensions (iterate, if possible)
 * abelain    boolean: if true, keep the section abelian.
 * elementary boolean: if true, keep generator order in section.
 * keeporder  boolean: if true, keep generator order in SQP.
 * modullist  integer: -1: calculate all p-modules and check them
 *                      0: take the list of all calculated p-modules
 *   >0: take the i-th list of p-modules;
 * tr_ext     [[j,i]]: additional sequence of pairs for the collector
 * semisimple boolean: if true, return after the first step
 * keepCollector [ ] : if true, keep the existing split/ nonsplit collector
 *                     (first step only)
 */

if keepCollector[1] eq false then
DeleteSplitCollector(SQP, p);
end if;
if keepCollector[2] eq false then
DeleteNonsplitCollector(SQP, p);
end if;

if modullist eq -1 then
tp := Modules(SQP, p);
end if;

mpn := {};
if nonsplit then

if keepCollector[2] eq false then
if keeporder then
ts := KeepPrimePower(SQP, p) cat tr_ext;
NonsplitCollector(SQP, p, ts);
else
NonsplitCollector(SQP, p);
end if;
end if;
// It`s a risk: we assume that no previous solution space for other
// modules has been calculated.
if modullist gt 0 then
SN := NonsplitExtensionSpace(SQP, p, modullist);
else
SN := NonsplitExtensionSpace(SQP, p);
end if;
mpn := {t: t in SN | t gt 0};
end if;

mpr := {};
if split then
if modullist gt 0 then
SR := SplitExtensionSpace(SQP, p, modullist);
else
SR := SplitExtensionSpace(SQP, p);
end if;
mpr := {t: t in SR | t gt 0};
end if;

flag := false;
if mpn ne {} then
tmp, SQR  := LiftNonsplitExtension(SQP,p);
if mpr ne {} then
tmp, SQR := LiftSplitExtension(SQR,p);
end if;
flag := true;
elif mpr ne {} then
tmp, SQR := LiftSplitExtension(SQP,p);
flag := true;
end if;

if flag eq false then
return false, _;
elif semisimple eq true then
return true, SQR;
end if;

while flag eq true do
if keeporder then
ts := KeepPrimePower(SQR, p) cat tr_ext;
else
ts := tr_ext;
end if;
if split then
ts cat:= KeepSplit(SQP, SQR);
end if;
if elementary then
ts cat:= KeepElementary(SQP, SQR);
end if;
if abelian then
ts cat:= KeepAbelian(SQP, SQR);
end if;

NonsplitCollector(SQR, p, ts);
// reminder: only the specified list of modules will be checked further on.
if modullist gt 0 then
SN := NonsplitExtensionSpace(SQR, p, modullist);
else
SN := NonsplitExtensionSpace(SQR, p);
end if;
mpn := {t: t in SN | t gt 0};
if mpn ne {} then
tmp1 := SQR;
tmp, SQR  := LiftNonsplitExtension(tmp1,p);
else
flag := false;
end if;
end while;

return true, SQR;

end function;

intrinsic AbelianSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-abelian module which lifts to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, true, true, false, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic AbelianSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal abelian module which lifts to a bigger quotient. If
PrimeCalc equals true, the relevant primes will be calculated first. If
ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := AbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic ElementaryAbelianSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maxinmal p-elementary abelian module which lifts to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, true, true, true, keeporder,ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic ElementaryAbelianSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal elementary abelian module which lifts to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := ElementaryAbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic SplitSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-group with a splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, false, false, false, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic SplitSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1,TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal nilpotent group with a splitting lift to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := SplitSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic SplitAbelianSection(SQP::SQProc, p::RngIntElt: ModuleList := -1,TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-abelian module with a splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, false, true, false, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic SplitAbelianSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal abelian group with a splitting lift to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := SplitAbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic SplitElementaryAbelianSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maxinmal p-elementary abelian module with a splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, false, true, true, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic SplitElementaryAbelianSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal elementary abelian group with a splitting lift to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := SplitElementaryAbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic NonsplitSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-group with a non splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, false, true, false, false, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic NonsplitSection(SQP::SQProc: PrimeCalc := true, ModuleList :=-1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal elementary abelian group with a splitting lift to a
 bigger quotient. If PrimeCalc equals true, the relevant primes will be
 calculated first. If ModuleList is 0, only the known modules will be taken into
 account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := NonsplitSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic NonsplitAbelianSection(SQP::SQProc, p::RngIntElt: ModuleList :=-1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-abelian module with a non splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, false, true, true, false, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic NonsplitAbelianSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal elementary abelian group with a splitting lift to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := NonsplitAbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

intrinsic NonsplitElementaryAbelianSection(SQP::SQProc, p::RngIntElt: ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal p-elementary abelian module with a splitting lift to a bigger quotient.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, false, true, true, true, keeporder, ModuleList: tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
else
return true, SQR;
end if;

end intrinsic;

intrinsic NonsplitElementaryAbelianSection(SQP::SQProc: PrimeCalc := true,ModuleList := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine the maximal elementary abelian group with a nonsplitting lift to a bigger
quotient. If PrimeCalc equals true, the relevant primes will be calculated
first. If ModuleList is 0, only the known modules will be taken into account.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := NonsplitElementaryAbelianSection(SQP, p: TrivialTails := TrivialTails);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;

SQProcImageEpi := function(SQP, SQR)

// install and return the canonical epimorphism G(SQR) ->> G(SQP).
// We assume that SQR is a lift of SQP!

GP := GetQuotient(SQP);
np := NPCgens(GP);
GR := GetQuotient(SQR);
nr := NPCgens(GR);
im := [GP.i : i in [1..np]] cat [Id(GP) : i in [np+1..nr]];

epi := hom<GR -> GP | im >;

return epi;
end function;

intrinsic PGroupSection(SQP::SQProc, p::RngIntElt:
ModuleList := -1, Steps := -1, TrivialTails := []) -> BoolElt, SQProc
{Determine a lift with a p-group, given by its lower central series.}

G := Codomain(SQP`SQ[1]);
keeporder := IsPureOrder(G);
flag, SQR := SQProcNextSection (SQP, p, true, false, true, true, keeporder,
ModuleList: semisimple := true, tr_ext := TrivialTails) ;

if flag eq false then
return false, _;
end if;

if Steps eq 1 then
return true, [* SQR *];
elif Steps gt 0 then
Steps -:= 1;
end if;

SQseq := [SQP, SQR];
PrintQuotient(SQR: Print := 0);
if ModuleList eq -1 then
ModuleList := 0;
end if;
while flag eq true and Steps ne 0 do
tr_ext := TrivialTails cat KeepPGroupWeights(SQseq);
if keeporder eq true then
tr_ext cat:= KeepPrimePower(SQR, p);
end if;
Gepi := SQProcImageEpi(SQP, SQR);
NonsplitCollector(SQR, p, tr_ext, [], Gepi);
flag, SQR := SQProcNextSection (SQR, p, false, true, true, true, false,
ModuleList:
semisimple := true, tr_ext := tr_ext, keepCollector := [true, true]) ;
if flag eq true then
Append(~SQseq, SQR);
end if;
Steps -:= 1;
end while;

return true, SQseq[#SQseq];
end intrinsic;

intrinsic NilpotentSection(SQP::SQProc: PrimeCalc := true, ModuleList := -1, TrivialTails := [], Steps := -1) -> BoolElt, SQProc
{Determine the maximal nilpotent group with a lift to a bigger quotient.
If PrimeCalc equals true, the relevant primes will be calculated first.
If ModuleList is 0, only the known modules will be taken into account.
Steps puts a limit on the weights of the p-groups of the nilpotent group.}

if PrimeCalc eq true then
Primes(SQP);
end if;

PP := SQP`Data[2];
SQseq := [* *];
for p in PP do
f, SQR := PGroupSection(SQP, p:
ModuleList := ModuleList, TrivialTails := TrivialTails, Steps := Steps);
if f eq true then
Append(~SQseq, <p, SQR>);
end if;
end for;

// First version: Just take the intersection of the kernels, do not attempt
// do save more than the basic information.
case #SQseq:
when 0:
return false, _;
when 1:
return true, SQseq[1,2];
else:
SQR := SQseq[1,2];
for i := 2to #SQseq do
tmp, SQR := ComposeQuotients(SQP, SQR, SQseq[i,2]: Check := false);
end for;
return true, SQR;
end case;

end intrinsic;


/*
These SolubleQuotient functions are completely duplicated below as
SolvableQuotient -- if you change one, fix the other.

That's not needed, since SolubleQuotient and SolvableQuotient are
defined to be identical in bind/s.b -- DR 2 nov 2010.
*/

intrinsic SolubleQuotient(F::GrpFP : NilpotencyClass := 0,
RatRepDegreeLimit := 0, SQTimeLimit:=0, QuotientSize:=0,
LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 2)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

EE, c := SolubleQuotientProcess(F: Print := Print, SQ_series := 1,
  RatRepDegreeLimit:=RatRepDegreeLimit, SQTimeLimit:=SQTimeLimit,
  SQ_PrimeSearchModus:=MSQ_PrimeSearchModus, SubSeriesLength:=LCSlimit,
  SQ_ModulCalcModus:=MSQ_ModulCalcModus, QuotientSize:=QuotientSize,
  SQ_CollectorModus := MSQ_CollectorModus, SeriesLength:=NilpotencyClass,
  SectionSize:=0);

Q := Codomain(EE`SQ[1]);
epi := EE`SQ[1];
e := hom<F->Q|[F.i@epi:i in [1..Ngens(F)]]>; /* this gives preimages */
w := EE`Series[2];
DeleteProcess(~EE);
comment := Message_SQ_return_comment(c);
return Q, e, w, comment;
end intrinsic;


intrinsic SolubleQuotient(F::GrpFP, n::RngIntElt : NilpotencyClass := 0,
RatRepDegreeLimit := 0, SQTimeLimit:=0, QuotientSize:=0,
LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 2)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

EE, c := SolubleQuotientProcess(F, n: Print := Print, SQ_series := 1,
  RatRepDegreeLimit:=RatRepDegreeLimit, SQTimeLimit:=SQTimeLimit,
  SQ_PrimeSearchModus:=MSQ_PrimeSearchModus, QuotientSize:=QuotientSize,
  SQ_ModulCalcModus:=MSQ_ModulCalcModus, SeriesLength:=NilpotencyClass,
  SQ_CollectorModus := MSQ_CollectorModus, SubSeriesLength:=LCSlimit,
  SectionSize:=0);

Q := Codomain(EE`SQ[1]);
epi := EE`SQ[1];
e := hom<F->Q|[F.i@epi:i in [1..Ngens(F)]]>; /* this gives preimages */
w := EE`Series[2];
DeleteProcess(~EE);
comment := Message_SQ_return_comment(c);
return Q, e, w, comment;
end intrinsic;



intrinsic SolubleQuotient(F::GrpFP, S::SetEnum : NilpotencyClass := 0,
RatRepDegreeLimit := 0, SQTimeLimit:=0, QuotientSize:=0,
LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 2)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

EE, c := SolubleQuotientProcess(F, S: Print := Print, SQ_series := 1,
RatRepDegreeLimit:=RatRepDegreeLimit, SQTimeLimit:=SQTimeLimit,
SQ_PrimeSearchModus:=MSQ_PrimeSearchModus, QuotientSize:=QuotientSize,
  SQ_ModulCalcModus:=MSQ_ModulCalcModus, SeriesLength:=NilpotencyClass,
SQ_CollectorModus := MSQ_CollectorModus, SubSeriesLength:=LCSlimit,
SectionSize:=0);

Q := Codomain(EE`SQ[1]);
epi := EE`SQ[1];
e := hom<F->Q|[F.i@epi:i in [1..Ngens(F)]]>; /* this gives preimages */
w := EE`Series[2];
DeleteProcess(~EE);
comment := Message_SQ_return_comment(c);
return Q, e, w, comment;
end intrinsic;


/*
intrinsic SolubleQuotient(F::GrpFP, S::SeqEnum : NilpotencyClass := 0,
RatRepDegreeLimit := 0, SQTimeLimit:=0, QuotientSize:=0,
LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 2)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

EE, c := SolubleQuotientProcess(F, S: Print := Print, SQ_series := 1,
RatRepDegreeLimit:=RatRepDegreeLimit, SQTimeLimit:=SQTimeLimit,
SQ_PrimeSearchModus:=MSQ_PrimeSearchModus, QuotientSize:=QuotientSize,
SQ_ModulCalcModus:=MSQ_ModulCalcModus, SeriesLength:=NilpotencyClass,
SQ_CollectorModus := MSQ_CollectorModus, SubSeriesLength:=LCSlimit,
SectionSize:=0);

Q := Codomain(EE`SQ[1]);
epi := EE`SQ[1];
e := hom<F->Q|[F.i@epi:i in [1..Ngens(F)]]>; // this gives preimages
w := EE`Series[2];
DeleteProcess(~EE);
comment := Message_SQ_return_comment(c);
return Q, e, w, comment;
end intrinsic;
*/



