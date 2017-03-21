freeze;

/* Herbert's stuff */
/* Intrinsic of general interest: Convert a representaion into a GModule
 * (this is the inverse function to Representation(Module M)
 */

intrinsic GModule(D::Map) -> ModGrp
{Return the G module M corresponding to the representation D.}

G := Domain(D);
S := [D(G.i) : i in [1 .. Ngens(G)]];
M := GModule(G, S);

return M;
end intrinsic;

/* 
 * Determination of Characters corresponding to representations.
 * The different version take the different types (represention, module and
 * internal form) into account.
 */

intCond := Conductor;   

intrinsic MakeCyclotomic(L::[FldAlgElt]:Sparse := false, Conductor := 0) -> []
{Given algebraic numbers known to lie in a cyclotomic field, change the
universe of the sequence to be cyclotomic.}

    K := Universe(L);
    Q := Rationals();
    if forall{x : x in L | x in Q} then
    return ChangeUniverse(ChangeUniverse(L, Q), 
	CyclotomicField(1:Sparse := Sparse));
    elif Type(K) eq FldCyc then
	return L;
    elif Type(K) eq FldQuad then
	c := intCond(K);
	K := CyclotomicField(c:Sparse := Sparse);
	return ChangeUniverse(L, K);
    end if;

    // general case, difficult...
    if not IsAbsoluteField(K) then
	K := AbsoluteField(K);
	ChangeUniverse(~L, K);
    end if;
    k := sub<K|L>;
    assert Degree(k) gt 1; // we caught Q earlier!!!
    assert IsAbelian(k);
    if Conductor eq 0 then
	c := Minimum(intCond(MaximalAbelianSubfield(k)));
    else 
	c := Conductor;
    end if;
    C := CyclotomicField(c:Sparse := Sparse);

    l, LC  := CanChangeUniverse(L, C);
//"C:", C; "New TES(C):"; TES(C); "Can change:", l; "C!w:", C!K.1;
    if l then
	return LC;
    end if;
    fl := IsSubfield(k, C);
    assert fl;
    ChangeUniverse(~L, k);
    return ChangeUniverse(L, C);
end intrinsic;

intrinsic CharacterFromTraces(RG::AlgChtr, CC::[RngElt]) -> AlgChtrElt
{Create the character in RG corresponding to the given traces in CC.
(Note: CC must describe a group character; no checking is done.)}

    try 
      // the easy case: it just works...
      C := RG ! CC;
    catch e
      CC := MakeCyclotomic(CC);
      C := RG ! CC;
    end try;

    AssertAttribute(C, "IsCharacter", true);
    return C;
end intrinsic;

intrinsic Character(D::Map) -> AlgChtrElt
{Create the character corresponding to the given representation D.}

    G := Domain(D);
    RG := CharacterRing(G);
    CG := ConjugacyClasses(G);

    CC := [Trace(D(x[3])) : x in CG]; 
    if Type(G) eq GrpMat and Type(BaseRing(G)) eq AlgQuat then
	CC := [Trace(x) : x in CC];
    end if;
    return CharacterFromTraces(RG, CC); //, CC;

end intrinsic;

intrinsic Character(P::RngIntElt) -> AlgChtrElt
{Create the character corresponding to the current representation specified 
by the process P}

GG, i := AbsolutelyIrreducibleRepresentationsProcessGroup(P);
SG := CompositionSeries(GG);
G  := SG[NPCgens(GG)+1-i];
RG := CharacterRing(G);
CG := ConjugacyClasses(G);

CC := [Trace(AbsolutelyIrreducibleRepresentationsApply(P, GG!x[3])) : x in CG];
C := RG ! CC;
AssertAttribute(C, "IsCharacter", true);

return C;
end intrinsic;

intrinsic Character(M::ModGrp) -> AlgChtrElt
{Create the character corresponding to the given G-module M.}
  if assigned M`Character then
    return M`Character;
  end if;

  D := Representation(M);
  C := Character(D);
  M`Character := C;
  return C;
end intrinsic;

/* 
 * July 23, 2000:  Definition of Process Type for representations of soluble
 *                 groups. In the first version, the setup of a process
 *                 include:
 *                 - Storing the composition series of G and determine the
 *                   biggest abelian subgroup in this series.
 *                 - Find the linear representations of this group with respect
 *                   to the given characteristics.
 *                 - proceed a step/by step orbit calculation of these reps.
 *                 - Initialize a loop over all representations.
 *
 * Attributes associated to the process type:
 * the Attributes themselves are tuples or lists agein, the index in brackets
 * refers to the i-th element.
 *
 * StartArgs:  Tuple that keeps the basic args from Init:
 *             [1]: Composition Series SG of the given soluble group
 *             [2]: the base field F
 *             [3]: The value of the optional arg GaloisAction
 *             [4]: The value of the optional arg DoneRemove
 *             [5]: Boolean, if true then absolutely irreducibles are the aim
 *
 * AbelLinReps: Data mainly needed for the first (abelian) step
 *              If the Group is small (immediate calculation), then 
 *              AbelLinReps = <[1]>. Otherwise:
 *             [1]: Sequence of integers, giving the indices of normal subgroups
 *                  in the composition series. The first entry refers to the
 *                  maximal abelian normal subgroup A in SG. The sequence
 *                  is chosen s.t. the minimum step between two indices is 2.
 *             [2]: the exponent r of the maximal abelian normal subgroup.
 *             [3]: List of lists of group generators, the i-th list holds the
 *                  generators with non/trivial action on the i-th normal
 *                  subgroup (defined by [1])
 *             [4]: The Ring R=Integers(r), r from [2].
 *             [5]: The Automorphisms of R which corresponds to Galois 
 *                  automorphisms of the extension field F[zeta_r]
 *             [6]; a list of matrices, describing the group action of G\A on
 *                  A (viewed as a module)
 *             [7]; the PCPrimes of G\A.
 * 
 * LoopPts:     List of pairs of lists, corresponding to the indices of the
 *              normal subgroups in SG. The first list in the pair holds the
 *              representations (in internal form) which needed to be performed.
 *              The second list is to keep the alreadz finished representations.
 *              If DoneRemove == true, the second list will be empty.
 * RepStack:    Pair of lists, keeping the representations of G which are ready
 *              to output.
 * Conditions:  keep the conditions for the representations.
 *             [1] maximal dimension: no limit ~ 0
 *             [2] set of integers, keeping the allowed exact dimensions.
 *             [3] list of sets of characters. The first entry the characters
 *                 of G which were initially given.
 *                 The other entries are the restrictions of these characters
 *                 to the normal subgroups of SG.
 *             [4] list of sets of kernel elements. The first entry is the
 *                 initial set, the following entries correspond to generators
 *                 of the intersection of the kernel with the normal subgroups.
 */

declare type SolRepProc;

declare attributes SolRepProc : StartArgs, AbelLinReps, LoopPts, RepStack, Conditions;


/* 
   the following functions deal with the internal form of the linear
   representations of an abelian group A. The linear representations are written
   as vectors in M = Module(A) with coefficient ring R = Integers(exp(A));
   We identify R with the exponents of a primitive exp(A)-root of unity in an
   suitable extension E of the input field.
   The functions simulate the galois action on E, the linear action of G\A on A,
   and the orbit algorithm on G\A on A.
*/

ExponentGaloisOrbit := function (L, K)

return { t* l  : t in K,  l in L}; 

end function;

// Help function: list the galois automorphisms, represented as powers
// of the r-th primitive root of unity.
// (char == 0: Return a set of all natural numbers 1..r-1 prime to r)

SetupGaloisAuts := function(r, p_char)

if p_char eq 0 then
	RU, phi := UnitGroup(Integers(r));
	K := {phi(k) : k in RU };
	return K;
end if;

d := 1;
while p_char^d mod r ne 1 do
	d +:= 1;
end while;

F := GF(p_char^d);
e := PrimitiveElement(F);
pe := MinimalPolynomial(e);
RU, phi := UnitGroup(Integers(r));
K  := {phi(k) : k in RU };
Kg := {i : i in K | MinimalPolynomial(e^(Integers()!i)) eq pe };

return Kg;

end function;

SetupActMatrices := function(G, k, RR)

// Help function: 
// G is a soluble group and S = <G.k .. G.n> is a normal subgroup of G in its 
// composition series. Describe the action G/S on S in terms of matrices: 
// The i-th row of the j-th matrix is the exponent vector of G.i^G.j (NF)
// P is the vector of the first k-1 elts of PCPrimes(G).

mats := [];
n := NPCgens(G);
pt := PCPrimes(G);
Pt := [pt[i] : i in [1..k-1]];
P := [];

MM := MatrixAlgebra(RR, n-k+1);
UM := MM!1;

for i := 1 to k-1 do
	matsi := [];
	for j := k to n do
		s := Eltseq(G.j^G.i);
		matsi cat:= [s[l] : l in [k..n] ];
	end for;
	mt := MM!matsi;
	if mt ne UM then
		Append(~mats, Transpose(mt));
		Append(~P, Pt[i]);
	end if;
end for;

return mats, P;
end function;

CalcOrbitNew := function(L, mm, P)

OO := {L};
d := #mm;

for i := 1 to d do
	OOT := {};
	MT := mm[i];
	for L in OO do
		LO := L * MT;
		if LO ne L then
			Include(~OOT, LO);
			for k := 2 to P[i] do
				LO := LO *MT;
				Include(~OOT, LO);
			end for;
		end if;
	end for;
	OO join:= OOT;
end for;
return OO;
end function;


CodeToRep := function(G,F, Lm, r)

// Convert the internal form of the representation of an abelian subgroup of G
// into an explicit representation (map)

L := [Integers()!t : t in Eltseq(Lm)];
g := GCD(r, GCD(L));
rr := r div g; // the root I really need to represent in F

if Characteristic(F) eq 0 then
	if rr le 2 then
		K := F;
		a := K!(-1);
	else
		if F eq Rationals() then
			t := rr;
		else
			t := LCM((rr), CyclotomicOrder(F));
		end if;
		K := CyclotomicField(t);
		a := K.1^(t div rr);
	end if;
else
	p := Characteristic(F);
	d := Degree(F);
	while (p^d - 1) mod rr ne 0 do
		d +:= 1;
	end while;

	K := GF(p^d);
	a := PrimitiveElement(K)^((p^d-1) div rr);
end if;
GM := GL(1, K);
GMM := MatrixAlgebra(K, 1);

R := hom<G -> GM | [GM!(GMM!a^(e div g)) : e in L]>;

return R;
end function;

/* -------------------------------------------------------*\
 * Check functions for conditions on representations.
 * The suffix 'Code' indicates that the function can be applied
 * to the linear representations, coded as module elts.
\* -------------------------------------------------------*/

CheckConditionMaxdimCode := function(OT, conds)

if conds[1] ne 0 and #OT gt conds[1] then
	return false;
else
	return true;
end if;

end function;

CheckConditionkernelCode := function(OT, conds)

if #conds[4] ne 0 then
	ker := conds[4, 2];
	n := #ker[1];
	for L in OT do
		R := CoefficientRing(Parent(L));
		for t in ker do
			s := R!0;
			for i := 1 to n do
				s +:= L[i] * t[i];
			end for;
			if s ne R!0 then
				return false;
			end if;
		end for;
	end for;
end if;

return true;
end function;

CheckConditionkernelIntern := function(P, conds, nn)

if #conds[4] ne 0 then
	G, i := AbsolutelyIrreducibleRepresentationsProcessGroup(P);
	idG := AbsolutelyIrreducibleRepresentationsApply(P, Id(G));
	ker := conds[4, nn];
	for t in ker do
		if P(t) ne idG then
			return false;
		end if;
	end for;
end if;

return true;
end function;

CheckConditionkernel := function(D, conds, nn)

if #conds[4] ne 0 then
	ker := conds[4, nn];
	idG := Codomain(D)!1;
	for t in ker do
		if D(t) ne idG then
			return false;
		end if;
	end for;
end if;

return true;
end function;

CheckConditionCharacterCode := function(OT, conds)

    if #conds[3] ne 0 then
	Chars := conds[3,2];
	Lm := Min(OT);
	F := Rationals();
	G := Group(Parent(Random(Chars)));
	r := Characteristic(CoefficientRing(Parent(Lm)));
	D := CodeToRep(G,F, Lm, r);
	CD := Character(D);
	flag := false;
	for cc in Chars do
		if InnerProduct(CD, cc) ne 0 then
		// My fault? "CD in cc" not interpreted correctly.
			flag := true;
			break;
		end if;
	end for;
	return flag;
    end if;

    return true;
end function;

CheckConditionCharacter := function(D, conds, nn)
    if #conds[3] ne 0 /* and #conds[3] ge nn */ then
	Chars := conds[3,nn];
	if Type(D) eq List then
	    assert #D eq 1;
	    D := D[1];
	end if;
	CD := Character(D);
	flag := false;
	for cc in Chars do
	    if InnerProduct(Restriction(CD, Group(Parent(cc))), cc) ne 0  then
		flag := true;
		break;
	    end if;
	end for;
	return flag;
    end if;
    return true;
end function;

NextOrbitsMinimum := function(LL, mm, P, K, conds)

// Take the minimal element of LL and remove its orbit from LL.
// If maxdim > 0, repeat the step until orbit length <= maxdim is valid.
// The return are the minimal elt and the modified set LL.

max_dim := conds[1];
while #LL ne 0 do
	L := Min(LL);
	OT := CalcOrbitNew(L, mm, P);
	if CheckConditionMaxdimCode(OT, conds) eq false then	
		GO := ExponentGaloisOrbit(OT, K);
		LL diff:= GO;
		continue;
	end if;
	if CheckConditionkernelCode(OT, conds) eq false then	
		GO := ExponentGaloisOrbit(OT, K);
		LL diff:= GO;
		continue;
	end if;
	if CheckConditionCharacterCode(OT, conds) eq false then	
		LL diff:= OT;
		continue;
	end if;

	GO := ExponentGaloisOrbit(OT, K);
	LL diff:= GO;
	return L, LL;
end while;

return false, LL;
end function;

/* Initialization function for small groups: 
 * All representaions will be calculated in the beginning and stored in a list.
 */

SolRepProcInitImmediate := function (G, F, galois_action, max_dim, exact_dim, DoneRemove, abs_irr)

SRP := New(SolRepProc);

SG := CompositionSeries(G);

if max_dim ne 0 then
	if exact_dim ne {} then
		exact_dim := {j : j in exact_dim | j le max_dim};
		max_dim := Max(exact_dim);
	end if;
elif exact_dim ne {} then
	max_dim := Max(exact_dim);
end if;

SRP`StartArgs := <SG,F,galois_action,DoneRemove, abs_irr>;
SRP`Conditions := [* max_dim, exact_dim, [* *], [* *] *];
SRP`AbelLinReps := <[1]>;

if abs_irr eq true then
print "Absolutely immediate";
	D := AbsolutelyIrreducibleModulesSchur(G,F: MaxDimension := max_dim, 
		GaloisAction := galois_action, ExactDimension := exact_dim);
else
print "non-Absolutely immediate:";
	D := IrreducibleModulesSchur(G,F: MaxDimension := max_dim, 
		GaloisAction := galois_action, ExactDimension := exact_dim);
print "non-Absolutely immediate finished";
end if;

SRP`RepStack := <D, [* *]>;
return SRP;

end function;


SolRepProcInit := function (G, F, galois_action, DoneRemove, abs_irr)


    SG := CompositionSeries(G);

    nn := 1;
    while nn le #SG and IsAbelian(SG[nn]) eq false do
    nn +:= 1;
    end while;
    while nn le #SG and IsNormal(G, SG[nn]) eq false do
	nn +:= 1;
    end while;

    t := nn-2;
    if t le 0 then
	SRP := SolRepProcInitImmediate(
	    G, F, galois_action, -1, {}, DoneRemove, true);
	return SRP;
    end if;

    nnv := [nn];
    ggv := [* [1] *]; // Default value for first entry

    SRP := New(SolRepProc);
    SRP`StartArgs  := <SG,F,galois_action,DoneRemove, abs_irr>;
    SRP`Conditions := [* 0, {}, [* *], [* *] *];
    SRP`RepStack   := <[* *], [* *]>;

    while t gt 0 do
	while t gt 1 and IsNormal(G, SG[t]) eq false do
	    t -:= 1;
	end while;
	if t eq 2 then
	    Append(~nnv, 1);
	    t := 0;
	else
	    Append(~nnv, t);
	    t -:= 2;
	end if;
	n_new := nnv[#nnv];
	n_old := nnv[#nnv-1];
	ga := [1..n_new-1];
	gq := [SG[1].j : j in [n_new..NPCgens(SG[1])]];
	gi := [j : j in ga | [h^(SG[1].j) : h in gq] ne gq ];
	Append(~ggv, gi);
	
    end while;

    p_char := Characteristic(F);
    LL, r := LinearRepresentationSetup(SG[nn], p_char, false);
    if #LL gt 1 then
	R := Integers(r);
	K :=  SetupGaloisAuts(r, p_char);
    else
	R := Integers(p_char);
	K := {1};
    end if;	

    AM, P   := SetupActMatrices (G, nn, R);
    MM := RModule(R, #LL[1]);
    L := {MM!l : l in LL};
    SRP`AbelLinReps := <nnv, r, ggv, R, K, AM, P>;

    SRP`LoopPts := [* *];
    for i := 1 to nn-1 do
	SRP`LoopPts[i] := <[* *], [* *]>;
    end for;
    SRP`LoopPts[nn] := <L, [* *]>;
    if nn eq 1 then
	return SRP;
    end if;

    return SRP;
end function;

ExtendRepStep := function (SRP)

    nnv := SRP`AbelLinReps[1];
    r  := SRP`AbelLinReps[2];
    CS        := SRP`StartArgs[1];
    F         := SRP`StartArgs[2];
    Drm       := SRP`StartArgs[4];
    max_dim   := SRP`Conditions[1];
    exact_dim := SRP`Conditions[2];
    conds     := SRP`Conditions;

    i := #nnv;
    while i gt 0 do
	n := nnv[i];
	if #SRP`LoopPts[n,1] eq 0 then
	    i -:= 1;
	else
	    break;
	end if;
    end while;

    if i eq 0 then
	return false, _;
    else
	n_old := nnv[i];
	n_new := nnv[i+1];

	if i eq 1 then
	    R := SRP`AbelLinReps[4];
	    K := SRP`AbelLinReps[5];
	    A := SRP`AbelLinReps[6];
	    P := SRP`AbelLinReps[7];
	    ll, L := NextOrbitsMinimum(SRP`LoopPts[n,1], A, P, K, conds);
	    SRP`LoopPts[n,1] := L;
	    if Type(ll) eq BoolElt then
		    return false, _;
	    end if;
	    lr := CodeToRep(CS[n_old],F,  ll, r);
	    Dl := [* AbsIrrFromMap(lr) *];
	else
	    ll := SRP`LoopPts[n,1,1];
	    Remove(~SRP`LoopPts[n,1], 1);
	    Dl := [* ll *];
	end if;

	GT := CS[n_new];
	nc := NPCgens(GT);
	gi := SRP`AbelLinReps[3, i+1];

	D := AbsolutelyIrreducibleRepresentationsProcess(CS[1],F, Dl,nc:
		GaloisAction := "Yes", MaxDimension := max_dim);
	if exact_dim ne {} then
	    DT := [* *];
	    if n_new eq 1 then
		EE := exact_dim;
	    else
		EE := {};
		for ee in exact_dim do
		    EE cat:= {i : i in Divisors(ee)};
		end for;
	    end if;
	    for dd in D do
		if 
		    AbsolutelyIrreducibleRepresentationsProcessDegree(dd) in EE 
		then
		    Append(~DT, dd);
		else
		    AbsolutelyIrreducibleRepresentationsDelete(dd);
		end if;
	    end for;
	    D := DT;
	end if;

	if Drm eq true then
	    AbsolutelyIrreducibleRepresentationsDelete(~Dl);
	else
	    Append(~SRP`LoopPts[n,2], Dl[1]);
	end if;
		
	if #D le 1 or n_new eq 1 then // also valid if #D eq 0.
	    for dd in D do
		Append(~SRP`LoopPts[n_new,1], dd);
	    end for;
	    return true, #D;
	end if;

	DG := [* *];
	for j := 1 to #D do
	    Append(~DG, 
		AbsolutelyIrreducibleRepresentationsProcess(
		    CS[1],F,[* D[j] *], nc
	    ));
	end for;
	
	DF := [0: j in [1..#D]];
	Ddegs := [AbsolutelyIrreducibleRepresentationsProcessDegree(d): d in D];

	v, iv := Min(DF);
	ivz := 1;

	while v le 0 do 
	    Ddegj := [i : i in [1..#D ] | Ddegs[i] eq Ddegs[iv] and DF[i] eq 0];
	    if Ddegj ne [] then
		dd := D[iv];

		for gg in gi do
		    pV := AbsIrrApplyConjugation(CS[1], dd, gg);
		    for k in Ddegj do
			DT := DG[k];
			done_flag := false;
			for l := 1 to #DT do
			    f, m := IsEquivalent(DT[l], pV);
			    if f eq true then
				done_flag := true;
				break;
			    end if;
			end for;

			if done_flag eq true then
			    DF[k] := -ivz;
			    break;
			end if;
		    end for;
		    AbsolutelyIrreducibleRepresentationsDelete(pV);
		end for;
	    end if;

	    DF[iv] := ivz;
	    v, iv := Min(DF);
	    if ivz + v ne 0 then
		    ivz +:= 1;
	    end if;
	end while;


	DR := [* *];
	dlist := [];
	iv := 1;
	for j := 1 to #D do
	    if DF[j] eq iv then
		act_deg := AbsolutelyIrreducibleRepresentationsProcessDegree(D[j]);
		good_rep := true;
		if max_dim gt 0 then
		    TT := [x:x in [1..#D]|DF[x] eq iv];
		    if #TT*act_deg gt max_dim then
			good_rep := false;
		    else
			if #conds[4] ne 0 then
			    for x in TT do
				good_rep := CheckConditionkernelIntern 
						(D[x], conds, n_new);
				if good_rep eq false then
				    break;
				end if;
			    end for;
			end if;
		    end if;
		end if;
		if good_rep eq true and #conds[3] ne 0 then
		    tmp_flag := false;
		    for tt := 1 to #DG[j] do
/*
"D:", DG[tt];
"conds:", conds;
"n_new:", n_new;
*/
			tmp_flag := CheckConditionCharacter
					(DG[tt], conds, n_new);
			if tmp_flag eq true then
			    ts := DG[tt];
			    DG[tt] := D[j];
			    D[j] := ts;
			    break;
			end if;
		    end for;
		    good_rep := tmp_flag;
		end if;
		if good_rep eq true then			
		    Append(~DR, D[j]);
		    Append(~dlist, act_deg);
		else
		    AbsolutelyIrreducibleRepresentationsDelete(D[j]);
		end if;
		iv +:= 1;
	    else
		AbsolutelyIrreducibleRepresentationsDelete(D[j]);
	    end if;
	end for;

	for k :=1  to #DG do
	    if Type(DG[k]) eq RngIntElt then
		AbsolutelyIrreducibleRepresentationsDelete(DG[k]);
	    else
		AbsolutelyIrreducibleRepresentationsDelete(~DG[k]);
	    end if;
	end for;

	SRP`LoopPts[n_new,1] cat:= DR;
	return true, #DR;
    end if;

end function;

PrepareRepForOutput := function(SRP, as_module)

CS       := SRP`StartArgs[1,1];
F        := SRP`StartArgs[2];
galois   := SRP`StartArgs[3];
Drm      := SRP`StartArgs[4];
abs_irr  := SRP`StartArgs[5];
maxdim   := SRP`Conditions[1];
exactdim := SRP`Conditions[2];
r  := SRP`AbelLinReps[2];

nnv := SRP`AbelLinReps[1];
if nnv[1] eq 1 then // we have an abelian group
	ll := SRP`LoopPts[1,1,1];
	Remove(~SRP`LoopPts[1,1],1);
	if Drm eq false then
		Append(~SRP`LoopPts[1,2] , ll);
	end if;
	lr := CodeToRep(CS,F,  ll, r);
	Dl := [* AbsIrrFromMap(lr) *];
	D := AbsolutelyIrreducibleModulesSchur(CS,F, Dl: GaloisAction := galois,
			MaxDimension := maxdim, ExactDimension := exactdim);
	AbsolutelyIrreducibleRepresentationsDelete(~Dl);
	SRP`RepStack[1] cat:= D;

	return true;
end if;

DP := SRP`LoopPts[1,1];
SRP`LoopPts[1,1] := [* *];

if as_module eq true then
	if abs_irr eq true then
		DD := AbsolutelyIrreducibleModulesSchur(CS, F, DP: GaloisAction := galois, 
			MaxDimension := maxdim, ExactDimension := exactdim);
	else
		DD := IrreducibleModulesSchur(CS, F, DP: 
			MaxDimension := maxdim, ExactDimension := exactdim);
	end if;
else
	if abs_irr eq true then
		DD := AbsolutelyIrreducibleModulesSchur(CS, F, DP: 
			GaloisAction := galois, MaxDimension := maxdim, 
			ExactDimension := exactdim);
		conds := SRP`Conditions;
		if #conds[3] ne 0 and galois eq "No" then
			tt := 1;
			while tt le #DD do
				tmp_flag := CheckConditionCharacter (DD[tt], conds, 1);
				if tmp_flag eq true then
					tt +:= 1;
				else
					Remove(~DD, tt);
				end if;
			end while;
		end if;
	else
		DD := IrreducibleModulesSchur(CS, F, DP: 
			MaxDimension := maxdim, ExactDimension := exactdim);
	end if;
end if;
/* Type(SRP`RepStack[1]); Type(DD); */
SRP`RepStack[1] cat:= SequenceToList(DD);
if Drm eq false then
	SRP`LoopPts[1,2] cat:= DP;
else
	AbsolutelyIrreducibleRepresentationsDelete(~DP);
end if;

return true;
end function;

SRPCondition := function(SRP, MaxDimension, ExactDimension, Characters, KernelElements)
// set the conditions for the representations.
// the return is true iff a condition has been set.

flag := false;
if Type(Characters) ne RngIntElt then
	if Type(Characters) eq AlgChtrElt then
		SRP`Conditions[3] := [* {Characters} *];
		ct := Characters;
		max_limit := ct[1];
		CC := ConjugacyClasses(SRP`StartArgs[1,1]);
		flag := true;
	elif Type(Characters) eq SetEnum then
		SRP`Conditions[3] := [* Characters *];
		CC := ConjugacyClasses(SRP`StartArgs[1,1]);
		max_limit := Max({t[1] : t in Characters});
		flag := true;
	end if;
	nnv := SRP`AbelLinReps[1];
	for i := 1 to #nnv-1 do
		k := nnv[1];
		SG := SRP`StartArgs[1,k];
		RC := {Restriction(cc, SG) : cc in SRP`Conditions[3,1]};
		Append(~SRP`Conditions[3], RC);
	end for;
	max_limit := Integers()!max_limit;
	if MaxDimension ge 0 then
		MaxDimension := Min(MaxDimension, max_limit);
	else
		MaxDimension := max_limit;
	end if;
end if;

if MaxDimension ge 0 then
	flag := true;
	if ExactDimension ne {} then
		ExactDimension := {j : j in ExactDimension | j le MaxDimension};
		SRP`Conditions[1] := Max(ExactDimension);
		SRP`Conditions[2] := ExactDimension;
	end if;
	SRP`Conditions[1] := MaxDimension;
elif ExactDimension ne {} then
	flag := true;
	SRP`Conditions[1] := Max(ExactDimension);
	SRP`Conditions[2] := ExactDimension;
end if;


if Type(KernelElements) ne RngIntElt then
	flag := true;
	if Type(KernelElements) eq SetEnum then
		SRP`Conditions[4] := [* KernelElements *];
	elif Type(KernelElements) eq GrpPCElt then
		SRP`Conditions[4] := [* {KernelElements} *];
	elif Type(KernelElements) eq SeqEnum then
		SRP`Conditions[4] := [* Seqset(KernelElements) *];
	end if;
	N, iota := ncl<SRP`StartArgs[1,1] | KernelElements>;
	w := {iota(g) : g in PCGenerators(N)};
	if #SRP`AbelLinReps ne 1 then // else "Immediate" is used
		I := SRP`AbelLinReps[1];
		for i := 1 to #I do
			SG := SRP`StartArgs[1, I[i]];
			ww := {t : t in w | t in SG};
				if i eq 1 then
					if #ww eq 0 then
					Append(~SRP`Conditions[4], ww);
				else
					tt := [Eltseq(d) : d in ww];
					nn := SRP`AbelLinReps[1,1];
					MM := Parent(Min(SRP`LoopPts[nn,1])); 
					R := CoefficientRing(MM); 
					ttnn := [[R!t[i] : i in [nn..#tt[1]]] : t in tt]; 
					Append(~SRP`Conditions[4], ttnn);
				end if;
			else
				Append(~SRP`Conditions[4], ww);
			end if;
			w diff:= ww;
		end for;
		end if;
end if;

return flag;
end function;


intrinsic AbsolutelyIrreducibleRepresentationsInit (G::GrpPC, F::FldRat :
    MaxDimension:= -1, ExactDimension:={}, Characters:= 0, KernelElements:= 0, 
	GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
 group G for the rational field F.}

    if #G le 1000 and Type(Characters) eq RngIntElt 
		  and Type(KernelElements) eq RngIntElt 
    then
	SRP := SolRepProcInitImmediate(G, F, GaloisAction, MaxDimension, 
		ExactDimension, DoneRemove, true);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, GaloisAction, DoneRemove, true);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic AbsolutelyIrreducibleRepresentationsInit (G::GrpPC, F::FldFin:
	MaxDimension:= -1, ExactDimension:={}, KernelElements:= 0, 
	    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
     group G for the rational field F.}

    Characters := 0; // to define in prime case
    if #G le 1000 and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, GaloisAction, MaxDimension, 
		ExactDimension, DoneRemove, true);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, GaloisAction, DoneRemove, true);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic AbsolutelyIrreducibleModulesInit (G::GrpPC, F::FldRat :
    MaxDimension:= -1, ExactDimension:={}, Characters:= 0, KernelElements:= 0, 
	GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
 group G for the finite field F.}

    if #G le 1000 and Type(Characters) eq RngIntElt 
		  and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, GaloisAction, MaxDimension, 
		ExactDimension, DoneRemove, true);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, GaloisAction, DoneRemove, true);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic AbsolutelyIrreducibleModulesInit (G::GrpPC, F::FldFin :
    MaxDimension:= -1, ExactDimension:={}, KernelElements:= 0, 
    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
group G for the finite field F.}

    Characters := 0; // to define in prime case
    if #G le 1000 and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, GaloisAction, MaxDimension, 
		ExactDimension, DoneRemove, true);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, GaloisAction, DoneRemove, true);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic IrreducibleRepresentationsInit (G::GrpPC, F::FldRat : 
    MaxDimension:= -1, ExactDimension:={}, Characters:= 0, KernelElements:= 0, 
    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
 group G for the rational field F.}

    if #G le 1000 and Type(Characters) eq RngIntElt 
	      and Type(KernelElements) eq RngIntElt then
//print "Immediate";
	SRP := SolRepProcInitImmediate (G, F, "Yes", MaxDimension, 
		    ExactDimension, DoneRemove, false);
    else
//print "Immediate denied";
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, "Yes", DoneRemove, false);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic IrreducibleRepresentationsInit (G::GrpPC, F::FldFin : 
    MaxDimension:= -1, ExactDimension:={}, KernelElements:= 0, 
    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
group G for the rational field F.}

    Characters := 0;
    if #G le 1000 and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, "Yes", MaxDimension, 
		ExactDimension, DoneRemove, false);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, "Yes", DoneRemove, false);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic IrreducibleModulesInit (G::GrpPC, F::FldRat : 
    MaxDimension:= -1, ExactDimension:={}, Characters:= 0, KernelElements:= 0, 
    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
group G for the finite field F.}

    if #G le 1000 and Type(Characters) eq RngIntElt 
	      and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, "Yes", MaxDimension, 
		ExactDimension, DoneRemove, false);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, "Yes", DoneRemove, false);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic IrreducibleModulesInit (G::GrpPC, F::FldFin : 
    MaxDimension:= -1, ExactDimension:={}, KernelElements:= 0, 
    GaloisAction := "No", DoneRemove := true) -> SolRepProc
{Initialize a Process for calculating all linear representations of a soluble
group G for the finite field F.}

    Characters := 0;
    if #G le 1000 and Type(KernelElements) eq RngIntElt then
	SRP := SolRepProcInitImmediate (G, F, "Yes", MaxDimension, 
		ExactDimension, DoneRemove, false);
    else
	GG := ConditionedGroup(G);
	SRP := SolRepProcInit(GG, F, "Yes", DoneRemove, false);
	if not (Characters cmpeq 0) then
	    if Type(Characters) eq SetEnum then
		Characters := {Restriction(x, GG):x in Characters};
	    else
		Characters := Restriction(Characters, GG);
	    end if;
	end if;
	flag := SRPCondition(SRP, 
	    MaxDimension, ExactDimension, Characters, KernelElements);
    end if;

    return SRP;
end intrinsic;

intrinsic NextRepresentation (SRP::SolRepProc) -> BoolElt, Map

{Return the next representation  or false if no further exist.}

Drm := SRP`StartArgs[4];
if #SRP`RepStack[1] ne 0 then
	D := SRP`RepStack[1,1];
	Remove(~SRP`RepStack[1], 1);
	if Drm eq false then
		Append(~SRP`RepStack[2], D);
	end if;
	if Type(D) eq ModGrp then
		return true, Representation(D);
	else
		return true, D;
	end if;
elif assigned(SRP`LoopPts) eq false then
	return false, _;
end if;

while #SRP`LoopPts[1,1] eq 0 do
	f, nD := ExtendRepStep (SRP);
	if f eq false then
		return false, _;
	end if;
end while;

f := PrepareRepForOutput(SRP, false);
D := SRP`RepStack[1,1];
Remove(~SRP`RepStack[1], 1);
if Drm eq false then
	Append(~SRP`RepStack[2], D);
end if;

return true, D;

end intrinsic;

intrinsic NextModule (SRP::SolRepProc) -> BoolElt, Map

{Return the next representation  or false if no further exist.}

Drm := SRP`StartArgs[4];
if #SRP`RepStack[1] ne 0 then
	D := SRP`RepStack[1,1];
	if Drm eq false then
		Append(~SRP`RepStack[2], D);
	end if;
	Remove(~SRP`RepStack[1], 1);
	if Type(D) eq Map then
		return true, GModule(D);
	else
		return true, D;
	end if;

elif assigned(SRP`LoopPts) eq false then
	return false, _, _, _, _;
end if;

while #SRP`LoopPts[1,1] eq 0 do
	f, nD := ExtendRepStep (SRP);
	if f eq false then
		return false, _;
	end if;
end while;

f := PrepareRepForOutput(SRP, true);
D := SRP`RepStack[1,1];
if Drm eq false then
	Append(~SRP`RepStack[2], D);
end if;
Remove(~SRP`RepStack[1], 1);

return true, D;

end intrinsic;

intrinsic AbsolutelyIrreducibleRepresentationProcessDelete(~SRP::SolRepProc)
{Free all data of the representation Process type.}

SRP`StartArgs   := 0;
SRP`Conditions  := 0;
nnv := SRP`AbelLinReps[1];
SRP`AbelLinReps := 0;
SRP`RepStack := 0;

for i := 2 to #nnv do
	if #SRP`LoopPts[i,1] ne 0 then
		AbsolutelyIrreducibleRepresentationsDelete(~(SRP`LoopPts[i,1]));
	end if;
	if #SRP`LoopPts[i,2] ne 0 then
		AbsolutelyIrreducibleRepresentationsDelete(~(SRP`LoopPts[i,2]));
	end if;
end for;
SRP`LoopPts := 0;

end intrinsic;

intrinsic Representations(cc::AlgChtrElt) -> List, BoolElt
{Return a list of absolutely irreducible representations which corresponds to
the constituents of the character cc. Each list element is a tuple <D, m>, 
with D the representation and m the multiplicity of D as constituent of cc.
The second argument is a control flag, it is true iff cc equals the sum over D.
The group of the character cc must be solvable.}

    CP := Parent(cc);
    G := Group(CP);

    if Type(G) ne GrpPC then
      require IsSolvable(G) : "Group of character must be solvable";
      P, onto_P := PCGroup(G);
      RP := CharacterRing(P);
      clP := Classes(P);
      ccP := RP![c[3] @@ onto_P @ cc: c in clP];
      L, flag := Representations(ccP);
      LL := [* *];
      for i := 1 to #L do
          t := L[i];
          if Type(t[1]) eq ModGrp then
              rho := Representation(t[1]);
              Append(~LL, <Representation(GModule(G, [(G.i)@onto_P@rho:i in [1..Ngens(G)]])), t[2]>);
          else
              Append(~LL, <onto_P*t[1], t[2]>);
          end if;
      end for;
      return LL, flag;
    end if;

    /*
    G := ConditionedGroup(G);
    ccG := Restriction(cc, G);
    */
    SRP := AbsolutelyIrreducibleRepresentationsInit(G,Rationals(): 
		Characters := cc);
    flag := true;
    success_flag := false;
    D := [* *];
    while flag eq true do
	flag, dd := NextRepresentation(SRP);
	if flag eq false then
	    break;
	end if;
	dc := Character(dd);

	ccG := Restriction(cc, Group(Parent(dc)));
	m := InnerProduct(ccG, dc);
	if m ne 0 then
	    td := <dd, m>;
	    print td, #D;
		Append(~D, td);
	    ccG -:= m* dc;
	    if IsZero(ccG) then
		success_flag := true;
		break;
	    end if;
	end if;
    end while;

    AbsolutelyIrreducibleRepresentationProcessDelete(~SRP);

    return D, success_flag;
end intrinsic;

intrinsic Characters (G::GrpPC: MaxDimension:= -1, 
	ExactDimension:={}, KernelElements:= 0, GaloisAction := "No") -> List
{Calculate a list of all irreducible Characters of a soluble Group G (with 
respect to conditions defined by the optional parameters.}

    SRP := AbsolutelyIrreducibleRepresentationsInit(G, Rationals(): 
	GaloisAction := "Yes",            MaxDimension := MaxDimension, 
	ExactDimension := ExactDimension, KernelElements := KernelElements); 

    CA := CharacterRing(G);
    CG := ConjugacyClasses(G);
    D := [* *];
    flag := true; 
    while flag eq true do   
	flag, dd := NextRepresentation(SRP);
	if flag eq false then
	    break;
	end if;

	S := [Trace(dd(cc[3])) : cc in CG];
	cs := CA!S; 
	K := CoefficientRing(Codomain(dd));
	if Type(K) eq FldRat or GaloisAction eq "Yes" then
	    Append(~D, cs);
	    continue;
	end if;

	r := CyclotomicOrder(K);
	U := [i : i in [1..r-1] | GCD(i,r) eq 1 ];
	DT := {GaloisConjugate(cs, j) : j in U};
	for d in DT do
	    Append(~D, d);
	end for;
    end while;

    AbsolutelyIrreducibleRepresentationProcessDelete(~SRP);

    return D;
end intrinsic;

