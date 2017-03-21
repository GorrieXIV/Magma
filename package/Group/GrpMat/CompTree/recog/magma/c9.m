/******************************************************************************
 *
 *    c9.m      Composition Tree Almost Simple Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-16
 *
 *    Version   : $Revision:: 2928                                           $:
 *    Date      : $Date:: 2014-12-06 15:55:43 +1100 (Sat, 06 Dec 2014)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: c9.m 2928 2014-12-06 04:55:43Z eobr007                         $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "recog.m" : ActionMapsInfo, NodeTypes, LeafInfo;
import "mathom.m" : AschbacherErrors, AschbacherError, ReductionWithScalar;
import "sporadic.m" : SporadicAlmostSimple;
import "defrepdata.m" : MaximumStableDerivativeIndex;
import "centre.m" : C9Centre;

import "../../GrpMat/lie/identify.m" : RecogniseSporadic;

// Number of random elements in stable derivative calculation
StableDerivativeElts := 10;

// Number of random elements in normal subgroup membership testing
NormalSubgroupElements := 100;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function PerfectCheckElements(G)
    if Category(G) eq GrpMat then
	return Maximum(NormalSubgroupElements, 2 * Degree (G));
    else
	return NormalSubgroupElements;
    end if;
end function;

function StableDerivative(G, slps : NumberRandom := StableDerivativeElts,
	Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
	ClosureErrorProb := 2^(-2), SubgroupChainLength := 5,
	MaxSteps := 3, SimpleGenerators := 5)

    steps := 0;
    while not IsProbablyPerfect(G : NumberRandom := PerfectCheckElements(G)) do
	// If we have computed 3 derived groups and we still don't have
	// a perfect group, then the original group cannot be almost simple
	if steps ge MaxSteps then
	    return false, _, _, _;
	end if;
	
	H_elts := [Generic(G) | ];
	H_slps := [];
	
	vprint CompositionTree, 6 :
	    "Obtain normal generators for derived group";
	for i in [1 .. NumberRandom] do
	    g, g_slp := Random(Randomiser);
	    h, h_slp := Random(Randomiser);
	    
	    Append(~H_elts, (g, h));
	    Append(~H_slps, (g_slp, h_slp));
	end for;
	
	H := sub<Generic(G) | H_elts>;
	genMap := [Index(H_elts, g) : g in UserGenerators(H)];
	H_slps := Evaluate(H_slps[genMap], slps);
	
	vprint CompositionTree, 6 : "Take normal closure";
	G, slps := NormalClosureMonteCarlo(G, H, slps, H_slps :
	    ErrorProb := ClosureErrorProb,
	    SubgroupChainLength := SubgroupChainLength);	
	Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G));

	if not IsTrivial(G) then
	    vprint CompositionTree, 6 : "Reduce number of generators";
	    
	    // The group is almost simple, so it has a small generating set
	    G_gens := [Generic(G) | ];
	    G_slps := [];
	    for i in [1 .. SimpleGenerators] do
		g, g_slp := Random(Randomiser);
		
		Append(~G_gens, g);
		Append(~G_slps, g_slp);
	    end for;
	    
	    G := sub<Generic(G) | G_gens>;
	    genMap := [Index(G_gens, g) : g in UserGenerators(G)];
	    slps := Evaluate(G_slps[genMap], slps);
	    Randomiser :=
		RandomProcessWithWords(G : WordGroup := WordGroup(G));
	end if;
	
	vprint CompositionTree, 6 : "Test for perfectness";
	steps +:= 1;
	SubgroupChainLength := Max(1, SubgroupChainLength - 1);
    end while;

    return true, G, slps, Randomiser;
end function;

/* decide if G/Z is Tits group */
function IsTitsGroup(G : Orders := [], NmrTries := 200)
    if #Orders eq 0 then 
	E := [Random(G) : i in [1 .. NmrTries]];
	orders := [CentralOrder(e) : e in E];
    else
	orders := Orders;
    end if;
 
  maxords := {i : i in orders | #{j: j in orders | j mod i eq 0} eq 1};
  if maxords eq {10, 12, 13, 16} then
      flag, X := StandardGenerators(G, "TF42" : Projective := true);
      if flag then
	  return true;
      end if;
  end if;
  
  return false;
end function;

AltSymNaming := function (G : NumberRandom := 500)
    center := C9Centre(G);
    ext := not IsTrivial(center);
  
    vprint CompositionTree, 4 : "Guess Alt degree, ext = ", ext;
    flag, name, degree :=
	GuessAltsymDegree(G : Extension := ext, mintries := NumberRandom);
    
    if flag and name eq "Alternating" then
	// Group should be simple modulo scalars at this stage
	vprint CompositionTree, 4 :
	    "Possible Alt, verify", name, degree;

        // EOB addition to deal with easy/a7 example
        // which otherwise is incorrectly identified as Sp(4, 13)
	if degree le 8 then 
           if Type (G) eq GrpMat then 
              flag := RandomSchreierBounded (G, 20160);
           else 
              RandomSchreier (G); flag := true;
           end if;
           if flag and (#center * Factorial (degree) div 2) mod #G eq 0 then 
              vprint CompositionTree, 4 : "Verified group is Alt ", degree;
              return true, [* <17, degree, ext> *]; 
           else
              return false, _;
           end if;
 	end if;

	if degree ge 9 then
	    if ext then
		flag := C9RecogniseAlternating(G, degree :
		    maxtries := 2 * NumberRandom);
	    else
		flag := RecogniseAlternating(G, degree :
		    Extension := false, maxtries := 2 * NumberRandom);
	    end if;
	    
	    if flag then 
                vprint CompositionTree, 4 : "Verifed group is Alt ", degree;
		return true, [* <17, degree, ext> *];
	    else 
		return false, _;
	    end if;
	else
	    return false, _;
	end if;
    end if;
  
    return false, _;
end function;

function SporadicNaming(G : NumberRandom := 500,
    Randomiser := RandomProcess(G))

    NumberRandom := Maximum (NumberRandom, 500);

    vprint CompositionTree, 4 : "Obtain random element batch";
    orders := {CentralOrder(Random(Randomiser)) :
	i in [1 .. NumberRandom]};

    if IsTitsGroup(G : Orders := orders, NmrTries := NumberRandom) then
       return true, [* <18, 0, "TF42"> *];
    end if;

    vprint CompositionTree, 4 : "Check for sporadics";
    names := RecogniseSporadic(orders);

    if #names gt 0 then
	vprint CompositionTree, 4 : "Possible sporadic, verify:", names;

	for name in names do
	    if StandardGenerators(G, name[3] : Projective := true) then
		return true, [* name *];
	    end if;
	end for;
    end if;

    return false, _;
end function;

function AlmostSimpleCheck(node)
    try
	vprint CompositionTree, 3 : "Find stable derivative";
        flag, derivate, derivateSLPs, Randomiser :=
	    StableDerivative(node`Group, UserGenerators(node`WordGroup) :
	    Randomiser := node`RandomProcess,
	    SubgroupChainLength := node`SubgroupChainLength);

	vprint CompositionTree, 3 : "Stable derivative found";
	
	if not flag or IsTrivial(derivate) then
	    return false, _;
	end if;

	flag, names := AltSymNaming(derivate :
	NumberRandom := Maximum (node`NamingElements, 10 * Degree(derivate)));
    
        if flag then
	    return flag, [names, [* derivate, derivateSLPs, Randomiser *]];
	end if;

	vprint CompositionTree, 3 : "Check for sporadics";
	flag, names := SporadicNaming(derivate :
	    NumberRandom := node`NamingElements, Randomiser := Randomiser);
    
        if flag then
	    return flag, [names, [* derivate, derivateSLPs, Randomiser *]];
	end if;
	
	vprint CompositionTree, 3 : "Find Lie characteristic";
	char := LieCharacteristic(derivate : Verify := false, 
	    NumberRandom := node`NamingElements);
        vprint CompositionTree, 4 : "Lie characteristic done";
	if char cmpeq false then
	    return false, _;
	end if;
	
	vprint CompositionTree, 3 : "Find Lie type";
	flag, names := LieType(derivate, char :
	    NumberRandom := node`NamingElements);

	if flag then
	    return flag, [[* names *],
		[* derivate, derivateSLPs, Randomiser *]];
	else
	    return flag, _;
	end if;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`almostsimple, Error := err>);        
    end try;
end function;

// Monte Carlo algorithm that determines if g is in the normal subgroup N of G
// A positive answer is always correct
function ElementInNormalSubgroup(G, N, g : order := CentralOrder,
    NumberRandom := NormalSubgroupElements, Randomiser := RandomProcess(N))

    if order eq CentralOrder then 
       m := CentralOrder(g : ParentGroup := G);
    else 
       m := Order (g);
    end if;
    
    for i in [1 .. NumberRandom] do
	a := Random(Randomiser);
        if order eq CentralOrder then 
           o := CentralOrder(a * g : ParentGroup := G);
        else 
           o := Order (a * g);
        end if;
        m := Gcd (m, o);
	if m eq 1 then 
	    return true;
	end if;
    end for;

    return false;
end function;

// Monte Carlo algorithm that constructs coset reps of the normal subgroup N
function ConstructCosets(G, N : order := CentralOrder,
    MaxCosets := 0, NumberRandom := NormalSubgroupElements,
    Randomiser := RandomProcess(N))

    cosetReps := [Identity(G)];
    t := 1;

    while t le #cosetReps do
	x := cosetReps[t];

	for i in [1 .. NumberOfGenerators(G)] do
	    g := x * G.i;
	    
	    if forall{o : o in cosetReps |
		not ElementInNormalSubgroup(G, N, o / g : order := order,
		NumberRandom := NumberRandom, Randomiser := Randomiser)} then
		Append(~cosetReps, g);

		if #cosetReps ge MaxCosets and MaxCosets gt 0 then
		    return cosetReps;
		end if;
	    end if;
	end for;
	
	t +:= 1;
    end while;

    return cosetReps;
end function;

function AlmostSimpleImage(G, N, reps, g : order := CentralOrder,
    NumberRandom := NormalSubgroupElements, Randomiser := RandomProcess(N),
	AllCosets := false)
	imageSet := {@ @};
    
    for i in [1 .. #reps - 1] do
	repeat
	    for j in {1 .. #reps} diff imageSet do
		
		if ElementInNormalSubgroup(G, N, reps[i] * g / reps[j] :
		    order := order, NumberRandom := NumberRandom,
		    Randomiser := Randomiser) then
		    
		    Include(~imageSet, j);
		    break;
		end if;
	    end for;

	    // If we know that we have all cosets, then repeat until a valid
	    // image is found
	until #imageSet ge i or not AllCosets;

	// No image found
	if #imageSet lt i then
	    return false;
	end if;
    end for;
    
    assert #imageSet eq #reps - 1;
	
    // Last image is determined
    Include(~imageSet, Rep({1 .. #reps} diff imageSet));
    return Sym(#reps) ! imageSet;
end function;

function FindQuasiSimpleGroup(node, name, data)
    if name[1] cmpeq 18 then
	vprint CompositionTree, 3 :
	    "Sporadic case, find quasi-simple group directly";
	    
	// For sporadic groups, construct kernel in a faster way
	isNotSimple, kernel, kernelSLPs :=
	    SporadicAlmostSimple(node`Group, name);

	if isNotSimple then
	    MaxCosets := 2;
	    Randomiser := RandomProcessWithWords(kernel :
		WordGroup := WordGroup(kernel));

	    return isNotSimple, kernel, kernelSLPs, Randomiser, MaxCosets;
	else
	    MaxCosets := 1;
	    return isNotSimple, _, _, _, MaxCosets;
	end if;
    else
	// Kernel is computed already
	assert #data gt 0;
	
	kernel := data[1];
	kernelSLPs := data[2];
	Randomiser := data[3];
	
	// Obtain maximum index of stable derivative
	if name[1] cmpeq 17 then 
	    // Alt/Sym
	    MaxCosets := 2;
	elif Category(node`Group) eq GrpMat and
	    forall{g : g in Generators(node`Group) | Determinant(g) eq 1} then
	    MaxCosets := MaximumStableDerivativeIndex(name[1], name[2],
		Degree(node`Group), name[3], CoefficientRing(node`Group));
	else
	    MaxCosets := 0;
	end if;
	
	vprint CompositionTree, 3 :
	    "Max index of stable derivative", MaxCosets;
	    
	isNotSimple := MaxCosets ne 1 select true else false;	
	return isNotSimple, kernel, kernelSLPs, Randomiser, MaxCosets;
    end if;
end function;

function ConstructOuterAutomorphisms(node, kernel, Randomiser, MaxCosets)
    // We need coset representatives of the simple group
    repeat
	cosetReps := ConstructCosets(node`Group, kernel :
	    Randomiser := Randomiser, MaxCosets := MaxCosets);

	vprintf CompositionTree, 3 :
	    "%o coset representatives found, depth %o\n", #cosetReps,
	    node`Depth;

	// We must have all cosets?
	safe := #cosetReps eq MaxCosets;
	    
	// Construct image
	genImages := [* AlmostSimpleImage(node`Group, kernel, cosetReps, g :
	    Randomiser := Randomiser, AllCosets := safe) :
	    g in UserGenerators(node`Group) *];

    	vprintf CompositionTree, 3 :
	    "Generator images found, depth %o\n", node`Depth;
    until forall{g : g in genImages | Category(g) ne BoolElt};

    genImages := [g : g in genImages];
    vprintf CompositionTree, 3 :
	    "Generator image sequence found, depth %o\n", node`Depth;

    return sub<Sym(#cosetReps) | genImages>, genImages, cosetReps, safe;
end function;

procedure AlmostSimpleHom(~node, data)
    try
	// We have already named the group
        names := data[1];

	vprint CompositionTree, 5 : "C9 names", names;
	
	if #names gt 1 then
	    error Error(rec<AschbacherError | Category :=
		AschbacherErrors`almostsimple,
		Error := "Multiple names not supported">);	
	end if;
	
	name := names[1];
	vprintf CompositionTree, 3 : "C9 class %o, depth %o\n",
	    name, node`Depth;
	
	isNotSimple, kernel, kernelSLPs, Randomiser, MaxCosets :=
	    FindQuasiSimpleGroup(node, name, data[2]);
	
	vprintf CompositionTree, 3 : "Simple group found, depth %o\n",
	    node`Depth;
	
	if isNotSimple then	    
	    image, genImages, cosetReps, FoundAllCosets :=
		ConstructOuterAutomorphisms(node, kernel, Randomiser,
		MaxCosets);
	else
	    genImages := [];
	    image := sub<Generic(node`Group) | >;
	end if;

	vprintf CompositionTree, 3 :
	    "Automorphisms of simple group found, depth %o\n", node`Depth;

	// Store name of the leaf
	// Sporadic groups have no defining field, and we get a string instead
	C := cop<Strings(), Integers(), Booleans()>;
	leafData := rec<LeafInfo | Family := C ! name[1],
	    DefiningField := C ! name[3], LieRank := name[2],
	    Name := name>;
	
	if isNotSimple and not IsTrivial(image) then
	    vprintf CompositionTree, 3 :
		"Group is not simple, setup image, depth %o\n", node`Depth;

	    // Construct reduction
	    reduction := hom<node`Group -> image | g :->
	    AlmostSimpleImage(node`Group, kernel, cosetReps, g :
		Randomiser := Randomiser, AllCosets := FoundAllCosets)>;
	    reductionScalar := func<g | Function(reduction)(g),
		Identity(node`Group), Identity(node`Group)>;
	    
	    // Test if element lies in some coset rep of the simple group
	    test := func<g | Category(AlmostSimpleImage(node`Group, kernel,
		cosetReps, g : Randomiser := Randomiser,
		AllCosets := FoundAllCosets)) eq GrpPermElt>;
	
	    // Store ActionMaps
	    node`ActionMaps := rec<ActionMapsInfo |
		Single := reduction,
		Scalar := reductionScalar,
		Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
		Test := test,
		ToKernelBatch := func<seq | seq>,
		FromKernelBatch := func<seq | seq>,
		BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
	    
	    // We already know image and kernel
	    node`Image`Group := image;
	    node`Image`InputGens := genImages;

	    node`CBM := func<node | Identity(node`Group)>;

	    // Set scalars
	    node`Kernel`Type := NodeTypes`leaf;
	    node`Kernel`LeafData := leafData;
	    node`Kernel`Scalar := node`Scalar;
	    node`Image`Scalar :=
		Function(node`ActionMaps`Single)(node`Scalar);
	    assert IsIdentity(node`Image`Scalar);	    
	else
	    vprintf CompositionTree, 3 :
		"Group is simple, make it a leaf, depth %o\n", node`Depth;

	    // node`Group must be simple, deal with it as a leaf
	    node`Type := NodeTypes`leaf;
	    node`LeafData := leafData;
	end if;	
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`almostsimple, Error := err>);	
    end try;
end procedure;
