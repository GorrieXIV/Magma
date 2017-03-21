/******************************************************************************
 *
 *    c8.m      Composition Tree Classical Groups Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm and Eamonn O'Brien
 *    Dev start : 2008-08-22
 *
 *    Version   : $Revision:: 3215                                           $:
 *    Date      : $Date:: 2016-05-23 22:52:22 +1200 (Mon, 23 May 2016)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: c8.m 3215 2016-05-23 10:52:22Z eobr007                         $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "recog.m" : ActionMapsInfo, NodeTypes, LeafInfo;
import "mathom.m" : AschbacherErrors, AschbacherError, FormScalarPatch,
    SpinorScalarPatch, ReductionWithScalar, DeterminantScalarPatch;
import "node.m" : AschbacherAlgorithms;
import "../../GrpMat/util/basics.m" : CanApplyDiscreteLog;

// Record field names in ClassicalForms
formName := AssociativeArray();
formName["symplectic"]       := "bilinearForm";
formName["unitary"]          := "sesquilinearForm";
formName["orthogonalminus"]  := "bilinearForm";
formName["orthogonalplus"]   := "bilinearForm";
formName["orthogonalcircle"] := "bilinearForm";

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

// If form is only preserved modulo scalars, obtain a reduction to
// a cyclic group from the action on the form
function FormActionCheck(node)
    try
	if not CanApplyDiscreteLog(CoefficientRing(node`Group)) then
	    return false, _;
	end if;

	if not IsIdentity(node`Scalar) then
	    G := sub<Generic(node`Group) | node`Group, node`Scalar>;
	else
	    G := node`Group;
	end if;

	vprintf CompositionTree, 4 : "Form type %o, mod scalars %o\n",
	    FormType(G), FormType(G : Scalars := true);
	
	formInfo := ClassicalForms(G : Scalars := true);
	
	if Category(formInfo`scalars) eq SeqEnum and
	    exists{s : s in formInfo`scalars | not IsOne(s)} then
	    vprint CompositionTree, 4 :
		"Classical form only preserved modulo scalars";	    
	    return true, formInfo;
	end if;
	
	return false, _;
    catch err
	// Sometimes the form call fail, catch the error and die gracefully
        return false, _;
    end try;
end function;

// If we have SO rather than Omega, obtain a reduction to C_2
// from SpinorNorm
function SpinorNormCheck(node)
    try
	if not CanApplyDiscreteLog(CoefficientRing(node`Group)) then
	    return false, _;
	end if;

	if not IsIdentity(node`Scalar) then
	    G := sub<Generic(node`Group) | node`Group, node`Scalar>;
	else
	    G := node`Group;
	end if;

	vprint CompositionTree, 9 : "Spinor norm check";

	// The form action check must be applied before this
	formInfo := ClassicalForms(G : Scalars := true);
	
	if formInfo`formType in
	    {"orthogonalcircle", "orthogonalplus", "orthogonalminus"} then
	    form := formInfo`bilinearForm;
	    vprint CompositionTree, 9 : "Form", form, formInfo`scalars;
	    assert forall{s : s in formInfo`scalars | IsOne(s)};
	    
	    I := CyclicGroup(GrpAb, 2);
	    genImages := [I ! SpinorNorm(g, form) : g in
		Append(ChangeUniverse(UserGenerators(node`Group),
		Generic(node`Group)), node`Scalar)];
	    
	    vprint CompositionTree, 9 : "Images", genImages;
	    if exists{g : g in genImages | not IsIdentity(g)} then	
		return true, <genImages, form>;
	    end if;
	end if;
	
	vprintf CompositionTree, 9 : "Spinor norm check failed";
	return false, _;
    catch err
	// Sometimes the form call fail, catch the error and die gracefully
        return false, _;
    end try;
end function;

function ClassicalCheck(node)
    try
	if Type (node`Group) eq GrpMat and 
	   CanApplyDiscreteLog(CoefficientRing(node`Group)) then
           if RecogniseClassical(node`Group) then 
              vprintf CompositionTree, 7 : "Found classical group, " cat
	         "degree %o, field size %o, type %o\n",
	         Degree(node`Group), #CoefficientRing(node`Group),
	         ClassicalType(node`Group);
	      return true, _;
	   end if;
	end if;
	
	return false, _;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`classical, Error := err>);        
    end try;
end function;

function FormAction(g, form, type)
    F := CoefficientRing(g);

    // g multiplies the form by a scalar, obtain this
    if type eq "unitary" then
	scalar := g * form * Transpose(FrobeniusImage(g,
	    Degree(F) div 2)) * form^(-1);
    else
	scalar := g * form * Transpose(g) * form^(-1);
    end if;

    if not IsScalar(scalar) then
	return F ! 0;
    end if;

    // Map to the field element
    return scalar[1, 1];
end function;

procedure FormActionHom(~node, formInfo)
    try
	assert formInfo`formType notin {"unknown", "linear"};    
        form := formInfo``(formName[formInfo`formType]);
    
	F := CoefficientRing(node`Group);
	I, inc := MultiplicativeGroup(F);
	
	// Discrete log
	toImage := Inverse(inc);
	
	vprint CompositionTree, 7 : "Calculate image generators";

	// The scalars may have been among the generators
	if #formInfo`scalars gt NumberOfGenerators(node`Group) then
	    node`Image`InputGens := toImage(Prune(formInfo`scalars));
	else
	    node`Image`InputGens := toImage(formInfo`scalars);
	end if;
	
	node`Image`Group := sub<I | node`Image`InputGens>;
	
	// Construct reduction hom
	reduction := hom<node`Group -> node`Image`Group |
	g :-> toImage(FormAction(g, form, formInfo`formType))>;
	
	vprint CompositionTree, 7 : "Set image scalar flag";
	
	node`Image`Scalar := Function(reduction)(node`Scalar);
	node`Image`ScalarGroup := sub<I | node`Image`Scalar>;
	fullImage := sub<I | node`Image`Group, node`Image`ScalarGroup>;
	
	test := func<g | not IsZero(x) and IsDivisibleBy(#fullImage, Order(x))
	    where x is FormAction(g, form, formInfo`formType)>;
	
	reductionScalar := func<g | FormScalarPatch(reduction,
	    node`Image`ScalarGroup, inc, node`Scalar, formInfo`formType, g)>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
	
	vprint CompositionTree, 7 : "Factorise", Order(I);

	// Magma forgets UserGenerators
	node`Image`Group`UserGenerators := node`Image`InputGens;
	I`FactoredOrder := Factorisation(Order(I));
	
	vprint CompositionTree, 7 : "Check image scalar flag";
	
	// Set scalars, kernel scalar must lie in SO, Sp, SU
	if formInfo`formType ne "unitary" then
	    assert node`Image`Scalar eq toImage(node`Scalar[1, 1]^2);
	    n := GCD(2, Order(node`Scalar));
	else
	    p := Characteristic(F);
	    assert node`Image`Scalar eq
		toImage(node`Scalar[1, 1]^(p^(Degree(F) div 2) + 1));
	    n := GCD(p^(Degree(F) div 2) + 1, Order(node`Scalar));
	end if;
	
	vprint CompositionTree, 7 : "Set kernel scalar flag";	
	node`CBM := func<node | Identity(node`Group)>;

	node`Kernel`Scalar := node`Scalar^(Order(node`Scalar) div n);
	assert IsIdentity(Function(reduction)(node`Kernel`Scalar));
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`classical, Error := err>);        
    end try;
end procedure;

procedure SpinorNormHom(~node, data)
    images := data[1];
    form := data[2];
    
    vprint CompositionTree, 4 : "Split off spinor norm image";

    // Finite simple group of order 2...
    node`Image`InputGens := Prune(images);
    node`Image`Scalar := images[#images];    
    node`Image`Group := sub<Universe(images) | node`Image`InputGens>;
    
    // Construct reduction
    reduction := hom<node`Group -> node`Image`Group |
    g :-> Universe(images) ! SpinorNorm(g, form)>;
    
    // Magma forgets UserGenerators
    node`Image`Group`UserGenerators := node`Image`InputGens;
    I := Universe(images);
    I`FactoredOrder := Factorisation(Order(I));
    
    // Set scalars
    node`Image`ScalarGroup := sub<Universe(images) | node`Image`Scalar>;
    fullImage := sub<Universe(images) | node`Image`Group,
	node`Image`ScalarGroup>;

    test := func<g | g * form * Transpose(g) eq form and
	(Universe(images) ! SpinorNorm(g, form)) in fullImage>;

    reductionScalar := func<g | SpinorScalarPatch(reduction,
	node`Image`ScalarGroup, node`Scalar, g)>;
    
    // Store ActionMaps
    node`ActionMaps := rec<ActionMapsInfo |
	Single := reduction,
	Scalar := reductionScalar,
	Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	Test := test,
	ToKernelBatch := func<seq | seq>,
	FromKernelBatch := func<seq | seq>,
	BatchTest := func<seq | forall{g : g in seq | test(g)}>>;    

    node`CBM := func<node | Identity(node`Group)>;
    
    // Kernel scalar must lie in Omega
    if IsIdentity(node`Image`Scalar) then
	node`Kernel`Scalar := node`Scalar;
    else
	node`Kernel`Scalar := node`Scalar^2;
    end if;
    assert IsIdentity(Function(reduction)(node`Kernel`Scalar));
end procedure;

procedure ClassicalHom(~node, data)
    try
	type := ClassicalType(node`Group);

        C := cop<Strings(), Integers(), Booleans()>;	    

        case type:
	when "linear":
	    name := <"A", Degree(node`Group) - 1,
		#CoefficientRing(node`Group)>;
	when "symplectic":
	    name := <"C", Degree(node`Group) div 2,
		#CoefficientRing(node`Group)>;
	when "unitary":
	    F := CoefficientRing(node`Group);
	    Fdef := sub<F | Degree(F) div 2>;
	    name := <"2A", Degree(node`Group) - 1, #Fdef>;
	when "orthogonalcircle":
	    name := <"B", (Degree(node`Group) - 1) div 2,
		#CoefficientRing(node`Group)>;
	when "orthogonalplus":
	    name := <"D", Degree(node`Group) div 2,
		#CoefficientRing(node`Group)>;
	when "orthogonalminus":
	    name := <"2D", Degree(node`Group) div 2,
		#CoefficientRing(node`Group)>;
	end case;
	
	vprint CompositionTree, 4 : "Classical type:", type;
	vprint CompositionTree, 4 : "Lie type:", name;
	
	node`LeafData := rec<LeafInfo |
	    Family := C ! name[1], DefiningField := C ! name[3],
	    LieRank := name[2], Name := name>;
	   
	// Deal with the node later
	node`Type := NodeTypes`leaf;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`classical, Error := err>);        
    end try;	
end procedure;

function DeterminantCheck(node)    
    // This breaks if the group is trivial
    G := sub<Generic(node`Group) | node`Group, node`Scalar>;
    flag := LCM([Order(Determinant(g)) : g in UserGenerators(G)]) gt 1 and
	CanApplyDiscreteLog(CoefficientRing(node`Group));

    return flag, _;
end function;

procedure DeterminantHom(~node, data)
    try
	// The image group is just F*
        F := CoefficientRing(node`Group);
	d := Degree(node`Group);
	image, Finc := MultiplicativeGroup(F);

	// Essentially discrete log
	toImage := Inverse(Finc);
	
	// In this case we already have the image
	node`Image`InputGens :=
	    [toImage(Determinant(g)) : g in UserGenerators(node`Group)];
	node`Image`Group := sub<image | node`Image`InputGens>;
	assert IsCyclic(node`Image`Group);
	
	// Construct reduction hom
	reduction := hom<node`Group -> node`Image`Group |
	g :-> toImage(Determinant(g))>;
		
	node`Image`Scalar := Function(reduction)(node`Scalar);
	node`Image`ScalarGroup := sub<image | node`Image`Scalar>;

	reductionScalar := func<g | DeterminantScalarPatch(reduction,
	    node`Image`ScalarGroup, Finc, node`Scalar, g)>;

	// Set scalars
	n := GCD(Order(node`Scalar), d);
	node`Kernel`Scalar := node`Scalar^(Order(node`Scalar) div n);
	assert Determinant(node`Kernel`Scalar) eq 1;
	
	fullImage := sub<image | node`Image`Group, node`Image`ScalarGroup>;
	test := func<g | IsDivisibleBy(#fullImage, Order(Determinant(g)))>;
	assert not IsTrivial(fullImage);
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>
	    >;

	node`CBM := func<node | Identity(node`Group)>;

	// Magma forgets UserGenerators
	node`Image`Group`UserGenerators := node`Image`InputGens;
	image`FactoredOrder := Factorisation(#image);

	assert node`Image`Scalar eq toImage(node`Scalar[1, 1]^d);
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`determinant, Error := err>);
    end try;
end procedure;
