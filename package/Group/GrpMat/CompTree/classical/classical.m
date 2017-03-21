freeze;

/******************************************************************************
 *
 *    classical.m    Classical groups package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Eamonn O'Brien, Elliot Costi, Henrik B��rnhielm
 *    Dev start : 2008-02-18
 *
 *    Version   : $Revision:: 3201                                           $:
 *    Date      : $Date:: 2016-05-18 14:53:04 +1000 (Wed, 18 May 2016)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: classical.m 3201 2016-05-18 04:53:04Z eobr007                  $:
 *
 *****************************************************************************/

import "recognition/black/odd/split.m": ConvertType;

 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ClassicalRecognition, 10;

declare attributes GrpMat : ClassicalRecognitionData;
declare attributes GrpPerm : ClassicalRecognitionData;
declare attributes GrpMat : SU32Data;
declare attributes GrpPerm : SU32Data;

ClassicalRecognitionInfo := recformat<
    type : Tup, // Classical type
    gens : SeqEnum, // Standard generators
    slps : SeqEnum, // SLPs of standard generators
    wordGroup : GrpSLP, // SLP group for returned SLPs
    cbmInput : GrpElt, // From Eamonn to input
    cbmMagma : GrpElt, // From input to Magma
    cbmStd : GrpElt, // From Magma to Eamonn
    form : AlgMatElt,
    natural : BoolElt,
    degree : RngIntElt,
    field : RngIntElt
    >;

import "recognition/basics.m": MagmaStandardCopy;
// import "rewriting/sp-natural.m" : SymplecticCBM;
// import "rewriting/orth_plus.m" : OmegaCBM;
// import "rewriting/su-natural.m" : UnitaryCBM;
// import "rewriting/su-natural_odd.m" : UnitaryOddCBM;
import "rewriting/change-basis.m": SymplecticCBM, OmegaCBM, UnitaryCBM, UnitaryOddCBM;
import "recognition/orthogonal/odd/dp.m" : MyOrthogonalForm;
import "recognition/standard.m" : SLChosenElements, SpChosenElements,
    SUChosenElements, SOChosenElements,
    MinusChosenElements, PlusChosenElements;
import "recognition/basics.m" : RecognitionError;

import "../reduce/parameters.m" : SLRybaParameters, SpRybaParameters,
    SURybaParameters, OmegaMinusRybaParameters, OmegaPlusRybaParameters,
    OmegaRybaParameters;

import "recognition/black/odd/base-omega.m": MyRecogniseOmegaPlus4,
MyRecogniseOmegaMinus4;

import "../reduce/reduce.m" : Reduction;
import "../reduce/parameters.m" : MaxRybaEvenFieldDegree;
import "../recog/magma/node.m" : ERROR_RECOGNITION, ERROR_MEMBERSHIP, ERROR_RYBA;
import "../GrpMat/util/forms.m" : NormaliseQuadForm;
import "../GrpMat/util/basics.m" : MatSLP;

import "recognition/modules/basics.m": IsHandledByRecogniseSmallDegree;

import "recognition/black/odd/main.m": IsBaseCase; 

import "recognition/black/odd/base.m": MySolveSLRep;

forward ClassicalConstructiveMembershipEngine, TransformOrthogonalForm,
    Omega2Recognition, ClassicalMembership;

MembershipTests := AssociativeArray();
MembershipTests[<"linear", true>] := func<g, form | IsOne(Determinant(g))>;
MembershipTests[<"symplectic", true>] :=
    func<g, form | g * form * Transpose(g) eq form>;
MembershipTests[<"unitary", true>] :=
    func<g, form | g * form * Transpose(FrobeniusImage(g, Degree(F) div 2)) eq
    form where F is CoefficientRing(g)>;

MembershipTests[<"orthogonalcircle", false>] := function(g, form)
    if Characteristic(CoefficientRing(g)) eq 2 then
        return NormaliseQuadForm(g * form * Transpose(g)) eq form;
    else
	return g * form * Transpose(g) eq form;
    end if;
end function;

MembershipTests[<"orthogonalcircle", true>] :=
    func<g, form | MembershipTests[<"orthogonalcircle", false>](g, form)
    and IsZero(SpinorNorm(g, form))>;

MembershipTests[<"orthogonalminus", false>] :=
    MembershipTests[<"orthogonalcircle", false>];
MembershipTests[<"orthogonalplus", false>] :=
    MembershipTests[<"orthogonalcircle", false>];
MembershipTests[<"orthogonalplus", true>] :=
    MembershipTests[<"orthogonalcircle", true>];
MembershipTests[<"orthogonalminus", true>] :=
    MembershipTests[<"orthogonalcircle", true>];

MembershipTests[<"SL", true>] := func<g, form | IsOne(Determinant(g))>;
MembershipTests[<"Sp", true>] :=
    func<g, form | g * form * Transpose(g) eq form>;
MembershipTests[<"SU", true>] :=
    func<g, form | g * form * Transpose(FrobeniusImage(g, Degree(F) div 2)) eq
    form where F is CoefficientRing(g)>;

MembershipTests[<"Omega", false>] := function(g, form)
    if Characteristic(CoefficientRing(g)) eq 2 then
        return NormaliseQuadForm(g * form * Transpose(g)) eq form;
    else
	return g * form * Transpose(g) eq form;
    end if;
end function;

MembershipTests[<"Omega", true>] :=
    func<g, form | MembershipTests[<"orthogonalcircle", false>](g, form)
    and IsZero(SpinorNorm(g, form))>;

MembershipTests[<"Omega-", false>] :=
    MembershipTests[<"Omega", false>];
MembershipTests[<"Omega+", false>] :=
    MembershipTests[<"Omega", false>];
MembershipTests[<"Omega+", true>] :=
    MembershipTests[<"Omega", true>];
MembershipTests[<"Omega-", true>] :=
    MembershipTests[<"Omega", true>];



/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/* 
intrinsic testClassicalRecognition(d :: RngIntElt, p :: RngIntElt,
    e :: RngIntElt) -> BoolElt
    { }

    return testClassicalRecognition(RandomConjugate(SU(d, GF(p, 2 * e))));
end intrinsic;

intrinsic Internal_testClassicalRecognition(G : Case := "unknown") -> BoolElt
    { }

    SetVerbose("ClassicalRecognition", 7);
    SetVerbose("User1", 0);
    SetVerbose("User2", 0);
    SetVerbose("User3", 0);
    SetVerbose("User4", 0);
    SetVerbose("User5", 0);
    SetVerbose("CompositionTree", 6);

    try
        flag := ClassicalConstructiveRecognition(G : Case := Case);
        assert flag;
	
	delete G`UserGenerators;
	assert Evaluate(G`ClassicalRecognitionData`slps,
	    UserGenerators(G)) eq [g^G`ClassicalRecognitionData`cbmInput :
	    g in G`ClassicalRecognitionData`gens];
	
	for i in [1 .. 10] do
	    g := Random(G`RandomProcess);
	    
	    flag, slp := ClassicalElementToWord(G, g);
	    assert flag;
	    
	    assert Evaluate(slp, G`ClassicalRecognitionData`gens) eq
		g^(G`ClassicalRecognitionData`cbmInput^(-1));
            
	    
	    slpUser := Evaluate(slp, G`ClassicalRecognitionData`slps);
	    assert Evaluate(slpUser, UserGenerators(G)) eq g;
	end for;
    catch e
	print e`Object;
        print e`Position;
    end try;
    
    return true;
end intrinsic;
*/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function RecogniseSLWrapper(G, d, q: RecognitionTries := 5)
    for i in [1 .. RecognitionTries] do
        flag, iso, inv := RecogniseSL(G, d, q);
        if flag then
            return true, iso, inv;
        end if;
    end for;
    return false, _, _;
end function;

function SmallFieldRecognition(G, gens, RybaParameters, order)
    d := Degree(G);
    F := CoefficientRing(G);
    q := #F;
    p := Characteristic(F);
    e := Degree(F);
    
    try
	useRyba, params := RybaParameters(G, d, q);

        if IsLinearGroup(G) then
	    cbm := Identity(G);
	elif IsOrthogonalGroup(G) and d eq 2 then
	    H := sub<Generic(G) | gens>;
	    cbm := Generic(G) ! (TransformOrthogonalForm(H) *
		TransformOrthogonalForm(G)^(-1));
	else
	    H := sub<Generic(G) | gens>;
	    cbm := Generic(G) ! (TransformForm(H) * TransformForm(G)^(-1));
	end if;
	
        if not useRyba then
	    vprint ClassicalRecognition, 4 : "RandomSchreier case";
	    if not HasAttribute(G, "FactoredOrder") and d ne 2 then
		AssertAttribute(G, "FactoredOrder", order);
	    end if;

	    RandomSchreier(G);

            // if G has large number of generators, then
            // Verify can be expensive even if |G| is small 
            // choose small # of random elements to generate subgroup S of G
            // when all generators of G are in S, then Verify (S), not G
            n := 5;
            if params[1] and #UserGenerators (G) gt 2 * n then
               vprint CompositionTree, 5: "Replace G by subgroup on fewer generators";
	       gensS := [];
               slpsS := [];
               S := sub<G | >;
               repeat
	          for i in [1 .. n] do
		    g, w := Random(G`RandomProcess);
		    if not IsIdentity (g) and not (g in gensS) then
                       Append (~gensS, g);
		       Append (~slpsS, w);
                    end if;
		  end for;
		
		  S := sub<Generic(G) | gensS>;
                  assert Ngens (S) eq #gensS;
	          RandomSchreier(S);

		  vprint ClassicalRecognition, 5 : "Verify BSGS for S";
		  Verify(S);

	          vprint ClassicalRecognition, 5 :
		    "Obtain SLPs of standard generators";
	       until forall{g : g in UserGenerators(G) | g in S};
	    
	       phi := InverseWordMap(S);
               slps := [Evaluate(phi(g^cbm), slpsS) : g in gens];

               // check that result is correct 
               // Y := Evaluate (slps, UserGenerators (G));
               // assert forall{i : i in [1..#Y] | [Y[i] eq gens[i]^cbm};

            else 
               if params[1] then
	          vprint ClassicalRecognition, 5 : "Verify BSGS for G";
		  Verify(G);
	       end if;
	    
               vprint ClassicalRecognition, 5 :
	         "Obtain SLPs of standard generators";

               phi := InverseWordMap(G);
               slps := [phi(g^cbm) : g in gens];
            end if;
	else
	    // Only small fields
	    if p eq 2 and (IsUnitaryGroup(G) select e div 2 else e) gt
		MaxRybaEvenFieldDegree then
		error ERROR_RECOGNITION;
	    end if;

	    // Bounded dimension for SL(d, 2): 
	    // construction of centraliser of involution often fails 
	    MaxRybaLinearDegree := 20;
	    if q eq 2 and d gt MaxRybaLinearDegree then 
		error ERROR_RECOGNITION;
	    end if;
	    
	    vprint ClassicalRecognition, 4 : "Ryba case";
            try 
               slps := [w where _, w is Reduction(G, g^cbm : Verify := params[1],
		CentraliserMethod := params[2], Central := params[4],
		LieRank := params[5], CentraliserCompletionCheck :=
		func<G, C, g, l | NumberOfGenerators(C) ge params[3]>) :
		g in gens];
            catch err
               error ERROR_RYBA;
            end try;
	end if;

	vprint ClassicalRecognition, 3 :
	    "Small field standard generators obtained";
	return gens, slps, cbm;
    catch err
	error ERROR_RECOGNITION;
    end try;
end function;

function SLSmallEvenRecognition(G)
    d := Degree(G);
    F := CoefficientRing(G);
    q := #F;

    try
	gens := SLChosenElements(G);
    
        if d eq 2 then
	    flag, _, _, g2slp := RecogniseSL2(G, q);
	    assert flag;
	    slps := [Function(g2slp)(g) : g in gens];
	elif d eq 3 then
	    flag, _, _, g2slp := RecogniseSL3(G, F : Verify := false);
	    assert flag;
	    
	    slps := [Function(g2slp)(g) : g in gens];	    
	else
	    gens, slps := SmallFieldRecognition(G, gens,
		SLRybaParameters, FactoredClassicalGroupOrder(ClassicalType(G), d, F));
	end if;

	return gens, slps, Identity(G);
    catch err
	error ERROR_RECOGNITION;
    end try;
end function;

function LargeToSmall(G, E, X, type, d, F, g, CB)
    f, w := ClassicalRewrite(G, E, type, d, #F, g);
    return Evaluate(w, X)^CB;
end function;

function SmallToLarge(S, E, X, type, d, F, g, CB)
    f, w := ClassicalRewrite(S, X, type, d, #F, g^(CB^-1));
    return Evaluate(w, E);
end function;

function LargeToWordGroup(G, E, W, type, d, F, g)
    f, w := ClassicalRewrite (G, E, type, d, #F, g);
    return Evaluate(w, W);
end function;

// G is isomorphic to SL2 but we have used CompTree
// must use CompTree structure to avoid black rewriting 

SetupSL2Maps := function (G, S, d, F, E, W, K, stdGens, type, CB)
   assert HasCompositionTree (G);

   f, toFactors, fromFactors, a3, a4, bb, goldToW := CompositionTreeSeries(G);

   tau := toFactors[#toFactors];
   phi := fromFactors[#toFactors];
   WG, delta := WordGroup(G);
   eps := CompositionTreeNiceToUser(G);
   W := SLPGroup (4);

   LargeToSmall := function (G, E, g)
      return Function (tau)(g);
   end function;

   SmallToLarge := function (G, g)
     return Function(phi)(g);
   end function;
      
   LargeToWordGroup := function (G, g, eps)
      f, w := CompositionTreeElementToWord(G, g);
      if not f then return false; end if;
      w := eps (w);
      return w;
   end function;
   
   phi := hom<Generic (G) -> K | x :-> LargeToSmall(G, stdGens, x)>;
   tau := hom<K -> Generic (G) | x :-> SmallToLarge(S, x)>;
   gamma := hom<Generic (G)-> WG | x :-> LargeToWordGroup(G, x, eps)>;
   delta := hom<WG -> Generic (G) | x :-> Evaluate(x, [G.i: i in [1 .. Ngens(G)]])>;
   return phi, tau, gamma, delta;
end function;

SetupMaps := function (G, type, d, F, E, W)
   stdGens := ClassicalStandardGenerators(type, d, F);
   S := sub<Generic(Universe(stdGens)) | stdGens>;

   if IsLinearGroup(S) then
       CB := Identity(S);
   else
       CB := TransformForm(S);
   end if;
   Fext := type eq "SU" select ext<F | 2> else F;
   K := MagmaStandardCopy(type, d, Fext);
   WG, delta := WordGroup(G);

   // SU(3, 2): can't set up maps using ClassicalRewriting 
   if type eq "SU" and d eq 3 and #F eq 2 then 
       if Degree (G) ne 3 then  
           phi := G`SU32Data[1]; tau := G`SU32Data[2]; 
           gamma := G`SU32Data[3]; delta := G`SU32Data[4];
       else 
           flag, phi := IsIsomorphic (G, K);
           gamma := delta^-1;
           tau := phi^-1;
       end if;
   elif (Type (G) eq GrpMat and 
       Characteristic (BaseRing (G)) eq Characteristic (F) and 
       type eq "SL" and d eq 2 and HasCompositionTree (G)) then
       vprint ClassicalRecognition, 1: "Use Composition tree to set up SL2 maps";
       phi, tau, gamma, delta := SetupSL2Maps (G, S, d, F, E, W, K, stdGens, 
					       type, CB);
   elif (d eq 3 and type eq "SL" and 
       assigned G`SL3Data and assigned G`SL3Data`RecognitionMaps) then
       rec := G`SL3Data`RecognitionMaps;
       phi := rec`iso;
       tau := rec`inv;
       gamma := rec`g2slp;
       delta := rec`slp2g; 
   else 
      vprint ClassicalRecognition, 1: "Use ClassicalRewrite for maps";
      phi := hom<Generic(G) -> Generic(K) | x :-> 
          LargeToSmall(G, E, stdGens, type, d, F, x, CB)>;
      tau := hom<Generic(K) -> Generic(G) | x :-> 
          SmallToLarge(S, E, stdGens, type, d, F, x, CB)>;
      gamma := hom<Generic (G) -> WG | x :-> 
            LargeToWordGroup(G, E, W, type, d, F, x)>; //typo? W to WG
      delta := hom<WG -> G | x :-> Evaluate(x, [G.i: i in [1 .. Ngens(G)]])>;
   end if;

   return phi, tau, gamma, delta;
end function;

MyIsBaseCase := function (type, d, q)
   if type eq "Omega+" and d in {4, 6} and q eq 2 then return false; end if;
   if type in {"Omega+", "Omega-"} and d eq 8 and q eq 2 then return false; end if;
   return IsBaseCase (type, d, q);
   // if q eq 2 then return false; end if;
   // if type eq "SU" and d eq 3 and q eq 2 then return false; end if;
   // if type in {"Omega+", "Omega-", "Omega"} and q eq 2 then return false; end if;
end function;

// is H a repn of small degree? Can we handle using small degree code?
ReduceToSmallDegree := function (H, type, d, q: Limit := 5)
   vprint ClassicalRecognition: "In ReduceToSmallDegree", d, Degree (H);
   if Type (H) eq GrpMat and IsAbsolutelyIrreducible (H) then 
      special := IsHandledByRecogniseSmallDegree (H, type, d, type eq "SU" select q^2 else q);
      vprint ClassicalRecognition: "Small degree code applicable?", special; 
      if not special then 
         return false, _, _; 
      end if;
   else
      return false, _, _; 
   end if;

   G := H;
   Pos := [1..Ngens (G)];

   F := BaseRing (H);
   f := Degree (F);
   if type eq "SU" then f := f div 2; end if;
   e := Degree (GF(q));

   // does small degree code solve the problem? 
   flag, K := RecogniseSmallDegree (H, type, d, q: Hard := false);
   if not flag then 
      vprint ClassicalRecognition, 1 : "RecogniseSmallDegree failed";
      return false, _, _; 
   end if;
      
   repeat 
      f, E, W := ClassicalConstructiveRecognition (K);
   until f;
   WG := WordGroup (G);
   W := Evaluate (W, [WG.i: i in Pos]);
   U := UserGenerators (G);
   E := Evaluate (W, U);

   Q, R := ClassicalStandardPresentation (type, d, q);
   found := #Set (Evaluate (R, E)) eq 1;
   if found then 
      return true, E, W;
   else 
      return false, _, _;
   end if;
end function;

// H is repn of SX (d, 2); attempt to retrieve natural copy 
ConstructNatural := function (H, type, d, q: Limit := 2)
   if not (q eq 2) then return false, _, _; end if;

   if type in {"Omega+", "Omega-"} and d in {8, 10} then return false, _, _; end if;
   // if type in {"Sp"} and d in {6, 8, 10} then return false, _, _; end if;

   G := H;
   S := Sections (H);
   natural := exists(K){K: K in S | Degree (K) eq d}; 

   dchoose2 := d * (d - 1) / 2;
   range := [dchoose2 - 2 .. dchoose2];
   ext := exists(K){K: K in S | Degree (K) in range};

   if not ext then 
      range := [dchoose2 + d - 2 .. dchoose2 + d];
      sym := exists(K){K: K in S | Degree (K) in range};
   else 
      sym := false;
   end if;

   if not natural and not ext and not sym then return false, _, _; end if;

   if ext or sym then  
      M := GModule (K); nmr := 1;
      repeat 
         nmr +:= 1;
         M := ExteriorSquare (M);
         CF := CompositionFactors (M);
         found := exists(c){c : c in CF | Dimension (c) eq d};
      until found or nmr gt Limit;
      if not found then return false, _, _; end if;
      K := ActionGroup (c);
   end if;

   // U := UserGenerators (K);
   assert Ngens (K) eq Ngens (G);
   f,a,b,c,d,e,w := ClassicalConstructiveRecognition (K, type, d, q);

   W := WordGroup (H);
   w := Evaluate (w, [W.i: i in [1..Ngens (H)]]);
   e := Evaluate (w, [H.i: i in [1..Ngens (H)]]);
   return true, e, w;
end function;

// standard generators for SU(3, 2)
SolveSU32 := function (H)
   o := #H;
   if not (o in {72, 216}) then return false, _, _; end if;
   E := ClassicalStandardGenerators ("SU", 3, 2); 
   S := sub<Universe (E) | E >;
   if o eq 216 then
       flag, phi := IsIsomorphic (S, H);
       delta := phi^-1;
       T := [phi (s): s in E];
   else
      F, tau := FPGroup (S);
      if Type (H) eq GrpMat then 
         delta, R := PermutationRepresentation (H);
      else 
         R := H;
         delta := hom <H -> R | [R.i: i in [1..Ngens (R)]]>;
      end if;
      Homs := Homomorphisms (F, R);
      phi := Homs[1];
      T := [phi (s @@ tau) @@ delta: s in E];
   end if;
   W, gamma := WordGroup (H);
   words := [t @@ gamma: t in T];

   // store maps -- can't set up using ClassicalRewriting 
   H`SU32Data := [delta, delta^-1, gamma^-1, gamma];

   return true, T, words;
end function;

// standard generators for Omega^+(4, 2) 
SolveOmegaPlus42 := function (H)

   o := #H;
   if not (o in {36}) then return false, _, _; end if;
   E := ClassicalStandardGenerators ("Omega+", 4, 2); 
   S := sub<Universe (E) | E >;
   flag, phi := IsIsomorphic (S, H);
   T := [phi (s): s in E];
   W, gamma := WordGroup (H);
   words := [t @@ gamma: t in T];
   return true, T, words;
end function;

// standard generators for Omega^-(4, 3) 
SolveOmegaMinus43 := function (H)
   o := #H;
   if not (o in {360}) then return false, _, _; end if;
   E := ClassicalStandardGenerators ("Omega-", 4, 3); 
   S := sub<Universe (E) | E >;
   flag, phi := IsIsomorphic (S, H);
   T := [phi (s): s in E];
   W, gamma := WordGroup (H);
   words := [t @@ gamma: t in T];
   return true, T, words;
end function;

// standard generators for Omega^+- (d, q) 
SolveOmega := function (H, type, d, q, order)
   o := #H;
   if not o eq order then return false, _, _; end if;
   E := ClassicalStandardGenerators (type, d, q);
   S := sub<Universe (E) | E >;
   flag, phi := IsIsomorphic (S, H);
   T := [phi (s): s in E];
   W, gamma := WordGroup (H);
   words := [t @@ gamma: t in T];
   return true, T, words;
end function;

// constructively recognise group via CompTree

CTClassicalSolve := function (G, type, d, q: UseCT := false)

   vprint ClassicalRecognition, 1: "\nCTClassicalSolve: Input repn has degree ", 
   Degree (G), " natural dimension = ", d, "type = ", type;

   // repn in defining char?
   DefChar := Type (G) eq GrpMat and Characteristic (BaseRing (G)) eq Characteristic (GF (q)); 

   if DefChar and IsAbsolutelyIrreducible (G) then
      flag, E, W := ReduceToSmallDegree (G, type, d, q);
      if flag then return flag, E, W; end if;
   end if;

   // RecogniseSmallDegree deals with ext and sym square of SU
   // ConstructNatural doesn't work for SU adjoint and delta 
   if DefChar and q eq 2 and type in {"Sp", "Omega+", "Omega-"} then
      vprint ClassicalRecognition, 1: "Call ConstructNatural";
      flag, E, W := ConstructNatural (G, type, d, q);
      if flag then 
         vprint ClassicalRecognition, 1: "ConstructNatural applied"; 
         return flag, E, W; end if;
   end if;

   // Deal with black copies of certain small groups
   if type eq "SU" and d eq 3 and q eq 2 then 
      return SolveSU32(G);
   elif type eq "Omega+" and d eq 4 and q eq 2 then 
      return SolveOmega (G, "Omega+", 4, 2, 36);
   elif type eq "Omega-" and d eq 4 and q eq 3 then 
      return SolveOmega (G, "Omega-", 4, 3, 360);
   elif Type (G) eq GrpPerm and type eq "Omega-" and d eq 4 and q eq 2 then 
      return SolveOmega (G, "Omega-", 4, 2, 60);
   elif Type (G) eq GrpPerm and type eq "Omega+" and d eq 6 and q eq 2 then 
      return SolveOmega (G, "Omega+", 6, 2, 20160);
   end if;

   // if q = 2 then we only have CT available for all but base cases 
   if UseCT eq false then 
      UseCT := (Type (G) eq GrpMat and (IsAbsolutelyIrreducible (G) eq false and 
           (d in {2} and q gt 9 and type in {"SL"}))) or 
               (MyIsBaseCase (type, d, q) eq false and q eq 2);
   end if;

   // second condition to avoid Omega^-(4, q) as standard copy  
   if UseCT eq false 
   // or (type eq "SL" and d eq 2 and Isqrt (q) eq #BaseRing (G)) 
   then 
      flag, E, W := Internal_ClassicalSolve (G, type, d, q);
      if flag then return true, E, W; else return false, _, _; end if;
   end if;

   if type eq "SL" and d gt 2 and q eq 2 then
      try 
         vprint ClassicalRecognition, 1: "Call Kantor-Seress for q = 2";
         E, W := MySolveSLRep (G, d, 2);
         if Type (E) eq BoolElt then return false, _, _; else 
         return true, E, W; end if;
      catch err
         error ERROR_RECOGNITION;
      end try;
   end if;

   if q eq 2 then 
     vprint ClassicalRecognition, 1: "*** q = 2 so we call CompositionTree ***";
   end if;

   // T := CompositionTree (G: FastTensorTest := true);
   vprint ClassicalRecognition, 1: "Call CompositionTree";
   T := CompositionTree (G);
   // DisplayCompTreeNodes (G);

   _, toFactor, _, _, _, _, goldToW := CompositionTreeSeries(G);
   m := #goldToW;
   tau := false;
   D := Domain (goldToW[m]);

   if q gt 2 and (Degree (D) ne d) then
      CleanCompositionTree (G);
      vprint ClassicalRecognition, 1: "*** Bad gold copy";
      flag, E, W := Internal_ClassicalSolve (G, type, d, q);
      if flag then return true, E, W; else return false, _, _; end if;
   end if;

   E := ClassicalStandardGenerators (type, d, q);
   S := sub<Universe (E) | E>;

   // special cases 
   // Omega3 vs SL2 
   // if (type eq "SL" and d eq 2) or (type eq "Omega-" and d eq 4) then 
   if (type eq "SL" and d eq 2) then 
      if Degree (D) ne 2 then
         f, tau, phi := RecogniseSL2 (D, q);
         D`MapToSL2 := tau;
         E := [Function (phi)(e): e in E];
      end if;
   end if;

   if type ne "SL" then 
      tr := TransformForm (S);
      tr2 := TransformForm (D);

      // conjugate standard generators E into domain D of goldToW[m]
      E := E^(tr * tr2^-1);
   end if;

   if type eq "Sp" and d eq 4 and IsOdd (q) then 
      if Degree (D) ne 4 then
         f, tau, phi := RecogniseSpOdd (D, 4, q);
         E := [Function (phi)(e): e in E];
      end if;
   end if;

   if type eq "SL" and d eq 4 then 
      if Degree (D) ne 4 then
         f, tau, phi := ClassicalConstructiveRecognition (D, "SL", 4, q);
         E := [Function (phi)(e): e in E];
      end if;
   end if;

   words := [Function(goldToW[m])(E[i]): i in [1..#E]];

   phi := CompositionTreeNiceToUser (G);
   W := [phi (w): w in words];

   N := CompositionTreeNiceGroup (G);
   E := Evaluate (words, [N.i: i in [1..Ngens (N)]]);

   Q, R := ClassicalStandardPresentation (type, d, q);

   // if q gt 2 and (Degree (D) ne d) then
   if #Set (Evaluate (R, E)) ne 1 then 
      CleanCompositionTree (G);
      vprint ClassicalRecognition, 1: "*** Bad gold copy";
      flag, E, W := Internal_ClassicalSolve (G, type, d, q);
      if flag then return true, E, W; else return false, _, _; end if;
   end if;

   return true, E, W;
end function;

function SLConstructiveRecognition(G, type, d, q, natural: UseCT := false)
    if natural then 
       if (q eq 2 and (IsOdd (d) or d gt 8)) or (q gt 2) then 
	  gens, slps, cbm := Internal_SolveSL(G);
       else
	  gens, slps, cbm := SLSmallEvenRecognition(G);
       end if;
    else
       //"Call black constructive recognition code";
       flag, gens, slps := CTClassicalSolve (G, "SL", d, q: UseCT := UseCT);
       if flag eq false then return false; end if;
       cbm := Identity (G);
    end if;

    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    return rec<ClassicalRecognitionInfo |
	type := <type, true>,
	cbmInput := Generic(G) ! cbm,
	cbmStd := Identity(G),
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := Type (G) eq GrpMat select IdentityMatrix(BaseRing (G), Degree (G)) else IdentityMatrix(GF(q), d), 
	cbmMagma := Identity(G),
        natural := natural,
        degree := d,
        field := q>;
        
end function;

function SUSmallEvenRecognition(G)
    d := Degree(G);
    F := CoefficientRing(G);
    assert IsEven(Degree(F));
    Fdef := sub<F | Degree(F) div 2>;
    q := #Fdef;
        
    try
	gens := SUChosenElements(G);
        H := sub<Generic(G) | gens>;
        cbm := Generic(G) ! (TransformForm(H) * TransformForm(G)^(-1));
        if d eq 3 then
	    flag, _, _, g2slp := RecogniseSU3(G, q);
	    assert flag;
	    slps := [Function(g2slp)(g^cbm) : g in gens];
	elif d eq 4 and not (q in {2, 4}) then
	    flag, _, _, g2slp := RecogniseSU4(G, q);
	    assert flag;
	    slps := [Function(g2slp)(g^cbm) : g in gens];	    
	else
	    gens, slps, cbm := SmallFieldRecognition(G, gens,
		SURybaParameters, FactoredClassicalGroupOrder(ClassicalType(G), d, F));
	    end if;
	return gens, slps, cbm;
    catch err
	error ERROR_RECOGNITION;
    end try;
end function;

function SUConstructiveRecognition (G, type, d, q, natural: UseCT := false)
    if Degree (G) eq 2 and d eq 2 then natural := false; end if;
    if natural then 
       F := GF (q);
       q0 := (#F);
       p := Characteristic (F);

       flag, form := UnitaryForm(G);
       error if not flag, ERROR_RECOGNITION;

       if (q0 eq 2 and (d in {4,5,6,7,9})) or 
	  (q0 eq 4 and (d in {3,4,5, 6})) then 
	  gens, slps, cbm := SUSmallEvenRecognition(G);
       else
	  gens, slps, cbm := Internal_SolveSU(G);
       end if;
       cbmStd := IsEven (d) select UnitaryCBM(G) else UnitaryOddCBM(G);
       cbmMagma := Generic(G) ! TransformForm(G);
    else
       //"Call black constructive recognition code";
       flag, gens, slps := CTClassicalSolve (G, "SU", d, q: UseCT := UseCT);
       if flag eq false then return false; end if;
       cbm := Identity (G);
       cbmStd := Identity (G);
       form := Type (G) eq GrpMat select 
           IdentityMatrix(BaseRing (G), Degree (G)) else IdentityMatrix(GF(q), d); 
       cbmMagma := Identity (G);
    end if;

    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    return rec<ClassicalRecognitionInfo |
	type := <type, true>,
	cbmInput := Generic(G) ! cbm,
	cbmStd := cbmStd,
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := form,
        natural := natural,
        degree := d,
        field := q,
	cbmMagma := cbmMagma>;
end function;

function SpConstructiveRecognition(G, type, d, q, natural: UseCT := false)
    if Degree (G) eq 2 and d eq 2 then natural := false; end if;

    if natural then 
       flag, form := SymplecticForm(G);
       assert flag;

       F := GF (q);
       if (q eq 2 and d in {6..12 by 2}) then 
	  vprint ClassicalRecognition, 3 : "Small field standard generators";
	  gens, slps, cbm := SmallFieldRecognition(G, SpChosenElements(G),
	    SpRybaParameters, FactoredClassicalGroupOrder(ClassicalType(G), d, F));
       else 
	  gens, slps, cbm := Internal_SolveSp(G);
       end if;

       cbmStd := SymplecticCBM(G);
       cbmMagma := Generic(G) ! TransformForm(G);
    else
       //"Call black constructive recognition code";
       flag, gens, slps := CTClassicalSolve (G, "Sp", d, q: UseCT := UseCT);
       if flag eq false then return false; end if;
       cbm := Identity (G);
       cbmStd := Identity (G);
       form :=  Type (G) eq GrpMat select IdentityMatrix (BaseRing (G), Degree (G)) else IdentityMatrix (GF(q), d);
;
       cbmMagma := Identity (G);
    end if;

    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    vprint ClassicalRecognition, 2 : "Sp standard generators found";
    
    return rec<ClassicalRecognitionInfo |
	type := <type, true>,
	cbmInput := Generic(G) ! cbm,
	cbmStd := cbmStd,
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := form,
        natural := natural,
        degree := d,
        field := q,
	cbmMagma := cbmMagma>;
	// cbmMagma := Generic(G) ! TransformForm(G)>;
end function;

function OmegaConstructiveRecognition(G, type, d, q, natural: UseCT := false)
    F := GF (q);


    // Omega_0 in char 2 is Sp
    assert Characteristic(F) gt 2;
    
    if natural then 
        flag, _, form := OrthogonalForm(G);
        error if not flag, ERROR_RECOGNITION;
    
        isOmega := forall{g : g in UserGenerators(G) |
        	IsZero(SpinorNorm(g, form))};
        cbmMagma := TransformForm(G);
    
        if isOmega then
        	gens, slps, cbm := Internal_SolveO(G);
        else
        	gens, slps, cbm := Internal_SolveSO(G);
        end if;
    else
        flag, gens, slps := CTClassicalSolve (G, "Omega", d, q: UseCT := UseCT);
        if flag eq false then return false; end if;

        isOmega := true;
        cbm := Identity (G);
        cbmStd := Identity (G);
        form :=  Type (G) eq GrpMat select IdentityMatrix (BaseRing (G), Degree (G)) else IdentityMatrix (GF(q), d);
	cbmMagma := Identity (G);
    end if;

    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    return rec<ClassicalRecognitionInfo |
	type := <type, isOmega>,
	cbmInput := Generic(G) ! cbm,
	cbmStd := Identity(G),
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := form,
        natural := natural,
        degree := d,
        field := q,
	cbmMagma := Generic(G) ! cbmMagma>; 
end function;

function OmegaMinusConstructiveRecognition(G, type, d, q, natural: UseCT := false)

    if natural then 
        F := GF (q);

// code to try to address OmegaMinus field problem
E<mu> := GF (#F^2);
w := PrimitiveElement (F);
flag := mu^(#F + 1) eq w;

        p := Characteristic (F);
        if d gt 2 then
           if p eq 2 then 
              flag, form := QuadraticForm(G);
           else
              flag, form := SymmetricBilinearForm (G);
            end if;

	   error if not flag, ERROR_RECOGNITION;
           cbmMagma := TransformForm(G);
        else
	   H, phi := ExtendField(Generic(G), ext<F | 2>);
           cbmMagma, form := TransformOrthogonalForm(G);
        end if;
    
        isOmega := forall{g : g in UserGenerators(G) |
         	IsZero(SpinorNorm(g, form))};

        if d gt 2 then
            if p eq 2 then 
	       vprint ClassicalRecognition, 3 : "Small field standard generators";
	    
      	       cbmStd := Identity(G);
	       order := FactoredClassicalGroupOrder("orthogonalminus", d, F);
	    
               // In char 2, SO = Omega, except in one case
	       if not isOmega and (d eq 2 or (d eq 4 and #F eq 2)) then
	           order *:= 2;
               end if;
               if (d in {8,10,12,14} and q eq 2) or (d in {8,10} and q eq 4) then
         	   gens, slps, cbm := SmallFieldRecognition(G, 
		MinusChosenElements(G), OmegaMinusRybaParameters, order);
               else 
		   gens, slps, cbm := Internal_SolveOMinus(G);
                   cbm := Generic(G) ! cbm;
               end if;
            else
	       if isOmega then
	          gens, slps, cbm := Internal_SolveOMinus(G);
	       else
		  gens, slps, cbm := Internal_SolveSOMinus(G);
	       end if;
	       cbmStd := Identity(G);
	       cbm := Generic(G) ! cbm;
            end if;
        else
            gens, slps, cbm := Omega2Recognition(G, type);
	    cbmStd := Identity(H);
        end if;
    else
        flag, gens, slps := CTClassicalSolve (G, "Omega-", d, q: UseCT := UseCT);
        if flag eq false then return false; end if;
        isOmega := true;
        cbm := Identity (G);
        cbmStd := Identity (G);
        form :=  Type (G) eq GrpMat select IdentityMatrix (BaseRing (G), Degree (G)) else IdentityMatrix (GF(q), d);
	cbmMagma := Identity (G);
    end if;
    
    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    return rec<ClassicalRecognitionInfo |
	type := <type, isOmega>,
	cbmInput := cbm,
	cbmStd := cbmStd,
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := form,
        natural := natural,
        degree := d,
        field := q,
	cbmMagma := Generic(G) ! cbmMagma>;
end function;

function OmegaPlusConstructiveRecognition(G, type, d, q, natural: UseCT := false)
    if natural then 
        F := GF (q);
        p := Characteristic (F);
        d := Degree(G);

        if d gt 2 then
            if p eq 2 then 
               flag, form := QuadraticForm(G);
            else
               flag, form := SymmetricBilinearForm (G);
            end if;

            error if not flag, ERROR_RECOGNITION;
	    cbmMagma := TransformForm(G);
        else
	    cbmMagma, form := TransformOrthogonalForm(G);
        end if;
    
        isOmega := forall{g : g in UserGenerators(G) |
	IsZero(SpinorNorm(g, form))};

        // q := #F;
        // p := Characteristic (F);
    
        if d gt 2 then
           if p eq 2 then
	      cbmStd := OmegaCBM(G);
	      order := FactoredClassicalGroupOrder("orthogonalplus", d, F);
	    
	      // In char 2, SO = Omega, except in one case
	      if not isOmega and (d eq 2 or (d eq 4 and #F eq 2)) then
	         order *:= 2;
	      end if;

              if (d in {4,8,10,12,14} and q eq 2) or (d eq 4 and q eq 4) then
		  vprint ClassicalRecognition, 3 : "Small field standard generators";
		  gens, slps, cbm := SmallFieldRecognition(G, 
			PlusChosenElements(G),
			OmegaPlusRybaParameters, order);
              else 
		  gens, slps, cbm := Internal_SolveOPlus(G);
        	  cbm := Generic(G) ! cbm;
              end if;
	    else
	       if isOmega then
	          gens, slps, cbm := Internal_SolveOPlus(G);
	       else
		  gens, slps, cbm := Internal_SolveSOPlus(G);
	       end if;
	       cbmStd := OmegaCBM(G);
   	       cbm := Generic(G) ! cbm;
	   end if;
        else
           gens, slps, cbm := Omega2Recognition(G, type);
           cbmStd := Identity(G);
        end if;
    else
        flag, gens, slps := CTClassicalSolve (G, "Omega+", d, q: UseCT := UseCT);
        if flag eq false then return false; end if;
        isOmega := true;
        cbm := Identity (G);
        cbmStd := Identity (G);
        form :=  Type (G) eq GrpMat select IdentityMatrix (BaseRing (G), Degree (G)) else IdentityMatrix (GF(q), d);
	cbmMagma := Identity (G);
    end if;

    if assigned G`SLPGroup then
	W := G`SLPGroup;
    else
	W := WordGroup(G);
    end if;
    
    return rec<ClassicalRecognitionInfo |
	type := <type, isOmega>,
	cbmInput := Generic(G) ! cbm,
	cbmStd := cbmStd,
	gens := gens,
	slps := slps,
	wordGroup := W,
	form := form,
        natural := natural,
        degree := d,
        field := q,
	cbmMagma := Generic(G) ! cbmMagma>;    
end function;

// Hash with individual recognition functions
RecognitionFunctions := AssociativeArray();
RecognitionFunctions["linear"]           := SLConstructiveRecognition;
RecognitionFunctions["symplectic"]       := SpConstructiveRecognition;
RecognitionFunctions["unitary"]          := SUConstructiveRecognition;
RecognitionFunctions["orthogonalminus"]  := OmegaMinusConstructiveRecognition;
RecognitionFunctions["orthogonalplus"]   := OmegaPlusConstructiveRecognition;
RecognitionFunctions["orthogonalcircle"] := OmegaConstructiveRecognition;
RecognitionFunctions["SL"]       := SLConstructiveRecognition;
RecognitionFunctions["Sp"]       := SpConstructiveRecognition;
RecognitionFunctions["SU"]       := SUConstructiveRecognition;
RecognitionFunctions["Omega-"]   := OmegaMinusConstructiveRecognition;
RecognitionFunctions["Omega+"]   := OmegaPlusConstructiveRecognition;
RecognitionFunctions["Omega"]    := OmegaConstructiveRecognition;

intrinsic ClassicalChangeOfBasis (G:: GrpMat[FldFin]) -> GrpMatElt[FldFin]
{ G is a classical group in its natural representation; 
return change-of-basis matrix to conjugate ClassicalStandardGenerators ()
to those returned by ClassicalConstructiveRecognition (G)}
    require assigned G`ClassicalRecognitionData: "First apply ClassicalConstructiveRecognition";
    return G`ClassicalRecognitionData`cbmInput;
end intrinsic;

// does result of ClassicalRecognition equal suppled type?

VerifyType := function (G, type, q)

   // if Degree (G) eq 2 and #BaseRing (G) eq 2 then return true; end if;
   result := ClassicalType (G);
   if Degree (G) eq 2 and #BaseRing (G) eq 2 then 
      return result in {"linear", "symplectic", "orthogonalminus"}; 
   elif Degree (G) eq 2 and #BaseRing (G) eq 4 then 
      return result in {"linear", "unitary", "orthogonalplus"};
   end if;

   if Degree (G) eq 2 then
      if type in {"linear", "symplectic"} and q eq #BaseRing (G) then 
         return true;
      elif type eq "unitary" and q^2 eq #BaseRing (G) then 
         return true;
      else
         return false;
      end if;
      // return result in {"linear", "symplectic", "unitary"}; 
   end if;
   
   case result: 
      when "linear": return type eq "SL";
      when "symplectic": return type eq "Sp";
      when "unitary": return type eq "SU";
      when "orthogonalplus": return type eq "Omega+";
      when "orthogonalminus": return type eq "Omega-";
      when "orthogonalcircle": return type eq "Omega";
      else return false;
   end case;
end function;

// G is a quasisimple classical group. 
// Construct standard generators S for G; return true, S
// and SLPs for S in defining generators of G. Otherwise return false.}

ClassicalConstructiveRecognitionNatural := function (G : type := "unknown", 
   Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G), 
   Scramble := 1)) 

    F := CoefficientRing(G);
    q := #F;
    p := Characteristic(F);
    d := Degree(G);


    
    if d lt 2 then
	return false, _, _;
    end if;

    natural := true;
    try
       if type eq "unknown" then
            flag := RecogniseClassical(G);
            if not flag then
                return false, _, _;
            end if;

            type := ClassicalType(G);
        end if;

	if not assigned G`RandomProcess then
	    G`RandomProcess := Randomiser;
	end if;

	// Hack for SL(2, 2) = SOMinus(2, 2)
	if d eq 2 and p eq 2 and type eq "orthogonalminus" and
	    not IsCyclic (G) then
	    type := "linear";
	end if;

        vprint ClassicalRecognition, 1: "Natural repn: Input Degree = ", Degree (G), "type = ", type;
		
	vprint ClassicalRecognition, 1: "Classical type", type;
	flag, recogniser := IsDefined(RecognitionFunctions, type);
	if not flag then
	    error Error(Sprintf("Unknown classical type: %o\n", type));
	end if;

        if type eq "unitary" then q := Isqrt (q); end if;

	G`ClassicalRecognitionData := recogniser (G, type, d, q, natural);
	vprint ClassicalRecognition, 1 : "Natural repn: Standard generators found";

        S :=  [g^G`ClassicalRecognitionData`cbmInput :
               g in G`ClassicalRecognitionData`gens];
        slps := G`ClassicalRecognitionData`slps;
        WG := WordGroup (Randomiser);
        return true, S, Evaluate (slps, [WG.i: i in [1..Ngens (WG)]]);
    catch err
	if err`Object cmpeq ERROR_RECOGNITION then
	    return false, _, _;
	end if;
	if err`Object cmpeq ERROR_MEMBERSHIP then
	    return false, _, _;
	end if;
	
	if err`Type eq "ErrUser" and Category(err`Object) eq Rec then
	    if Format(err`Object) cmpeq RecognitionError then
		// Die gracefully
		return false, _, _;
	    end if;
	end if;

	error Error(err);
    end try;
 end function;

intrinsic ClassicalConstructiveRecognition (G:: GrpMat[FldFin]) -> BoolElt, [], [] 
{ Determine if G is a quasisimple classical group in natural representation.
  If so, construct standard generators S for G; return true, S
  and SLPs for S in defining generators of G. Otherwise return false. }

  return ClassicalConstructiveRecognitionNatural (G);

end intrinsic;

// G must be a constructively recognised classical group. 
// If g in an element of G, then express g as an SLP in the standard generators 
// of G and return true and the SLP; otherwise return false. 
function ClassicalElementToWordNatural(G, g)
    
    if not assigned G`ClassicalRecognitionData then
	error Error("G must be a recognised classical group");
        //"Must first run CompositionTree on G";
        //T := CompositionTree (G);
    end if;

    natural := G`ClassicalRecognitionData`natural;

    if natural then
       if not ClassicalMembership(G, g, G`ClassicalRecognitionData`form,
         G`ClassicalRecognitionData`type) then
	return false, _;
       end if;    
    end if;
    
    W := G`ClassicalRecognitionData`wordGroup;

    // Change of basis to put g in Magma copy in correct basis
    cbm := G`ClassicalRecognitionData`cbmInput^(-1);

    vprint ClassicalRecognition, 8 : "Obtain SLP of element";

    // Obtain g as SLP in generators of G (modulo Eamonn's identity)
    flag, slp := ClassicalConstructiveMembershipEngine(G, g,
	G`ClassicalRecognitionData`type, cbm,
	G`ClassicalRecognitionData`cbmInput^(-1),
	G`ClassicalRecognitionData`gens,
	G`ClassicalRecognitionData`slps,
	G`ClassicalRecognitionData`natural,
	G`ClassicalRecognitionData`degree,
	G`ClassicalRecognitionData`field);

    vprint ClassicalRecognition, 8 : "SLP obtained";
    return true, slp;

    if flag then
	//print NumberOfGenerators(Parent(slp)), #(G`ClassicalRecognitionData`gens);
	assert NumberOfGenerators(Parent(slp)) in 
	       {#(G`ClassicalRecognitionData`gens), 
		#(G`ClassicalRecognitionData`gens) - 1};
	return true, slp;
    else
	return false, _;
    end if;
end function;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Find change of basis that puts group in block diagonal form
// assuming such a basis exists
function blockDiagonalise(G : OrderFactors := func<l | l>)

    V := VectorSpace(G);
    M := GModule(G);
    factors := OrderFactors(CompositionFactors(M));
    homos := [GHom(f, M) : f in factors];
    assert forall{h : h in homos | Dimension(h) eq 1};
        
    basis := &cat[[V ! (x * Morphism(X, M)) :
	x in Basis(X)] where X is Image(homo.1) : homo in homos];
    cbm := Matrix(CoefficientRing(G), Degree(G), Degree(G), basis);
    return Generic(G) ! cbm^(-1);
end function;

// Constructively recognise Omega(2,q) (+ or -)
function Omega2Recognition(G, type)
    assert NumberOfGenerators(G) le 1;

    F := CoefficientRing(G);

    W := WordGroup(G`RandomProcess);
    if type eq "orthogonalplus" and #F le 5 then
	if #G eq 2 then
	    return [G.1], [W.1], Identity(G);
	end if;
    end if;
    
    // With O- we need to extend the field to make it diagonalisable
    if type eq "orthogonalminus" then
	G_ext, inc := ExtendField(Generic(G), ext<F | 2>);
	G := sub<G_ext | inc(G.1)>;

	if #F eq 3 then
	    if #G eq 2 then
		return [G.1], [W.1], Identity(G);
	    end if;
	end if;
    end if;

    // Change-of-basis necessary for membership testing
    cbm := blockDiagonalise(G);
    
    return [G.1^cbm], [W.1], cbm^(-1);
end function;

// Constructive membership testig in Omega(2, q) (+ or -)
function Omega2Rewriting(G, g, type, cbm, gens, slps)
    F := CoefficientRing(G);
    G_ext, inc := ExtendField(Generic(G), ext<F | 2>);

    // With O- we need to extend the field to make it diagonalisable
    if type[1] eq "orthogonalminus" then
	G := sub<G_ext | inc(G.1)>;
	g := inc(g);
    end if;
    
    // Special cases for order 2
    if type[1] eq "orthogonalplus" and #F le 5 or
	type[1] eq "orthogonalminus" and #F eq 3 then
	if #G eq 2 then
	    if g eq gens[1] then
		return true, slps[1];
	    elif IsIdentity(g) then
		return true, slps[1]^0;
	    else
		return false, _;
	    end if;
	end if;
    end if;
    
    // Membership testing in cyclic groups is discrete log
    if IsDiagonal(g^cbm) then
	k := Log(gens[1][1, 1], (g^cbm)[1, 1]);

	if k ge 0 then
	    return true, slps[1]^k;
	end if;
    end if;

    return false, _;
end function;

// Transform orthogonal forms to standard forms, including dimension 2
function TransformOrthogonalForm(G)
    flag, type, form := MyOrthogonalForm(G);
    assert flag;
    
    return TransformForm(form, type), form,
	[CoefficientRing(G) | 1 : i in [1 .. NumberOfGenerators(G)]];
end function;

function ClassicalMembership(G, g, form, type)
    F := CoefficientRing(G);
    return MembershipTests[type](g, form);
end function;

TypeConversion := AssociativeArray();
TypeConversion["linear"] := "SL";
TypeConversion["symplectic"] := "Sp";
TypeConversion["unitary"] := "SU";
TypeConversion["orthogonalminus"] := "Omega-";
TypeConversion["orthogonalplus"] := "Omega+";
TypeConversion["orthogonalcircle"] := "Omega";

function ClassicalConstructiveMembershipEngine(G, g, type,
    cbm, cbmTest, gens, slps, natural, d, q)

   if natural then 
    d := Degree(G);

    if d eq 2 and type[1] in {"orthogonalplus", "orthogonalminus"} then
        return Omega2Rewriting(G, g, type, cbm, gens, slps);
    end if;
    
    if type[1] eq "unitary" then
	F := CoefficientRing(G);	
	Fdef := sub<F | Degree(F) div 2>;
	q := #Fdef;
    else
	F := CoefficientRing(G);
	q := #F;
    end if;
   end if;
	
    if type[1] in {"SL", "Sp", "SU", "Omega+", "Omega-", "Omega"} then 
       typeStr := type[1]; 
    else
      typeStr := TypeConversion[type[1]];
    end if;

    if natural then
       vprint ClassicalRecognition, 10 : "Call rewriting natural version ...";
       flag, slp := ClassicalRewriteNatural (typeStr, cbm^-1, g);
    else 
       vprint ClassicalRecognition, 10 : "Call rewriting non-natural version ...";
       flag, slp := ClassicalRewrite(G^cbm, gens, typeStr, d, q, g^cbm);
    end if;

    if not flag then
	return false, _, _;
    else
	assert Evaluate(slp, gens) eq g^cbmTest;
	// return true, Evaluate(slp, slps);
	return true, slp;
    end if;
end function;


intrinsic ClassicalElementToWord (G:: Grp, g:: GrpElt) -> BoolElt, GrpSLPElt 
{G is a constructively recognised classical group. 
 If g in an element of G, then express g as an SLP in the standard generators 
of G and return true and the SLP; otherwise return false. }

    require Type (G) in {GrpMat, GrpPerm}: "Group must be matrix or permutation group";
    
    if not assigned G`ClassicalRecognitionData then
	error Error("G must be a recognised classical group");
        //"Must first run CompositionTree on G";
        //T := CompositionTree (G);
    end if;

    natural := G`ClassicalRecognitionData`natural;

    if natural then
       if not ClassicalMembership(G, g, G`ClassicalRecognitionData`form,
         G`ClassicalRecognitionData`type) then
	return false, _;
       end if;    
    end if;
    
    W := G`ClassicalRecognitionData`wordGroup;

    // Change of basis to put g in Magma copy in correct basis
    cbm := G`ClassicalRecognitionData`cbmInput^(-1);

    vprint ClassicalRecognition, 8 : "Obtain SLP of element";

    // Obtain g as SLP in generators of G (modulo Eamonn's identity)
    flag, slp := ClassicalConstructiveMembershipEngine(G, g,
	G`ClassicalRecognitionData`type, cbm,
	G`ClassicalRecognitionData`cbmInput^(-1),
	G`ClassicalRecognitionData`gens,
	G`ClassicalRecognitionData`slps,
	G`ClassicalRecognitionData`natural,
	G`ClassicalRecognitionData`degree,
	G`ClassicalRecognitionData`field);

    vprint ClassicalRecognition, 8 : "SLP obtained";
    return true, slp;

    if flag then
	assert NumberOfGenerators(Parent(slp)) in 
	       {#(G`ClassicalRecognitionData`gens), 
		#(G`ClassicalRecognitionData`gens) - 1};
	return true, slp;
    else
	return false, _;
    end if;
end intrinsic;

IsValidInput := function (G, type, d, q)
   if Type (G) eq GrpPerm then return true; end if;
   if d eq 4 and type eq "Omega+" then return true; end if;
   if d eq 4 and type eq "Sp" and q eq 2 then return true; end if;
   if d eq 3 and type eq "SU" and q eq 2 then return true; end if;

   F := GF (q);
   p := Characteristic (F);
   flag, result := LieType (G, p: Perfect := true);

   if type eq "SL" then
      type := "A"; rank := d - 1;
   elif type eq "SU" then
      type := "2A"; rank := d - 1;
   elif type eq "Sp" then
      type := "C"; rank := d div 2;
   elif type eq "Omega+" then
      type := "D"; rank := d div 2;
   elif type eq "Omega-" then
      type := "2D"; rank := d div 2;
   elif type eq "Omega" then
      type := "B"; rank := d div 2;
   end if;
   if flag then result := ConvertType (type, result, q); end if;
   valid := flag and result cmpeq <type, rank, q>;
   return valid;
end function;

intrinsic ClassicalConstructiveRecognition (G:: Grp, type :: MonStgElt, d :: RngIntElt, 
q :: RngIntElt : Verify := false) -> BoolElt, Map, Map, Map, Map, [], []
{G is isomorphic to a central quotient of classical group of 
specified <type> in dimension d, with defining field GF (q);
the string <type> is one of SL, Sp, SU, Omega, Omega+, Omega-.
Construct standard generators for G; if successful, then 
return true, maps between G and its standard copy, rewriting maps,
standard generators of G and their SLPs in the defining generators of G; 
otherwise return false. If Verify is true, then check that the supplied parameters 
for an input matrix representation are correct.}
   require Type (G) in {GrpMat, GrpPerm}: "Group must be matrix or permutation group";
   require IsPrimePower (q): "Field size is not valid";
   require d ge 2: "Dimension must be at least 2";
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]:
      "Type is not valid";
   if type in ["Omega+", "Omega-"] then require d gt 3: "Dimension must be even and at least 4"; end if;

   if type in ["Omega"] then require IsOdd (d) and d ge 3 and IsOdd (q): "Dimension must be odd and at least 3 and field must have odd characteristic"; end if;

    if type in ["Omega"] then require IsOdd (d) and d ge 3 and IsOdd (q): "Dimension must be odd and at least 3 and field must have odd characteristic"; end if;

   // if type eq "SU" and d eq 3 then require q gt 2: "Does not apply to SU(3, 2)"; end if;

   if IsTrivial (G) then
	    return false, _, _, _, _, _, _;
   end if;
   if assigned (G`RecognitionMaps) then 
      maps := G`RecognitionMaps;
      data := maps[#maps];
//      if data cmpne <type, d, q> then 
//         error "Input group already recognised for following parameters",  data;
//      end if;
      if #maps eq 7 then 
         return true, maps[1], maps[2], maps[3], maps[4], maps[5], maps[6];
      else 
         return true, maps[1], maps[2], maps[3], maps[4];
      end if;
   end if;

   // remember and remove user generators 
   if assigned G`UserGenerators then 
      hold := G`UserGenerators; 
      delete G`UserGenerators; 
   end if;

    try
        if Type (G) eq GrpMat and d eq Degree (G) and 
            (q eq #BaseRing (G) or q^2 eq #BaseRing (G)) then 
            natural := RecogniseClassical (G);
            if natural and VerifyType (G, type, q) eq false then 
          // error "Input group is classical natural of type ", ClassicalType (G);
               natural := false;
            end if;
        else 
            natural := false;
	end if;

        if not natural and Verify then 
           valid := IsValidInput (G, type, d, q); 
           if not valid then 
              "Parameters of input group does not match those supplied";
              return false, _,_,_,_,_,_; 
           end if;
        end if;
	vprint ClassicalRecognition, 1 : "Classical type", type;

	flag, recogniser := IsDefined(RecognitionFunctions, type);
	if not flag then
	    error Error(Sprintf("Unknown classical type: %o\n", type));
	end if;

        result := recogniser (G, type, d, q, natural);
        // assert Type (result) cmpne BoolElt;
        if Type (result) cmpeq BoolElt then return false, _,_,_,_,_,_; end if;

	G`ClassicalRecognitionData := result;
	vprint ClassicalRecognition, 1 : "B Standard generators found";

        if natural then 
           S :=  [g^G`ClassicalRecognitionData`cbmInput :
                   g in G`ClassicalRecognitionData`gens];
        else 
           S := G`ClassicalRecognitionData`gens;
        end if;
        slps := G`ClassicalRecognitionData`slps;

        alpha, beta, gamma, delta := SetupMaps (G, type, d, GF(q), S, slps);

	G`RecognitionMaps := <alpha, beta, gamma, delta, S, slps, <type, d, q>>;
        if assigned hold then G`UserGenerators := hold; end if;
        return true, alpha, beta, gamma, delta, S, slps;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION then
	    return false, _, _, _, _, _, _;
	end if;
	if err`Object cmpeq ERROR_MEMBERSHIP then
	    return false, _, _, _, _, _, _;
	end if;
	if err`Type eq "ErrUser" and Category(err`Object) eq Rec then
	    if Format(err`Object) cmpeq RecognitionError then
		// Die gracefully
	        return false, _, _, _, _, _, _;
	    end if;
	end if;
	error Error(err);
    end try;
end intrinsic;
