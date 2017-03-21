/******************************************************************************
 *
 *    reduce.m  Composition Tree "Ryba" code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Eamonn O'Brien and Henrik B‰‰rnhielm
 *    Dev start : 2008-04-26
 *
 *    Version   : $Revision:: 3132                                           $:
 *    Date      : $Date:: 2015-08-09 15:12:12 +1000 (Sun, 09 Aug 2015)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: reduce.m 3132 2015-08-09 05:12:12Z eobr007                     $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "../recog/magma/node.m" : ERROR_MEMBERSHIP;
import "../recog/magma/node.m" : ERROR_RYBA;

 // Error object in exceptions
RybaError := recformat<
    Description : MonStgElt, 
    Error : Any>;

// Data stored with each involution 
RybaInfo := recformat<
    SLP             : GrpSLPElt, // SLP of involution in group gens
    Centraliser     : Grp, // Involution centraliser
    CentraliserSLPs : SeqEnum>; 

declare attributes Grp : RybaDB;

forward UseRandomSchreier, UseCompositionTree;

CentraliserMethods := AssociativeArray();
CentraliserMethods["BSGS"] := UseRandomSchreier;
CentraliserMethods["CT"]   := UseCompositionTree;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

/* implementation of reduction algorithm (also known as Ryba)
   described in Holmes et al., J. Group Theory, 2008 */
   
procedure SetupRybaDB(G)
    if not assigned G`RybaDB then
	// Important to set universe to generic group
	G`RybaDB := AssociativeArray(Generic(G));
    end if;
end procedure;

procedure RemoveRybaDB(G)
    if assigned G`RybaDB then
	for g in Keys(G`RybaDB) do
	    if assigned G`RybaDB[g]`Centraliser then
		delete G`RybaDB[g]`Centraliser`CTNodeData;
	    end if;
	end for;
    end if;

    delete G`RybaDB;
end procedure;

function LookupRybaDB(G, g, w : Central := false, MaxTries := 100)
    for h in Keys(G`RybaDB) do
	flag, c, c_w := AreInvolutionsConjugate(G, g, w, h,
	    G`RybaDB[h]`SLP : Central := Central, MaxTries := MaxTries);

	if flag then
	    return true, c, c_w, G`RybaDB[h]`Centraliser,
		G`RybaDB[h]`CentraliserSLPs;
	end if;
    end for;

    return false, _, _, _, _;
end function;

procedure InsertRybaDB(G, g, w, C, C_slps)
    G`RybaDB[g] := rec<RybaInfo |
	SLP := w,
	Centraliser := C,
	CentraliserSLPs := C_slps>;
end procedure;

/* construct centraliser of involution of g having word wg in G; 
   return centraliser and SLPs for its generators in terms of G */
       
function ConstructCentraliser(G, g, wg : Central := false, MaxTries := 100,
    CentraliserCompletionCheck :=
	func<G, C, g, l | NumberOfGenerators(C) ge 10>)

    // Check if involution conjugacy class is known
    flag, c, w, C, E := LookupRybaDB(G, g, wg : 
         Central := Central, MaxTries := MaxTries);
    
    if not flag then
	C, E := CentraliserOfInvolution(G, g, wg : Central := Central,
	   CompletionCheck := CentraliserCompletionCheck);
	c := Identity(G);
	w := Identity(WordGroup(G));

	// Insert new involution conjugacy class
	InsertRybaDB(G, g, wg, C, E);
    end if;
	
    return C, E, c, w;
end function;

/* RandomSchreier to solve word problem for g */

function UseRandomSchreier(G, g : verify := false)
    vprint CompositionTree, 4 : "Apply RandomSchreier";
    RandomSchreier(G);
    if verify then
	vprint CompositionTree, 4 : "Verify BSGS";
	Verify(G);
	vprint CompositionTree, 4 : "Verification finished";
    end if;
    
    phi := InverseWordMap (G);
    if not (g in G) then
	return false, _;
    end if;
    
    w := phi(g);
    return true, w;
end function;

function UseCompositionTree(G, g : verify := false)
    if not HasCompositionTree(G) then
	tree := CompositionTree(G : Verify := verify);
    end if;
    
    WN2W := CompositionTreeNiceToUser(G);
    flag, slp := CompositionTreeElementToWord(G, g);
    if flag then
	return true, WN2W(slp);
    else
	return false, _;
    end if;
end function;

/* g^x may be an element of C, a subgroup of H;
   if so, write g as a word in generators of H;
   WC are the SLPs in generators of H for generators of C;

   SolveCentraliser solves word problem for C;
   it takes as input C and g^x; decides membership of g^x in C;
   it returns true, SLP or false, _ */ 

WriteElement := function (H, C, WC, g, x, wx : Verify := false,
                          SolveCentraliser := UseRandomSchreier)
   try
      h := g^x;
      flag, wh := SolveCentraliser (C, h : verify := Verify);
      if not flag then 
         return false, _;
      end if;
   catch err
       vprint CompositionTree, 10 :  "WriteElement error";
       error ERROR_MEMBERSHIP;
   end try;

   W := WordGroup (H);
   theta := hom <Parent (wh) -> W | WC>;
   wh := theta (wh); 
   return true, wx * wh * wx^-1;
end function;

/* return space centralised by b */

CentralisingSpace := function (b)
   P := Parent (b);
   F := BaseRing (P);
   d := Degree (P);
   MA := MatrixAlgebra (F, d);
   x := MA!b - Identity (MA);
   return Nullspace (x);
end function;

/* y is (projective) involution; does its centraliser suitably split space? */
 
IsGoodInvolution := function (H, y, range)

   S := CentralisingSpace (y);
   s := Dimension (S);
   d := Degree (H);
   if s in range or (d - s) in range then return true, s; end if;

   /* possible projective order 2 */
   if y^2 ne y^0 then 
      F := BaseRing (H);
      flag, w := IsSquare (F!-1);
      if flag then 
         y1 := ScalarMatrix (d, w) * y;
         S := CentralisingSpace (y1);
         s := Dimension (S);
         return s in range or (d - s) in range, s; 
      else
         return true, d div 2;
      end if;
   else
      return false, s;
   end if;
end function;

/* first and second involutions */

ChooseInvolution := function (H, g : 
   MaxTries := Maximum (10 * Degree (H), 100), fct := Order)

   d := Degree (H);

   W := WordGroup (H);
   P := RandomProcessWithWords (H: WordGroup := W);

   if Characteristic (BaseRing (H)) eq 2 then
      // range := [d div 2..d div 2 + 2];
      range := [2..d - 2];
   else 
      range := [d div 2..5 * d div 8]; 
   end if;

   if d eq 4 then range := [2]; end if;

   if #range eq 0 then 
       vprint CompositionTree, 10 : "Range is too narrow";
       error ERROR_MEMBERSHIP;
   end if; 

   nmr := 0;
   I := []; E := []; W := []; Dim := [];
   repeat
     nmr +:= 1;
     h, wh := Random (P);
     gh := g * h;
     o := fct (gh);
     if IsEven (o) then 
        z := (gh)^(o div 2);
        if IsScalar (z) eq false then 
           flag, s := IsGoodInvolution (H, z, range);
           if flag then 
	       vprint CompositionTree, 6: "Number of elements sampled to "
		   cat "find suitable involutions is ", nmr;
	       return z, h, wh, s;
	   end if;
           I[#I + 1] := z;
           E[#E + 1] := h;
           W[#W + 1] := wh;
           Dim[#Dim + 1] := s;
        end if;
     end if;
   until nmr gt MaxTries;

   if nmr gt MaxTries then return false, _, _, _; end if;

   mid := d div 2;
   X := [AbsoluteValue (x - mid) : x in Dim];
   if #X eq 0 then return $$ (H, g); end if;
   min, pos := Minimum (X);

   return I[pos], E[pos], W[pos], Dim[pos];

end function;

ThirdInvolution := function (H, z, t: 
   MaxTries := Maximum (500, 20 * Degree (H)), fct := Order)

   d := Degree (H);
   F := BaseRing (H);

   W := WordGroup (H);
   P := RandomProcessWithWords (H : WordGroup := W);

   if Characteristic (BaseRing (H)) eq 2 then
      // range := [d div 3.. Minimum (7 * d div 8, d - 2)];
      range := [2 .. d - 2];
   else 
      range := [d div 2 - 1..5 * d div 8 + 1]; 
   end if;
   if #range eq 0 then
       vprint CompositionTree, 10 : "Range is too narrow";
       error ERROR_MEMBERSHIP;
   end if; 

   I := []; E := []; W := []; Dim := [];
   nmr := 0;
   repeat 
      a, wa := Random (P);
      nmr +:= 1;
      y := z^a * t;
      o := fct (y);
      if IsEven (o) then 
         y := y^(o div 2);
         if IsScalar (y) eq false then 
            flag, s := IsGoodInvolution (H, y, range);
            if flag then return y, a, wa, s; end if;
            I[#I + 1] := y;
            E[#E + 1] := a;
            W[#W + 1] := wa;
            Dim[#Dim + 1] := s;
         end if;
      end if;
   until nmr gt MaxTries;

   if nmr gt MaxTries then return false, _, _, _; end if;

   mid := d div 2;
   X := [AbsoluteValue (x - mid) : x in Dim];
   if #X eq 0 then return $$ (H, z, t); end if;
   min, pos := Minimum (X);

   return I[pos], E[pos], W[pos], Dim[pos];

end function;

/* select three involutions whose centralisers have Lie 
   ranks a bounded fraction of that of H */

ClassicalSelect := function (H, g : MaxTries := 100, Central := false)

   if Central then fct := CentralOrder; else fct := Order; end if;

   vprint CompositionTree, 6: "Entering ClassicalSelect";
       
   /* find h such that g * h has even order to obtain involution z */
   nmr := 0;
   repeat 
      z, h, wh, fixed := ChooseInvolution (H, g: fct := fct);
      nmr +:= 1;
   until nmr gt MaxTries or Type (z) ne BoolElt;

   if nmr gt MaxTries then 
      vprint CompositionTree, 10 : "ClassicalSelect failed to find first non-scalar involution";
      error ERROR_MEMBERSHIP;
   end if;

   vprint CompositionTree, 6 :
       "Fixed space for first involution has dimension", fixed;

   gh := g * h;

   /* find t an H-involution, distinct from z */
   second := 0; secondL := MaxTries;
   repeat 
      nmr := 0; L := MaxTries div 10; found := false;
      repeat 
         t, one, two, fixed := ChooseInvolution (H, Id (H): fct := fct); 
         if Type (t) ne BoolElt then 
            o := fct (one);
            wt := two^(o div 2);
            found := z ne t;
            vprint CompositionTree, 6: 
               "Fixed space for second involution is ", fixed;
         end if;
         nmr +:= 1;
      until (nmr gt L) or found;
   
      /* find a random H-conjugate of z such that z * t has 
         even order and so obtain a third involution y */
      if found then 
         y, a, wa, fixed := ThirdInvolution (H, z, t: 
                            MaxTries := MaxTries, fct := fct);
         found := Type (y) ne BoolElt; 
      end if;
      second +:= 1;
   until found or second gt MaxTries;

   if second gt MaxTries then 
      vprint CompositionTree, 10 : "ClassicalSelect failed to construct second or third non-scalar involution";
      error ERROR_MEMBERSHIP; 
   end if;

   z := z^a; 

   vprint CompositionTree, 6: "Fixed space for third involution is ",
       Dimension (CentralisingSpace (y));

   vprint CompositionTree, 6 : "Leaving ClassicalSelect";
   return t, wt, y, z, gh, a, wa, wh;

end function; 

/* implementation of Ryba strategy for membership testing;
   given H a subgroup of G, decide if g, an element of G, 
   is also element of H;

   return true, element of word group or false, _;
   
   if Central is true, then use projective centralisers;
   MaxTries is the maximum number of elements sampled
   to construct an involution

   valid CentraliserMethods are BSGS and CT
*/

function Reduction(H, g : Central := false, Verify := false, 
    LieRank := 0, MaxTries := Maximum (5000, 10 * Degree (H)),
    CentraliserMethod := "BSGS", ConjugationTries := 100,
        NumberTrials := 3,
	CentraliserCompletionCheck := func<G, C, g, l |
	NumberOfGenerators(C) ge 100>)

   vprint CompositionTree, 4 : "Entering Reduction/Ryba";

   if CentraliserMethod notin Keys(CentraliserMethods) then
       error Error(rec<RybaError |
	   Description := "Unknown centraliser solving method",
	   Error := CentraliserMethod>);
   end if;
   
   if Central eq true then fct := CentralOrder; else fct := Order; end if;

   W := WordGroup (H);
   
   if assigned H`RandomProcess then 
      P := H`RandomProcess;
   else
      P := RandomProcessWithWords (H: WordGroup := W);
      H`RandomProcess := P;
   end if;

   if IsIdentity (g) or Ngens (H) eq 0 then 
      return true, Identity (W);
   end if;

   vprint CompositionTree, 7 : "Setup Ryba DB";

   // Create database with known involutions and centralisers
   SetupRybaDB(H);
   
   if Type (H) eq GrpMat and LieRank gt 1 then
      vprint CompositionTree, 4 : "Using ClassicalSelect Reduction/Ryba";
      t, wt, y, z, gh, a, wa, wh := ClassicalSelect (H, g: Central := Central,
                                    MaxTries := MaxTries);
   else 
      vprint CompositionTree, 4 : "Using Standard Reduction/Ryba";
      /* find h such that g * h has order 2 ell */
      nmr := 0;
      repeat 
         h, wh := Random (P);
         o := fct (g * h);
         nmr +:= 1;
      until IsEven (o) or nmr gt MaxTries;

      if nmr gt MaxTries then 
          vprint CompositionTree, 10 : "Failed to find first element of even order";
          error ERROR_MEMBERSHIP;
      end if;
  
      ell := o div 2;
      gh := g * h;
      z := (gh)^(ell);

      /* find t an H-involution, distinct from z */
      nmr := 0; L := MaxTries div 10;
      repeat 
         flag, t, wt := RandomElementOfOrder (H, 2: Randomiser := P,
                                                 Central := Central);
         nmr +:= 1;
         complete := (flag eq true and z ne t) or (nmr eq L);
      until complete;
   
      if nmr eq L then 
          vprint CompositionTree, 10 : "Failed to find second element of even order";
          error ERROR_MEMBERSHIP;
      end if;

      /* find a random H-conjugate of z 
         such that z * t has order 2m */
      nmr := 0;
      repeat 
         a, wa := Random (P);
         o := fct (z^a * t);
         nmr +:= 1;
      until IsEven (o) or nmr gt MaxTries;

      if nmr gt MaxTries then 
          vprint CompositionTree, 10 : "Failed to find third element of even order";
          error ERROR_MEMBERSHIP;
      end if;

      m := o div 2;
      z := z^a; 
      y := (z * t)^(m);

   end if; /* selection of 3 involutions */

   /* construct centraliser T of t in H and decide if y is in T */
   T, wT, x, wx := ConstructCentraliser (H, t, wt: Central := Central,
       MaxTries := ConjugationTries,
       CentraliserCompletionCheck := CentraliserCompletionCheck);

   trial := 0;
   repeat 
      flag, wy := WriteElement (H, T, wT, y, x, wx :
         SolveCentraliser := CentraliserMethods[CentraliserMethod],
           Verify := Verify);
      trial +:= 1;
   until flag or trial gt NumberTrials; 

   if not flag then return false, _; end if;

   /* construct centraliser Y of y in H and decide if z is in Y */
   Y, wY, x, wx := ConstructCentraliser (H, y, wy: Central := Central,
       MaxTries := ConjugationTries,
       CentraliserCompletionCheck := CentraliserCompletionCheck);

   trial := 0;
   repeat 
      flag, wz := WriteElement (H, Y, wY, z, x, wx : Verify := Verify,
         SolveCentraliser := CentraliserMethods[CentraliserMethod]);
      trial +:= 1;
   until flag or trial gt NumberTrials; 

   if not flag then return false, _; end if;

   /* construct centraliser Z of z in H and decide
      if g * h is in Z */
   Z, wZ, x, wx := ConstructCentraliser (H, z, wz: Central := Central,
       MaxTries := ConjugationTries,
       CentraliserCompletionCheck := CentraliserCompletionCheck);

   gh := gh^a;
   trial := 0;
   repeat 
      flag, wgh := WriteElement (H, Z, wZ, gh, x, wx : Verify := Verify,
         SolveCentraliser := CentraliserMethods[CentraliserMethod]);
      trial +:= 1;
   until flag or trial gt NumberTrials; 

   if not flag then return false, _; end if;

   wg := wa * wgh * wa^-1 * wh^-1;
   
   vprint CompositionTree, 4 : "Leaving Reduction/Ryba";
   return true, wg;
end function; 
