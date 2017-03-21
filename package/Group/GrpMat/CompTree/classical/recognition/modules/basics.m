freeze;

import "sym-square.m": RecogniseSymmetricSquare, SymmetricSquarePreimage;
import "alt-square.m": RecogniseAlternatingSquare, AlternatingSquarePreimage;
import "delta.m": RecogniseDelta, DeltaPreimage;
import "dualdelta.m": RecogniseDualDelta, DualDeltaPreimage;
import "adjoint.m": RecogniseAdjoint, AdjointPreimage;
import "construct.m": MyAlternatingSquare, MySymmetricSquare, MyAdjointRepresentation,
   MyDeltaRepresentation, MyDualDeltaRepresentation;

// does G satisfy form of specified type?
SatisfiesForm := function (G, form, TypeString)
   if TypeString eq "2A" then
      e := Degree (BaseRing (G)) div 2;
      found := forall{i: i in [1..Ngens (G)] |
          G.i * form * Transpose (FrobeniusImage (G.i, e)) eq form};
   elif TypeString in ["B", "C", "D", "2D"] then
      found := forall{i: i in [1..Ngens (G)] |
          G.i * form * Transpose (G.i) eq form};
   end if;
   return found;
end function;

// determine form preserved by G
IdentifyForm := function (G, TypeString: Scalars := false)
   if TypeString eq "A" then return false, false, _; end if;
   forms := ClassicalForms (G: Scalars := Scalars);
   if TypeString eq "2A" then form := forms`sesquilinearForm;
   elif TypeString in ["B", "C", "D", "2D"] then form := forms`bilinearForm;
   end if;
   if form cmpeq false then return false, _, _; end if;
   return true, form, forms`scalars;
end function;

// G preserves form mod scalars; rescale generators so that G fixes the form
TryFixForm := function (G, TypeString)

   if TypeString eq "A" then return false, G, false; end if;

   has_form, form := IdentifyForm (G, TypeString: Scalars := false);
   if has_form then return true, G, form; end if;

   has_form, form, scalars := IdentifyForm (G, TypeString: Scalars := true);
   if not has_form then return false, G, false; end if;

   d := Degree (G);

   if TypeString eq "2A" then 
      q := Isqrt (#BaseRing (G));
      S := [Root (x, q + 1): x in scalars];
   else
      S := [Root (x, 2): x in scalars];
   end if;
   S := [Generic (G) ! ScalarMatrix (d, s^-1): s in S];
   X := [G.i * S[i]: i in [1..#S]];
   A := sub<Generic (G) | X >;
   assert SatisfiesForm (A, form, TypeString);
   return true, A, form;
end function;

FixForm := function (A, TypeString: FormTrial := 10^7)

   if TypeString eq "A" then return false, A, false; end if;
   found, form := IdentifyForm (A, TypeString);
   vprint SmallDegree: "Initial group preserves form?", found; 
   if found then return found, A, form; end if;

   d := Degree (A);
   q := #BaseRing (A);
   myRootsOfUnity := AllRoots (One (GF (q)), d);
   // "# of roots is ", #myRootsOfUnity;
   myGrp := A; nmrForm := 0;
   gens := [Generic (A) ! A.i : i in [1..Ngens (A)]];
   while not found and nmrForm lt FormTrial do 
      nmrForm +:= 1; 
      if nmrForm mod 1000 eq 0 then 
         vprint SmallDegree: "Form trial", nmrForm; 
      end if;
      myList := gens;
      for i in [1..Ngens (A)] do
          myList[i] := myList[i] * Generic (A)!ScalarMatrix (d, Random (myRootsOfUnity));
      end for;
      myGrp := sub<Generic (A) | myList>;
      found, form := IdentifyForm (myGrp, TypeString);
   end while;
   vprint SmallDegree: "Form preserved?", found, nmrForm;
   if found then return true, myGrp, form; else return false, _, _; end if;
end function;

ScalarMultiple := function (g, lambda)
   P := Parent (g);
   F := BaseRing (P);
   d := Degree (P);
   return MatrixAlgebra (F, d) ! lambda * g;
end function;

ScaleMatrix := function (g)
   det := Determinant (g);
   if det eq 1 then return g; end if;
   m := Nrows (g);
   roots := AllRoots (det, m);
   if (#roots eq 0) then return false; end if;
   mu := 1/roots[1];
   return ScalarMultiple (g, mu);
end function;

ScaleMatrix2 := function (g)
   det := Determinant (g);
   m := Nrows (g);
   mu := 1;
   if det ne 1 then mu := -1; else mu := 1; end if;
   return ScalarMultiple (g, mu);
end function;

ScaleMatrices := function (gList)
   dets := [Determinant (g) : g in gList];
   m := Nrows (gList[1]);
   newList := [];
   for i in [1..#gList] do;
      if Determinant (gList[i]) eq 1 then
   	Append (~newList, gList[i]);
      else
  	myMat := -gList[i];
   	Append (~newList, myMat);
      end if;
   end for;
   return newList;
end function;

FindScalarMultipleOverSubfield := function (mat, subfield)
	d := Nrows(mat);
	Grp := GL (d, subfield);
	try return Grp!mat; catch e; end try;	
	for i in [1..d^2] do
		E := Eltseq(mat);
		if (E[i] eq 0) then continue; end if;
		newmat := ScalarMultiple (mat, E[i]^(-1));
		try 
			return Grp!newmat;
		catch e; 
		end try;
	end for;
	return false;
end function;

/* return the value d' (between d-2 and d depending on the type) */
getExtensionDegree := function (d, typeString)
	if (typeString eq "A") then return d; end if;
	if (typeString eq "C") then return d; end if;
	if (typeString eq "2D") then return d; end if;
	if (typeString eq "D") then return d-2; end if;
	if (typeString eq "B") then return d-1; end if;
	if (typeString eq "2A") then 
		if IsEven (d) then return d-1; else return d; end if;
	end if;
end function;

// Check whether the order of g is divisible by a ppd of q^d - 1
Test := function (g, d, q)
   m := q^d * &*[(q^j - 1): j in Divisors (d) | j ne d];
   return g^m ne 1;
end function;

// Find a special element
ChooseSingerElt := function (G, TypeString, d: NumberRandom := 100)
	n := Degree (G);
	F := BaseRing (G);
	e := getExtensionDegree (d, TypeString);
	q := #F;
	p := Characteristic (F);
	f := Degree (F);
	qq := p^(f div 2);

        /* find Singer cycle in G */
	count := 1;
	repeat
		repeat
			g := Random (G);
			count +:= 1;
			//check if characteristic polynomial has any irreducible factors of 'forbidden' degree
			Char := CharacteristicPolynomial (g);
			sqfree := SquareFreeFactorization (Char);
			if (#sqfree ge 3) then continue; end if;
			nonlinearfactors := [x[1]: x in sqfree | Degree(x[1]) gt 1];
			if (#nonlinearfactors ne 1) then continue; end if;
			degrees := [ x[1]: x in DistinctDegreeFactorization (nonlinearfactors[1])];
			if (not e in degrees) then continue; end if;
			forbiddendegrees := [x : x in degrees | not x in [1, 2, e div 2, e]];
			if #forbiddendegrees ge 2 then continue; end if;
			break;
		until count ge NumberRandom;
                if count ge NumberRandom then 
                   vprint SmallDegree: "Failed to construct special element"; 
		   return false, _, _, _;
                end if;

		E := GF (q^e);
		MA := MatrixAlgebra (E, n); 
		s := MA ! Eltseq (g);

	        /* diagonalise s */
		EV := Eigenvalues (s);

		EVWithoutOnes := {@ ev[1]: ev in EV | ev[1] ne 1 @};
		NumberOfLargeEigenspaces := #{ev : ev in EV | ev[2] ge 2};

		MaxNumOfLargeEigenspaces := 1;
                if (TypeString eq "A" and not Degree(G) in [d^2-1, d^2-2]) then 
                     MaxNumOfLargeEigenspaces := 0; 
                end if;

		/* stop the search if s is a ppd(d,q,e)-element with enough eigenvalues, or if we run out of time */
	until ((#EVWithoutOnes ge 1 and Test(EVWithoutOnes[1], e, q) and 
               NumberOfLargeEigenspaces le MaxNumOfLargeEigenspaces) 
               or count ge NumberRandom);
        if count ge NumberRandom then 
           vprint SmallDegree: "Failed to construct special element"; 
           return false, _, _, _;
        end if;

	//deal with complications in the unitary case for d even
	if (TypeString eq "2A" and IsEven (d) and n le d^2-2) then
		toohighpowers := [x^((qq^(e)+1) div (qq+1)): x in EVWithoutOnes | x^((qq^(e)+1) div (qq+1)) ne 1];
		if #toohighpowers ge 1 then 
			exp := Maximum([ Order(x): x in toohighpowers ]);
			s := s^exp;
			EV := Eigenvalues (s);		
		end if;
	end if; 

	if (count ge NumberRandom) then 
		vprint SmallDegree: "Failed to construct special element";  
		return false, _, _, _;
	else
		vprint SmallDegree: "Found special element after randomly choosing", count, "elements";
	end if;

	/* what is the multiplicity of 1 */
	flag := exists(x){ x: x in EV | x[1] eq 1};
	if flag then ones := x[2]; else ones :=0; end if;
	/*now forget the other multiplicities */
	EV := [e[1]: e in EV];

        /* construct Frobenius orbits */
	ev := [];
	for i in [1..#EV] do
		v := EV[i];
		if v in &join (ev) then continue; end if;
		orbit := {@ v^(q^j): j in [0..d - 1] @};
		Append (~ev, orbit);
	end for;

	if (TypeString eq "2A" and IsEven (d) and (Degree(G) gt d*(d-1)/2)) then
		mySingleton := [x[1] : x in ev | #x eq 1];
                if #mySingleton gt 0 then 
                   mySingleton := mySingleton[1];
                   if (mySingleton ne 1) then 
			s:=s^Order (mySingleton); 
			EV := Eigenvalues (s);	

			/* what is the multiplicity of 1 */
			flag := exists(x){x: x in EV | x[1] eq 1};
			if flag then ones := x[2]; else ones :=0; end if;
			/* now forget the other multiplicities */
			EV := [e[1]: e in EV];

		        /* construct Frobenius orbits  */
			ev := [];
			for i in [1..#EV] do
				v := EV[i];
				if v in &join (ev) then continue; end if;
				orbit := {@ v^(q^j): j in [0..d - 1] @};
				Append (~ev, orbit);
			end for;
                   end if;
		end if;
	end if;
	return true, s, ev, ones;
end function;

ConstructListOfPossibleGroups := function(K)
	Coefs:= [x: x in CartesianPower([One(Generic(K)),-One(Generic(K))], Ngens(K))];
	myList:=[ sub<Generic(K)|[ tuple[i]*K.i : i in [1..Ngens(K)]]> : tuple in Coefs];
	return myList;
end function;

TestPlusMinusForPerfection := function(myList)
	return [gp : gp in myList | IsProbablyPerfect (gp)];
end function;

TestPlusMinusForDeterminants := function(myList) 
	newList := [];
	for gp in myList do
		if not (-1 in [Determinant (gp.i) : i in [1..Ngens(gp)]]) then Append (~newList, gp); end if; 
	end for;
	return newList;
end function;

fixSigns := function (K, G)
	myList := ConstructListOfPossibleGroups (K);
	if #myList eq 1 then return true, myList[1]; end if;
	if (IsOdd (#BaseRing(K))) then
		myList := TestPlusMinusForDeterminants (myList);
	end if;
	if #myList eq 0 then return false, _; end if;
	return true, myList[1];
end function;

// preimage group stored as last item of record 
RetrieveExistingData := function (G)
   C := G`SmallDegree; l := #C;
   if G`SmallDegree[1] eq "AltSquare" then return true, G`SmallDegree[l]; end if;
   if G`SmallDegree[1] eq "SymSquare" then return true, G`SmallDegree[l]; end if;
   if G`SmallDegree[1] eq "DeltaSquare" then return true, G`SmallDegree[l]; end if;
   if G`SmallDegree[1] eq "DualDeltaSquare" then return true, G`SmallDegree[l]; end if;
   if G`SmallDegree[1] eq "Adjoint" then return true, G`SmallDegree[l]; end if;
end function;

// use LieType to find the isomorphism type of G
intrinsic RecogniseSmallDegree (G :: GrpMat) -> BoolElt, GrpMat  
{if G is a defining characteristic absolutely irreducible representation of 
a classical group H of degree d and G has degree in [d + 1..d^2], then 
return true and H, otherwise false}

	require IsAbsolutelyIrreducible (G): "G must be absolutely irreducible";

	if assigned G`SmallDegree then return RetrieveExistingData (G); end if;

	vprint SmallDegree: "Determine the LieType ...";
	flag, type := LieType (G, Characteristic (BaseRing (G)));
	require flag: "G is not of Lie Type";

	TypeString := type[1];
	r := type[2];
	q := type[3];
	vprint SmallDegree: "Input group is of Lie Type", TypeString, "with rank", r, "and field size", q;

	if (TypeString in ["A", "2A"]) then d := r+1; end if;
	if (TypeString in ["C", "D", "2D"]) then d := 2*r; end if;
	if (TypeString in ["B"]) then d := 2*r+1; end if;

        FamilyTypes := AssociativeArray();
        FamilyTypes["A"] := "SL";
        FamilyTypes["B"] := "Omega";
        FamilyTypes["C"] := "Sp";
        FamilyTypes["D"] := "Omega+";
        FamilyTypes["2A"] := "SU";
        FamilyTypes["2D"] := "Omega-";
        type := FamilyTypes[TypeString]; 

        n := Degree (G);
        require n in [d + 1..d^2]: "Degree of the representation must be in range ", [d + 1..d^2];
	//certain coincidences must be caught
	if (TypeString eq "2A" and d eq 4 and Degree (G) in [20]) then 
		TypeString := "2D";
		d := 6;
	end if;
	if (TypeString eq "A" and d eq 4 and Degree (G) in [15, 36]) then 
		TypeString := "D";
		d := 6;
	end if;
	if (TypeString eq "A" and d eq 2 and Degree (G) eq 16) then 
		TypeString := "2D";
		d := 4;
	end if;
	if (TypeString eq "A" and d eq 2 and Degree (G) eq 9) then 
		TypeString := "B";
		d := 3;
	end if;
	if (TypeString eq "C" and d eq 4 and Degree (G) eq 25) then 
		TypeString := "B";
		d := 5;
	end if;
	return RecogniseSmallDegree (G, type, d, q);
end intrinsic;

SmallDegreeImpossibleInfo := recformat<
    Adjoint   : UserProgram,
    Delta     : UserProgram,
    SymSquare : UserProgram,
    AltSquare : UserProgram>;

RecogniseSmallDegreeImpossibleData := AssociativeArray();

RecogniseSmallDegreeImpossibleData["A"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | d le 2>,
    AltSquare := func<d, q | d le 3>,
    SymSquare := func<d, q | (d le 3 or (d eq 4 and q eq 3))>,
    Delta     := func<d, q | d le 2 or (d eq 3 and q le 4)>>;

RecogniseSmallDegreeImpossibleData["C"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | false>,
    AltSquare := func<d, q | (q eq 2 or d le 7)>,
    SymSquare := func<d, q | (q eq 3 or d le 5)>,
    Delta     := func<d, q | d le 3>>;

// q is underlying field size, not defining field size
RecogniseSmallDegreeImpossibleData["2A"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | (q eq 4 or d eq 4 or d le 2)>,
    AltSquare := func<d, q | d le 4 or (d eq 6 and q eq 4)>,
    SymSquare := func<d, q | d le 4>,
    Delta     := func<d, q | (d le 2 or (d in {4,5} and q eq 16)) or (d in {5} and q eq 81)>>;

RecogniseSmallDegreeImpossibleData["B"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | false>,
    AltSquare := func<d, q | (q eq 2 or d le 7)>,
    SymSquare := func<d, q | (q eq 3 or d le 6)>,
    Delta     := func<d, q | (q le 8 or d le 2) or (q eq 9 and d eq 3)>>;

RecogniseSmallDegreeImpossibleData["D"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | false>,
    AltSquare := func<d, q | (q eq 2 or d le 9)>,
    SymSquare := func<d, q | (q eq 3 or d le 9)>,
    Delta     := func<d, q | d le 5>>;

RecogniseSmallDegreeImpossibleData["2D"] := rec<SmallDegreeImpossibleInfo |
    Adjoint   := func<d, q | false>,
    AltSquare := func<d, q | (q eq 2 or d le 7)>,
    SymSquare := func<d, q | (q eq 3 or d le 5)>,
    Delta     := func<d, q | d le 3>>;


// type can be either "A", "B" etc or "SL", "Omega" etc
// q should be underlying field, not definition field 
function IsHandledByRecogniseSmallDegree (G, type, d, q)
    if type eq "2A" then q := q^2; end if;

    case type:
        when "SU": type := "2A";
        when "SL": type := "A";
        when "Omega": type := "B";
        when "Omega+": type := "D";
        when "Omega-": type := "2D";
        when "Sp": type := "C";
     end case;

    if not (Category(G) eq GrpMat and IsDivisibleBy (q, #CoefficientRing (G))) then
       return false;
    end if;
    n := Degree(G);

    if not (n gt d and n le d^2) then
	return false;
    end if;
    if n eq d^2 then
        // "** CHECK Delta";
	return not RecogniseSmallDegreeImpossibleData[type]`Delta(d, q);
    end if;
    if type in {"A", "2A"} and n in [d^2 - 2, d^2 - 1] then
        // "** CHECK Adjoint";
	return not RecogniseSmallDegreeImpossibleData[type]`Adjoint(d, q);
    end if;
    dchoose2 := d * (d - 1) / 2;
    if n in [dchoose2 - 2 .. dchoose2] then
        // "** CHECK Alt Square";
	return not RecogniseSmallDegreeImpossibleData[type]`AltSquare(d, q);
    end if;
    if IsOdd (q) and n in [dchoose2 + d - 2 .. dchoose2 + d] then
        // "** CHECK Sym Square";
	return not RecogniseSmallDegreeImpossibleData[type]`SymSquare(d, q);
    end if;
    
    return false;
end function;

intrinsic RecogniseSmallDegree (G :: GrpMat, type :: MonStgElt, d ::
RngIntElt, q :: RngIntElt : Hard := true, FieldLimit := 2^14) -> BoolElt, GrpMat  
{if G is a defining characteristic absolutely irreducible representation of 
a classical group H of type <type>, degree d, and defining field GF (q), 
and G has degree in [d + 1..d^2], then return true and H, otherwise false;
the string <type> is one of SL, Sp, SU, Omega, Omega+, Omega-.
}
    require IsAbsolutelyIrreducible(G): "G must be absolutely irreducible";
    require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: "Type is not valid";

    case type:
        when "SU": TypeString := "2A";
        when "SL": TypeString := "A";
        when "Omega": TypeString := "B";
        when "Omega+": TypeString := "D";
        when "Omega-": TypeString := "2D";
        when "Sp": TypeString := "C";
     end case;
    n := Degree (G);
    require n in [d + 1..d^2]: "Degree of the representation must be in range ", [d + 1..d^2];

    if assigned G`SmallDegree then return RetrieveExistingData (G); end if;

    if TypeString eq "B" then 
        require IsOdd (d): "Degree must be odd";
    elif TypeString in {"C", "D", "2D"} then
        require IsEven (d): "Degree must be even";
    end if;

    flag := IsHandledByRecogniseSmallDegree (G, TypeString, d, q);
    if not flag then "Code does not apply to these parameters"; return false, _; end if;
        
    F := BaseRing (G);
    p := Characteristic (F);
    f := Degree (F);

    // for unitary case change q to be underlying field size 
    if TypeString eq "2A" then q := q^2; end if;

    flag, e := IsPowerOf (q, p);
    require flag: "Input group must be in defining characteristic";

    require e mod f eq 0: "Base ring of input group and supplied field size are incompatible";
 
    dchoose2 := d*(d-1)/2;

    //try the alternating square 
    if (n in [dchoose2 - 2..dchoose2]) then 
       flag, A := RecogniseAlternatingSquare (G, TypeString, q); 
       if flag then return flag, A; end if;
    end if;

    //try the symmetric square
    if (n in [dchoose2 + d-2..dchoose2+d]) then
	flag, A := RecogniseSymmetricSquare (G, TypeString, q); 
	if flag then return flag, A; end if;
    end if;

    //try delta and dual delta
    if (n eq d^2) then
        if Hard eq false and q gt FieldLimit then return false, _; end if;
        flag, K := RecogniseDelta (G, TypeString, q: Hard := Hard);
        if not flag and TypeString in {"A", "2A"} then
           flag, K := RecogniseDualDelta (G, TypeString, q: Hard := Hard);
        end if;
        if flag then return flag, K; end if;
    end if;

    //try adjoint
    if (n in [d^2-2, d^2-1]) then 
        if Hard eq false and q gt FieldLimit then return false, _; end if;
        return RecogniseAdjoint (G, TypeString, q: Hard := Hard);
    end if;

    return false, _;
end intrinsic;

// G may be over a smaller field 
SetupGroup := function (G, g)
   q := G`SmallDegree[#G`SmallDegree];
   if q ne #BaseRing (G) then 
      GG := sub<GL(Degree (G), q) | [G.i: i in [1..Ngens (G)]]>;
      GG`SmallDegree := G`SmallDegree;
      g := Generic (GG)!g;
   else 
      GG := G;
   end if;
   return GG, g;
end function;

intrinsic SmallDegreePreimage (G :: GrpMat, g :: GrpMatElt: Limit := 10) -> BoolElt, GrpMatElt 
{if RecogniseSmallDegree has been applied to G and g is in G, then return true and the 
preimage of g; otherwise return false. Limit controls the number of attempts to 
construct the preimage.}

	require assigned G`SmallDegree: "Recognition for small degree modules: "
		cat "Must first apply RecogniseSmallDegree";

	string := G`SmallDegree[1];
	if string eq "SymSquare" then 
            return SymmetricSquarePreimage (G, g, Limit); 
	elif string eq "AltSquare" then 
            return AlternatingSquarePreimage (G, g, Limit);
	elif string eq "DeltaSquare" then 
            return DeltaPreimage (G, g, Limit);
	elif string eq "DualDeltaSquare" then 
            return DualDeltaPreimage (G, g, Limit);
	elif string eq "Adjoint" then 
            return AdjointPreimage (G, g, Limit);
	end if;
end intrinsic;

intrinsic SmallDegreeImage (G :: GrpMat, h :: GrpMatElt) -> BoolElt, GrpMatElt 
{if RecogniseSmallDegree has been applied to G and h is in the preimage of G, 
then return true and the image of h in G; otherwise return false.}

   require assigned G`SmallDegree: "Recognition for small degree modules: "
      cat "Must first apply RecogniseSmallDegree";

   Data := G`SmallDegree;
   len := #Data;
   H := Data[len];
   m := Ngens (G);
   assert Ngens (H) eq m;

   // is h a generator of H or the identity?
   gens := [Generic (H) | H.i: i in [0..m]];
   pos := Position (gens, h);
   if pos ne 0 then pos -:= 1; return true, G.pos; end if;

   form := Data[len - 2];
   K := sub<Generic (H) | H, h>;
   assert Ngens (K) eq m + 1;

   // is h in H?
   TypeString := Data[len - 3];
   if (TypeString eq "A" and Determinant (h) ne 1) or 
      (TypeString ne "A" and not SatisfiesForm (K, form, TypeString)) then 
      return false, _; 
   end if;

   rep := Data[1];
   if rep eq "AltSquare" then 
      K := MyAlternatingSquare (K);
   elif rep eq "SymSquare" then 
      K := MySymmetricSquare (K);
   elif rep eq "Adjoint" then 
      K := MyAdjointRepresentation (K);
   elif rep eq "DeltaSquare" then 
      e := Data[4];
      K := MyDeltaRepresentation (K, e);
   elif rep eq "DualDeltaSquare" then 
      e := Data[4];
      K := MyDualDeltaRepresentation (K, e);
   else error "SmallDegreeImage: Type of repn is unknown";
   end if;

   M := GModule (G);
   L := sub<Generic (K) | [ K.i: i in [1..m]]>;
   N := GModule (L);
   flag, CB := IsIsomorphic (N, M);
   if not flag then 
      error "SmallDegreeImage: Modules are not isomorphic"; 
   end if;
   image := K.(m + 1);
   return true, Generic (G) ! (CB^-1 * image * CB);
end intrinsic;
