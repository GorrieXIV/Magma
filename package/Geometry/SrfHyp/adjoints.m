// *********************************************************************
// * Package: adjoints.mag                                             *
// * =====================                                             *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 06.12.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute the vector space of (m,n)-adjoints for a projective     *
// *   surface in P^3.                                                 *
// *                                                                   *
// *********************************************************************

// freeze;

DEBUG_FIX := false;
DEBUG_HOMS := true;
DEBUG_HOMS := false;

VERB := true; DEBUG := true;
VERB := false; DEBUG := false;

DO_MOD := true;
DO_MOD_ONLY := false;
DO_MOD_ONLY := true;

declare verbose Classify, 1;

import "../../Ring/RngPowAlg/power_series.m" : EvlMod;



// ======================================
// = Auxillary functions (not exported) =
// ======================================

// compute the Ansatz-space for (m,n)-adjoints
// -------------------------------------------
// input:  a polynomial 's' in four variables and integers 'm' and 'n'
// output: a basis for the vector space of forms modulo 's' of degree
//         'n + m * (TotalDegree(s) - 4)'
function Ansatz(s, m, n)
	N := n + m * (TotalDegree(s) - 4);
	S := Parent(s);
	vs := [ S |]; lmon := LeadingMonomial(s);
	if N lt 0 then return vs; end if;
	for zi := 0 to N do
	    for yi := 0 to N-zi do
		for xi := 0 to N-zi-yi do
		    // add monomial if it is part of a basis of O_X(N)
		    mon := (S.4)^zi*(S.3)^yi*(S.2)^xi*(S.1)^(N-zi-yi-xi);
		    if not IsDivisibleBy(mon, lmon) then
		        Append(~vs, mon);
		    end if;
		end for;
	    end for;
	end for;
	return vs;
end function;

// get adjoint conditions for a vector space
// -----------------------------------------
// input:  the basis 'vs' of a vector space of forms, a formal
//         desingularization 'vals' and an integer 'm'
// output: the sequence of conditions for the subspace of those forms that
//         vanish with 'm' times the adjoint order along each formal prime
//         divisor in 'vals'
function GetAdjointConditions(vals, vs, m:
    do_mod := false, do_mod_only := false, ech := 0)

	vprint Classify: "--------- Entering GetAdjointConditions ----------";
	if #vs eq 0 then return vs; end if;
	F := BaseRing(Parent(Representative(vs)));
	IVec := RSpace(Integers(), 4);
	
if VERB then
"%%%%%%%%%%%%%%%%%";
"%%%%%%%%%%%%%%%%%";
"GetAdjointConditions:";
"do_mod:", do_mod;
"do_mod_only:", do_mod_only;
ZEIT:=Cputime();
"NUM VALUATIONS:", #vals;
end if;

	// compute adjoint conditions for each valuation
	con := [];
	num := 0;
	for val in vals do
	num := num+1;
		aux, adjord := Explode(val); X, Y, Z, W := Explode(aux);
		Fext := BaseRing(Domain(Z));

if VERB then
"\n***********************************";
printf "DO VALUATION %o (of %o) with adjoint order %o and field %o.\n",
num, #vals, adjord, Fext;
"Cumulative HomAdjoints time:", Cputime(ZEIT);
end if;

		Xseq := [X, Y, Z, W];
		
		// early abort
		if m*adjord le 0 then
			continue;
		end if;
		
		function do_expand(Xseq)
		    approx := []; good := true;
		    for si := 1 to #Xseq do
			    s := Xseq[si];
			    if VERB then
				printf "%%%%\nGet expand for s %o: %o\n",
				    si, s;
			    end if;
			    good, app := Expand(s, m*adjord);
//good, app := Expand(s, m*adjord+5);
			    if not good then
				error "series not expandable";
			    end if;
			    //"Res:", app;
			    Append(~approx, app);
		    end for;
//printf "Values = %o\n", approx; "approx universe:", Universe(approx);
		    return approx;
		end function;
		
		function get_con(approx)
		    // derive conditions
		    evl := EvlMod(approx, m*adjord);
		    vecs := [];
		    for v in vs do
			    // approximate series substitution
			    ss := evl(v);
    //printf "c_{%o}(%o) + \n", v, ss;
			    
			    // read of trailing coefficients
			    vec := [LeadingCoefficient(Coefficient(ss, 1, i))
				    : i in [0..m*adjord-1]];
			    Append(~vecs, vec);
		    end for;
		    return vecs;
		end function;

		vecs := 0;
		approx := 0;
		if not do_mod_only then
		    //"Get vecs:"; ZEIT := Cputime();
		    IndentPush();
		    approx := do_expand(Xseq);
		    //"***\nREPEAT expand"; approx := do_expand(Xseq);
		    vecs := get_con(approx);
		    IndentPop();
		    //"Get vecs time:", Cputime(ZEIT);
		    //"orig vecs:", vecs;
		end if;

		//"ech:", ech;
		if do_mod and ech cmpne 0 then
		    seen := {};
		    seen_agen := {};

		    NEW_APPROXK := true;
		    if NEW_APPROXK then
			UB := Fext;
			U := 0;
		    else
			U := Universe(approx);
			//"GOT U:", U: Maximal;
			assert Type(U) eq RngMPol;

			nv := Rank(U);
			UB := BaseRing(U);
		    end if;

		    //K := GF(11863279);
		    //ech := 0;
		    //last_rank := -1;

		    K := BaseRing(ech);
		    PK := PolynomialRing(K);
		    last_rank := Nrows(ech);

		    /*
		    homs go from UB to L (ext of K).
		    */

		    function get_ff_ext(CF, g)
			K := BaseRing(Parent(g));
			if Degree(g) eq 1 then
			    L := K;
			    im := Roots(g)[1, 1];
			else
			    L<w> := ext<K | g>;
			    assert MinimalPolynomial(L.1) eq g;
			    im := L.1;
			end if;
			return L, im;
		    end function;

		    function get_ff_ext_hom(CF, g)
			K := BaseRing(Parent(g));
			L, im := get_ff_ext(CF, g);
			h := hom<CF -> L | im>;
			return L, h;
		    end function;

		    function get_cf_homs(CF)
			if Type(CF) eq FldRat then
			    homs := [hom<CF -> K |>];
			elif Type(CF) eq FldNum then
			    if DEBUG_HOMS then
				"FldNum case:", CF;
			    end if;
			    homs := <>;
			    def := PK!DefiningPolynomial(CF);
			    for t in Factorization(def) do
				assert t[2] eq 1;
				g := t[1];
				if DEBUG_HOMS then
				    "def factor over K:", g;
				end if;
				L, h := get_ff_ext_hom(CF, g);
				Append(~homs, h);
			    end for;
			end if;
			return homs;
		    end function;

/*
		    function get_homs_FldFundefL(RF, h0, ro, rand)
//ro := 0;
			homs := [];
			L := Codomain(h0);
			if ro cmpne 0 and #ro ge 1 then
			    //if #seen_agen eq #ro then
				//error "TOO MANY agens", seen_agen;
			    //end if;
			    repeat
				agen := Random(ro)[1];
			    until
				agen notin seen_agen
				or #seen_agen eq #ro;
			    Include(~seen_agen, agen);

			    "Use agen:", agen;
			    h := hom<RF -> L | h0, rand>;
			    h := hom<UB -> L | h, agen>;

			    //UL := ChangeRing(U, L);
			    //h := hom<U -> UL | h, [UL.i: i in [1 .. nv]]>;
			else
			    // Use smallest defL!
			    edeg := Degree(defL);
			    UBL := quo<Parent(defL) | defL>;
			"UBL:", UBL;
			    //h := hom<RF -> L | rand>;
if DEBUG_HOMS then
    "h0:", h0;
    "RF:", RF;
    "UBL:", UBL;
end if;
			    h0l := hom<
				Domain(h0) -> UBL | x :-> UBL!h0(x)>;
			    h := hom<RF -> UBL | h0l, UBL!rand>;
			    h := hom<UB -> UBL | h, UBL.1>;

			    //UL := ChangeRing(U, UBL);
			    //h := hom<U -> UL | h, [UL.i: i in [1 .. nv]]>;
			end if;
		    end function;
*/

		    function get_homs(UB)
			seen := {}; // should be passed in or in attr!
			seen_agen := {}; // should be passed in or in attr!

			t := Type(UB);
			if t in { FldRat, FldNum } then
			    return get_cf_homs(UB);
			end if;

			if DEBUG_HOMS then
			    IndentPush();
			    "gethoms(): UB", UB;
			end if;

			homs := <>;
			if Type(UB) eq FldFunRat then
			    RF := BaseRing(UB);
			    RF_homs := get_homs(RF);

			    repeat
				rand := Random(K);
			    until rand notin seen;
			    Include(~seen, rand);
			    if DEBUG_HOMS then
				"rand:", rand;
			    end if;
			    for h0 in RF_homs do
				h := hom<UB -> Codomain(h0) | h0, rand>;
				Append(~homs, h);
			    end for;
			elif
			    Type(UB) eq FldFun and
			    Type(BaseRing(UB)) eq FldFunRat and
			    Type(ConstantField(UB)) in { FldRat, FldNum }
			then
		// OLD:
			    if DEBUG_HOMS then
				"Simple FF case";
				UB;
			    end if;

			    CF := ConstantField(UB);
			    CF_homs := get_cf_homs(CF);
			    def := DefiningPolynomial(UB);

			    if DEBUG_HOMS then
				"def:", def;
				"Parent(def):", Parent(def);
			    end if;

			    RF := BaseRing(UB);

			    for h0 in CF_homs do
				L := Codomain(h0);
				RFL := FunctionField(L);
				t := 0;
				repeat 
				    t +:= 1;
				    if t ge 10 then
					if DEBUG_HOMS then "Give up"; end if;
					ro := 0;
					break;
				    end if;
				    rand := Random(L);
				    repeat
					rand := Random(L);
				    until rand notin seen;
				    //Include(~seen, rand);
				    if DEBUG_HOMS then
					"rand:", rand;
					"CF:", CF;
					"RFL:", RFL;
					"Par def:", Parent((def));
					"Univ def:", Universe(Eltseq(def));
				    end if;
				    /*
				    defL := [
					Evaluate(RFL!c, rand): c in Eltseq(def)
				    ];
				    */
				    h := hom<RF -> L | h0, rand>;
				    defL := [h(c): c in Eltseq(def)];
				    defL := Polynomial(defL);
				    if DEBUG_HOMS then
					"defL:", defL;
					Factorization(defL);
				    end if;
				    ro := Roots(defL);
				until #ro ge 1;

ro := 0; // need to handle all conjugates:
				if ro cmpne 0 and #ro ge 1 then
				    /*
				    if #seen_agen eq #ro then
					error "TOO MANY agens", seen_agen;
				    end if;
				    */
				    repeat
					agen := Random(ro)[1];
				    until
					agen notin seen_agen
					or #seen_agen eq #ro;
				    Include(~seen_agen, agen);

				    if DEBUG_HOMS then
					"Use agen:", agen;
				    end if;
				    h := hom<RF -> L | h0, rand>;
				    h := hom<UB -> L | h, agen>;

				    //UL := ChangeRing(U, L);
				    //h := hom<U -> UL | h, [UL.i: i in [1 .. nv]]>;
				else
				    // Use smallest defL!
				    edeg := Degree(defL);
				    if 1 eq 1 then
					for t in Factorization(defL) do
					    assert t[2] eq 1;
					    g := t[1];
					    if DEBUG_HOMS then
						"Hom for g:", g;
					    end if;
					    L, im := get_ff_ext(UB, g);
					    if DEBUG_HOMS then
						"L:", L;
						"im:", im;
					    end if;
					    //UBL := Codomain(UBL_h);
					    UBL := L;

					    h0l := hom<
						Domain(h0) -> UBL |
						x :-> UBL!h0(x)
					    >;
					    h := hom<RF -> UBL | h0l, UBL!rand>;
					    h := hom<
						UB -> UBL | h, im
					    >;
					    Append(~homs, h);
					end for;
				    else
					UBL := quo<Parent(defL) | defL>;
					//h := hom<RF -> L | rand>;
					if DEBUG_HOMS then
					    "UBL:", UBL;
					    "h0:", h0;
					    "RF:", RF;
					    "UBL:", UBL;
					end if;
					h0l := hom<
					    Domain(h0) -> UBL | x :-> UBL!h0(x)
					>;
					h := hom<RF -> UBL | h0l, UBL!rand>;
					h := hom<UB -> UBL | h, UBL.1>;
					Append(~homs, h);
				    end if;

				    //UL := ChangeRing(U, UBL);
				    //h := hom<U -> UL | h, [UL.i: i in [1 .. nv]]>;
				end if;

			    end for;
			elif Type(UB) eq FldFun then
			    if DEBUG_HOMS then
				"General FldFun case";
			    end if;

			    RF := BaseRing(UB);
			    RF_homs := get_homs(RF);

			    def := DefiningPolynomial(UB);
			    if DEBUG_HOMS then
				"def:", def;
				"Parent(def):", Parent(def);
			    end if;

			    for h0 in RF_homs do
				L := Codomain(h0);
				RFL := FunctionField(L);

				defL := Polynomial([h0(c): c in Eltseq(def)]);

				if DEBUG_HOMS then
				    "defL:", defL;
				    Parent(defL);
				    "defL fact:", defL;
				    Factorization(defL);
				end if;

				ro := Roots(defL);

//ro := 0;
ro := 0; // need to handle all conjugates:
				if ro cmpne 0 and #ro ge 1 then
				    /*
				    if #seen_agen eq #ro then
					error "TOO MANY agens", seen_agen;
				    end if;
				    */
				    repeat
					agen := Random(ro)[1];
				    until
					agen notin seen_agen
					or #seen_agen eq #ro;
				    Include(~seen_agen, agen);

				    if DEBUG_HOMS then
					"Use agen:", agen;
				    end if;
				    //h := hom<RF -> L | h0, rand>;
				    h := hom<UB -> L | h0, agen>;

				else
				    // Use smallest defL!
				    edeg := Degree(defL);
				    UBL := quo<Parent(defL) | defL>;
				    //h := hom<RF -> L | rand>;
				    if DEBUG_HOMS then
					"UBL:", UBL;
					"h0:", h0;
					"RF:", RF;
					"UBL:", UBL;
				    end if;
				    h0l := hom<
					Domain(h0) -> UBL | x :-> UBL!h0(x)>;
				    //h := hom<RF -> UBL | h0l, UBL!rand>;
				    h := hom<UB -> UBL | h0l, UBL.1>;

				end if;

				Append(~homs, h);
			    end for;
			else
			    if DEBUG_HOMS then
				U: Magma;
				"Base ring:", BaseRing(U);
			    end if;
			    error "GetAdjointConditions: UNKNOWN BASE TYPE", U;
			end if;
			if DEBUG_HOMS then
			    printf "Return %o hom(s); codoms: %o\n", #homs,
				<Codomain(f): f in homs>;
			    IndentPop();
			end if;
			return homs;
		    end function;

//IndentPush();
		    modc := 0;
		    done := false;
		    stab := 0;
		    MZEIT:=Cputime();
		    while true do

			modc +:= 1;
			if VERB then
			    printf "\n****\nCumulative Val %o time: %o\n",
				num, Cputime(MZEIT);
			    "Mod count:", modc;
			end if;

			edeg := 0;
			homs := get_homs(UB);

			if VERB then
			    "GOT homs:", homs;
			end if;

			if #homs eq 0 then
			    break;
			end if;

			for h0 in homs do
			    L := Codomain(h0);

			    approxK := 0;
			    if not do_mod_only then
				U := Universe(approx);
				nv := Rank(U);
				UL<[z]> := ChangeRing(U, L);
				h := hom<U -> UL | h0, [UL.i: i in [1 .. nv]]>;
				approxK := [h(x): x in approx];

				//"normal approxK:", approxK;
			    end if;

			    if NEW_APPROXK then
				function fix_series(X: OUI := 0, UIL := 0)
				    Y := Copy(X);
if DEBUG_FIX then
				    "\n***\nFIX Y", Y;
				    "Y`type:", Y`type;
				    //TES(Y);
end if;

				    if Y`type eq 1 then
					assert not assigned Y`defpol;
					assert not assigned Y`init;
					IndentPush();
					YY := fix_series(Y`series: OUI := OUI, UIL := UIL);
					Y`series := YY;
					//"Y`subs:", Y`subs;
					Y`subs := [
					    fix_series(y: OUI := OUI, UIL := UIL):
					    y in Y`subs
					];
					IndentPop();
					if DEBUG_FIX then
					    "NEW Y:", Y;
					end if;
					return Y;
				    end if;

if DEBUG_FIX then
				    IndentPush();
end if;
				    if assigned Y`init then
					UI := Parent(Y`init);
if DEBUG_FIX then
"ORIG par Y`init UI:", UI;;
//"TES ORIG par Y`init UI:"; TES(UI);
"Given UIL:", UIL;
end if;
					if OUI cmpne 0 and
					    IsIdentical(OUI, UI) then
					    // Use UIL
					    assert UIL cmpne 0;
					else
if DEBUG_FIX then
					    "FORCE RESET";
end if;
					    OUI := 0;
					    UIL := 0;
					end if;

					if UIL cmpeq 0 then
					    OUI<[oz]> := UI;
					    UIL<[z]> := ChangeRing(UI, L);
					end if;

					assert Rank(UIL) eq Rank(UI);
					UI2 := ChangeRing(UI, Fext);
					//UI2 := UI;
if DEBUG_FIX then
"UI2:", UI2;
"New UIL:", UIL;
end if;

					yi := Y`init;
					co := ChangeUniverse(
					    Coefficients(yi), Fext
					);
					mons := [
					    UI2 | Monomial(UI2, Exponents(m)):
					    m in Monomials(yi)
					];
if DEBUG_FIX then
"orig yi:", yi;
end if;
					yi := Polynomial(co, mons);
if DEBUG_FIX then
"Fext yi:", yi;
"Monomials(yi):", Monomials(yi);
end if;

//"c seq:", ChangeUniverse(Coefficients(yi), Fext);
//"m seq:", [Monomial(UI2, Exponents(m)): m in Monomials(yi)];
/*
					    ChangeUniverse(Coefficients(yi),
						Fext),
					    [UI2!m: m in Monomials(yi)]
					);
*/
					//UL2 := DR;
					h1 := hom<UI2 -> UIL |
					    h0, [UIL.i: i in [1 .. Rank(UI)]]>;
					Y`init := h1(yi);
					if DEBUG_FIX then
					    "New Y`init:", Y`init;
					    "Parent New Y`init:",
						Parent(Y`init);
					    //"TES New Y`init:";
					    // TES(Parent(Y`init));
					end if;
				    end if;
				    if assigned Y`defpol then
					U := Parent(Y`defpol);
					BU := BaseRing(U);
					if DEBUG_FIX then
					    "ORIG U:", U;
					    //"TES ORIG U:"; TES(U);
					    //"TES ORIG BaseRing(U):";
					    //TES(BaseRing(U));
					end if;

					if IsIdentical(BU, UI) then
					    if DEBUG_FIX then
						"ID CASE";
					    end if;
					    // h1: BU -> BUL
					    BUL := UIL;
					    BU2 := Domain(h1);
					else
					    if DEBUG_FIX then
						"NON ID CASE";
					    end if;
					    BUL := ChangeRing(BU, L);
					    BU2 := ChangeRing(BU, Fext);
					    h1 := hom<BU2 -> BUL |
						h0, [BUL.i: i in [1..Rank(BUL)]]
					    >;
					end if;
					if DEBUG_FIX then
					    "NEW BUL:", BUL;
					    //"TES:"; TES(BUL);
					end if;

					UL<u> := PolynomialRing(BUL);
					U2 := PolynomialRing(
					    ChangeRing(BU, Fext)
					);
					if DEBUG_FIX then
					    "UL:", UL;
					    "U2:", U2;
					    "par Y D:", Parent(Y`defpol);
					    "UL:", UL;
					    "h0:", h0;
					    "U2:", U2;
					    "orig:", (Y`defpol);
					    //"coerce:", U2 ! (Y`defpol);
					end if;
					//h := hom<U2 -> UL | h0>;
					/*
					h := hom<BaseRing(U2) -> BUL |
					    h0, [BUL.i: i in [1..Rank(BUL)]]>;
					*/

					CR := CoefficientRing(BU2);
					im := [];
					for yi in Eltseq(Y`defpol) do
					    co := ChangeUniverse(
						Coefficients(yi), CR
					    );
					    mons := [
						BU2|
						Monomial(BU2, Exponents(m)):
						m in Monomials(yi)
					    ];
					    nyi := Polynomial(co, mons);
					    Append(~im, nyi);
					end for;

					if DEBUG_FIX then
					    "im after mon change:", im;
					    "univ:", Universe(im);
					    "h1:", h1;
					end if;

					h := h1;
					im := [h(x): x in im];
					if DEBUG_FIX then
					    "coeff im:", im;
					end if;

					im := Polynomial(im);
					if DEBUG_FIX then
					    "final im:", im;
					end if;

					//Y`defpol := UL!Y`defpol;
					if DEBUG_FIX then
					    "OLD defpol:", Y`defpol;
					    "NEW defpol:", im;
					end if;
					Y`defpol := im;
				    //"TES BUL:"; TES( BUL);
				    //"TES BR im:"; TES(BaseRing(Parent(im)));

					DR := BUL;
				    end if;
				    if 0 eq 1 then
					Y`subs := [];
				    elif assigned Y`subs then
					new := [];
					//"Y`subs len:", #Y`subs;
					for y in Y`subs do
					    ny := fix_series(y: OUI := OUI, UIL := UIL);
					    //ny`series := Y;
					    Append(~new, ny);
					end for;
					Y`subs := new;
				    end if;
				    /*
				    if assigned Y`series then
					//Y`series := fix_series(Y`series);
					Y`series := Y;
				    end if;
				    */
				    if DEBUG_FIX then
					IndentPop();
					"NEW Y:", Y;
				    end if;
				    return Y;
				end function;

				//XseqK := [fix_series(X): X in Xseq];
				XseqK := [];
				for xi := 1 to #Xseq do
				    y := fix_series(Xseq[xi]);
				    //printf "Got fixed series %o: %o\n", xi, y;
				    //TES(y);
				    Append(~XseqK, y);
				end for;

				if DEBUG_FIX then
				    "orig Xseq:", Xseq;
				    "Got XseqK before expand:", XseqK;
				end if;

				if VERB then
				    IndentPush();
				    "DO modular expand";
				end if;
				//time
				approxK1 := do_expand(XseqK);
				if VERB then
				    IndentPop();
				end if;

				if DEBUG_FIX then
				    "orig Xseq:", Xseq;
				    "Got XseqK after expand:", XseqK;
				end if;

				if DEBUG_FIX then
				    "orig approxK:", approxK;
				    "modular approxK:", approxK1;
				end if;

				if approxK cmpne 0 then
				    if Sprint(approxK1) ne Sprint(approxK) then
					"approxK:", approxK;
					"approxK1:", approxK1;
					error "NON-MATCHING";
				    end if;
				end if;
				approxK := approxK1;
			    end if;

			    if VERB then
				"Get mod vecsK:"; ZEIT := Cputime();
				IndentPush();
			    end if;

			    //time
			    vecsK := get_con(approxK);
			    vecsK := Transpose(Matrix(vecsK));
			    if VERB then
				IndentPop();
				"Get mod vecsK time:", Cputime(ZEIT);
				//"vecsK:", vecsK; Universe(vecsK);
			    end if;
			    //"Par vecsK mat:", Parent(vecsK);
			    while true do
				//"orig vecsK:", vecsK;
				L := BaseRing(vecsK);
				if VERB then
				    "Now L:", L;
				end if;
				if Type(L) ne FldFin then
				    edeg := Degree(L);
				    es := func<x | EltseqPad(x)>;
				elif Type(L) eq FldFin and Degree(L) gt 1 then
				    edeg := Degree(L, K);
				    es := func<x | Eltseq(x, K)>;
				else
				    break;
				end if;

				nq := [];
				for i := 1 to Nrows(vecsK) do
				    vv := [[]: k in [1 .. edeg]];
				    for j := 1 to Ncols(vecsK) do
					//e := EltseqPad(vecsK[i, j], edeg);
					e := es(vecsK[i, j]);
					for k := 1 to edeg do
					    vv[k][j] := e[k];
					end for;
				    end for;
				    nq cat:= vv;
				end for;
				vecsK := Matrix(nq);
				//"expand vecsK:", vecsK;
			    end while;

			    if VERB then
				"Final par expanded vecsK mat:", Parent(vecsK);
			    end if;
			    nech := EchelonForm(vecsK);
			    RemoveZeroRows(~nech);
			    if VERB then
				"New partial rank:", Nrows(nech);
				"nech:", nech; "nech par:", Parent(nech);
			    end if;
			    if ech cmpeq 0 then
				ech := nech;
			    else
				//"old ech par:", Parent(ech);
				ech := EchelonForm(VerticalJoin(ech, nech));
				//"final ech par:", Parent(ech);
			    end if;
			    RemoveZeroRows(~ech);
			    rank := Nrows(ech);
			    if VERB then
				"New updated rank:", Nrows(ech);
			    end if;
			    //"Ech:", Transpose(ech);
			end for;

			if VERB then
			    "NOW ECH RANK:", rank;
			end if;
			if rank eq last_rank then
			    stab +:= 1;
			    if stab eq 2 then
				done := true;
				break;
			    end if;
			else
			    stab := 0;
			    if VERB then
				printf "last_rank: %o, rank: %o; retry\n",
				    last_rank, rank;
			    end if;
			end if;
			last_rank := rank;

			if done then
			    break;
			end if;

		    end while;
		    if VERB then
			printf "TOTAL Val %o time: %o\n", num, Cputime(MZEIT);
		    end if;
		    //IndentPop();

		end if;

		if do_mod_only then
		    continue;
		end if;

		// transpose to read off constraints
		V := VectorSpace(Fext, #vs);
		conext := [ V ! v : v in RowSequence(Transpose(Matrix(vecs)))];
		
		// transform relations back to base field

		if DEBUG then
		    printf "Constraints before = %o\n", conext;
		    Parent(conext);
		    printf "Constraints before ech =\n%o\n",
			EchelonForm(Matrix(conext));
		    printf "Constraints before trans = \n%o\n",
			Transpose(Matrix(conext));
		end if;

		contrans := TransformRelations(F, conext);
		if DEBUG then
		    printf "Constraints after = %o\n", contrans;
		    Parent(contrans);
		end if;
		con := con cat contrans;

	if DEBUG then
	    crank := Rank(Matrix(con));
	    "Now con rank:", crank;
	    if ech cmpne 0 and Nrows(ech) ne crank then
		"BAD";
		error "STOP";
	    end if;
	end if;

	end for;

	if VERB then
	"Total GetAdjointConditions time:", Cputime(ZEIT);
	end if;
	
	vprint Classify: "--------- Leaving GetAdjointConditions ----------";
	return con, ech;
end function;


// compute adjoint subspace of a space of forms
// --------------------------------------------
// input:  the basis 'vs' of a vector space of forms and a set of linear
//         constraints 'con'
// output: the subspace fulfilling the linear constraints
function ProduceAdjointsFromMat(vs, S)
	n := Ncols(S);
	if Nrows(S) lt n then
		
		adjoints := [];
		for bi := 1 to Nrows(S) do
			adjb := 0;
			for i := 1 to #vs do
				adjb := adjb + S[bi, i]*vs[i];
			end for;
			if not adjb eq 0 then
				Append(~adjoints, adjb);
			end if;
		end for;
	else
		
		// there are no adjoint conditions
		adjoints := vs;
	end if;
	return adjoints;
end function;

function ProduceAdjoints(vs, con)
    if not #con eq 0 then
	// there are adjoint conditions
	contrans := Transpose(Matrix(con));
	
	sol := BasisMatrix(Nullspace(contrans));
	return ProduceAdjointsFromMat(vs, sol);

	// produce basis of adjoint subspace
	//"Get sol"; time
	//sol := Nullspace(contrans);
	adjoints := [];
	//"sol:", sol;


	for b in Basis(sol) do
		adjb := 0;
		for i := 1 to #vs do
			adjb := adjb + b[i]*vs[i];
		end for;
		if not adjb eq 0 then
			Append(~adjoints, adjb);
		end if;
	end for;
    else
	// there are no adjoint conditions
	adjoints := vs;
    end if;
    return adjoints;
end function;

// actual function to compute the v.s. of (m,n)-adjoints
function homAdjoints(m,n,p : FormalDesing := 0)

    if VERB then
	ZEIT:=Cputime();
	printf "START homAdjoints %o %o %o\n", m,n,p;
    end if;

    S := Parent(p); F := BaseRing(S);
    vprint Classify: "------------ Entering HomAdjoints -------------";
    vprintf Classify: "m: %o, n: %o \n", m, n;
    
    // is precomputation available?
    if Type(FormalDesing) eq RngIntElt then
	FormalDesing := FormallyResolveProjectiveHypersurface(
	    p: AdjComp := true
	);
    end if;
    
    // produce basis of Ansatz space
    vs := Ansatz(p, m, n);

    if VERB then
	"NUM COORDS:", #vs;
	"vs:", [Sprint(x): x in vs];
	"Parent(vs):", Parent(vs);
    end if;

    vprintf Classify: "dim vs: %o \n", #vs;
    
    // get 'm'-adjoint conditions

    BR := BaseRing(Universe(vs));

    do_mod := DO_MOD;
    do_mod_only := DO_MOD_ONLY;

    adj1 := 0;
    if
	do_mod and
	(Type(BR) eq FldRat or Type(BR) eq FldNum and IsSimple(BR))
    then
	PQ := PolynomialRing(RationalField());
	DQ := {};
	if Type(BR) eq FldNum then
	    Include(~DQ, DefiningPolynomial(BR));
	end if;
	IndentPush();
	for val in FormalDesing do
	    aux, adjord := Explode(val); X, Y, Z, W := Explode(aux);
	    F := BaseRing(Domain(Z));
	    if VERB then
		"INIT check Fext:", F;
	    end if;
	    D := <>;
	    if Type(F) eq FldFun then
		BF := BaseRing(F);
		CF := ConstantField(F);
		if Type(BF) eq FldFunRat and Type(CF) eq FldRat then
		    def := DefiningPolynomial(F);
		    //"func field def:", def;
		    D := <def>;
		elif Type(BF) eq FldFunRat and Type(CF) eq FldNum then
		    def := DefiningPolynomial(F);
		    //"func field def:", def;
		    D := <def>;
		    def := DefiningPolynomial(CF);
		    //"ANF def:", def;
		    Append(~D, def);
		end if;
	    end if;
	    for def in D do
		l, defq := IsCoercible(PQ, def);
		if l then
		    Include(~DQ, defq);
		end if;
	    end for;
	end for;
	IndentPop();

	M := 0;
	P := 11863280;
	ech := 0;
	if VERB then
	    "DQ:", DQ;
	end if;

	while true do
	    for i := 1 to 1000 do
		P := PreviousPrime(P);
		PK := PolynomialRing(GF(P));
		success := false;
		if not exists{f: f in DQ | not IsSquarefree(PK!f)} then
		    success := forall{f: f in DQ | #Roots(PK!f) gt 0};
		    if success then
			break;
		    end if;
		end if;
		if VERB then
		    "Fail DQ test on:", P;
		end if;
	    end for;

	    if not success then
		if VERB then
		    "Failed to find prime";
		end if;
		break;
	    end if;

	    if VERB then
		"New P:", P;
		IndentPush();
	    end if;

	    K := GF(P);
	    ech := ZeroMatrix(K, 0, #vs);

	    adj1 := 0;
	    con := 0;
	    try
		con, ech := GetAdjointConditions(FormalDesing, vs, m:
		do_mod := do_mod, do_mod_only := do_mod_only, ech := ech);
		success := true;
	    catch e
		//"got error:", e;
		success := false;
	    end try;

	    if VERB then
		IndentPop();
		//"con:", con; "Parent(con):", Parent(con);
	    end if;

	    if not success then
		if VERB then
		    "Failed in modular GetAdjointConditions";
		end if;
		break;
	    end if;

	    /*
	    if not DO_MOD_ONLY then
		if VERB then
		    "con rank:", Rank(Matrix(con));
		end if;
		assert Rank(Matrix(con)) eq Rank(ech);
	    end if;
	    */

	    sol := BasisMatrix(NullspaceOfTranspose(ech));
	    if VERB then
		"Got mod sol:", sol;
	    end if;
	    sol := Matrix(IntegerRing(), sol);

	    nz := 0;
	    if 1 eq 1 then
		sol := Transpose(sol);
		ntr := Nrows(sol);
		nz := [i: i in [1 .. Nrows(sol)] | not IsZero(sol[i])];
		sol := RowSubmatrix(sol, nz);
		sol := Transpose(sol);
		if VERB then
		    "reduced sol:", sol;
		end if;
	    end if;

	    if M cmpeq 0 then
		solM := sol;
		M := P;
	    else
		solM := CRT([solM, sol], [M, P]);
		M *:= P;
	    end if;

	    if VERB then
		"Now M:", M;
		"Now solM:", solM;
	    end if;

	    //success, Y := LLLReconstruction(Matrix(IntegerRing(), solM), M);
	    nr := Nrows(solM);
	    nc := Ncols(solM);
	    J := VerticalJoin(solM, MatrixRing(IntegerRing(), nc)!M);
	    //"J:", J;
	    J := LLL(J: Sort);
	    RemoveZeroRows(~J);
	    //"LLL J:", J;
	    lnorms := [Ilog2(Norm(J[i])): i in [1 .. Nrows(J)]];
	    if VERB then
		"LLL lnorms:", lnorms;
	    end if;

	    success := #lnorms in {0,nr} or lnorms[nr + 1] - lnorms[nr] ge 10;
	    if VERB then
		"LLL success:", success;
	    end if;

	    if success then
		Y := RowSubmatrix(J, nr);
		if VERB then
		    "Got reduced recon Y:", Y;
		end if;
		if nz cmpne 0 then
		    Y := Transpose(Y);
		    YY := ZeroMatrix(IntegerRing(), ntr, Ncols(Y));
		    for i := 1 to #nz do
			YY[nz[i]] := Y[i];
		    end for;
		    Y := Transpose(YY);
		end if;
		if VERB then
		    "Got expanded recon Y:", Y;
		end if;
		Y := EchelonForm(Matrix(RationalField(), Y));
		adj1 := ProduceAdjointsFromMat(vs, Y);

		if VERB then
		    "adj1:", adj1;
		end if;
		break;
	    end if;

	    /*
	    if DEBUG then
		"bad sol:", sol: Magma;
		"P:", P;
		error "FAIL LLL";
	    end if;
	    */
	end while;
    else
	do_mod := false;
	do_mod_only := false;
	success := false;
    end if;

    if not success or not do_mod_only then
	if VERB then
	    "Do non-mod GetAdjointConditions";
	    IndentPush();
	end if;
	con := GetAdjointConditions(FormalDesing, vs, m); // non mod
	if VERB then
	    IndentPop();
	    "Now ProduceAdjoints";
	    IndentPush();
	end if;
	adjoints := ProduceAdjoints(vs, con);
	if VERB then
	    IndentPop();
	end if;
    end if;

    if adj1 cmpeq 0 or not do_mod_only then
	// produce adjoint basis
	if adj1 cmpne 0 then
	    if VERB then
		"CHECK mod and non-mod adjoints agree";
	    end if;
	    assert adjoints eq adj1;
	end if;
    else
	adjoints := adj1;
    end if;

    if VERB then
	printf "FINISH homAdjoints %o %o %o\n", m,n,p;
	"Total HomAdjoints time:", Cputime(ZEIT);
    end if;

    vprint Classify: "------------ Leaving HomAdjoints -------------";
    return adjoints;

end function;

