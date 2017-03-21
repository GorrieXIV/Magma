freeze;

asw_testing_checks := 0;
by_ramification := false;

strong_chinese_switch := 50;

declare type FldFunAb;
declare attributes FldFunAb:
  D,  // the divisor used to define the field,
  U,  // the subgroup 
  C,  // the conductor - if known
  F,  // the function field - if known
  g,  // the genus - if known
  N,  // the number of places of degree 1
  dk, // the degree of the ECF
  disc,// the discrimant divisor
  witts; // a list of witt vectors, entries set for those components 
  	 // which are ASW extensions
	 // primitive element of Kummer extension otherwise 

////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////

/* cannot get the divisir from the map...
intrinsic AbelianExtension(m::map[GrpAb, DivFun]) -> FldFunAb
  {}
end intrinsic;
*/

intrinsic AbelianExtension(D::DivFunElt, U::GrpAb) -> FldFunAb
  {Creates the abelian extension defined by D and U.}
  r, mr := RayClassGroup(D);
  require U subset r:
    "The 2nd argument must be a subgroup of the ray class group modulo the 1st";
  q, mq := quo<r|U>;
  require IsFinite(q) :
    "The subgroup must be of finite index in the ray class group";

  A := New(FldFunAb);

  A`D := D;
  A`U := U;
  return A;
end intrinsic;

intrinsic Print(A::FldFunAb, l::MonStgElt) 
  {}
  r, mr := RayClassGroup(A`D);
  q, mq := quo<r|A`U>;

  "Abelian extension of type", AbelianInvariants(q);
  any := false;
  if assigned A`g then
    printf "of genus %o, ", A`g;
    any := true;
  end if;
  if assigned A`N then
    printf "with %o rational places, ", A`N;
    any := true;
  end if;
  if assigned A`dk then
    printf "and exact constant field of degree %o", A`dk;
    any := true;
  end if;
  if any then
    printf "\n";
  end if;
  "Defined modulo", A`D;
  "over", FunctionField(A`D);
  if l eq "Maximal" then
    if assigned A`C then
      "Of conductor", A`C;
    end if;
    if assigned A`disc then
      "And discrimant divisor", A`disc;
    end if;
    if assigned A`F then
      "As a function field", A`F;
    end if;
  end if;
end intrinsic;   

intrinsic FunctionField(A::FldFunAb:WithAut := false) -> FldFun
  {Computes an explicit representation of A as a finite extension.}
  if assigned A`F then
    if (WithAut and Type(A`F) eq SeqEnum) or 
    					(not WithAut and Type(A`F) eq FldFun) then
	return A`F, A`witts;
    end if;
    if not WithAut and Type(A`F) ne FldFun then
	return FunctionField([DefiningPolynomial(x) : x in A`F] : Check := false), 								A`witts;
    end if;
    if WithAut and Type(A`F) ne SeqEnum then
	return [FunctionField(x) : x in DefiningPolynomials(A`F)];
    end if;
  end if;
  F, _, witts := InternalRayClassField(A`D, A`U:WithAut := WithAut);
  A`F := F;
  A`witts := witts;
  return F;
end intrinsic;    

intrinsic Conductor(A::FldFunAb) -> DivFunElt
  {The conductor of A}
  if assigned A`C then
    return A`C;
  end if;
  A`C := Conductor(A`D, A`U);
  return A`C;
end intrinsic;

intrinsic DiscriminantDivisor(A::FldFunAb) -> DivFunElt
  {The discrimant divisor of A}
  if assigned A`disc then
    return A`disc;
  end if;
  A`disc := DiscriminantDivisor(A`D, A`U);
  return A`disc;
end intrinsic;

intrinsic DegreeOfExactConstantField(A::FldFunAb) -> RngIntElt
  {The degree of the exact constant field of A}
  if assigned A`dk then
    return A`dk;
  end if;
  A`dk := DegreeOfExactConstantField(A`D, A`U);
  return A`dk;
end intrinsic;

intrinsic Genus(A::FldFunAb) -> RngIntElt
  {The genus of A}
  if assigned A`g then
    return A`g;
  end if;
  A`g := Genus(A`D, A`U);
  return A`g;
end intrinsic;

intrinsic MaximalAbelianSubfield(F::FldFun: 
             Cond := false, AS := false) -> FldFunAb
  {Computes the maximal abelian subfield of simple extension F as an abelian extension}
   
  D, U := NormGroup(F:Cond := Cond, AS := AS);  
  return AbelianExtension(D, U);
end intrinsic;

intrinsic DecompositionType(A::FldFunAb, p::PlcFunElt) -> SeqEnum
  {The decomposition type of p in A as a list of pairs <f, e>}
  return DecompositionType(A`D, A`U, p);  
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOne(A::FldFunAb) -> RngIntElt
  {The number of places of degree one in A}
  if assigned A`N then
    return A`N;
  end if;
  A`N := NumberOfPlacesOfDegreeOne(A`D, A`U);
  return A`N;
end intrinsic;

intrinsic Degree(A::FldFunAb) -> RngIntElt
  {The relative degree of A}
  r, mr := RayClassGroup(A`D);
  q, mq := quo<r|A`U>;
  return #q;
end intrinsic;

intrinsic BaseField(A::FldFunAb) -> FldFunG
  {The coefficient field of A}
  return FunctionField(A`D);
end intrinsic;


function make_compatible(A, B)
  D := LCM(A`D, B`D);
  RD, mRD := RayClassGroup(D);
  RA, mRA := RayClassGroup(A`D);
  RB, mRB := RayClassGroup(B`D);
  //hA := hom<RD -> RA | [RD.i @ mRD @@ mRA : i in [1..Ngens(RD)]]>;
  //hB := hom<RD -> RB | [RD.i @ mRD @@ mRB : i in [1..Ngens(RD)]]>;
  hA := InducedMap(mRD, mRA, IdentityHomomorphism(Codomain(mRD)), D);
  hB := InducedMap(mRD, mRB, IdentityHomomorphism(Codomain(mRD)), D);
  return D, (A`U) @@ hA, (B`U) @@ hB;
end function;

intrinsic 'subset'(A::FldFunAb, B::FldFunAb) -> BoolElt
  {Tests if A is a subfield of B, for abelian extensions of the same base field}

  require BaseField(A) cmpeq BaseField(B):
    "Both fields must be defined over the same base";

  D, UA, UB := make_compatible(A, B);
  return UB subset UA;
end intrinsic

intrinsic 'eq'(A::FldFunAb, B::FldFunAb) -> BoolElt
  {Tests if A equals B, for abelian extensions of the same base field}

  require BaseField(A) cmpeq BaseField(B):
    "Both fields must be defined over the same base";

  D, UA, UB := make_compatible(A, B);
  return UB eq UA;
end intrinsic

intrinsic 'meet'(A::FldFunAb, B::FldFunAb) -> FldFunAb
  {The intersection of A and B, for abelian extensions of the same base field}

  require BaseField(A) cmpeq BaseField(B):
    "Both fields must be defined over the same base";

  D, UA, UB := make_compatible(A, B);
  return AbelianExtension(D, sub<RayClassGroup(D)| UB,  UA>);
end intrinsic

intrinsic '*'(A::FldFunAb, B::FldFunAb) -> FldFunAb
  {The compositum of A and B, for abelian extensions of the same base field}

  require BaseField(A) cmpeq BaseField(B):
    "Both fields must be defined over the same base";

  D, UA, UB := make_compatible(A, B);
  return AbelianExtension(D, UB meet UA);
end intrinsic;

//import "../../../../nonexport/package/FldFun/KUMMER_ASW.m":AS_Reduction;

function artin_schreier_witt_quotient(F, u, S)

    p := Characteristic(F);
    W := Parent(u);		// WittRing
    n := Length(W);
    vals := [];
    z := [];
    done_P := [false : i in [1 .. #S]];
    for m in [1 .. n] do
	uu := Eltseq(u);

	if uu[m] eq 0 then
	    Append(~z, 0);
	    Append(~vals, [0 : i in [1 .. #S]]);
	    continue;
	end if;

	z_P := [CoefficientField(F) | ];
	s := [];
	vals_m := [];
	for i in [1 .. #S] do
	    if done_P[i] then
		Append(~vals_m, 0);
		continue;
	    end if;
	    P := S[i];
//uu[m], Valuation(uu[m], P);
	    val, z_Pm := func<|ArtinSchreierReduction(uu[m], P)>();
//val, z_Pm;
	    //z_Pm,  val:= AS_Reduction(uu[m], P);
	    //val := -val;
	    if val ge 0 then
		//z_Pm;
		/// z_Pm may make negative valuation positive so we need to keep
		//z_Pm -:= z_Pm;
	    elif val lt 0 then
		done_P[i] := true;
	    end if;
	    if not IsZero(z_Pm) then
		Append(~s, P);
		Append(~z_P, z_Pm);
	    end if;
	    Append(~vals_m, val);
	end for;
	Append(~vals, vals_m);
	if #s gt 0 or #z_P gt 1 then
	    if p gt strong_chinese_switch then
		z_m := StrongApproximation(s, z_P, [1 : i in [1 .. #s]]);
	    else
		z_m := CRT(s, z_P, [1 : i in [1 .. #s]] : IntegralOutside := true);
	    end if;
	else 
	    z_m := Universe(z_P)!0;
	end if;
	Append(~z, z_m);
//z_P, z_m;

	w := [Parent(z_m) | 0 : i in [1 .. n]];
	w[m] := z_m;
	u -:= ArtinSchreierImage(W!w);

    end for;

    return W!z, vals, u;

end function;

function artin_schreier_witt_quotients_by_ramification(F, u, S)

    W := Parent(u);		// WittRing
    n := Length(W);
    vals := [[] : i in [0 .. n]];
    z := [[] : i in [0 .. n]];
    Sk := [[] : i in [0 .. n]];

    for i in [1 .. #S] do
	uu := u;
	P := S[i];
	l := n + 1;
	z_P := [CoefficientField(F) | ];
	vals_P := [];
	uum := Eltseq(uu);
	for m in [1 .. n] do
	    val := Valuation(uum[m], P);
	    if val lt 0 then
"AS reduction... starting with valuation", val;
		l := m;
		break;
	    end if;
	    Append(~z_P, 0);
	    if val cmpeq Infinity() then
		val := 0;
	    end if;
	    Append(~vals_P,  val);
	end for;

	for m in [l .. n] do
	    uum := Eltseq(uu);
	    val, z_Pm := ArtinSchreierReduction(F, uum[m], P);
	    //z_Pm,  val:= AS_Reduction(uum[m], P);
	    //val := -val;
	    Append(~z_P, z_Pm);
	    Append(~vals_P, val);
"valuation now: ", val;
	    if val lt 0 then
		l := m;
		z_P cat:= [0 : i in [m+1 .. n]];
		vals_P cat:= [0 : i in [m+1 .. n]];
		break;
	    end if;
	    w := [Parent(z_Pm) | 0 : i in [1 .. n]];
	    w[m] := z_Pm;
	    uu +:= ArtinSchreierImage(W!w);
	end for;

	Append(~(Sk[n+1-l+1]), P);
	Append(~(z[n+1-l+1]), z_P);
	Append(~(vals[n+1-l+1]), vals_P);
    end for;

    // both sequences with entries for each ram deg
    return z, Sk, vals;

end function;

function new_AS_Reduction(u, P, DC, t)
    rho := FunctionField(DC)!0;
    p := Characteristic(FunctionField(P));
    n := Integers()!Log(p, Degree(FunctionField(DC), FunctionField(P))) + 1;
    lambda := Valuation(u,DC);
    "Somewhere where AS reduction is happening: starting with ", lambda;
    w_DC := UniformizingElement(DC);
    assert Valuation(w_DC, DC) eq 1;              /// remove
    while (lambda lt 0) and (0 eq lambda mod p) do
	l := lambda div p;  //  l < 0!
	lr := Ceiling(l/p^(n-t-1));
	//            www := w_DC^l;
	if false then
	    w_P := func<|Parent(u)!StrongApproximation([P],[FunctionField(P)!0], [lr])>();
	else
	    w_P := UniformizingElement(P)^lr;
	end if;
	www := w_P * w_DC^(l-p^(n-t-1)*lr);
	x_1 := u +(rho^p-rho);
	x_2 := www^p;
	alpha := Lift(Root(Evaluate(x_1/x_2,DC),p),DC);
	rho := rho - alpha*www;          //- or +
	lambda_old := lambda;                          //// claus
	lambda := Valuation(u+(rho^p-rho),DC);
	"lambda now: ", lambda;                        //// claus
	if lambda_old ge lambda then                   //// claus
	"OH DEAR";                            //// claus
	Z := Integers();                             //// claus
	Z`Error := [* DC, u, t, Infty, n, P *]; /// claus
	end if;                                       //// claus
	assert lambda_old lt lambda;                 //// claus
    end while;

    return lambda, rho;
end function;

declare verbose ASW, 2;

forward asw_max_ord;

function asw_S_max_ord_pseudo_basis(F, u, S, finite, eq_ord)

    // Witt vector and tower
    u, T := Explode(u);
orig_u := u;

    W := Parent(u);
    p := Characteristic(F);
    n := Length(W);
    assert p^n eq Degree(F);

    WF := WittRing(F, n);
    // artin schreier witt generator
    alpha := [F!(T.1)];
    d := [CoefficientField(F) | Basis(eq_ord(T))[2]/T.1]; 
    C := CoefficientField(T);
    Ck := [T];

    while #alpha lt n do
	Insert(~alpha, 1, F!C.1);
	Insert(~d, 1, CoefficientField(F)!(Basis(eq_ord(C))[2]/C.1));
	Insert(~Ck, 1, C);
	C := CoefficientField(C);
    end while;
    alpha := WF!alpha;
    d_r := d[#d];
    vprint ASW, 1 : "d = ", d;

    vr := [[] : i in [0 .. n]];
    vu := [[] : i in [0 .. n]];
    // artin schreier quotient
    // sequence of sequence of valuations : 
    //		for each level in tower a sequence for each prime
    // u - (z^p - z)
    z, vals, u := func<|artin_schreier_witt_quotient(F, u, S)>();
    //assert z eq W!0;

    // better ASW generator
    if not &and[IsZero(zz) : zz in Eltseq(z)] then
	amz := func<|alpha - WF!Eltseq(z)>();
    else
	amz := alpha;
    end if;
//CoefficientField(T)!Eltseq(alpha)[1];
//"alpha = ", Eltseq(alpha)[2];
    amz := Eltseq(amz);
//CoefficientField(T)!amz[1];
//"amz = ", amz[2];
    
    Sk := [[] : i in [0 .. n]];
    rho := [];
    decomps := [];
    l := 1;

    alpha_u := [Universe(amz) | 0 : i in [0 .. n]];

    // Group the primes according to their ramification
    if by_ramification then
	DECOMP := [[] : i in [0 .. n]];
	RHO := [[] : i in [0 .. n]];
    end if;
    CT := CoefficientField(T);
    TCT := T;
    for i in [1 .. #S] do
	// vals contains 0 corresponding to unramification, -ve for ramification
	nz := n;
	for j in [1 .. n] do
	    if vals[j][i] lt 0 then
		nz := j - 1;
		break;
	    end if;
	end for;

	Append(~(Sk[n - nz + 1]), S[i]);
	//ramification degree is p^(n-nz)

	if true or nz eq n then
	    Append(~(vu[n - nz + 1]), 0);
	else
	    Append(~(vu[n - nz + 1]), vals[nz + 1][i]);
	end if;

	if nz lt n - 1 or (n eq 1 and nz eq n - 1) then
	    //min /:= p;
	    _t := Cputime();
	    if CoefficientField(T) eq FunctionField(S[i]) then
		decomp := [S[i]];
	    else
		decomp := func<|Decomposition(CT, S[i])>();
	    end if;
	    vv := [];

	    for j in [1 .. #decomp] do
//[Valuation(TrailingCoefficient(DefiningPolynomial(TCT)), dcmp) : dcmp in decomp];
		vv[j], ZZ := func<|ArtinSchreierReduction(-TrailingCoefficient(DefiningPolynomial(T)), decomp[j] : MinimumPlace := S[i])>();
		if not IsZero(ZZ) then
		    Append(~rho, ZZ);
		    Append(~decomps, decomp[j]);
		end if;
	    end for;
	    vprint ASW, 1 : "Decomp and reduce over top coeff field of tower :", Cputime(_t);

//vv;
	    assert #Seqset(vv) eq 1;
	    Append(~(vr[n-nz + 1]), Rep(vv));

	    if by_ramification then
		DECOMP[n-nz+1] cat:= decomp;
		RHO[n-nz+1] cat:= ZZ;
	    end if;
	else
	    // ram index = p
	    if n gt 1 and nz eq n - 1 then
		_, _, l := XGCD(p, -vals[nz + 1][i]);
		l := -l;
	    end if;
	    if nz lt n then
		Append(~(vr[n-nz + 1]), vals[nz + 1][i]);
	    else
		Append(~(vr[n-nz + 1]), 0);
	    end if;
	end if;

	if nz gt 0 then
	    // Make sure they are all set from the extensions below
	    for j in [1 .. nz] do
		//assert alpha_u[n - nz + 1] in {0, amz[nz]};
		alpha_u[n - j + 1] := amz[j];
	    end for;
	else 
	    assert n eq 1 or nz lt n - 1;
	end if;

    end for;

    vprint ASW, 1 : "zeta = ", z;
    vprint ASW, 2 : "alpha - zeta = ", amz;
    vprint ASW, 1 : "Sk = ", Sk;
    vprint ASW, 1 : "vals = ", vals;
    vprint ASW, 1 : "vals_ram = ", vr;

    alpha_r := Eltseq(alpha)[n];
    if by_ramification then
	alpha_r := [alpha_r : i in [0 .. n]];
    end if;
    if #decomps gt 0 then
//DECOMP;
//decomps;
//[#r : r in RHO];
//#rho;
	// Need a StrongApprox even when there is only one element to get an
	// element which is integral at all the other primes of this finiteness
	// NEED ONE rho_i using all primes BECAUSE ????  Fraatz 3, 3 wrong!
	// Something to do with how we combine the orders avoiding the +
	if by_ramification then
	for i in [1 .. #DECOMP] do
	    if #DECOMP[i] lt 1 then
		continue;
	    end if;
	    rho_i := func<|StrongApproximation(DECOMP[i], RHO[i], [1 : j in [1 .. #DECOMP[i]]])>();
	    if rho_i ne 0 then
	    TwoGenerators(DECOMP[i][1]);
	    _s, _e := Support(Divisor(rho_i));
	    [TwoGenerators(p) : p in _s], _e;
	    end if;
	    alpha_r[i] -:= F!rho_i;
	end for;
	else
	_ := MaximalOrderInfinite(RationalExtensionRepresentation(Parent(rho[1])));
	if p gt strong_chinese_switch then
	    vprint ASW, 1 : "Strong Approx: ";
	    vtime ASW, 1 : rho_i := func<|StrongApproximation(decomps, rho, [1 : i in [1 .. #decomps]])>();
	else
	    vprint ASW, 1 : "Strong Approx by Chinese Remainder : ";
	    vtime ASW, 1 : rho_i := func<|CRT(decomps, rho, [1 : i in [1 .. #decomps]] : IntegralOutside := true)>();
	end if;
	if asw_testing_checks gt 0 then
	if IsZero(rho_i) then
	    assert &and[IsZero(r) : r in rho];
	else
	zr := Zeros(rho_i);
	zp := Poles(rho_i);
	for i in [1 .. #decomps] do
	    Exclude(~zr, decomps[i]);
	    Exclude(~zp, decomps[i]);
	    assert Valuation(rho[i] - rho_i, decomps[i]) ge 1;
	end for;
	//assert #zr eq 0;
	assert &and[not IsFinite(x) : x in zp];
	end if;
	end if;
	vprint ASW, 2 : "rho_P = ", rho;
	vprint ASW, 1 : "rho = ", rho_i;
	 if asw_testing_checks gt 0 and Seqset(rho) ne {0} then
	 [TwoGenerators(p) : p in _s], _e where _s, _e := Support(Divisor(rho_i));
	 end if;
	alpha_r -:= F!rho_i;
	end if;
    end if;
    if by_ramification then 
	alpha_r := [a*d_r : a in alpha_r];
    else
	alpha_r *:= d_r;
    end if;
    alpha_rp := amz[n];//^l;
//d;
//z, vals, u;
//"Valuation(z, P) = ", [[Valuation(zz, P) : P in S] : zz in Eltseq(z)];
//[[Valuation(au, P) : P in &cat[Decomposition(F, P) : P in S]] : au in Eltseq(alpha)];
//[[Valuation(au, P) : P in &cat[Decomposition(F, P) : P in S]] : au in alpha_u];
//[[Valuation(au, P) : P in &cat[Decomposition(F, P) : P in S]] : au in amz];
//ChangeUniverse(amz, T);

    alpha_rp *:= d_r;

    abs := IsAbsoluteOrder(eq_ord(F));

    // Initialise a pseudo matrix
    pb := [];

    assert #Sk eq n + 1;
    k := [k : k in [0 .. n] |  #Sk[k+1] gt 0 ];
    min_k := Min(k);
    max_k := Max(k);
    vprint ASW, 1 : "ram deg exponents = ", k;
    // compute largest unramified basis
    unram_basis := [F | 1];
    d_unram := [[]];
    for j := n to min_k + 1 by -1 do
//Numerator(alpha_u[j], EquationOrderFinite(F));
if asw_testing_checks gt 0 then
for i in [min_k+1 .. min_k+1+n-j] do
if #Sk[i] gt 0 then
"val((alpha - zeta)_j) = ", Valuation(alpha_u[j], Decomposition(F, Sk[i][1])[1]), i;
end if;
end for;
end if;
//Denominator(alpha_u[j], EquationOrderFinite(F));
	auj := alpha_u[j]*d[#d - (j-1)];
//"val(d_j(alpha - zeta)_j) = ", Valuation(auj, Decomposition(F, S[1])[1]);
//Valuation(Numerator(auj, EquationOrderFinite(F)), Decomposition(F, S[1])[1]);
//Denominator(auj, EquationOrderFinite(F));
	ub := [Parent(auj) | 0 : i in [2 .. p-1]];
	dub := [];
	Insert(~ub, 1, 1);
	Append(~dub, <d[#d - (j-1)], 0>);
	Insert(~ub, 2, auj);
	Append(~dub, <d[#d - (j-1)], 1>);
	for i in [3 .. p] do
	    ub[i] := func<|ub[i-1]*auj>();
	    Append(~dub, <d[#d - (j-1)], i-1>);
	end for;
	// These should be in the same order with respect to x and y
//	unram_basis := func<|[x*y : x in unram_basis, y in ub]>();
	unram_basis := &cat[[unram_basis[i]*ub[j] : i in [1 .. #unram_basis]] : j in [1 .. #ub]];
//	d_unram := [Append(x, y) : x in d_unram, y in dub];
	d_unram := &cat[[Append(d_unram[i],dub[j]) : i in [1 .. #d_unram]] : j in [1 .. #dub]];
//d_unram;
//unram_basis;
    end for;

OLD := not true;
_min_k := min_k;

    repeat
	_min_k := Minimum(k);
	if not OLD then
	    min_k := Minimum(k); 	//reset for 2nd iteration
	end if;
	vprint ASW, 1 : "Loop for min_k = ", _min_k;
	for i in [0 .. p^(n-_min_k)-1] do 
	    //retrieve unram basis element
	    pow_u := unram_basis[i+1];
	    du := d_unram[i+1];
	    pow_u_pow_r := pow_u;
	    if _min_k le 1 then
		j_bound := _min_k;
	    elif OLD then
		j_bound := _min_k;
	    elif i eq 0 then
		j_bound := max_k;
	    else
		// elt of k <= n-?
		jk := [kk : kk in k | p^kk le p^n/(i+1) ];
		j_bound := Maximum(jk);
//"jb = ", j_bound;
	    end if;
	    for j in [0 .. p^j_bound-1] do
		if abs then
		    D := CoefficientField(F)!1;
		else
		    D := 1*MaximalOrder(eq_ord(CoefficientField(F)));
		end if;
		if j gt 0 then
		    if min_k le 1 then
			pow_u_pow_r *:= alpha_rp;
		    else
			pow_u_pow_r *:= alpha_r;
		    end if;
		end if;
		/*
		Need to consider 2 cases, the unramified and ram deg p primes
		and the ramified primes separately - these are the 2 iterations
		of the repeat loop
		*/
		if _min_k le 1 then
		    _k_range := [1 .. 2];
		elif OLD then
		    _k_range := [_min_k+1];
		else
		    _k_range := [3 .. n+1];
		end if;
//_k_range, j_bound;
		for _k in _k_range do
		    for kk := 1 to #Sk[_k] do 
			P := Sk[_k][kk];
			if j gt 0 then
			    vPdr := Valuation(d_r, P);
			else
			    vPdr := 0;
			end if;
			if _k le j_bound+1 then
			    vtime ASW, 2 : vPdu := &+[Integers() | du[i][2]*Valuation(du[i][1], P) : i in [1 .. #du]];
//_k, _k_range, du, vPdu;
			else
			    vPdu := 0;
			end if;

			// What do I need to compute \mu_ij?
			mu_ij := Ceiling((- j*vr[_k][kk])/p^(_k - 1)) - (vPdr*j)- vPdu;
			if abs then
			    D *:= UniformizingElement(P)^mu_ij;
			else
			    D *:= Ideal(P)^mu_ij;
			end if;
//k, kk, j, i, vPdr, mu_ij, Floor((- j*vr[_k][kk])/p^(_k - 1)) - (vPdr*j);
		    end for;
		end for;
//Valuation(D, P), Valuation(pow_u_pow_r, Decomposition(F, P)[1]);
//Valuation(Numerator(pow_u_pow_r, EquationOrderFinite(F)), Decomposition(F, P)[1]);
//Denominator(pow_u_pow_r, EquationOrderFinite(F));
		Append(~pb, <D, func<|pow_u_pow_r>()>);

	    end for;
	    vprint ASW, 1 : "Number of pseudo generators currently: ", #pb;
	end for;
	if #k eq 1 then
	    min_k := 2; // to exit the loop
	else
	    Exclude(~k, _min_k);
	end if;
    until (not OLD and min_k gt 1) or (OLD and _min_k eq max_k);

if GetVerbose("ASW") gt 1 or asw_testing_checks gt 0 then
"Valuations of ideals = ", [[Valuation(x[1], abs select P else Ideal(P)) : x in pb] : P in S];
else
vprint ASW, 2 : "pb = ", pb;
end if;
if abs then
//Factorization(Numerator(Determinant(Matrix([Eltseq(x[2]) : x in pb]))));
//Factorization(Denominator(Determinant(Matrix([Eltseq(x[2]) : x in pb]))));
//[Valuation(x, Decomposition(F, S[1])[1]) : x in Eltseq(Matrix([Eltseq(x[2]) : x in pb]))];
end if;

    return pb, Sk, alpha_r, assigned rho_i select rho_i else 0, d;

end function;

function order_from_pseudo_basis(O, pb, S)
    // Hermite the pseudo matrix

    B := BaseRing(O);
    abs := IsAbsoluteOrder(O);
    deg := Degree(O);
    finite := IsFiniteOrder(O);
    if abs then
	M := Matrix(FieldOfFractions(B), [Eltseq(pbi[2]*pbi[1]) : pbi in pb]);
	if finite then
	    den := Denominator(M);
	else
	    min_val := Minimum([Degree(Denominator(c)) - Degree(Numerator(c)) : c in Eltseq(M)]);
	    den := FieldOfFractions(B).1^(min_val);
	    den := ValuationRing(Parent(den))!(den);
	end if;
	M *:= den;
	if S cmpne false then
            vprint ASW, 1: "Pruning the prime list";
	    fden := Factorization(den);
	    den := 1;
	    for P in S do
		for ff in fden do
		    if Valuation(ff[1], P) gt 0 then
			den *:= ff[1]^ff[2];
			Exclude(~fden, ff);
		    end if;
		end for;
	    end for;
	    M := VerticalJoin(M, den*IdentityMatrix(CoefficientRing(M), deg));
	end if;
	// Put together primes of different ramification
	// fancy efficient hermite only works for finite orders so far
	// although we attempted infinite as far as we could (need quo for vring)
	if true and (finite or Nrows(M) gt deg) then
	    vprint ASW, 1 : "Hermite Form neccesary to obtain a basis: ", Nrows(M) gt deg;
	    if finite then
		l := Factorisation(SquarefreePart(den));
	    else
		l := Factorisation(den);
		assert #l eq 1;
	    end if;
            m := 1;
	    if #l eq 0 then
		H := Matrix(B, M);
	    end if;
            vtime ASW, 1: for L in l do
	      if finite then
		  m1 := func<|L[1]^(Valuation(den, L[1])+1)>();
	      else
		  m1 := func<|L[1]^(Valuation(den)+1)>();
	      end if;
              h := func<|HermiteForm(Matrix(quo<B|m1>, M))>();
              if m eq 1 then
                H := Matrix(B, h);
                m := m1;
              else
                g, e, f := Xgcd(m, m1);
                assert g eq 1;
                assert e*m + f*m1 eq 1;
                H := func<|Matrix(B, H)*m1*f+Matrix(B, h)*m*e>();
                m*:= m1;
                H := func<|Matrix(quo<B|m>, H)>();
                for i := 1 to deg do
                  g := Gcd(B!H[i][i], m);
                  e := Modinv(B!H[i][i] div g, m div g);
                  H[i] *:= e;
                end for;
                H := func<|Matrix(B, H)>();
//                assert HermiteForm(Matrix(CoefficientRing(h),H)) eq h;
              end if;
            end for;
            vprint ASW, 1: "Final HNF";
            vtime ASW, 1: H := HermiteForm(H);
//            assert H eq HermiteForm(Matrix(B, M));
            M := H;
        elif true or Nrows(M) gt deg then
	// a hermite is worth it otherwise the construction of the order is 
	// too slow
	    vprint ASW, 1 : "Hermite Form really neccesary to obtain a basis: ", Nrows(M) gt deg;
            vtime ASW, 1: M := HermiteForm(Matrix(B, M));
	end if;
	M := Submatrix(M, 1, 1, deg, deg);
	vprint ASW, 1 : "Construct order : ";
	vtime ASW, 1 : m := Order(O, Matrix(B, M), B!den : Check := asw_testing_checks gt 0);
	//Factorization(Discriminant(m));
	//Factorization(Index(m, O));
    else
	B := MaximalOrder(B);
	vprint ASW, 1 : "Construct module :";
	vtime ASW, 1 : M := Module(pb);
	if S cmpne false then
SCALE := true;
	    pm := PseudoMatrix(M);
	    den := B!!Discriminant(O);
	    if SCALE then
		pm := den*pm;
	    end if;
	    fden := Factorization(den);
//"Original den = ", fden;
	    if SCALE then
		den := 1*B;
	    end if;
	    for P in S do
		for ff in fden do
		    if Valuation(ff[1], Ideal(P)) ne 0 then
			if SCALE then
			    den *:= ff[1]^ff[2];
			else
			    den /:= ff[1]^ff[2];
			end if;
			Exclude(~fden, ff);
		    end if;
		end for;
	    end for;
//"S den = ", Factorization(den);
//pbm;
//[Factorization(x) : x in pbi];
//Factorization(ideal_S);
	    if SCALE then
		pm := VerticalJoin(pm, PseudoMatrix([den : i in [1 .. deg]], IdentityMatrix(CoefficientRing(pm), deg)));
		pm := HermiteForm(pm);
		pm *:= den^-1;
	    else
		pm := VerticalJoin(den*pm, PseudoMatrix([1*B : i in [1 .. deg]], IdentityMatrix(CoefficientRing(pm), deg)));
	    end if;
	    M := Module(pm);
	end if;
	assert Ngens(M) eq Degree(M);
	assert Degree(M) eq Degree(O);
	vprint ASW, 1 : "Construct order :";
	vtime ASW, 1 : m := func<|Order(O, M : Check := asw_testing_checks gt 0)>();
	//,Looks like this is an unnecessary expense NFBasis := #pb ne deg)>();
    end if;
    return m;
end function;

function asw_S_max_ord(F, u, S, finite, eq_ord, divisor, ret_ord)

    abs := IsAbsoluteOrder(eq_ord(F));
    _, T := Explode(u);
    assert AbsoluteDegree(F) eq AbsoluteDegree(T);
    assert #Factorization(Degree(F)) eq 1;
if asw_testing_checks gt 0 then
if abs then
time disc_eq := Discriminant(eq_ord(F));
else
time disc_eq := Discriminant(ext<MaximalOrder(CoefficientRing(eq_ord(F))) | DefiningPolynomial(eq_ord(F))>);
end if;
time fact_disc_eq_ord := Factorization(disc_eq);
    if finite then
    time MaximalOrderFinite(T);
    time disc_max := Discriminant(MaximalOrderFinite(F));
    else 
    time MaximalOrderInfinite(T);
    time disc_max := Discriminant(MaximalOrderInfinite(F));
    end if;
else
fact_disc_eq_ord := [];
disc_eq := 1;
disc_max := 1;
end if;

    if #S eq 0 then
	return eq_ord(F), [], [[] : i in [0 .. #Eltseq(u[1])]], fact_disc_eq_ord, disc_eq, disc_max;
    end if;

    deg := Degree(F);

    if finite then
	max_ord := MaximalOrderFinite;
    else
	max_ord := MaximalOrderInfinite;
    end if;

    if abs then
	CM := RSpace(FieldOfFractions(CoefficientRing(eq_ord(F))), deg);
    else
	CM := RSpace(FieldOfFractions(max_ord(CoefficientField(F))), deg);
    end if;

    m := eq_ord(F);
    vtime ASW, 1 : pb, Sk, alpha_r, rho_i, d := asw_S_max_ord_pseudo_basis(F, u, S, finite, eq_ord);
    vprint ASW, 1 : "was the time to compute basis : ";
    // This doesn't work if pb describes an order which does not contain
    // the equation order, add is needed

    pb := func<|[<x[1]/den, CM!Eltseq(num)> where num, den := IntegralSplit(x[2], eq_ord(F)) : x in pb]>();
    //pb := func<|[<x[1], CM!Eltseq(FieldOfFractions(eq_ord(F))!x[2])> : x in pb]>();

if ret_ord and asw_testing_checks gt 0 then
    m := order_from_pseudo_basis(m, pb, ret_ord select S else false);
disc_m := Discriminant(m);
try
deg_disc_eq := Degree(Discriminant(disc_eq));
catch e ""; end try;
"fact(disc(eq_ord)) = ", fact_disc_eq_ord;
try
deg_disc_m := Degree(Discriminant(disc_m));
catch e ""; end try;
time fact_disc_m := Factorization(disc_m);
"fact(disc(computed order)) = ", fact_disc_m;

try
deg_disc_max := Degree(Discriminant(disc_max));
catch e ""; end try;
"fact(disc(max_ord)) = ", Factorization(disc_max);

if assigned deg_disc_eq then
assert deg_disc_eq le deg_disc_m;
assert deg_disc_m le deg_disc_max;
end if;

assert &and[#sk eq 0 : sk in Sk[1 .. 2]] or Basis(eq_ord(F))[2] in m;

    // check maximal at places in S
    for i in [1 .. #S] do
	P := S[i];
	if abs then
	    assert Valuation(disc_m, P) le Valuation(disc_eq, P);
	    assert Valuation(disc_m, P) eq Valuation(disc_max, P);
	else
	    assert Valuation(disc_m, Ideal(P)) le Valuation(CoefficientRing(m)!!disc_eq, Ideal(P));
	    assert Valuation(disc_m, Ideal(P)) eq Valuation(disc_max, Ideal(P));
	end if;
    end for;
//[[Valuation(MaximalOrderFinite(F)!!x[1]*F!Eltseq(x[2]), Ideal(P)) : x in pb] : P in &cat[Decomposition(F, s) : s in S]];

"fact(Index) = ", Factorization(Index(m, EquationOrder(m)));
    return m, pb, Sk, fact_disc_eq_ord, disc_eq, disc_max;
end if;

    if ret_ord then
	m := order_from_pseudo_basis(m, pb, ret_ord select S else false);
    end if;

    return m, pb, Sk, fact_disc_eq_ord, disc_eq, disc_max;

end function;

function asw_max_ord(F, u, finite)

// need the Witt elt u, either stored or from the Witt tower 
// probably best to store u since it takes less space
// attribute of Witt elts, one for each component

    if finite then 
	eq_ord := EquationOrderFinite;
	max_ord := MaximalOrderFinite;
	divisor := FiniteDivisor;
    else 
	eq_ord := EquationOrderInfinite;
	max_ord := MaximalOrderInfinite;
	divisor := InfiniteDivisor;
    end if;

    S := []; exp := [];
    for uu in Eltseq(u[1]) do
	if uu eq 0 then
	    continue;
	end if;
	_S, _exp := Support(divisor(Divisor(uu)));
	S cat:= _S; exp cat:= _exp;
    end for;
    vprint ASW, 2 : S, exp;
    S := [Universe(S) | S[i] : i in [1 .. #S] | exp[i] lt 0];
    S := Setseq(Seqset(S));
    vprint ASW, 1 : "S = ", S;

    // Compute this first so we can get primes from a smaller discriminant
    m, pb, Sk, fact_disc_eq_ord, disc_eq, disc_max := asw_S_max_ord(F, u, S, finite, eq_ord, divisor, false);

    abs := IsAbsoluteOrder(eq_ord(F));
    // R_1 \subset R_2 so if either of these have been computed then
    // don't need to recompute for the unramified primes since done
    if (#Sk[1] eq 0 and #Sk[2] eq 0) then
	vprint ASW, 1 : "Compute discriminant:";
	vtime ASW, 1 : disc_m := Discriminant(m);
	if abs then
	    fd := &cat[Zeros(CoefficientField(F)!x[1]) : x in Factorization(disc_m)];
	    unram_pl := [P : P in fd | P notin S];
	else
	    disc_m := max_ord(CoefficientField(F))!!disc_m;
	    min := [x[1] : x in Factorization(Minimum(disc_m))];

	    decomp := func<|&cat[Decomposition(max_ord(CoefficientField(F)), m) : m in min]>();
	    unram_pl := [Place(P) : P in decomp | Place(P) notin S and Valuation(disc_m, P) gt 0];
	end if;
	// since these places DO NOT appear in u, zeta_P will be 0 for all so same
	// basis at all these places - so just use one
	if #unram_pl gt 0 then
	    _, pbu := asw_S_max_ord(F, u, [unram_pl[1]], finite, eq_ord, divisor, false);
	    pb cat:= pbu;
	    // maximal order computation, 3rd arg is for S-max computation
	    m := order_from_pseudo_basis(eq_ord(F), pb, false);
	elif #pb gt 0 then
	    m := order_from_pseudo_basis(m, pb, false);
	else
	    assert #S eq 0;
	end if;
    else
	m := order_from_pseudo_basis(m, pb, false);
	unram_pl := [];
    end if;

    // May need to make a new eq_ord over a maximal order if the coefficient
    // ring is not maximal and the equation order is
    if not abs and not IsMaximal(CoefficientRing(m)) then
	deg := Degree(F);
	assert #S eq 0 and #unram_pl eq 0;
	pb := [<MaximalOrder(CoefficientRing(m))!!1, b[i]> : i in [1 .. deg]] where b is Basis(m);
	// maximal order computation, 3rd arg is for S-max computation
	m := order_from_pseudo_basis(m, pb, false);
	assert IsMaximal(CoefficientRing(m));
	fact_disc_eq_ord := [];
    end if;

if asw_testing_checks gt 0 then
//What about places outside of S? Want these essentially unchanged but if
//changed then more maximal at these places

    disc_m := Discriminant(m);
    SU := S cat unram_pl;
    // check maximal at all places we considered, yes again, after the "add"
    for P in SU do
	if abs then
	    assert Valuation(disc_m, P) le Valuation(disc_eq, P);
	    assert Valuation(disc_m, P) eq Valuation(disc_max, P);
	else
	    assert Valuation(disc_m, Ideal(P)) le Valuation(CoefficientRing(m)!!disc_eq, Ideal(P));
	    assert Valuation(disc_m, Ideal(P)) eq Valuation(disc_max, Ideal(P));
	end if;
    end for;
    fact_disc_m := Factorization(Discriminant(m));
"disc(computed order) = ", fact_disc_m;
"fact(disc(max_ord)) = ", Factorization(disc_max);
//Zeros(F.1);
    for fac in fact_disc_eq_ord do
	if abs then
	if Zeros(CoefficientField(F)!fac[1])[1] notin SU then
	Valuation(disc_m, fac[1]) ne fac[2] select "VAL CHANGED AT " else "", fac[1];
	end if;
	elif Place(fac[1]) notin SU then
	Valuation(disc_m, fac[1]) ne fac[2] select "VAL CHANGED AT " else "", fac[1];
	end if;
	try
	v := Valuation(disc_m, fac[1]);
	catch e
	v := Valuation(disc_m);
	end try;
	assert v le fac[2];
    end for;

    for fac in fact_disc_m do
	if abs then
	if Zeros(CoefficientField(F)!fac[1])[1] notin SU then
	Valuation(disc_eq, fac[1]) ne fac[2] select "VAL CHANGED AT " else "", fac[1];
	end if;
	elif Place(fac[1]) notin SU then
	Valuation(disc_eq, fac[1]) ne fac[2] select "VAL CHANGED AT " else "", fac[1];
	end if;
	try
	v := Valuation(disc_eq, fac[1]);
	catch e
	v := Valuation(disc_eq);
	end try;
	assert v ge fac[2];
    end for;
end if;

    SetOrderMaximal(m, true);
    return m;

end function;

procedure asw_S_max_orders(F, u, finite)
    if finite then 
	eq_ord := EquationOrderFinite;
	divisor := FiniteDivisor;
    else 
	eq_ord := EquationOrderInfinite;
	divisor := InfiniteDivisor;
    end if;

    S := []; exp := [];
    for uu in Eltseq(u[1]) do
	if uu eq 0 then
	    continue;
	end if;
	_S, _exp := Support(divisor(Divisor(uu)));
	S cat:= _S; exp cat:= _exp;
    end for;
    vprint ASW, 2 : S, exp;
    S := [Universe(S) | S[i] : i in [1 .. #S] | exp[i] lt 0];
    S := Setseq(Seqset(S));
    vprint ASW, 1 : "S = ", S;
    //S, exp := Support(&+[divisor(Divisor(uu)) : uu in Eltseq(u[1]) | uu ne 0]);
    //S := [Universe(S) | S[i] : i in [1 .. #S] | exp[i] lt 0];

    for k in [1 .. #S] do
    for s in Setseq(Subsets(Seqset(S), k)) do
	s;
	time _ := asw_S_max_ord(F, u, Setseq(s), finite, eq_ord, divisor, true);
	/*
	try
	catch e
	    "S_max for", s, "failed";
	end try;
	*/
    end for;
    end for;
end procedure;

function maximal_order(A, finite, Al, Partial)
    F := FunctionField(A);

    //check attribute

    if finite and assigned F`MaximalOrderFinite then
	return F`MaximalOrderFinite;
    end if;

    if not finite and assigned F`MaximalOrderInfinite then
	return F`MaximalOrderInfinite;
    end if;

    DA := DiscriminantDivisor(A);
    DA := DivisorGroup(RationalExtensionRepresentation(FunctionField(DA)))!DA;
    if finite then 
	max_ord := MaximalOrderFinite;
	eq_ord := EquationOrderFinite;
	eq_ord_F := EquationOrderFinite(F);
	DA := FiniteDivisor(DA);
	I := Ideals(DA);
    else
	max_ord := MaximalOrderInfinite;
	eq_ord := EquationOrderInfinite;
	eq_ord_F := EquationOrderInfinite(F);
	DA := InfiniteDivisor(DA);
	_, I := Ideals(DA);
    end if;

    C := DefiningPolynomials(F);
    cF := CoefficientField(F);
    abs := IsAbsoluteOrder(eq_ord_F);

    p := Characteristic(F);
    // components are all cyclic extensions
    d := [];
    for i in [1 .. #C] do

	if Al eq "Round2" then
	    c := FunctionField(C[i]);
	    Embed(c, F, F.i);
	    if abs then
		time Append(~d, MaximalOrder(eq_ord(c) : Al := "Round2"));
	    else
		e := max_ord(CoefficientField(c));
		if e eq eq_ord(CoefficientField(c)) then
		    e := eq_ord(c);
		else
		    e := ext<e | DefiningPolynomial(eq_ord(c))>;
		end if;
		time Append(~d, MaximalOrder(e : Al := "Round2"));
	    end if;
	    continue;
	end if;

	deg := Degree(C[i]);
	if deg mod p ne 0 then
if not IsExport() then
"ne Kummer";
end if;
	    c := FunctionField(C[i]);
	    Embed(c, F, F.i);
	    // Kummer 
	    // check degrees or coeff rings? 
	    // These might be isomorphic but I'm not sure what the equality will do
	    PAw := Parent(A`witts[i]);
	    if PAw ne c then 
		//assert AbsoluteDegree(c) ne AbsoluteDegree(PAw);
		//assert AbsoluteDegree(c)*Degree(CoefficientField(PAw)) eq AbsoluteDegree(PAw);
		assert CoefficientField(c) ne CoefficientField(PAw);
		assert CoefficientField(c) eq CoefficientField(CoefficientField(PAw));

		/*
		eq_max := true;
		u := cF!A`witts[i][2];
		u := u*max_ord(cF);
		for P in Support(A`D) do
		    iP := Ideal(P);
		    if not IspMaximalByDedekind(eq_ord(c), iP) then
			eq_max := false;
			break;
		    end if;
		    vu := Valuation(u, iP);
		    u /:= iP^vu;
		end for;

		if eq_max then
		    fact_u := Factorization(u);
		    for P in fact_u do
			if not IspMaximalByDedekind(eq_ord(c), P) then
			    eq_max := false;
			    break;
			end if;
		    end for;
		
		    if eq_max then
			Append(~d, max_ord(c));
			continue;
		    end if;
		end if;
		*/

		ac := RationalExtensionRepresentation(CoefficientField(PAw));
		kum_abs := ext<ac | DefiningPolynomial(PAw)>;
		Embed(kum_abs, PAw, PAw.1);

		da := Basis(eq_ord(kum_abs))[2]/kum_abs.1;
		dP := Basis(eq_ord(PAw))[2]/PAw.1;

		da := RationalFunctionField(ConstantField(c))!da;
		dP := Parent(da)!dP;
		daddP := da/dP;
		
		dd := [1, daddP];
		for i in [2 .. Degree(c) - 1] do
		    Append(~dd, dd[i]*daddP);
		end for;

		// meet
		kum_abs_m := max_ord(kum_abs);
		// BUT NEED TO COERCE OVER COEFF RING PAw first!!
		pb := PseudoBasis(Module(kum_abs_m));
		RM := RModule(max_ord(CoefficientField(PAw)), Degree(PAw));
		M := Module([<max_ord(CoefficientField(PAw))!!(dd[i]*t[1]), RM!Eltseq(t[2])> where t is pb[i] : i in [1 .. #pb]]);
		PAwm := Order(eq_ord(PAw), M : Check := asw_testing_checks gt 0);
		Embed(c, PAw, A`witts[i]);
		m := PAwm meet c;
if not IsExport() then 
		//Factorization(Discriminant(m));
		assert Discriminant(m) eq Discriminant(max_ord(c));
"ne Disc check passed on meet : need to remove this!";
end if;
	    else 
		// c is kummer so use it directly
		//" c is kummer so use it directly";
		m := max_ord(c);
	    end if;
	    Append(~d, m);
	else
	    assert #Factorization(deg) eq 1;
	    assert IsDefined(A`witts, i);
	    c := UnderlyingField(A`witts[i][2], CoefficientField(A));
	    assert DefiningPolynomial(c) eq DefiningPolynomials(F)[i];
	    Embed(c, F, F.i);
	    if deg eq p then
if not IsExport() then
"ne Artin--Schreier";
end if;
		// AS
		Append(~d, max_ord(c));
	    else 
if not IsExport() then
"ne Artin--Schreier-Witt";
		// ASW?
		"MAX ORD TIME";
		//time max_ord(c);
		"ASW TIME";
end if;
		Append(~d, asw_max_ord(c, A`witts[i], finite));
	    end if;
	end if;
    end for;

    g := [F|1 ];
    B := BaseRing(eq_ord_F);
    if not abs then
	B := MaximalOrder(B);
	id := [ideal<B | 1> ];
    end if;
    for i in [1..#C] do
	o := d[i];
	g := [ i*F!o.j : i in g, j in [1..Degree(o)]];
	if not abs then
	    pm := CoefficientIdeals(o);
	    id := [ i*pm[j] : i in id, j in [1..Degree(o)]];
	end if;
    end for;

    M := KSpace(FieldOfFractions(B), Degree(F));
    if not abs then
	m := [ <id[i], M!Eltseq(FieldOfFractions(eq_ord_F)!g[i])> : i in [1..#g] ];
	vprint MaximalOrder, 2: "... done, the normal form";
	m := Module(m);
	vprint MaximalOrder, 2: "... done, the new order";
	g := func<|Order(eq_ord_F, m : Check := asw_testing_checks gt 0)>();
    else
	m := Matrix([ M!Eltseq(FieldOfFractions(eq_ord_F)!g[i]) : i in [1..#g] ]);
	M := MatrixRing(B, Degree(F));
	if finite then
	    den := Denominator(m);
	else
	    min_val := Minimum([Degree(Denominator(c)) - Degree(Numerator(c)) : c in Eltseq(m)]);
	    den := FieldOfFractions(B).1^(min_val);
	end if;
	m *:= den;
	g := func<|Order(eq_ord_F, M!m, B!den : Check := asw_testing_checks gt 0)>();
    end if;
    if #C gt 1 then
	U := Parent(Discriminant(d[1]));
	if abs then 
	    d := Gcd([U | Discriminant(i) : i in d]);
	else 
	    d := &+ [ U | Discriminant(i) : i in d];
	end if;
    end if;
if asw_testing_checks gt 0 then
"g : ";
try
Degree(Discriminant(g));
catch e
"";
end try;
Factorization(Discriminant(g));
"eq_ord(F) : ";
try
Degree(Discriminant(eq_ord(F)));
catch e
"";
end try;
Factorization(Discriminant(EquationOrder(g)));
end if;
    if #C eq 1 or (#C eq 2 and (d cmpeq 1 or not abs and d eq BaseRing(g)!1*BaseRing(g))) or (abs and B!Discriminant(g) eq B!Minimum(I) or (not abs and Discriminant(g) eq I)) then
	SetOrderMaximal(g, true);
    else
	if Partial then
	    "Failed to get the maximal order this way!\n";
	    "Disc is ", Discriminant(g);
	    "It ought to ", DA;
	    "So sqrt(index) is ", Sqrt(Discriminant(g)/I);
	    return g;
	else
	    //Discriminant(eq_ord_F);
	    //Discriminant(g);
	    g := func< | MaximalOrder(g:Discriminant := abs select B!Minimum(I) else I)>();
	end if;
    end if;
if asw_testing_checks gt 0 then
Factorization(Discriminant(g));
Factorization(Discriminant(max_ord(F)));
else 
    if finite then 
	F`MaximalOrderFinite := g;
    else
	F`MaximalOrderInfinite := g;
    end if;
end if;
    return g;

end function;

intrinsic MaximalOrderFinite(A::FldFunAb : Al := "Default", Partial := false) -> RngFunOrd
{The finite maximal order of A};
    require Al in {"Default", "Round2"} : "Parameter Al must be either \"Default\" or \"Round2\"";
    return maximal_order(A, true, Al, Partial);
end intrinsic;

intrinsic MaximalOrderInfinite(A::FldFunAb : Al := "Default", Partial := false) -> RngFunOrd
{The infinite maximal order of A};
    require Al in {"Default", "Round2"} : "Parameter Al must be either \"Default\" or \"Round2\"";
    return maximal_order(A, false, Al, Partial);
end intrinsic;

intrinsic MaximalOrderFinite(u::RngWittElt) -> RngFunOrd
{The finite maximal order of the function field defined by u (F(rho^-1(u)) where rho is the Artin--Schreier operator) as an extension of the coefficient field F of u}
    E := FunctionField(u);
    FF := UnderlyingField(E, CoefficientField(Parent(u)));
    vtime ASW, 1 : M := asw_max_ord(FF, <u, E>, true);
    return M;
end intrinsic;

intrinsic MaximalOrderInfinite(u::RngWittElt) -> RngFunOrd
{The infinite maximal order of the function field defined by u (F(rho^-1(u)) where rho is the Artin--Schreier operator) as an extension of the coefficient field F of u}
    E := FunctionField(u);
    FF := UnderlyingField(E, CoefficientField(Parent(u)));
    vtime ASW, 1 : M := asw_max_ord(FF, <u, E>, false);
    return M;
end intrinsic;

intrinsic MaximalOrders(u::RngWittElt) -> RngFunOrd
{The finite and infinite maximal orders of the function field defined by u (F(rho^-1(u)) where rho is the Artin--Schreier operator) as an extension of the coefficient field F of u}
    E := FunctionField(u);
    FF := UnderlyingField(E, CoefficientField(Parent(u)));
    vtime ASW, 1 : MF := asw_max_ord(FF, <u, E>, true);
    vtime ASW, 1 : MI := asw_max_ord(FF, <u, E>, false);
    return MF, MI;
end intrinsic;

intrinsic SMaximalOrder(u::RngWittElt, S::[PlcFunElt])->RngFunOrd
{An order of the function field defined by u (F(rho^-1(u))) where rho is the Artin-Schreier operator) as an extension of the coefficient field F of u which is maximal at all places in S};
    W := Parent(u);
    require FunctionField(Universe(S)) eq BaseRing(W) : "Arguments must share a common function field";

    E := FunctionField(u);
    FF := UnderlyingField(E, CoefficientField(W));

    fin := {IsFinite(P) : P in S};
    require #fin eq 1 : "Places in argument 2 must have same finiteness";
    fin := Rep(fin);

    eq_ord := fin select <EquationOrderFinite, FiniteDivisor> else <EquationOrderInfinite, InfiniteDivisor>;
    eq_ord, divisor := Explode(eq_ord);

    vtime ASW, 1 : M := asw_S_max_ord(FF, <u, E>, S, fin, eq_ord, divisor, true);
    return M;

end intrinsic;

/*
k<w> := GF(4);
kt<t> := PolynomialRing(k);
ktx<x> := PolynomialRing(kt);
K := FunctionField(x^3-w*t*x^2+x+t);
lp := Places(K, 2);
D := 4*lp[2]+2*lp[6];
R, mR := RayClassGroup(D);
inf := InfinitePlaces(K);
U1 := sub<R | [x@@ mR : x in inf]>;
U2 := sub<R | [5*R.i : i in [1..Ngens(R)]]>;
U3 := sub<R | U1, U2>;
A := AbelianExtension(D, U3);
SetDebugOnError(true);
MaximalOrderFinite(A);
MaximalOrderInfinite(A);
*/
