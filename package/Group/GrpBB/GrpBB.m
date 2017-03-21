freeze;
 
declare type GrpBB [GrpBBElt];

declare attributes GrpBB:
    One,
    group,
    generators,
    supergroup,
    slots;

declare type GrpBBElt;

declare attributes GrpBBElt:
    Parent,
    Element;

function BB_elt_create(B, x)
    y := New(GrpBBElt);
    if assigned B`supergroup then
	y`Parent := B`supergroup;
    else
	y`Parent := B;
    end if;
    y`Element := x;
    return y;
end function;

//
// Creation
//
intrinsic NaturalBlackBoxGroup(H::Grp) -> GrpBB
{Construct the natural blackbox group from concrete group H}
    G := New(GrpBB);
    G`group := H;
    G`One := BB_elt_create(G, One(H));
    G`generators := [G | H.i: i in [1 .. Ngens(H)]];
    return G;
end intrinsic;

//
// Printing
//
intrinsic Print(G::GrpBB, level::MonStgElt)
{}
    printf "Natural blackbox group";
    /*
    if level eq "Debug" then
	printf " (%o)", Efield(G);
    end if;
    */
    if level eq "Minimal" then
	return;
    end if;
    printf " with %o generators", Ngens(G);
    if level eq "Default" then
	return;
    end if;
    next := ": ";
    for i in [1 .. Ngens(G)] do
	printf "%o%o", next, G.i;
	next := ", ";
    end for;
end intrinsic;

intrinsic Print(x::GrpBBElt, level::MonStgElt)
{}
    printf "GrpBBElt ", x`Element;
    if IsVerbose("User5") and ISA(Type(x`Element), Mtrx) and
	    Type(CoefficientRing(x`Element)) eq FldFin then
	K := CoefficientRing(x`Element);
	rho := PrimitiveElement(K);
	q := #K;
	printf "[ ";
	next := "[ ";
	for i in [1 .. Nrows(x`Element)] do
	    for y in Eltseq(x`Element[i]) do
		if y eq 0 then
		    printf "%o0*Z(%o)", next, q;
		else
		    exp := Log(rho, y);
		    if exp eq 1 then
			printf "%oZ(%o)", next, q;
		    else
			printf "%oZ(%o)^%o", next, q, exp;
		    end if;
		end if;
		next := ", ";
	    end for;
	    next := " ], [ ";
	end for;
	printf " ] ]";
    else
	printf "%o", x`Element;
    end if;
end intrinsic;

///
/// Coercion
///
intrinsic IsCoercible(G::GrpBB, S::.) -> BoolElt, Any
{}
    if Type(S) eq GrpBBElt then
	if Parent(S) eq G then
	    return true, S;
	end if;
    elif Type(S) eq RngIntElt and S eq 1 then
	return true, G`One;
    end if;
    fl, res := IsCoercible( G`group, S);
    if fl then
	return true, BB_elt_create(G, res);
    else
	return false, "Illegal coercion.";
    end if;
end intrinsic;

///
/// Membership and Equality
///
intrinsic 'in'(x::., G::GrpBB) -> BoolElt
{}
    if Type(x) eq GrpBBElt then
	return x`Parent eq G;
    end if;
    return false;
end intrinsic;

intrinsic Parent(x::GrpBBElt) -> GrpBB
{}
    return x`Parent;
end intrinsic;

intrinsic 'eq'(G::GrpBB, H::GrpBB) -> BoolElt
{Test equality of the groups G and H}
    return G`group cmpeq H`group;
end intrinsic;

intrinsic 'eq'(x::GrpBBElt, y::GrpBBElt) -> BoolElt
{test equality of x and y}
    require Parent(x) eq Parent(y):
	"Cannot compare elements of different BB groups";
    return x`Element eq y`Element;
end intrinsic;

///
/// arithmetic operations
///

compatible := function(x, y)
    G := Parent(x);
    H := Parent(y);
    if G eq H then
	return true, G;
    end if;
    if assigned G`supergroup then
	G := G`supergroup;
    end if;
    if assigned H`supergroup then
	H := H`supergroup;
    end if;
    if G eq H then
	return true, G;
    end if;
    return false, 0;
end function;

intrinsic '*'(x::GrpBBElt, y::GrpBBElt) -> GrpBBElt
{The product of x and y}
    f, G := compatible(x, y);
    require f: "Cannot multiply elements of different BB groups";
    return BB_elt_create(G, x`Element * y`Element);
end intrinsic;

intrinsic '^'(x::GrpBBElt, n::RngIntElt) -> GrpBBElt
{the n-th power of x}
    return BB_elt_create(Parent(x), x`Element^n);
end intrinsic;

intrinsic '^'(x::GrpBBElt, y::GrpBBElt) -> GrpBBElt
{The conjugate of x by y, y^-1*x*y}
    f, G := compatible(x, y);
    require f: "Cannot conjugate elements of different BB groups";
    return BB_elt_create(G, x`Element^y`Element);
end intrinsic;

intrinsic Commutator(x::GrpBBElt, y::GrpBBElt) -> GrpBBElt
{The commutator x^-1*y^-1*x*y}
    f, G := compatible(x, y);
    require f: "Cannot commute elements of different BB groups";
    return BB_elt_create(G, (x`Element, y`Element));
end intrinsic;

///
/// i-th generator
///
intrinsic '.'(G::GrpBB, i::RngIntElt) -> GrpBBElt
{the i-th generator of G}
    requirerange i, 1, #G`generators;
    return G`generators[i];
end intrinsic;

///
/// Ngens
///
intrinsic Ngens(G::GrpBB) -> RngIntElt
{The number of generators of G}
    return #G`generators;
end intrinsic;

///
/// Generators
///
intrinsic Generators(G::GrpBB) -> SetEnum
{The generators of G}
    return {G.i: i in [1 .. Ngens(G)]};
end intrinsic;

///
/// Random
///

procedure InitPseudoRandom(G, nslots, scramble)
    n := Ngens(G);
    if n eq 0 then
	G`slots := [];
	return;
    end if;
    len := Max([nslots, n+1, 3]);
    G`slots := [G.i: i in [1 .. n]] cat [G.Random([1..n]): i in [n+1 .. len]];
v4 := GetVerbose("User4");
v3 := GetVerbose("User3");
SetVerbose("User4", false);
SetVerbose("User3", false);
    for i in [1 .. scramble] do
	_ := PseudoRandom(G);
    end for;
SetVerbose("User4", v4);
SetVerbose("User3", v3);
end procedure;

intrinsic PseudoRandom(G::GrpBB) -> GrpBBElt
{A pseudo-random element of G}
    if IsVerbose("User3") then
	print "PseudoRandom";
    end if;
    /*
    if IsVerbose("User4") and ISA(Type(One(G)`Element), Mtrx) and
	    Type(CoefficientRing(One(G)`Element)) eq FldFin then
	printf "Choose your own 'random' matrix: (y/n) ";
	read ans;
	ans := &cat Split(ans, " \t");
	if #ans gt 0 and ans[1] eq "y" or ans[1] eq "[" then
	    K := CoefficientRing(One(G)`Element);
	    rho := PrimitiveElement(K);
	    s := " ";
	    if ans[1] eq "[" then
		s cat:= ans;
	    end if;
	    while	#[i: i in [1 .. #s] | s[i] eq "["] ne
			#[i: i in [1 .. #s] | s[i] eq "]"] do
		read t;
		s cat:= t;
	    end while;
	    ss := Split(s, ",[] \n\t");
	    ss := ss[2 .. #ss];
	    cnv := function(K, x)
		if x[1] eq "0" then
		    return K!0;
		else
		    f, _, q := Regexp("^Z\\\((.*)\\\)(\\\^(.*))?$", x);
		    if #q eq 1 then
			return K ! PrimitiveElement(GF(StringToInteger(q[1])));
		    end if;
		    return K ! PrimitiveElement(GF(StringToInteger(q[1]))) ^ StringToInteger(q[3]);
		end if;
	    end function;
	    res :=  G ! G`group ! [cnv(K, x): x in ss];
	    print res;
	    return res;
	end if;
    end if;
    */
    if not assigned G`slots then
	i := Ngens(G);
	InitPseudoRandom(G, i + 2, Max(i * 10, 100));
    end if;

    len := #G`slots;
    if len eq 0 then
	return One(G);
    end if;

    i := Random([1 .. len - 1]);
    j := Random([1 .. len - 2]);
    if j ge i then
	j +:= 1;
    end if;

    G`slots[j] := G`slots[j] * G`slots[i];
    G`slots[len] := G`slots[len] * G`slots[j];

    return G`slots[len];

end intrinsic;

///
/// Underlying element (evil hack)
///
intrinsic UnderlyingElement(x::GrpBBElt) -> GrpElt
{The underlying concrete group element of x}
    return x`Element;
end intrinsic;

///
/// Subgroup
///
intrinsic Subgroup(G::GrpBB, Q::[GrpBBElt]) -> GrpBB
{Form the subgroup of G generated by the elements of Q}
    S := New(GrpBB);
    S`group := G`group;
    if assigned G`supergroup then
	S`supergroup := G`supergroup;
    else
	S`supergroup := G;
    end if;
    S`One := G`One;
    S`generators := [S | x`Element: x in Q];
    return S;
end intrinsic;

intrinsic Identity(G::GrpBB) -> GrpBBElt
{The identity element of G}
    return G`One;
end intrinsic;

intrinsic Order(x::GrpBBElt) -> RngIntElt
{The order of  the underlying element of x, if it exists}
    return Order(x`Element);
end intrinsic;
