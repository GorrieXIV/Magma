freeze;

intrinsic CharacterRing(Q::SeqEnum[Tup]) -> AlgChtr
{Create a character ring corresponding to the classes data given by the pairs in Q}
    Z := Integers();
    order := &+[Z|t[2]: t in Q];
    require forall{t: t in Q | order mod Z!t[1] eq 0}: "Element order does not divide group order";
    require forall{t: t in Q | order mod Z!t[2] eq 0 and (order div Z!t[2]) mod Z!t[1] eq 0}: "Class size does not divide group order";
    return CharacterRing(NewClasses(order, Q));
end intrinsic;

intrinsic CharacterRing(T::SeqEnum[AlgChtrElt]) -> AlgChtr
{The  character ring of the characters in T}
    return Universe(T);
end intrinsic;

intrinsic PowerMap(R::AlgChtr) -> Map
{The power map associated with R}
    fl, pm := HasAttribute(R, "PowerMap");
    if fl then return pm; end if;
    fl, G := HasAttribute(R, "Group");
    if fl then
	return PowerMap(G);
    end if;
    error "No PowerMap or Group stored in character ring";
end intrinsic;

intrinsic IntegralClasses(R::AlgChtr) -> SetEnum
{The set of numbers of the integral conjugacy classes of the group
of R}
    ncl := Nclasses(R);
    a1 := assigned R`PowerMap;
    a2 := #KnownIrreducibles(R) eq ncl;
    a3 := assigned R`Group;
    require a1 or a2 or a3 : "Unable to compute integral classes";
    if a1 or (not a2 and a3) then
	pm := PowerMap(R);
	cl := ClassesData(R);
	return {i : i in [1..ncl] | forall{j : j in [2..o-1] | 
	    GCD(o, j) ne 1 or pm(i,j) eq i} where o := cl[i,1] };
    end if;
    assert a2;
    Z := Integers();
    X := KnownIrreducibles(R);
    return {i : i in [1..ncl] | CanChangeUniverse([x[i]:x in X], Z) };
end intrinsic;

intrinsic GroupIsSoluble(R::AlgChtr) -> BoolElt
{ }
    ncl := Nclasses(R);
    a2 := #KnownIrreducibles(R) eq ncl;
    a3 := assigned R`Group;
    require  a2 or a3 : "Unable to determine solubility";

    if a3 and ISA(Type(R`Group), GrpPC) then
	return true;
    end if;

    if a2 then
	X := KnownIrreducibles(R);
	normals := { {1}, {1..ncl} };
	for x in X do
	    k := {i : i in [1..ncl] | x[i] eq x[1] };
	    if k in normals then continue; end if;
	    normals := normals join { k meet n : n in normals };
	end for;
	Exclude(~normals, {1});
	ord := 1;
	cl := ClassesData(R);
	normals := [ <n, &+[cl[i,2] : i in n]> : n in normals ];
	Sort(~normals, func<x,y|x[2]-y[2]>);
	Gord := GroupOrder(R);
	while ord lt Gord do
	    t := normals[1];
	    if IsPrimePower(t[2] div ord) then
		N := t[1];
		normals := [ s : s in normals | s[1] ne N and N subset s[1] ];
		ord := t[2];
	    else
		return false;
	    end if;
	end while;
	return true;
    end if;

    assert a3;
    return IsSoluble(R`Group);

end intrinsic;

intrinsic CharacterTable(R::AlgChtr) -> SeqEnum[AlgChtrElt]
{The full character table of the group underlying R}
    X := KnownIrreducibles(R);
    if #X eq Nclasses(R) then
	return X;
    end if;
    if assigned R`Group then
	return CharacterTable(R`Group);
    end if;
    require false : "Unable to compute character table";
end intrinsic;

intrinsic Conjugate(x::FldRatElt, k::RngIntElt) -> FldRatElt
{Return x}
    return x;
end intrinsic;

intrinsic Conjugate(x::RngIntElt, k::RngIntElt) -> FldRatElt
{Return x}
    return x;
end intrinsic;
