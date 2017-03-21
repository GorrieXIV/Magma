freeze;

_persum_im := function(f, mp)
    /*
    mp is a sequence of images from the finitely presented group f 
    as permutation groups. The procedure 
    constructs a homomorphic image of f as a permutation group p, which is 
    the intransitive sum of the permutation groups in the sequence mp.
    */

    l := #mp;
    if l eq 1 then
	return mp[1];
    end if;
    n := &+ [Integers() | Degree(x): x in mp];
    p := SymmetricGroup(n);
    pgens := [];

    assert forall{x: x in mp| Ngens(x) eq Ngens(f)};

    for k := 1 to Ngens(f)  do
	s := [];
	n1 := 0;
	for j := 1 to l do
	    n2 := Degree(mp[j]);
	    s cat:= Eltseq(mp[j].k);
	    for i := n1 + 1 to n1 + n2  do
		s[i] := s[i] + n1;
	    end for;
	    n1 +:= n2;
	end for;
	pgens cat:= [p ! s];
    end for;
    p := sub<p | pgens>;
    return p;
end function;

_coshom_im := function(f, hseq)
    /*
    This is a generalization of the standard function CosetImage.
    hseq is a sequence of subgroups of the finitely presented group f.
    CosetImage is called on each subgroup in hseq to produce the
    sequence mp of permutation group images of f.
    The procedure persum_im (above) is then called to construct a homomorphic
    image of f as an intransitive group p.
    */

    mp := [CosetImage(f, x): x in hseq[2]];
    p := _persum_im(f, mp);
    return p;
end function;

_coshom := function(f, hseq)
    /*
    This is a generalization of the standard function CosetAction.
    hseq is a sequence of subgroups of the finitely presented group f.
    CosetImage is called on each subgroup in hseq to produce the
    sequence mp of permutation group images of f.
    The procedure persum_im (above) is then called to construct a homomorphic
    image of f as an intransitive group p.
    The hom m:f->p is then set up.
    */

    mp := [CosetImage(f, x): x in hseq[2]];
    p := _persum_im(f, mp);
    m := hom<f->p|[p.i:i in [1..Ngens(f)]]>;
    return m, p;
end function;

intrinsic PermutationGroup(D::DB, i::RngIntElt: Representation := 1) -> GrpPerm
{Return the i-th perfect group in the database as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, i);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    P := _coshom_im(G, R[Representation]);
    return P;
end intrinsic;

intrinsic PermutationGroup(D::DB, o::RngIntElt, i::RngIntElt: Representation := 1) -> GrpPerm
{Return the i-th perfect group in the database of order o as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, o, i);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    P := _coshom_im(G, R[Representation]);
    return P;
end intrinsic;

intrinsic PermutationGroup(D::DB, top::MonStgElt: Representation := 1) -> GrpPerm
{Return the perfect group in the database named 'top' as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, top);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    P := _coshom_im(G, R[Representation]);
    return P;
end intrinsic;

intrinsic PermutationGroup(D::DB, top::MonStgElt, prime::RngIntElt, exp::RngIntElt, n::RngIntElt: Variant := 1, Representation := 1) -> GrpPerm
{Return the perfect group in the database which is 'top'#prime<exp, n>
as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, top, prime, exp, n: Variant := Variant);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    P := _coshom_im(G, R[Representation]);
    return P;
end intrinsic;

intrinsic PermutationGroup(G::GrpFP, R::<>) -> GrpPerm
{Return the permutation group image of G under the homomorphism denoted by R
(which should be an element of the sequence returned by Group(D[pfgps], ...)}
    require #R eq 2: "Argument 2 does not have two entries";
    require Type(R[2]) eq SeqEnum:
	"The second entry of argument 2 is not a sequence";
    require Universe(R[2]) cmpeq PowerStructure(GrpFP):
	"The second entry of argument 2 is not a sequence of fp groups";
    require forall{x: x in R[2] | x subset G}: "The second entry of argument 2 is not a sequence of subgroups of argument 1";
    P := _coshom_im(G, R);
    return P;
end intrinsic;

intrinsic PermutationRepresentation(D::DB, i::RngIntElt: Representation := 1) -> Map, GrpFP, GrpPerm
{An isomorphism from the i-th perfect group G in the database as a fp group
onto a representation of G as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, i);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    f, P := _coshom(G, R[Representation]);
    return f, G, P;
end intrinsic;

intrinsic PermutationRepresentation(D::DB, o::RngIntElt, i::RngIntElt: Representation := 1) -> Map, GrpFP, GrpPerm
{An isomorphism from the i-th perfect group G of order o in the database
as a fp group onto a representation of G as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, o, i);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    f, P := _coshom(G, R[Representation]);
    return f, G, P;
end intrinsic;

intrinsic PermutationRepresentation(D::DB, top::MonStgElt: Representation := 1) -> Map, GrpFP, GrpPerm
{An isomorphism from the perfect group G named 'top' as a fp group
onto a representation of G as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, top);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    f, P := _coshom(G, R[Representation]);
    return f, G, P;
end intrinsic;

intrinsic PermutationRepresentation(D::DB, top::MonStgElt, prime::RngIntElt, exp::RngIntElt, n::RngIntElt: Variant := 1, Representation := 1) -> Map, GrpFP, GrpPerm
{An isomorphism from the perfect group G which is 'top'#prime<exp, n>
as a fp group onto a representation of G as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    require Representation ge 1:
	"Parameter 'Representation' must be a positive integer";
    G, R := Group(D, top, prime, exp, n: Variant := Variant);
    require Representation le #R:
	"Only", #R, "permutation representations are available";
    f, P := _coshom(G, R[Representation]);
    return f, G, P;
end intrinsic;

intrinsic PermutationRepresentation(G::GrpFP, R::<>) -> Map, GrpPerm
{A homomorphism from G onto a permutation group P defined by R
(which should be an element of the sequence returned by Group(D[pfgps], ...)}
    require #R eq 2: "Argument 2 does not have two entries";
    require Type(R[2]) eq SeqEnum:
	"The second entry of argument 2 is not a sequence";
    require Universe(R[2]) cmpeq PowerStructure(GrpFP):
	"The second entry of argument 2 is not a sequence of fp groups";
    require forall{x: x in R[2] | x subset G}: "The second entry of argument 2 is not a sequence of subgroups of argument 1";
    f, P := _coshom(G, R);
    return f, P;
end intrinsic;

intrinsic NumberOfRepresentations(D::DB, i::RngIntElt) -> RngIntElt
{The number of available representations of the i-th perfect group in the
database as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    _, R := Group(D, i);
    return #R;
end intrinsic;

intrinsic NumberOfRepresentations(D::DB, o::RngIntElt, i::RngIntElt) -> RngIntElt
{The number of available representations of the i-th perfect group of order o
in the database as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    _, R := Group(D, o, i);
    return #R;
end intrinsic;

intrinsic NumberOfRepresentations(D::DB, top::MonStgElt) -> RngIntElt
{The number of available representations of the perfect group named 'top'
in the database as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    _, R := Group(D, top);
    return #R;
end intrinsic;

intrinsic NumberOfRepresentations(D::DB, top::MonStgElt, prime::RngIntElt, exp::RngIntElt, n::RngIntElt: Variant := 1) -> RngIntElt
{The number of available representations of the perfect group 
'top'#prime<exp, n> as a permutation group}
    require DatabaseType(D) eq "pfgps":
	"Argument 1 is not a perfect group database";
    G, R := Group(D, top, prime, exp, n: Variant := Variant);
    return #R;
end intrinsic;
