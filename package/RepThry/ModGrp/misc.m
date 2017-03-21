freeze;

intrinsic OldChangeGroup(M::ModGrp, G2::Grp) -> ModGrp
{Given a G-module M, return the G2-module with the same action generators;
G2 must be isomorphic to G, with matching generators}

    G := Group(M);
    ng := Ngens(G);
    require Ngens(G2) eq ng: "Groups have different numbers of generators";

    return GModule(G2, [ActionGenerator(M, i): i in [1 .. ng]]: Check := false);

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic LiftModule(M::ModGrp, phi::Map) -> ModGrp
{Given a H-module M for some group H and a surjective group homomorphism 
phi: G -> H, return a G-module N that is the lift of M to G}

    rho := Representation(M);
    G := Domain(phi);
    G_action := [ Codomain(rho) | G.j @ phi @ rho : j in [1..Ngens(G)]];
    return GModule(G, G_action);

end intrinsic;


////////////////////////////////////////////////////////////////////

intrinsic LiftModules(Q::SeqEnum, phi::Map) -> ModGrp
{Given a sequence Q of H-modules M for some group H and a surjective 
group homomorphism phi : G -> H, return a sequence of G-modules whose 
terms are the lifts to G of the H-modules of Q}

    G := Domain(phi);
    return [ LiftModule(M, phi) : M in Q ];

end intrinsic;


////////////////////////////////////////////////////////////////////

intrinsic LiftModules(L::List, phi::Map) -> ModGrp
{Given a List L of H-modules M for some group H and a surjective 
group homomorphism phi : G -> H, return a sequence of G-modules whose 
terms are the lifts to G of the H-modules of L}

    G := Domain(phi);
    return [ LiftModule(M, phi) : M in L ];

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic GModule(l::AlgChtrElt, p::RngIntElt) -> ModGrp
{The G-module corresponding to the linear character l in characteristic p}

    if p eq 0 then return GModule(l); end if;
    require IsPrime(p): "2nd argument must be prime";
    require IsLinear(l): "1st argument must be a linear character";
    G := Group(Parent(l));
    ord := #G div KernelOrder(l);
    require ord mod p ne 0: "Not a p-modular character";
    C := Universe(Eltseq(l));
    assert ord eq CyclotomicOrder(C);
    if ord eq 1 then k := 1; else k := Modorder(p, ord); end if;
    K := GF(p, k);
    if Type(G) eq GrpPC then ngens := NPCgens(G);
    else ngens := Ngens(G); end if;
    mats := [];
    if ord eq 1 then
	for i := 1 to ngens do
	    Append(~mats, Matrix(1,1,[K|G.i@l]));
	end for;
    else
	z := PrimitiveElement(K);
	z := z ^ ((p^k-1) div ord);
	f := hom<C->K|z>;
	for i := 1 to ngens do
	    Append(~mats, Matrix(1,1,[G.i@l@f]));
	end for;
    end if;
    return GModule(G, mats);
end intrinsic;



