freeze;

intrinsic IsScalarGroup(G::GrpMat) -> BoolElt
{Whether or not the group G consists entirely of scalar matrices}
    return forall{x:x in Generators(G)|IsScalar(x)};
end intrinsic;


change_base := function(G, B)
    H := sub<Generic(G)|G>;
    BSGS(G);
    GB := Base(G);
    if Type(B) eq SeqEnum then B := [* x : x in B *]; end if;
    for x in GB do Append(~B, x); end for;
    H`Base := B;
    fl, ord := HasAttribute(G, "Order");
    if fl then
	H`Order := ord;
	RandomSchreier(H:Eliminate:=false);
    end if;
    return H;
end function;

intrinsic ChangeBase(G::GrpMat, B::Tup) -> GrpMat
{}
    return change_base(G, B);
end intrinsic;

intrinsic ChangeBase(G::GrpMat, B::List) -> GrpMat
{}
    return change_base(G, B);
end intrinsic;

intrinsic ChangeBase(G::GrpMat, B::SeqEnum) -> GrpMat
{The matrix group with the same generators as G but with initial base
set to B}
    return change_base(G, B);
end intrinsic;

intrinsic JordanBlock(C::Mtrx, n::RngIntElt) -> Mtrx
{Jordan block of size n*Nrows(C)}

    d := Nrows(C);
    require d eq Ncols(C) : "matrix must be square";
    
    m := n*d;
    R := BaseRing(C);

    J := MatrixAlgebra(R,m)!0;

    InsertBlock(~J, C, 1,1 );
    for i in [2..n] do
        pos := (i-1)*d+1;
        InsertBlock(~J, C, pos,pos );
        J[pos-1,pos] := 1;
    end for;

    return J;
end intrinsic;

intrinsic JordanBlock(p::RngUPolElt, n::RngIntElt) -> Mtrx
{Jordan block of size n*Degree(p)}
    require IsIrreducible(p) : "polynomial must be irreducible";
    return JordanBlock(CompanionMatrix(p),n);
end intrinsic;

intrinsic HomogeneousBlock(p::RngUPolElt, Q::SeqEnum[RngIntElt]) -> Mtrx
{Homogeneous block with Jordan block sizes given in the sequence Q}
    require IsIrreducible(p) : "polynomial must be irreducible";
    return DiagonalJoin(< JordanBlock(p,i) : i in Sort(Q) >);
end intrinsic;


intrinsic IsHomomorphism(G::GrpMat, H::GrpMat, Q::SeqEnum[GrpMatElt]) -> BoolElt, Map
{Return the value true if the sequence Q defines a homomorphism from the group G to the group H}
    W, w := WordGroup(G);
    F, f := FPGroupStrong(G);
    sgens := [F.i@f :i in [1..Ngens(F)]];
    sgens := [g@@w: g in sgens];
    sgens := Evaluate(sgens, Q);
    S := SLPGroup(Ngens(F));
    rels := [S|LHS(r)*RHS(r)^-1:r in Relations(F)];
    rels := Evaluate(rels, sgens);
    if forall{x:x in rels|IsIdentity(x)} then
	return true, hom<G->H|Q>;
    else
	return false, _;
    end if;
end intrinsic;
