freeze;

/////////////////////////////////////////////////////////////////////////
// map.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 41262 $
// $Date: 2012-12-02 01:25:19 +1100 (Sun, 02 Dec 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Defines maps between toric lattices.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": subsequences_to_integers;
import "../utilities/strings.m": need_brackets, seq_to_string;
import "../polyhedron/coneembedding.m": ce_get_embedding, ce_get_origin;
import "../polyhedron/attributes.m": integral_representative;
import "lattice.m": lattice_get_Zlattice, lattice_get_Qlattice, dual_lattice_string;
import "gradedlattice.m": impose_grading;
import "point.m": index_of_sublattice;

declare attributes Map:
    toric_lattice_map,   // The map at the level of the lattice
    toric_space_map,     // The map at the level of the vector space
    matrix,              // A matrix representation of the map
    dual_map,            // The dual map. 
    kernel_embedding;    // embedding of kernel of phi.

declare attributes TorLatElt:
    lattice_map;         // If v is regarded as a grading, this is the map:
                         // Dual(Ambient(v)) -> ScalarLattice(), w -> v * w

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// True iff the cokernel of the toric lattice map defined by the given matrix 
// is torsion free
function is_cokernel_of_lattice_map_torsion_free(M)
    if Nrows(M) eq 0 or Ncols(M) eq 0 then
        return true;
    end if;
    return index_of_sublattice(M) eq 1;
end function;

// Given a Z-modules map phi: M1 -> M2, a cone C in L1 (where underlying
// Z-module of L1 is M1) and an element v in M2 returns as follows:
// * if v is contained in phi(C), then returns w in C, such that phi(w) = v
// * otherwise, returns Preimage(w,phi).
function preimage_for_module_map(v, phi, C)
    w:=Ambient(C) ! (v @@ phi);
    if w in C then
        return w;
    end if;
    kernel1:=[Ambient(C) ! (Domain(phi) ! b) : b in Basis(Kernel(phi))];
    kernel:=Cone(LinearConeGenerators(kernel1));
    Cw:=(kernel + Cone(w));
    // Note: We don't want to store this sublattice, because of the grading.
    L,emb:=Sublattice(Append(kernel1, w) : name:="Graded sublattice");
    CCw:=Cw @@ emb;
    CC:=(C @@ emb) meet CCw;
    kernel:=kernel @@ emb;
    if CC subset kernel then
        return w;
    end if;
    grading:=Representative(MinimalInequalities(CCw));
    level:=grading * (w @@ emb);
    if IsIntegral(level) then
        impose_grading(L : grading:=grading);
        P:=Polyhedron(CC : level:=level);
        emb2:=ce_get_embedding(P);
        origin:=ce_get_origin(P);
        if not IsEmpty(P) then
            rep:=integral_representative(P);
            if IsIntegral(rep) then
                return emb(emb2(rep) + origin);
            end if;
        end if;
        return w;
    end if;
    for r in RGenerators(CC) do
        prod := grading * r;
        if prod ne 0 then
            return (level / prod) * r;
        end if;
    end for;
end function;

/////////////////////////////////////////////////////////////////////////
// Related Map at the Level of the Underlying Vector Space
/////////////////////////////////////////////////////////////////////////

function lattice_map(phi)
    if not assigned phi`toric_lattice_map then
        phi`toric_lattice_map:=hom<lattice_get_Zlattice(Domain(phi)) ->
              lattice_get_Zlattice(Codomain(phi)) |
              RowSequence(DefiningMatrix(phi))>;
    end if;
    return phi`toric_lattice_map;
end function;

function space_map(phi)
    if not assigned phi`toric_space_map then
        phi`toric_space_map:=hom<lattice_get_Qlattice(Domain(phi)) ->
              lattice_get_Qlattice(Codomain(phi)) | 
              RowSequence(DefiningMatrix(phi))>;
    end if;
    return phi`toric_space_map;
end function;

function dual_lattice_map(phi)
    return lattice_map(Dual(phi));
end function;

function dual_space_map(phi)
    return space_map(Dual(phi));
end function;

/////////////////////////////////////////////////////////////////////////
// Map Creation
/////////////////////////////////////////////////////////////////////////

intrinsic HomConstr(L1::TorLat, L2::TorLat, RHS::. :
    Check := false ) -> Map
{Hom constructor for toric lattices}
    // First we manipulate our input into a standard form
    if Type(RHS) eq SeqEnum then
        if ExtendedCategory(RHS) eq SeqEnum[TorLatElt] then
            if Universe(RHS) ne L2 then
                return "Elements of sequence must lie in codomain";
            end if;
            RHS:=Matrix(RHS);
         elif ISA(ExtendedCategory(RHS), SeqEnum[SeqEnum]) then   
            bool,M:=subsequences_to_integers(RHS);
            if bool then
                RHS:=Matrix(M);
            end if;
        end if;
    end if;
    if Type(RHS) in [ModMatRngElt, ModMatFldElt, AlgMatElt] then
        n1:=Nrows(RHS);
        n2:=Ncols(RHS);
        if n1 ne Dimension(L1) or n2 ne Dimension(L2) then
            return "Dimensions of arguments do not match";
        end if;
        // Only do work if we're not in the degenerate cases
        if not (IsZero(n1) or IsZero(n2)) then
            bool,M:=subsequences_to_integers(RowSequence(Transpose(RHS)));
            if not bool then
                 return "Does not define a lattice homomorphism";
            end if;
            if Type(RHS) eq ModMatRngElt then
                matrix:=ChangeRing(Transpose(RHS),Rationals());
            else
                matrix:=ChangeRing(Matrix(M),Rationals());
            end if;
            if n1 eq n2 and not IsZero(Determinant(matrix)) then
                inv:=RowSequence(matrix^-1);
                is_inv,inv:=subsequences_to_integers(inv);
            else
                is_inv:=false;
            end if;
            matrix:=ChangeRing(Transpose(matrix),Integers());
        end if;
    else
        return "Cannot construct lattice homomorphism from arguments";
    end if;
    // Handle the degenerate cases
    if IsZero(n1) or IsZero(n2) then 
        if IsZero(n1) and IsZero(n2) then 
            phi:=map<L1->L2 | x:-> Zero(L2), y:-> Zero(L1)>;
        else
            phi:=map<L1->L2 | x:-> Zero(L2), y:-> Zero(L1)>;
        end if;
        phi`matrix:=ZeroMatrix(Integers(), n1, n2);
    else
        // Construct the map (and its inverse if it exists)
        if is_inv then
            phi:=map<L1->L2 | 
              x:-> [&+[m[j]*xx[j]:j in [1..#xx]]:m in M] where xx is Eltseq(x),
              y:-> [&+[m[j]*yy[j]:j in [1..#yy]]:m in M] where yy is Eltseq(y)>;
        else
            phi:= map<L1->L2 | 
              x:-> [&+[m[j]*xx[j]:j in [1..#xx]]:m in M] where xx is Eltseq(x)>;
        end if;
        if assigned matrix then 
            phi`matrix:=matrix;
        end if;
    end if;
    return phi;
end intrinsic;

intrinsic LatticeMap(L1::TorLat, L2::TorLat,M::ModMatRngElt)
    -> Map[TorLat,TorLat]
{Toric lattice homomorphism L1 --> L2 given by matrix M}
    require Nrows(M) eq Dimension(L1): 
       "Number of rows of the matrix must equal the dimension L1";
    require Ncols(M) eq Dimension(L2):
       "Number of columns of the matrix must equal the dimension of L2";
    return hom< L1 -> L2 | M>;
end intrinsic;

intrinsic LatticeMap(L1::TorLat, L2::TorLat, M::AlgMatElt)
    -> Map[TorLat,TorLat]
{}
    require Nrows(M) eq Dimension(L1):
       "Number of rows of the matrix must equal the dimension of L1";
    require Ncols(M) eq Dimension(L2):
       "Number of columns of the matrix must equal the dimension of L2";
    return hom< L1 -> L2 | M>;
end intrinsic;

intrinsic LatticeMap(L::TorLat, S::SeqEnum[TorLatElt]) -> Map[TorLat,TorLat]
{Toric lattice homomorphism L --> Universe(S) given by sending the standard basis for L to S}
    require not IsNull(S): "Illegal null sequence";
    require #S eq Dimension(L):
        "The number of elements in S must equal the dimension of L";
    return hom< L -> Universe(S) | S >;
end intrinsic;

intrinsic LatticeMap(v::TorLatElt) -> Map[TorLat,TorLat]
{Toric lattice map Dual(Parent(v)) --> Z given by v}
    if not assigned v`lattice_map then 
        phi := map< Dual(Parent(v)) -> ScalarLattice() | x :-> [x*v] >;
        v`lattice_map:=phi;
    end if;
    return v`lattice_map;
end intrinsic;

intrinsic Dual(phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{The toric lattice map dual to phi}
    if not assigned phi`dual_map then
        phi`dual_map:=hom< Dual(Codomain(phi)) -> Dual(Domain(phi)) |
            Transpose(DefiningMatrix(phi)) >;
        phi`dual_map`dual_map:=phi;
    end if;
    return phi`dual_map;
end intrinsic;

intrinsic IdentityMap(L::TorLat) -> Map[TorLat,TorLat]
{The trivial automorphism of the toric lattice L}
    return map< L -> L | x :-> x, y :-> y >;
end intrinsic;

intrinsic KernelEmbedding(phi::Map[TorLat,TorLat] : 
    name:="ker(" cat need_brackets(PrintName(Domain(phi))) cat " -> "
            cat need_brackets(PrintName(Codomain(phi))) cat ")",
    dual_name:=dual_lattice_string(name))
    -> Map[TorLat,TorLat]
{The toric lattice map Kernel(phi) --> Domain(phi). The kernel itself can be obtained as Domain(Kernel(phi))}
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    if not assigned phi`kernel_embedding then
       _,phi`kernel_embedding:=Sublattice(KernelBasis(phi):name:=name,dual_name:=dual_name);
    end if;
    return phi`kernel_embedding;
end intrinsic;

intrinsic KernelEmbedding(v::TorLatElt : 
    name:="ker " cat seq_to_string(Eltseq(v),"<",","),
    dual_name:=dual_lattice_string(name))
    -> Map[TorLat,TorLat]
{The toric lattice map Kernel(v) --> Dual(Parent(v)) given by the form v}
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    return KernelEmbedding(LatticeMap(v):name:=name,dual_name:=dual_name);
end intrinsic;

intrinsic ChangeBasis(v::TorLatElt) -> Map[TorLat,TorLat]
{Given a primitive form v (i.e. a point in the dual lattice), returns a change of basis of Dual(Parent(v)) such that Kernel(v) --> the standard codimension 1 lattice.}
    // Sanity check
    require IsPrimitive(v): "Argument must be a primitive lattice point.";
    // Build the change of basis matrix
    emb:=KernelEmbedding(v);
    M:=DefiningMatrix(emb);
    phi:=LatticeMap(v);
    u:=Preimage(phi,Codomain(phi).1);
    M:=VerticalJoin(M,Matrix([u]))^-1;
    // Return the map
    L:=Dual(Parent(v));
    return hom< L -> L | M >;
end intrinsic;

intrinsic ZeroMap(L1::TorLat,L2::TorLat) -> Map[TorLat,TorLat]
{The zero map L1 --> L2}
    if IsZero(Dimension(L1)) and IsZero(Dimension(L2)) then
        return map< L1 -> L2 | x :-> Zero(L2), y :-> Zero(L1) >;
    end if;
    return map< L1 -> L2 | x :-> Zero(L2) >;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Arithmetic of Maps
/////////////////////////////////////////////////////////////////////////

intrinsic '+'(phi1::Map[TorLat,TorLat], phi2::Map[TorLat,TorLat])
    -> Map[TorLat,TorLat]
{The sum of phi1 and phi2}
    require Domain(phi1) cmpeq Domain(phi2):
        "Arguments have incompatibile domains.";
    require Codomain(phi1) cmpeq Codomain(phi2):
        "Arguments have incompatibile codomains.";
    return LatticeMap(Domain(phi1), Codomain(phi1),
           DefiningMatrix(phi1) + DefiningMatrix(phi2));
end intrinsic;

intrinsic '-'(phi1::Map[TorLat,TorLat], phi2::Map[TorLat,TorLat])
    -> Map[TorLat,TorLat]
{The difference of phi1 and phi2}
    require Domain(phi1) cmpeq Domain(phi2):
        "Arguments have incompatibile domains.";
    require Codomain(phi1) cmpeq Codomain(phi2):
        "Arguments have incompatibile codomains.";
    return LatticeMap(Domain(phi1), Codomain(phi1),
           DefiningMatrix(phi1) - DefiningMatrix(phi2));
end intrinsic;

intrinsic '-'(phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{The toric lattice map -phi}
    return LatticeMap(Domain(phi), Codomain(phi), -DefiningMatrix(phi));
end intrinsic;

intrinsic '*'(n:: RngIntElt, phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{The toric lattice map n times phi}
    return LatticeMap(Domain(phi), Codomain(phi), n * DefiningMatrix(phi));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Map Equality
/////////////////////////////////////////////////////////////////////////

intrinsic 'eq' (phi1::Map[TorLat,TorLat], phi2::Map[TorLat,TorLat]) -> BoolElt
{True iff the maps are equal}
    return Domain(phi1) cmpeq Domain(phi2)
            and Codomain(phi1) cmpeq Codomain(phi2)
            and DefiningMatrix(phi1) cmpeq DefiningMatrix(phi2);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Map Attributes and Properties
/////////////////////////////////////////////////////////////////////////

intrinsic DefiningMatrix(phi::Map[TorLat, TorLat]) -> ModMatRngElt
{The defining matrix of the toric lattice map}
    if not assigned phi`matrix then 
        B:=Basis(Domain(phi));
        if IsEmpty(B) then 
            phi`matrix:=ZeroMatrix(Integers(),
                 Dimension(Domain(phi)), Dimension(Codomain(phi)));
        else
            phi`matrix:=Matrix(phi(B));
        end if;
    end if;
    return phi`matrix;
end intrinsic

intrinsic KernelBasis(phi::Map[TorLat,TorLat]) -> SeqEnum[TorLatElt]
{The basis of the kernel of the toric lattice map}
    B:=Basis(Kernel(DefiningMatrix(phi)));
    return [Domain(phi)| v : v in B];
end intrinsic;

intrinsic ImageBasis(phi::Map[TorLat,TorLat]) -> SeqEnum[TorLatElt]
{The basis of the image of the toric lattice map}
    return [Codomain(phi)! v : v in Basis(Image(DefiningMatrix(phi)))];
end intrinsic;

intrinsic IsCokernelTorsionFree(phi::Map[TorLat,TorLat]) -> BoolElt
{True iff the cokernel of the toric lattice map is torsion free}
    return is_cokernel_of_lattice_map_torsion_free(DefiningMatrix(phi));
end intrinsic;

intrinsic Expand(phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{Expansion map of the toric lattice map}
    return hom<Domain(phi) -> Codomain(phi)| DefiningMatrix(phi)>;
end intrinsic;

intrinsic IsIdentity(phi::Map[TorLat,TorLat]) -> BoolElt
{True iff the map is identity}
    return Domain(phi) cmpeq Codomain(phi) and DefiningMatrix(phi) cmpeq 
           IdentityMatrix(Integers(), Dimension(Domain(phi)));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Map Application to Points
/////////////////////////////////////////////////////////////////////////

intrinsic '*' (phi::Map[TorLat,TorLat], v::TorLatElt) -> TorLatElt
{}
    require Domain(phi) cmpeq Parent(v): "Vector must lie in the domain";
    lat_phi:=space_map(phi);
    v:=Domain(lat_phi) ! Eltseq(v);
    return Codomain(phi) ! lat_phi(v);
end intrinsic;

intrinsic '*' (phi::Map[TorLat,TorLat], S::SeqEnum) -> Map[TorLat,TorLat]
{}
    return [phi * s: s in S];
end intrinsic;

intrinsic '*' (phi::Map[TorLat,TorLat], S::SetEnum) -> Map[TorLat,TorLat]
{}
    return {phi * s : s in S};
end intrinsic;

intrinsic '*' (v::TorLatElt, phi::Map[TorLat,TorLat]) -> TorLatElt
{}
    require Codomain(phi) cmpeq Dual(Parent(v)):
        "Vector must be a form on the codomain";
    lat_phi:=dual_space_map(phi);
    v:=Domain(lat_phi) ! Eltseq(v);
    return Dual(Domain(phi)) ! lat_phi(v);
end intrinsic;

intrinsic '*' (S::SeqEnum, phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{}
    return [s * phi : s in S];
end intrinsic;

intrinsic '*' (S::SetEnum, phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{}
    return {s * phi : s in S};
end intrinsic;

intrinsic Preimage(phi::Map[TorLat,TorLat],v::TorLatElt) -> TorPol
{}
    require v in Codomain(phi): "Vector must lie in the codomain";
    return v @@ phi;
end intrinsic;

intrinsic Preimage(phi::Map[TorLat,TorLat],S::SeqEnum) -> TorPol
{}
    return [Preimage(phi,s) : s in S];
end intrinsic;

intrinsic Preimage(phi::Map[TorLat,TorLat],S::SetEnum) -> TorPol
{The preimage under the toric lattice map phi}
    return {Preimage(phi,s) : s in S};
end intrinsic;

intrinsic IsInImage(v::TorLatElt,phi::Map[TorLat,TorLat] : integral:=true)
    -> BoolElt
{True iff v=phi(w) for some w in Domain(phi). By default w must be integral. If parameter 'integral' is set to false, then w might be rational.}
    require Type(integral) eq BoolElt: "Parameter 'integral' must be a boolean";
    require v in Codomain(phi): "Vector must lie in the codomain";
    require IsIntegral(v) or not integral:
        "Vector must be integral or parameter 'integral' must be set to false";
    if integral then
        lat_phi:=lattice_map(phi);
    else 
        lat_phi:=space_map(phi);
    end if;
    v:=Codomain(lat_phi) ! Eltseq(v);
    return v in Image(lat_phi);
end intrinsic

intrinsic '@@' (v::TorLatElt,phi::Map[TorLat,TorLat]) -> TorLatElt
{}
    require v in Codomain(phi): "Vector must lie in the codomain";
    if IsIntegral(v) then
        lat_phi:=lattice_map(phi);
        v:=Codomain(lat_phi) ! Eltseq(v);
        if v in Image(lat_phi) then
            return Domain(phi) ! (v @@ lat_phi);
        end if;
    end if;
    lat_phi:=space_map(phi);
    v:=Codomain(lat_phi) ! Eltseq(v);
    require v in Image(lat_phi): "Elemement has no preimage";
    return Domain(phi) ! (v @@ lat_phi);
end intrinsic;

intrinsic '@@' (S::SeqEnum,phi::Map[TorLat,TorLat]) -> SeqEnum
{}
    return [s @@ phi : s in S];
end intrinsic;

intrinsic '@@' (S::SetEnum,phi::Map[TorLat,TorLat]) -> SeqEnum
{The preimage under the toric lattice map phi}
    return {s @@ phi : s in S};
end intrinsic;

intrinsic Image(phi::Map[TorLat,TorLat],v::TorLatElt) -> TorLatElt
{}
    require v in Domain(phi): "Vector must lie in the domain";
    lat_phi:=space_map(phi);
    v:=Domain(lat_phi) ! Eltseq(v);
    return Codomain(phi) ! lat_phi(v);
end intrinsic;

intrinsic Image(phi::Map[TorLat,TorLat],S::SeqEnum) -> SeqEnum
{}
    return [Image(phi,s) : s in S];
end intrinsic;

intrinsic Image(phi::Map[TorLat,TorLat],S::SetEnum) -> SeqEnum
{The image under the toric lattice map phi}
    return {Image(phi,s) : s in S};
end intrinsic;

intrinsic '@' (v::TorLatElt,phi::Map[TorLat,TorLat]) -> TorLatElt
{}
    require v in Domain(phi): "Vector must lie in the domain";
    return Image(phi,v);
end intrinsic;

intrinsic '@' (S::SeqEnum,phi::Map[TorLat,TorLat]) -> SeqEnum
{}
    return [s @ phi : s in S];
end intrinsic;

intrinsic '@' (S::SetEnum,phi::Map[TorLat,TorLat]) -> SeqEnum
{The image under the toric lattice map phi}
    return {s @ phi : s in S};
end intrinsic;
