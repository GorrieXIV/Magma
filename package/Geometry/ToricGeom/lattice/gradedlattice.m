freeze;

/////////////////////////////////////////////////////////////////////////
// gradedlattice.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 23885 $
// $Date: 2009-11-04 19:45:09 +1100 (Wed, 04 Nov 2009) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for imposing gradings on a toric lattice.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// An (n+1)-dimensional graded toric lattice L is simply Z^{n+1} along
// with a lattice height function defined in terms of a primitive lattice
// vector u in the dual of L, and suitable choice of origin at height 1
// (wrt to u). Alternatively, an existing toric lattice L can have a
// grading assigned taking the direct sum Z x L.
/////////////////////////////////////////////////////////////////////////

import "../utilities/strings.m": impose_brackets;
import "lattice.m": dual_lattice_string;

declare attributes TorLat:
    origin,              // The origin of L/grading of Dual(L)
    emb_height_0,        // The embedding of the sublattice at height 0
    emb_graded_lattice;  // The embedding of L into a graded lattice

declare attributes Map:
    graded_map;          // the extension to graded lattices;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the default "origin" for the lattice (or cone) L at the given height
function default_origin(L,height)
    return (ScalarLattice().1 * height) @@ LatticeMap(Grading(L));
end function;

// Assigns the a grading to the toric lattice L. The grading and origin can
// be specified, however they naturally default to a grading on the first
// coordinate. If specified, the grading must be a lattice vector in Dual(L),
// and the origin must be an integral lattice point in L at height one w.r.t.
// the grading.
// Obviously, the origin is at height one => the "grading" vector is primitive.
// Conversely, a (primitive) grading => exists a lattice point at height one.
procedure impose_grading(L : grading:="default", origin:="default")
    // We delay assigning the data to the lattice until we know that it's
    // valid, otherwise we might leave L (or Dual(L)) in a corrupt state.
    // If the default grading is not being used, we need to check that it is
    // primitive.
    if grading cmpeq "default" then
        grading:=Dual(L).1;
    else
        valid:=true;
        if Type(grading) eq TorLatElt then
            valid:=IsInDual(grading,L);
        else
            valid,grading:=IsCoercible(Dual(L),grading);
        end if;
        error if not valid or not IsPrimitive(grading), "impose_grading: The grading must be given by a primitive vector in the dual lattice";
    end if;
    // Now we need to check that the origin is compatible with the grading
    if origin cmpeq "default" then
        origin:=ScalarLattice().1 @@ LatticeMap(grading);
    else
        valid:=true;
        if Type(origin) eq TorLatElt then
            valid:=Parent(origin) eq L;
        else
            valid,origin:=IsCoercible(L,origin);
        end if;
        error if not valid or not IsIntegral(origin) or origin * grading ne 1,
            Sprintf("impose_grading: The origin must be an integral point in the lattice at height 1 with respect to the grading %o",grading);
    end if;
    // Now we assign the grading to the lattice and its dual
    D:=Dual(L);
    D`origin:=grading;
    L`origin:=origin;   
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic GradedToricLattice(L::TorLat :
            name:="gr" cat impose_brackets(PrintName(L)),
            dual_name:=dual_lattice_string(name)) -> TorLat, Map[TorLat,TorLat]
{}
    // We assign gradings to both L and Dual(L) in one go: This is because we
    // must construct the dual (the grading lives in the dual) and we do not
    // want the lattice to change status at some point (i.e. non-graded to
    // graded).
    if not assigned L`emb_graded_lattice then
        DL:=Dual(L);
        LL,emb_Z,emb,proj_Z,proj:=DirectSum(ScalarLattice(), L : 
                                              name:=name, dual_name:=dual_name);
        LL`emb_height_0:=emb;
        LL`origin:=LL.1;
        
        DLL:=Dual(LL);
        DLL`emb_height_0:=Dual(proj);
        DLL`origin:=DLL.1;
        LL`origin`lattice_map:=Dual(emb_Z);
        DLL`origin`lattice_map:=proj_Z;
        L`emb_graded_lattice:=emb;
        DL`emb_graded_lattice:=Dual(proj);
    end if;
    return Codomain(L`emb_graded_lattice),L`emb_graded_lattice;
end intrinsic;

intrinsic GradedToricLattice(n::RngIntElt : 
            grading:=[Integers() | 1] cat [Integers() | 0 : i in[1..n]], 
            origin:="default",
            name:="Z^%d_gr",
            dual_name:=dual_lattice_string(name)) -> TorLat, Map[TorLat,TorLat]
{The direct sum of the one-dimensional toric lattice Z with L (or with Z^n) with default grading given by projection on to Z. Also gives the sublattice embedding at height zero.}
    require n ge 0: "Dimension must be nonnegative"; 
    require ExtendedType(grading) eq SeqEnum[RngIntElt] and #grading eq n + 1 : 
           Sprintf("Grading must be a sequence of integers of length %o",n + 1);
    L:=ToricLattice(n + 1 : name:=name, dual_name:=dual_name);
    impose_grading(L : grading:=Dual(L) ! grading, origin:=origin);
    require not IsZero(Grading(L)) : "Grading must be non-zero"; 
    require IsPrimitive(Grading(L)) : "Grading must be primitive";
    _,emb:=HeightZeroSublattice(L);
    return L,emb;
end intrinsic;

intrinsic IsGraded(L::TorLat) -> BoolElt
{True iff L is a graded toric lattice.}
    return assigned L`dual and assigned Dual(L)`origin;
end intrinsic;

intrinsic Grading(L::TorLat) -> TorLatElt,TorLatElt
{The grading of the toric lattice L. If L is not graded, then gives the default grading (1,0,...,0).}
    require Dimension(L) ge 1: "Lattice must be at least one-dimensional";
    if IsGraded(L) then return Dual(L)`origin; end if;
    return Dual(L).1;
end intrinsic;

intrinsic HeightZeroSublattice(L::TorLat) -> TorLat, Map[TorLat,TorLat]
{The toric sublattice at height zero in the graded lattice L, together with the embedding map}
    require IsGraded(L): "Lattice must be graded"; 
    if not assigned L`emb_height_0 then 
        emb := KernelEmbedding(Grading(L)); 
        L`emb_height_0:=emb;
    end if;
    return Domain(L`emb_height_0), L`emb_height_0;
end intrinsic;

intrinsic Graded(phi::Map[TorLat,TorLat]) -> Map[TorLat,TorLat]
{The natural extension of phi to a map of graded lattices}
    if not assigned phi`graded_map then   
        domain:=Domain(phi);
        codomain:=Codomain(phi);
        grDomain:=GradedToricLattice(domain); 
        grCodomain:=GradedToricLattice(codomain);
        M:=DefiningMatrix(phi);
        grM:=DiagonalJoin(Matrix([[1]]) , M);
        grphi:=hom<grDomain -> grCodomain| grM>;
        phi`graded_map:=grphi;
    end if;
    return phi`graded_map;
end intrinsic;
