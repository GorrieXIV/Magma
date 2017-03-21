freeze;

/////////////////////////////////////////////////////////////////////////
// lattice.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Describes the underlying lattice in which the toric constructions
// take place.
/////////////////////////////////////////////////////////////////////////

import "../polyhedron/newton.m": newton_clear_cache;
import "../utilities/strings.m": seq_to_string, need_brackets, remove_brackets, impose_brackets, cross_prod_string;
import "point.m": change_lattice_point_parent, row_matrix_to_lattice_vector;
import "map.m": is_cokernel_of_lattice_map_torsion_free;

declare type TorLat[TorLatElt];
declare attributes TorLat:
    id,             // The unique identifying number of the lattice L
    dim,            // The dimension of the lattice L
    name,           // The name assigned to this lattice (for printing)
    dual,           // The dual Hom(L,\Z), if assigned, otherwise the name
    emb_maps,       // Any embedding maps
    proj_maps,      // Any projection maps
    summands,       // If L is a direct sum, contains the summands
    sublattice,     // If LL is a sublattice of L, contains LL
    suplattice,     // If L is a sublattice of LL, contains LL
    coverlattice,   // If L is a quotient of LL, contains LL
    zero,           // The zero element of the lattice L
    zero_cone,      // The zero cone in L
    zero_fan,       // The zero fan in L
    empty_polytope, // The empty polyhedron in L
    lattice_cache;  // A cache of "offspring" lattices

/////////////////////////////////////////////////////////////////////////
// Data Store
/////////////////////////////////////////////////////////////////////////

// The store for the toric lattice caches. Do not use directly!
toric_lattice_store:=NewStore();

intrinsic CacheClearToricLattice()
{Clear the internal toric lattice cache}
    // Clear the cache of Newton polytopes
    newton_clear_cache();
    // We need to save and restore the id, otherwise horrific things might
    // happen
    bool,id:=StoreIsDefined(toric_lattice_store,"id");
    StoreClear(toric_lattice_store);
    if bool then
        StoreSet(toric_lattice_store,"id",id);
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Returns true if defining matricies of the given sequence of lattice maps
// equals the given sequence of matrices.
function lattice_maps_equal_matrices(maps,mats)
    if Type(maps) eq SeqEnum then
        if #maps eq #mats then
            for i in [1..#maps] do
                if not DefiningMatrix(maps[i]) cmpeq mats[i] then
                    return false;
                end if;
            end for;
            return true;
        end if;
    elif #mats eq 1 then
        return DefiningMatrix(maps) cmpeq mats[1];
    end if;
    return false;
end function;

// Returns the lattice's private cache
function get_lattice_cache(L)
    if not assigned L`lattice_cache then
        L`lattice_cache:={PowerStructure(TorLat)|};
    end if;
    return L`lattice_cache;
end function;

// Adds the lattice LL to the private cache of L
procedure add_to_lattice_cache(L,LL)
    if assigned L`lattice_cache then
        Include(~L`lattice_cache,LL);
    else
        L`lattice_cache:={PowerStructure(TorLat)|LL};
    end if;
end procedure;

// Returns a ZZ-module of the given dimension
function lattice_get_Zlattice_of_dim(n)
    bool,z_cache:=StoreIsDefined(toric_lattice_store,"Z module cache");
    if not bool then
        z_cache:=[];
    end if;
    if not IsDefined(z_cache,n+1) then
        z_cache[n+1]:=RModule(Integers(),n);
        StoreSet(toric_lattice_store,"Z module cache",z_cache);
    end if;
    return z_cache[n+1];
end function;

// Returns the underlying ZZ-module
function lattice_get_Zlattice(L)
    return lattice_get_Zlattice_of_dim(Dimension(L));
end function;

// Returns the underlying QQ-module
function lattice_get_Qlattice(L)
    n:=Dimension(L);
    bool,vs_cache:=StoreIsDefined(toric_lattice_store,"Vectorspace cache");
    if not bool then
        vs_cache:=[];
    end if;
    if not IsDefined(vs_cache,n+1) then
        vs_cache[n+1]:=RModule(Rationals(),n);
        StoreSet(toric_lattice_store,"Vectorspace cache",vs_cache);
    end if;
    return vs_cache[n+1];
end function;

// Sets the print name of the lattice L and its dual.
// Any occurance of "%d" will be replaced with the dimension of the lattice.
// Think before using this function! Names are an important part of what
// defines a toric lattice uniquely.
procedure assign_lattice_names(L,name,dual_name)
    // First substitute any occurance of "%d" for the dimension
    dim:=IntegerToString(Dimension(L));
    name:=SubstituteString(name,"%d",dim);
    dual_name:=SubstituteString(dual_name,"%d",dim);
    // Now change the names
    L`name:=name;
    if not assigned L`dual or Type(L`dual) eq MonStgElt then
        L`dual:=dual_name;
    else
        D:=Dual(L);
        D`name:=dual_name;
    end if;
end procedure;

// Given a sequence of sequences S, returns the dimension of the first element
// of S, or 0 if it is empty
function seq_dim(S)
    return #S eq 0 select 0 else #Representative(S);
end function;

// Returns the string describing L^n
function lattice_n_times_name(L,n)
    if n eq 1 then
        return PrintName(L);
    else
        return need_brackets(PrintName(L)) cat "^" cat IntegerToString(n);
    end if;
end function;

// Returns the default n-dimensional lattice name
function default_lattice_name(n)
    return n eq 1 select "Z" else "Z^" cat IntegerToString(n);
end function;

// Returns a string <v1,v2,...,vn> for all non-integral vectors in S.
// The string is truncated as illustrated above to show only three vectors.
// Does not make any attempt to remove vectors that would be redundant in the
// span.
function span_string_of_nonintegral_vectors(S)
    S:=[Universe(S) | v : v in S | not IsIntegral(v)];
    if not IsEmpty(S) then
        if #S eq 1 then
            str:=seq_to_string(Eltseq(S[1]`row_matrix),"<",",");
        elif #S eq 2 then
            str:=Sprintf("<%o, %o>",S[1],S[2]);
        elif #S eq 3 then
            str:=Sprintf("<%o, %o, %o>",S[1],S[2],S[3]);
        else
            str:=Sprintf("<%o, %o, ..., %o>",S[1],S[2],S[#S]);
        end if;
    else
        str:="< >";
    end if;
    return str;
end function;

// Adds "^*" to the given string. Does this intelligently, so that e.g. (N^*)^*
// will simply be returned as N.
function dual_lattice_string(S)
    error if Type(S) ne MonStgElt,"dual_lattice_string: Input must be a string";
    if #S gt 2 and S[#S-1] eq "^" and S[#S] eq "*" then
        return remove_brackets(S[1..#S-2]);
    end if;
    return need_brackets(S) cat "^*";
end function;

// Allocates the memory for a new toric lattice
function new_toric_lattice()
    bool,id:=StoreIsDefined(toric_lattice_store,"id");
    if not bool then id:=0; end if;
    L:=New(TorLat);
    L`id:=id;
    StoreSet(toric_lattice_store,"id",id + 1);
    return L;
end function;

// Returns the cached n-dimensional toric lattice
function lattice_from_cache(n)
    bool,lattice_cache:=StoreIsDefined(toric_lattice_store,"lattice cache");
    if not bool then
        lattice_cache:=[PowerStructure(TorLat)|];
    end if;
    if not IsDefined(lattice_cache,n+1) then
        // Create a new n-dimensional toric lattice
        name:=default_lattice_name(n);
        dual_name:=dual_lattice_string(name);
        L:=new_toric_lattice();
        L`dim:=n;
        assign_lattice_names(L,name,dual_name);
        lattice_cache[n+1]:=L;
        StoreSet(toric_lattice_store,"lattice cache",lattice_cache);
    end if;
    return lattice_cache[n+1];
end function;

// Returns a copy of the given toric lattice, along with the trivial isomorphism
// from L to the copy.
function copy_lattice(L : name:=PrintName(L), dual_name:=DualPrintName(L))
    LL:=ToricLattice(Dimension(L) : name:=name, dual_name:=dual_name);
    iso:=hom<L -> LL | IdentityMatrix(Rationals(),Dimension(L))>;
    if assigned L`emb_maps then
        if Type(L`emb_maps) eq SeqEnum then
            LL`emb_maps:=[emb * iso : emb in L`emb_maps];
        else
            LL`emb_maps:=L`emb_maps * iso;
        end if;
    end if;
    if assigned L`proj_maps then
        inv:=iso^-1;
        if Type(L`proj_maps) eq SeqEnum then
            LL`proj_maps:=[inv * proj : proj in L`proj_maps];
        else
            LL`proj_maps:=inv * L`proj_maps;
        end if;
    end if;
    if assigned L`summands then
        LL`summands:=L`summands; end if;
    if assigned L`sublattice then
        LL`sublattice:=L`sublattice; end if;
    if assigned L`suplattice then
        LL`suplattice:=L`suplattice; end if;
    if assigned L`coverlattice then
        LL`coverlattice:=L`coverlattice; end if;
    return LL,iso;
end function;

// Returns true iff the duals for every lattice in the sequence S are already
// known. If so, also returns the sequence of duals.
function dual_known_for_sequence(S)
    SS:=[PowerStructure(TorLat)|];
    for L in S do
        if Type(L`dual) eq TorLat then
            Append(~SS,Dual(L));
        else
            return false,_;
        end if;
    end for;
    return true,SS;
end function;

// Returns true iff the described direct sum is already known. If so,
// also returns the cached direct sum.
function direct_sum_known_to_lattice(L,S,name,dual_name)
    // First look in L's cache
    for LL in get_lattice_cache(L) do
        if IsDirectSum(LL) and PrintName(LL) eq name and
          DualPrintName(LL) eq dual_name and Summands(LL) eq S then
            return true,LL;
        end if;
    end for;
    // It's possible that the dual is known
    bool,S:=dual_known_for_sequence(S);
    if bool then
        for LL in get_lattice_cache(Dual(L)) do
            if IsDirectSum(LL) and PrintName(LL) eq dual_name and
              DualPrintName(LL) eq name and Summands(LL) eq S then
                return true,Dual(LL);
            end if;
        end for;
    end if;
    return false,_;
end function;

// Returns true iff the described sublattice is already known. If so,
// also returns the cached sublattice.
function sublattice_known_to_lattice(L,dim,mtrx_emb,name,dual_name)
    // First check in L's cache
    for LL in get_lattice_cache(L) do
        if IsSublattice(LL) and PrintName(LL) eq name and
          DualPrintName(LL) eq dual_name then
            sup,emb:=Superlattice(LL);
            if sup eq L and DefiningMatrix(emb) cmpeq mtrx_emb then
                return true,LL;
            end if;
        end if;
    end for;
    // It's possible that the dual is known
    if Type(L`dual) eq TorLat then
        mtrx:=Transpose(mtrx_emb);
        D:=Dual(L);
        // How can the dual be realised? Are they of equal dimension?
        if Dimension(L) eq dim then
            for LL in get_lattice_cache(D) do
                if IsSuperlattice(LL) and PrintName(LL) eq dual_name and
                  DualPrintName(LL) eq name then
                    sub,emb:=Sublattice(LL);
                    if sub eq D and DefiningMatrix(emb) cmpeq mtrx then
                        return true,Dual(LL);
                    end if;
                end if;
            end for;
        end if;
        // Can is be as a quotient?
        if is_cokernel_of_lattice_map_torsion_free(mtrx_emb) then
            for LL in get_lattice_cache(D) do
                if IsQuotient(LL) and PrintName(LL) eq dual_name and
                  DualPrintName(LL) eq name then
                    cover,proj:=Coverlattice(LL);
                    if cover eq D and DefiningMatrix(proj) cmpeq mtrx then
                        return true,Dual(LL);
                    end if;
                end if;
            end for;
        end if;
    end if;
    return false,_;
end function;

// Returns true iff the described superlattice is already known. If so,
// also returns the cached superlattice.
function superlattice_known_to_lattice(L,mtrx_emb,name,dual_name)
    // First check in L's cache
    for LL in get_lattice_cache(L) do
        if IsSuperlattice(LL) and PrintName(LL) eq name and
          DualPrintName(LL) eq dual_name then
            sub,emb:=Sublattice(LL);
            if sub eq L and DefiningMatrix(emb) cmpeq mtrx_emb then
                return true,LL;
            end if;
        end if;
    end for;
    // It's possible that the dual is known
    if Type(L`dual) eq TorLat then
        L:=Dual(L);
        mtrx_emb:=Transpose(mtrx_emb);
        for LL in get_lattice_cache(L) do
            if IsSublattice(LL) and PrintName(LL) eq dual_name and
              DualPrintName(LL) eq name then
                sup,emb:=Superlattice(LL);
                if sup eq L and DefiningMatrix(emb) cmpeq mtrx_emb then
                    return true,Dual(LL);
                end if;
            end if;
        end for;
    end if;
    return false,_;
end function;

// Returns true iff the described quotient is already known. If so,
// also returns the cached quotient.
function quotient_known_to_lattice(L,mtrx_proj,name,dual_name)
    // First check in L's cache
    for LL in get_lattice_cache(L) do
        if IsQuotient(LL) and PrintName(LL) eq name and
          DualPrintName(LL) eq dual_name then
            cover,proj:=Coverlattice(LL);
            if cover eq L and DefiningMatrix(proj) cmpeq mtrx_proj then
                return true,LL;
            end if;
        end if;
    end for;
    // It's possible that the dual is known
    if Type(L`dual) eq TorLat then
        L:=Dual(L);
        mtrx_emb:=Transpose(mtrx_proj);
        for LL in get_lattice_cache(L) do
            if IsSublattice(LL) and PrintName(LL) eq dual_name and
              DualPrintName(LL) eq name then
                sup,emb:=Superlattice(LL);
                if sup eq L and DefiningMatrix(emb) cmpeq mtrx_emb then
                    return true,Dual(LL);
                end if;
            end if;
        end for;
    end if;
    return false,_;
end function;

// Returns the direct sum of the given lattices S
// Set 'check_cache' to false to avoid checking the cache -- avoid infinite
// loops!
function lattice_direct_sum(S,name,dual_name : check_cache:=true)
    // Handle the stupid cases first
    len:=#S;
    if len eq 0 then
        // THINK: Don't want to do this really
        L:=lattice_from_cache(0);
        return L,[Maps(L,L)|],[Maps(L,L)|];
    elif len eq 1 then
        return L, [phi], [phi] where phi is IdentityMap(L) where L is Representative(S) ;
    end if;
    // Is this already known?
    if check_cache then
        bool,L:=direct_sum_known_to_lattice(S[1],S,name,dual_name);
    else
        bool:=false;
    end if;
    if not bool then
        // Create the embeddings and projections
        sumlat,embs,projs:=DirectSum([lattice_get_Zlattice(LL):LL in S]);
        // Create the new direct sum
        L:=new_toric_lattice();
        L`dim:=Dimension(sumlat);
        assign_lattice_names(L,name,dual_name);
        // Record the summands, embeddings and projections
        L`summands:=S;
        mtrx_embs:=[*Matrix(embs[i](Basis(lattice_get_Zlattice(S[i])))):
                                                        i in [1..len]*];
        mtrx_projs:=[*Matrix(proj(Basis(sumlat))) : proj in projs*];
        L`emb_maps:=[LatticeMap(S[i],L,mtrx_embs[i]):i in [1..len]];
        L`proj_maps:=[LatticeMap(L,S[i],mtrx_projs[i]):i in [1..len]];
        if #S eq 2 then
		L`proj_maps[1]`kernel_embedding:=L`emb_maps[2];
                L`proj_maps[2]`kernel_embedding:=L`emb_maps[1];
        end if;
        // Add this direct sum to the cache
        add_to_lattice_cache(S[1],L);
    end if;
    return L,L`emb_maps,L`proj_maps;
end function;

// Attaches the lattice and it's dual together
procedure lattice_attach_dual(L,M)
    L`dual:=M;
    M`dual:=L;
end procedure;

// Creates the dual if the lattice L was created as a direct sum
procedure dual_lattice_direct_sum(L,name,dual_name)
    Ms:=[PowerStructure(TorLat)|Dual(Ls):Ls in L`summands];
    M:=lattice_direct_sum(Ms,name,dual_name : check_cache:=false);
    lattice_attach_dual(L,M);
    for i in [1..#Ms] do
	    M`emb_maps[i]`dual_map:=L`proj_maps[i];
            M`proj_maps[i]`dual_map:=L`emb_maps[i];
	    L`emb_maps[i]`dual_map:=M`proj_maps[i];
            L`proj_maps[i]`dual_map:=M`emb_maps[i];
    end for;
    if #Ms eq 2 then
            M`proj_maps[1]`kernel_embedding:=M`emb_maps[2];
            M`proj_maps[2]`kernel_embedding:=M`emb_maps[1];
    end if;
end procedure;

// Create the dual if the lattice L was created as a superlattice
procedure dual_lattice_superlattice(L,name,dual_name)
    M:=ToricLattice(Dimension(L):name:=name,dual_name:=dual_name);
    // We have to be a little careful before calling Dual(map),
    // since this will call Dual(lattice) and can lead to an
    // infinite loop. So first we tie in the duals.
    lattice_attach_dual(L,M);
    M`emb_maps:=Dual(L`emb_maps);
    M`suplattice:=Dual(L`sublattice);
end procedure;

// Create the dual if the lattice L was created as a sublattice of LL
procedure dual_lattice_sublattice(L,name,dual_name)
    LL:=L`suplattice;
    emb:=L`emb_maps;
    M:=ToricLattice(Dimension(L):name:=name,dual_name:=dual_name);
    lattice_attach_dual(L,M);
    if Dimension(L) eq Dimension(LL) then
        // If they are of equal dimension, this is easy
        M`emb_maps:=Dual(emb);
        M`sublattice:=Dual(LL);
    end if;
    if IsCokernelTorsionFree(emb) then
        // Can we realise the dual as a quotient?
        M`proj_maps:=Dual(emb);
        M`coverlattice:=Dual(LL);
    end if;
end procedure;

// Create the dual if the lattice L was create as a quotient of LL
procedure dual_lattice_quotientlattice(L,name,dual_name)
    M:=ToricLattice(Dimension(L):name:=name,dual_name:=dual_name);
    lattice_attach_dual(L,M);
    M`emb_maps:=Dual(L`proj_maps);
    M`suplattice:=Dual(L`coverlattice);
end procedure;

// Create the dual if the lattice L comes with no baggage
procedure dual_lattice_default(L,name,dual_name)
    M:=ToricLattice(Dimension(L) : name:=name,dual_name:=dual_name);
    lattice_attach_dual(L,M);
end procedure;

/////////////////////////////////////////////////////////////////////////
// Printing and Hash Value
/////////////////////////////////////////////////////////////////////////

intrinsic PrintNamed(L::TorLat,level::MonStgElt,name::MonStgElt)
{The toric lattice description}
    printf "%o-dimensional ", Dimension(L);
    if IsGraded(L) then
       printf "graded ";
    end if;
    if name eq "$" then
        printf "toric lattice %o", PrintName(L);
    else
        printf "toric lattice %o = %o", name, PrintName(L);
    end if;
    if IsGraded(L) then
       printf " with grading %o", Grading(L);
    end if;
end intrinsic;

intrinsic Hash(L::TorLat) -> RngIntElt
{The hash value for the toric lattice}
    return L`id;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Membership, Coercion, and Maps
/////////////////////////////////////////////////////////////////////////

intrinsic 'in'(S::., L::TorLat) -> BoolElt
{Is S an element of the lattice L}
    return Type(S) eq TorLatElt and Parent(S) eq L;
end intrinsic;

intrinsic IsCoercible(L::TorLat,v::.) -> BoolElt,TorLatElt
{Can the object be coerced into the lattice L}
    type:=ExtendedCategory(v);
    if ISA(type,TorLatElt) then
        if Parent(v) eq L then
            return true, v;
        elif Dimension(Parent(v)) eq Dimension(L) then
            return true, change_lattice_point_parent(v,L);
        end if;
    elif (ISA(type, RngIntElt) or ISA(type, FldRatElt)) and IsZero(v) then
        return true, LatticeVector(L,[Integers()|0 : i in [1..Dimension(L)]]);
    elif type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt] then
        if #v eq Dimension(L) then
            return true, LatticeVector(L,v);
        end if;
    elif Type(v) eq Mtrx then
        if (CoefficientRing(v) cmpeq Integers() or
            CoefficientRing(v) cmpeq Rationals()) and NumberOfRows(v) eq 1 and
            NumberOfColumns(v) eq Dimension(L) then
            return true, row_matrix_to_lattice_vector(L,v);
        end if;
    elif Type(v) eq LatElt or Type(v) eq ModFldElt or Type(v) eq ModEDElt or
         Type(v) eq ModTupRngElt or Type(v) eq ModTupFldElt then
        v:=Eltseq(v);
        type:=ExtendedCategory(v);
        if (type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt])
                                        and #v eq Dimension(L) then
            return true, LatticeVector(L,v);
        end if;
    end if;
    return false, "Illegal coercion";
end intrinsic;

intrinsic SubConstr(L::TorLat, RHS::. : Check := false )
    -> TorLat, Map
{Sub constructor for lattices.}
    if ExtendedCategory(RHS) eq SeqEnum[TorLatElt] and Universe(RHS) eq L then
        LL, emb:=Sublattice(RHS);
        return LL, emb;
    else
        return "error message", _;
    end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// Equality and Basis
///////////////////////////////////////////////////////////////////////

intrinsic 'eq' (L1::TorLat, L2::TorLat) -> BoolElt
{True iff the two toric lattices equivalent}
    return L1`id eq L2`id;
end intrinsic;

intrinsic '.'(L::TorLat, i::RngIntElt) -> TorLatElt
{The i-th element of the standard basis of the toric lattice L}
    d:=Dimension(L);
    require i ge 1 and i le d:
        Sprintf("Value for basis element should be in the range [1..%o]",d);
    return Basis(L)[i];
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////////////////////////

intrinsic ToricLattice(n::RngIntElt:
                       name:=default_lattice_name(n),
                       dual_name:=dual_lattice_string(name) ) -> TorLat
{A toric lattice of dimension n.}
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    require n ge 0: "The dimension must be non-negative";
    L:=new_toric_lattice();
    L`dim:=n;
    assign_lattice_names(L,name,dual_name);
    return L;
end intrinsic;

intrinsic ToricLattice(S::SeqEnum[SeqEnum[RngIntElt]]:
              name:="sub" cat impose_brackets(default_lattice_name(seq_dim(S))),
              dual_name:=dual_lattice_string(name))
              -> TorLat, Map[TorLat,TorLat]
{The toric sublattice generated by the sequence S of sequences of integers, together with the embedding map to the toric lattice Z^n.}
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
                                "Parameter 'dual_name' should be a string";
    if #S ne 0 then
        dim:=#Representative(S);
        require &and[#v eq dim : v in S]:
                               "The vectors must be of the same dimension";
    else
        dim:=0;
    end if;
    L:=lattice_from_cache(dim);
    LL,emb:=Sublattice([L | v : v in S] : name:=name,dual_name:=dual_name);
    return LL,emb;
end intrinsic;

intrinsic ScalarLattice() -> TorLat
{The one dimensional toric lattice of scalars}
    bool,scalar_lattice:=StoreIsDefined(toric_lattice_store,"Scalar lattice");
    if not bool then
        name:="Z";
        dual_name:="Z";
        scalar_lattice:=new_toric_lattice();
        scalar_lattice`dim:=1;
        assign_lattice_names(scalar_lattice,name,dual_name);
        scalar_lattice`dual:=scalar_lattice;
        StoreSet(toric_lattice_store,"Scalar lattice",scalar_lattice);
    end if;
    return scalar_lattice;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Direct Sums, Quotients, Sublattices, and Superlattices
/////////////////////////////////////////////////////////////////////////

intrinsic '+'(L1::TorLat, L2::TorLat) -> TorLat
{The direct sum of L1 and L2}
    return DirectSum(L1,L2);
end intrinsic;

intrinsic DirectSum(L1::TorLat, L2::TorLat :
    name:=need_brackets(PrintName(L1)) cat " x "
            cat need_brackets(PrintName(L2)),
    dual_name:=dual_lattice_string(name))
    -> TorLat, Map[TorLat,TorLat], Map[TorLat,TorLat], Map[TorLat,TorLat],
            Map[TorLat,TorLat]
{The direct sum of L1 and L2, together with the following natural maps: the embedding of L1, the embedding of L2, the projection onto L1, and the projection onto L2.}
    L,embs,projs:=DirectSum([L1,L2]:name:=name,dual_name:=dual_name);
    return L,embs[1],embs[2],projs[1],projs[2];
end intrinsic;

intrinsic DirectSum(S::[TorLat] :
    name:=cross_prod_string([PowerStructure(MonStgElt)|PrintName(L) : L in S]),
    dual_name:=dual_lattice_string(name))
    -> TorLat, SeqEnum[Map[TorLat,TorLat]], SeqEnum[Map[TorLat,TorLat]]
{The direct sum of the lattices in S, together with the following sequences of natural maps: the embeddings of lattices in S, and the projections onto lattices in S.}
    require not IsNull(S): "Illegal null sequence";
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    L,emb_maps,proj_maps:=lattice_direct_sum(S,name,dual_name);
    return L,emb_maps,proj_maps;
end intrinsic;

intrinsic '^'(L::TorLat, n::RngIntElt :
    name:=lattice_n_times_name(L,n),dual_name:=dual_lattice_string(name))
    -> TorLat,SeqEnum[Map[TorLat,TorLat]],SeqEnum[Map[TorLat,TorLat]]
{The direct sum of n copies of the lattice L, together with the following sequences of natural maps: the embeddings of the components, the projections onto the components.}
    // Is there anything to do?
    if n eq 1 then
            return L, IdentityMap(L);
    end if;
    // Construct the appropriate direct sum
    LL,maps_embs,maps_projs:=DirectSum([PowerStructure(TorLat) |
                    L : i in [1..n]] : name:=name,dual_name:=dual_name);
    return LL,maps_embs,maps_projs;
end intrinsic;

intrinsic Sublattice(S::SetEnum[TorLatElt] : name:=false, dual_name:=false )
    -> TorLat, Map[TorLat,TorLat]
{}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:="sub" cat impose_brackets(PrintName(Universe(S)));
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Check that the vectors are integral
    require IsIntegral(S): "Vectors must be integral";
    // Return the sublattice and its embedding
    LL,emb:=Sublattice(SetToSequence(S) : name:=name, dual_name:=dual_name);
    return LL,emb;
end intrinsic;

intrinsic Sublattice(S::SeqEnum[TorLatElt] : name:=false, dual_name:=false)
    -> TorLat, Map[TorLat,TorLat]
{The toric sublattice generated by the sequence of integral vectors S, together with the embedding map}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:="sub" cat impose_brackets(PrintName(Universe(S)));
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Check that the vectors are integral
    require IsIntegral(S): "Vectors must be integral";
    // Is there anything to do?
    L:=Universe(S);
    if AreGenerators(S) then
        return L, IdentityMap(L);
    end if;
    // Create the embedding
    sublat,emb:=sub<lattice_get_Zlattice(L) | [Eltseq(v) : v in S]>;
    mtrx_emb:=Matrix(emb(Basis(sublat)));
    // Is this sublattice already known?
    dim:=Dimension(sublat);
    bool,LL:=sublattice_known_to_lattice(L,dim,mtrx_emb,name,dual_name);
    if not bool then
        // Create the sublattice
        LL:=new_toric_lattice();
        LL`dim:=dim;
        assign_lattice_names(LL,name,dual_name);
        // Record the superlattice and the embedding
        LL`suplattice:=L;
        LL`emb_maps:=LatticeMap(LL,L,mtrx_emb);
        // Add this sublattice to the cache
        add_to_lattice_cache(L,LL);
    end if;
    return LL, LL`emb_maps;
end intrinsic;

intrinsic Quotient(v::TorLatElt :
    name:=need_brackets(PrintName(Parent(v))) cat " / " cat
                seq_to_string(Eltseq(PrimitiveLatticeVector(v)),"<",","),
    dual_name:=dual_lattice_string(name))
    -> TorLat, Map[TorLat,TorLat]
{The quotient of the toric lattice by the sublattice generated by the primitive vector of v, together with the quotient map.}
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Is there anything to do?
    L:=Parent(v);
    if IsZero(v) then
        return L, IdentityMap(L);
    end if;
    // Make the vector primitive
    v:=PrimitiveLatticeVector(v);
    // Create the projection
    quolat,proj:=quo<lattice_get_Zlattice(L) | Eltseq(v)>;
    mtrx_proj:=Matrix(proj(Basis(lattice_get_Zlattice(L))));
    // Is this quotient already known?
    bool,LL:=quotient_known_to_lattice(L,mtrx_proj,name,dual_name);
    if not bool then
        // Create the quotient lattice
        LL:=new_toric_lattice();
        LL`dim:=Dimension(quolat);
        assign_lattice_names(LL,name,dual_name);
        // Record what this is a quotient of and the quotient map
        LL`coverlattice:=L;
        LL`proj_maps:=LatticeMap(L,LL,mtrx_proj);
        // Add this quotient to the cache
        add_to_lattice_cache(L,LL);
    end if;
    return LL,LL`proj_maps;
end intrinsic;

intrinsic Quotient(S::SetEnum[TorLatElt] : name:=false, dual_name:=false)
    -> TorLat, Map[TorLat,TorLat]
{}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:="quo" cat impose_brackets(PrintName(Universe(S)));
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Return the quotient lattice and the quotient map
    L,phi:=Quotient(SetToSequence(S) : name:=name, dual_name:=dual_name);
    return L,phi;
end intrinsic;

intrinsic Quotient(S::SeqEnum[TorLatElt] : name:=false, dual_name:=false)
    -> TorLat, Map[TorLat,TorLat]
{The quotient of the ambient lattice by the linear subspace spanned by the sequence of vectors S, together with the quotient map}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:="quo" cat impose_brackets(PrintName(Universe(S)));
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Is there anything to do?
    if IsZero(S) then
        L:=Universe(S);
        return L, IdentityMap(L);
    end if;
    // We do this the easy way by creating the dual lattice first
    SS:=LinearSpanEquations(S);
    L,phi:=Sublattice(SS : name:=dual_name,dual_name:=name);
    L:=Dual(L);
    return L, L`proj_maps;
end intrinsic;

intrinsic AddVectorToLattice(v::TorLatElt:
    name:=need_brackets(PrintName(Parent(v))) cat " + " cat
                                    seq_to_string(Eltseq(v),"<",","),
    dual_name:=dual_lattice_string(name))
    -> TorLat, Map[TorLat,TorLat]
{}
      L,phi:=AddVectorToLattice([v]);
      return L,phi;
end intrinsic;

intrinsic AddVectorToLattice(S::SetEnum[TorLatElt]:name:=false,dual_name:=false)
    -> TorLat, Map[TorLat,TorLat]
{}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:=need_brackets(PrintName(Universe(S))) cat " + " cat
                                    span_string_of_nonintegral_vectors(S);
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Return the overlattice and the embedding
    LL,phi:=AddVectorToLattice(SetToSequence(S) :
                                              name:=name, dual_name:=dual_name);
    return LL,phi;
end intrinsic;


intrinsic AddVectorToLattice(S::SeqEnum[TorLatElt]:name:=false,dual_name:=false)
    -> TorLat, Map[TorLat,TorLat]
{The lattice generated by the addition of the vector v, or by the vectors in the
 sequence S, together with the embedding map into the new lattice}
    require not IsNull(S): "Illegal null sequence";
    if Type(name) eq BoolElt and not name then
        name:=need_brackets(PrintName(Universe(S))) cat " + " cat
                                    span_string_of_nonintegral_vectors(S);
    end if;
    if Type(dual_name) eq BoolElt and not dual_name then
        dual_name:=dual_lattice_string(name);
    end if;
    require Type(name) eq MonStgElt: "Parameter 'name' should be a string";
    require Type(dual_name) eq MonStgElt:
        "Parameter 'dual_name' should be a string";
    // Is there anything to do?
    L:=Universe(S);
    S:=[L | v : v in S | not IsIntegral(v)];
    if IsEmpty(S) then
        return L, IdentityMap(L);
    end if;
    // Extend the lattice
    Z:=lattice_from_cache(#S);
    sum,m1,m2:=DirectSum(L,Z);
    B:=m2*Basis(Z);
    LL,phi:=Quotient([sum | sum ! (B[i] - m1 * S[i]) : i in [1..#S]] :
                                          name:=name,dual_name:=dual_name);
    // Record the sublattice data and the embedding
    LL`sublattice:=L;
    LL`emb_maps:=Expand(m1 * phi);
    return LL,LL`emb_maps;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Dual Functions
/////////////////////////////////////////////////////////////////////////

intrinsic Dual(L::TorLat) -> TorLat
{The toric lattice dual to L.}
    if Type(L`dual) eq MonStgElt then
        name:=DualPrintName(L);
        dual_name:=PrintName(L);
        // We proceed on a case-by-case basis depending on how L was
        // created
        if IsDirectSum(L) then
            dual_lattice_direct_sum(L,name,dual_name);
        elif IsSuperlattice(L) then
            dual_lattice_superlattice(L,name,dual_name);
        elif IsSublattice(L) then
            dual_lattice_sublattice(L,name,dual_name);
        elif IsQuotient(L) then
            dual_lattice_quotientlattice(L,name,dual_name);
        else
            dual_lattice_default(L,name,dual_name);
        end if;
    end if;
    return L`dual;
end intrinsic;

intrinsic IsInDual(v::TorLatElt, L::TorLat) -> BoolElt
{True iff the point is in the dual of the lattice L.}
    if Type(L`dual) eq TorLat then
        return v in Dual(L);
    end if;
    return false;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Access Functions
/////////////////////////////////////////////////////////////////////////

intrinsic Dimension(L::TorLat) -> RngIntElt
{The dimension of the toric lattice L.}
    return L`dim;
end intrinsic;

intrinsic IsDirectSum(L::TorLat) -> BoolElt
{True iff the lattice was constructed as a direct sum}
    return assigned L`summands;
end intrinsic;

intrinsic Summands(L::TorLat)
    -> SeqEnum[TorLat], SeqEnum[Map[TorLat,TorLat]],
    SeqEnum[Map[TorLat,TorLat]]
{If the lattice L was constructed as a direct sum, gives the summands, together with the following sequences of natural maps: the embeddings of lattices in L, and the projections onto lattices in L.}
    require IsDirectSum(L):"Lattice was not constructed as a direct sum";
    return L`summands, L`emb_maps, L`proj_maps;
end intrinsic;

intrinsic IsSublattice(L::TorLat) -> BoolElt
{True iff the lattice was constructed as a sublattice}
    return assigned L`suplattice;
end intrinsic;

intrinsic Superlattice(L::TorLat) -> TorLat, Map[TorLat,TorLat]
{If the lattice L was constructed as a sublattice of S, gives S together with the embedding map.}
    require IsSublattice(L):"Lattice was not constructed as a sublattice";
    return L`suplattice, L`emb_maps;
end intrinsic;

intrinsic IsSuperlattice(L::TorLat) -> BoolElt
{True iff the lattice was constructed by the addition of a vector}
    return assigned L`sublattice;
end intrinsic;

intrinsic Sublattice(L::TorLat) -> TorLat, Map[TorLat,TorLat]
{If the lattice L was constructed by the addition of a vector to the sublattice S, gives S together with the embedding map}
    require IsSuperlattice(L):
          "Lattice was not constructed by addition of a vector to a sublattice";
    return L`sublattice, L`emb_maps;
end intrinsic;

intrinsic IsQuotient(L::TorLat) -> BoolElt
{True iff the lattice was constructed by taking a quotient.}
    return assigned L`coverlattice;
end intrinsic;

intrinsic Coverlattice(L::TorLat) -> TorLat, Map[TorLat,TorLat]
{If the lattice L was constructed by taking a quotient of the lattice S, gives S together with the projection map}
    require IsQuotient(L): "Lattice was not constructed as a quotient";
    return  L`coverlattice, L`proj_maps;
end intrinsic;

intrinsic AreGenerators(S::SetEnum[TorLatElt]) -> BoolElt
{}
    require not IsNull(S): "Illegal null sequence";
    // Are the vectors integral?
    require IsIntegral(S): "Vectors must be integral";
    // Return the result
    return AreGenerators(SetToSequence(S));
end intrinsic;

intrinsic AreGenerators(S::SeqEnum[TorLatElt]) -> BoolElt
{True iff the vectors of S generate the toric lattice L. The vectors must be integer.}
    require not IsNull(S): "Illegal null sequence";
    // Are the vectors integral
    require IsIntegral(S): "Vectors must be integral";
    if IsEmpty(S) then
        return IsZero(Dimension(Universe(S)));
    end if;
    // Check if they're generators
    if Rank(Matrix(Integers(),S)) ne Dimension(Universe(S)) then
        return false;
    end if;
    return Index(S) eq 1;
end intrinsic;

intrinsic Basis(L::TorLat) -> SeqEnum[TorLatElt]
{The integral standard basis of the lattice L.}
    B:=RowSequence(IdentityMatrix(Integers(),Dimension(L)));
    ChangeUniverse(~B,L);
    return B;
end intrinsic;

intrinsic Basis(L::TorLat, i::RngIntElt) -> TorLatElt
{The i-th integral standard basis vector of the lattice L.}
    seq:=ZeroSequence(Integers(),Dimension(L));
    seq[i]:=1;
    return LatticeVector(L,seq);
end intrinsic;

intrinsic Zero(L::TorLat) -> TorLatElt
{The zero vector of the lattice L.}
    if not assigned L`zero then
        L`zero:=LatticeVector(L,ZeroSequence(Integers(),Dimension(L)));
    end if;
    return L`zero;
end intrinsic;

intrinsic Representative(L::TorLat) -> TorLatElt
{A representative element of the toric lattice L.}
    return Zero(L);
end intrinsic

intrinsic PrintName(L::TorLat) -> MonStgElt
{The print name of the lattice L.}
    return L`name;
end intrinsic;

intrinsic DualPrintName(L::TorLat) -> MonStgElt
{The print name of the dual lattice to L.}
    if Type(L`dual) eq MonStgElt then
        return L`dual;
    else
        return PrintName(L`dual);
    end if;
end intrinsic;
