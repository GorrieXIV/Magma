freeze;

////////////////////////////////////////////////////////////////////////
// cone.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 41262 $
// $Date: 2012-12-02 01:25:19 +1100 (Sun, 02 Dec 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for manipulating cones in toric lattices.
/////////////////////////////////////////////////////////////////////////

import "../utilities/strings.m": seq_calc_widths, seq_to_aligned_string;
import "../lattice/lattice.m": lattice_from_cache;
import "../lattice/point.m": lattice_vector_to_row_matrix, row_matrix_to_lattice_vector;
import "generators.m": cone_has_inequalities, are_R_generators_minimal, are_inequalities_minimal, generators_copy, generators_minus, generators_change_ambient;
import "attributes.m": attributes_copy, attributes_minus, attributes_change_ambient;
import "properties.m": properties_copy, properties_minus, properties_change_ambient;
import "faces.m": faces_copy, faces_minus, faces_change_ambient;
import "singularities.m": singularities_copy, singularities_minus, singularities_change_ambient;

declare type TorCon;
declare attributes TorCon:
    height_1_slice,         // The polyhedron at height 1 w.r.t. ambient grading
    hash;                   // The hash value

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Allocates the memory for a cone in the lattice L.
// Note that the lattice isn't essential so long as it can be recovered from
// other information about the cone (such as the Rgens, or the dual, etc.), but
// since it's hard to think of a situtation where the lattice isn't known, this
// constructor requires it.
function create_raw_cone(L)
    C:=New(TorCon);
    C`lattice:=L;
    return C;
end function;

// Creates a duplicate of the cone, but not of the dual
function duplicate_without_dual(C)
    dC:=create_raw_cone(Ambient(C));
    generators_copy(C,dC);
    attributes_copy(C,dC);
    properties_copy(C,dC);
    faces_copy(C,dC);
    singularities_copy(C,dC);
    return dC;
end function;

// Creates a duplicate of the cone and of its dual
function duplicate_cone(C)
    dC:=duplicate_without_dual(C);
    if assigned C`dual then
        dD:=duplicate_without_dual(Dual(C));
        dC`dual:=dD;
        dD`dual:=dC;
    end if;
    return dC;
end function;

// Calculates -C, but not of the dual
function minus_without_dual(C)
    dC:=create_raw_cone(Ambient(C));
    generators_minus(C,dC);
    attributes_minus(C,dC);
    properties_minus(C,dC);
    faces_minus(C,dC);
    singularities_minus(C,dC);
    return dC;
end function;

// Creates a new cone equal to the positive quadrant of the toric lattics L
function internal_positive_quadrant(L)
    rays:=Basis(L);
    C:=Cone(rays);
    C`is_simplicial:=true;
    C`is_of_max_dim:=true;
    C`is_terminal:=true;
    C`is_canonical:=true;
    C`gorenstein_index:=1;
    C`are_Rgens_minimal:=true;
    C`dim:=Dimension(L);
    C`index:=1;
    return C;
 end function;

/////////////////////////////////////////////////////////////////////////
// Printing and hash value
/////////////////////////////////////////////////////////////////////////

intrinsic PrintNamed(C::TorCon,level::MonStgElt,name::MonStgElt)
{The cone description}
    // First we collect the basic information about the cone
    if assigned C`dim then
        descstr:=Sprintf("%o-dimensional ", Dimension(C));
        if assigned C`is_simplicial then  
            if  IsSimplicial(C) then
                descstr cat:= "simplicial cone";
            else 
       	        descstr cat:= "non-simplicial cone";
            end if;
        else
            descstr cat:= "cone";
        end if;
    else
        if assigned C`is_simplicial then  
            if  IsSimplicial(C) then
              descstr := "Simplicial cone";
            else 
  	      descstr := "Non-simplicial cone";
            end if;
        else
            descstr := "Cone";
        end if;
    end if;
    if not name eq "$" then
        descstr cat:= Sprintf(" %o", name);
    end if;
    // If the print level is minimal, we can stop here
    if level eq "Minimal" then
        printf descstr;
        return;
    end if;
    // If the print level is maximal we output the ambient toric lattice
    if level eq "Maximal" then
        descstr cat:= Sprintf(" in %o", Ambient(C));
    end if;
    // Carry on constructing the string
    if assigned C`Rgens then
        if IsEmpty(RGenerators(C)) then 
            descstr cat:= " supported at 0";
        else
            rgens:=[Eltseq(v) : v in RGenerators(C)];
            widths:=seq_calc_widths(rgens);
            if are_R_generators_minimal(C) then
                if #rgens eq 1 then
                    descstr cat:=" with minimal generator:";
                else
                    descstr cat:=Sprintf(" with %o minimal generators:",#rgens);
                end if;
             else
                if #rgens eq 1 then
                    descstr cat:= " with generator:";
                else
                    descstr cat:= Sprintf(" with %o generators:", #rgens);
                end if;
           end if;
        end if;
    end if;
    // We only output the inequalities if we don't know the generators, or
    // if the print level is maximal
    if (not assigned C`Rgens or level eq "Maximal") and
      cone_has_inequalities(C) then
        if assigned C`Rgens then
            if assigned widths then
                ineqstr:="\nand ";
            else
                ineqstr:=" and ";
            end if;
        else
            ineqstr:=" ";
        end if;
        if IsEmpty(Inequalities(C)) then
            ineqstr cat:= "equal to the full space";
        else
            ineqs:=[Eltseq(u) : u in Inequalities(C)];
            Iwidths:=seq_calc_widths(ineqs);
            if are_inequalities_minimal(C) then
                if #ineqs eq 1 then
                   ineqstr cat:="with minimal inequality:";
                else
                   ineqstr cat:=Sprintf("with %o minimal inequalities:",#ineqs);
                end if;
            else
                if #ineqs eq 1 then
                    ineqstr cat:= "with inequality:";
                else
                    ineqstr cat:= Sprintf("with %o inequalities:",#ineqs);
                end if;
            end if;
            if assigned widths and #widths eq #Iwidths then
                for i in [1..#widths] do
                    if widths[i] lt Iwidths[i] then
                        widths[i]:=Iwidths[i];
                    end if;
                end for;
                Iwidths:=widths;
            end if;
        end if;
    end if;
    // Cat together the information
    prefix:="    ";
    if assigned widths then
        descstr cat:= Sprintf("\n%o%o",prefix,seq_to_aligned_string(
                                              rgens, widths,"(",",",prefix));
    end if;
    if assigned ineqstr then
        if assigned Iwidths then
            descstr cat:= Sprintf("%o\n%o%o",ineqstr,
                 prefix,seq_to_aligned_string(ineqs,Iwidths,"(",",",prefix));
        else
            descstr cat:= ineqstr;
        end if;
    end if;
    // Finally output the string
    printf descstr;
end intrinsic;

intrinsic Hash(C::TorCon) -> RngIntElt
{The hash value for the cone C}
    if not assigned C`hash then
        C`hash:=Hash(Seqset(Rays(C)));
    end if;
    return C`hash;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Arithmetic, intersection, inclusion, and equality of cones
/////////////////////////////////////////////////////////////////////////

intrinsic '+'(C1::TorCon, C2::TorCon) -> TorCon
{The arithmetic sum of the cones C1 and C2}
    require Ambient(C1) eq Ambient(C2): "Cones must lie in the same space";
    C:=Cone(RGenerators(C1) cat RGenerators(C2));
    return C;
end intrinsic;

intrinsic '-'(C::TorCon) -> TorCon
{The minus cone C}
    mC := minus_without_dual(C);
    if assigned C`dual then
        mD:=minus_without_dual(Dual(C));
        mC`dual:=mD;
        mD`dual:=mC;
    end if;
    return mC;
end intrinsic;

intrinsic '*'(C::TorCon,M::Mtrx) -> TorLatElt
{The cone generated by v * M for each generator v in C with a square matrix M}
    L:=Ambient(C);
    dim:=Dimension(L);
    require NumberOfRows(M) eq NumberOfColumns(M) and
            NumberOfRows(M) eq dim:
        Sprintf("Argument 2 must be a %o x %o (square) matrix",dim,dim);
    require CoefficientRing(M) cmpeq Integers() or
            CoefficientRing(M) cmpeq Rationals():
        "Argument 2 must have integral or rational entries";
    if Dimension(C) eq 0 then return C; end if;
    if CoefficientRing(M) cmpeq Integers() then
        M:=ChangeRing(M,Rationals());
    end if;
    gens:=[L | row_matrix_to_lattice_vector(L,
                    lattice_vector_to_row_matrix(v) * M) : v in RGenerators(C)];
    return Cone(gens);
end intrinsic;

intrinsic 'meet' (C1::TorCon, C2::TorCon) -> TorCon
{The cone which is the intersection of C1 and C2.}
    require Ambient(C1) eq Ambient(C2): "Cones must live in the same lattice";
    C:=ConeWithInequalities(Inequalities(C1) cat Inequalities(C2));
    return C;
end intrinsic;

intrinsic 'subset'(C1::TorCon,C2::TorCon) -> BoolElt
{True iff C1 and C2 are the same cone}
    if assigned C2`dim or assigned C2`Rgens then
        if Dimension(C2) lt Dimension(C1) then return false; end if;
    end if;
    // If C2 knows its Rgens, perhaps it is enough to check the inclusion
    // on Rgens (this is intended for faster calculations for Faces)?
    if assigned C2`Rgens and RGenerators(C1) subset RGenerators(C2) then 
        return true;
    end if;
    return &and[ray in C2 : ray in RGenerators(C1)];
end intrinsic;

intrinsic 'eq'(C1::TorCon,C2::TorCon) -> BoolElt
{True iff C1 and C2 are the same cone}
    if not Hash(C1) eq Hash(C2) then
        return false;
    end if;
    if are_R_generators_minimal(C1) and are_R_generators_minimal(C2) then
        return Seqset(MinimalRGenerators(C1)) cmpeq
            Seqset(MinimalRGenerators(C2));
    end if;
    if are_inequalities_minimal(C1) and are_inequalities_minimal(C2) then
        return Seqset(MinimalInequalities(C1)) cmpeq
            Seqset(MinimalInequalities(C2));
    end if;
    return C1 subset C2 and C2 subset C1;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Change ambient lattice
/////////////////////////////////////////////////////////////////////////

intrinsic ChangeAmbient(C::TorCon, L::TorLat) -> TorCon
{Creates new cone in lattice L, which have the same geometry as C}
    // Sanity check
    if L eq Ambient(C) then return C; end if;
    require Dimension(L) eq Dimension(Ambient(C)): Sprintf("The dimension of the lattice (%o) must equal the dimension of the ambient of the cone (%o)",Dimension(L),Dimension(Ambient(C)));
    // Create a new cone
    dC:=create_raw_cone(L);
    // Copy over the data
    generators_change_ambient(C,dC,L);
    attributes_change_ambient(C,dC,L);
    properties_change_ambient(C,dC,L);
    faces_change_ambient(C,dC,L);
    singularities_change_ambient(C,dC,L);
    // Return the new cone
    return dC;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Creation of cones
/////////////////////////////////////////////////////////////////////////

intrinsic Cone(S::SeqEnum[SeqEnum[RngIntElt]]) -> TorCon
{}
    require not IsEmpty(S): "Sequence must contain at least one vector";
    dim:=#S[1];
    require &and[#v eq dim : v in S]: "Vectors must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,L);
    return Cone(S);
end intrinsic;

intrinsic Cone(S::SeqEnum[SeqEnum[FldRatElt]]) -> TorCon
{}
    require not IsEmpty(S): "Sequence must contain at least one vector";
    dim:=#S[1];
    require &and[#v eq dim : v in S]: "Vectors must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,L);
    return Cone(S);
end intrinsic;

intrinsic Cone(S::SetEnum[TorLatElt]) -> TorCon
{}
    require not IsNull(S): "Illegal null sequence";
    return Cone(Setseq(S));
end intrinsic;

intrinsic Cone(S::SeqEnum[TorLatElt]) -> TorCon 
{The cone generated by the vectors in S}
    require not IsNull(S): "Illegal null sequence";
    L:=Universe(S);
    if IsEmpty(S) then return ZeroCone(L); end if;
    if #S eq 1 then return Cone(S[1]); end if;
    C:=create_raw_cone(L);
    C`Rgens:=S;
    return C;
end intrinsic;

intrinsic Cone(v::TorLatElt) -> TorCon 
{}
    L:=Parent(v);
    if IsZero(v) then return ZeroCone(L); end if;
    C:=create_raw_cone(L);
    C`is_simplicial:=true;
    C`are_Rgens_minimal:=true;
    v:=PrimitiveLatticeVector(v);
    C`Rgens:=[L | v]; 
    C`dim:=1;
    C`index:=1;
    C`is_of_max_dim:=Dimension(L) eq 1;
    D:=Dual(C);
    D`is_of_max_dim:=true;
    D`dim:=Dimension(L);
    D`index:=1;
    return C;
end intrinsic;

intrinsic Cone(v::SeqEnum[RngIntElt]) -> TorCon
{}
    dim:=#v;
    require not dim eq 0: "Vector must be of positive dimension";
    L:=lattice_from_cache(dim);
    return Cone(L ! v);
end intrinsic;

intrinsic Cone(v::SeqEnum[FldRatElt]) -> TorCon
{The one-dimensional cone generated by the toric lattice point v}
    dim:=#v;
    require not dim eq 0: "Vector must be of positive dimension";
    L:=lattice_from_cache(dim);
    return Cone(L ! v);
end intrinsic;

intrinsic Cones(R::[TorLatElt],S::[SeqEnum[RngIntElt]] ) -> SeqEnum[TorCon]
{The sequence of cones generated by the toric lattice points in R with indices in S (i.e. the i-th cone in the sequence is generated by the points R[i1],...,R[ik], where S[i] = [i1,...,ik])}
    require not IsNull(R): "Illegal null sequence";
    require Maximum(&cat S) le #R and Minimum(&cat S) ge 1: 
        Sprintf("The indices in argument 2 must be in the range 1..%o",#R);
    return [PowerStructure(TorCon)|Cone([Universe(R)|R[j] : j in I]) : I in S];
end intrinsic;

intrinsic Dual(C::TorCon) -> TorCon
{The dual cone to the cone C}
    if not assigned C`dual then
        C`dual:=create_raw_cone(Dual(Ambient(C)));
        C`dual`dual:=C;
    end if;
    return C`dual;
end intrinsic;

intrinsic ConeWithInequalities(S::SeqEnum[TorLatElt]) -> TorCon 
{}
    require not IsNull(S): "Illegal null sequence";
    L:=Universe(S);
    C:=create_raw_cone(Dual(L));
    D:=Dual(C);
    D`Rgens:=S;
    return C;
end intrinsic;

intrinsic ConeWithInequalities(S::SeqEnum[SeqEnum[RngIntElt]]) -> TorCon
{}
    require not IsEmpty(S): "Sequence must contain at least one form";
    dim:=#S[1];
    require &and[#v eq dim : v in S]: "Forms must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,Dual(L));
    return ConeWithInequalities(S);
end intrinsic;

intrinsic ConeWithInequalities(S::SeqEnum[SeqEnum[FldRatElt]]) -> TorCon
{}
    require not IsEmpty(S): "Sequence must contain at least one form";
    dim:=#S[1];
    require &and[#v eq dim : v in S]: "Forms must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,Dual(L));
    return ConeWithInequalities(S);
end intrinsic;

intrinsic ConeWithInequalities(S::SetEnum[TorLatElt]) -> TorCon 
{The cone defined by inequalities of the form v >= 0 for all v in S}
    require not IsNull(S): "Illegal null sequence";
    return ConeWithInequalities(Setseq(S));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Useful constructions
/////////////////////////////////////////////////////////////////////////

intrinsic ZeroCone(L::TorLat) -> TorCon 
{The cone in the toric lattice L supported at 0}
    if not assigned L`zero_cone then
        C:=create_raw_cone(L);
        C`Rgens :=[L|];
        C`is_simplicial:=true;
        C`is_of_max_dim:=Dimension(L) eq 0;
        C`is_smooth:=true;
        C`is_terminal:=true;
        C`is_canonical:=true;
        C`dim:=0;
        C`index:=1;
        D:=Dual(C);
        D`Rgens:=LinearConeGenerators(Basis(Dual(L)));
        D`are_Rgens_minimal:=true;
        D`dim:=Dimension(L);
        D`index:=1;
        D`is_of_max_dim:=true;
        D`cone_in_sublattice:=D;
        D`cone_in_sublattice_map:=IdentityMap(Dual(L));
        L`zero_cone:=C; 
        if Dimension(L) eq 0 then 
            dL:=Dual(L);
            dL`zero_cone:=D;
        end if;
    end if;
    return L`zero_cone;
end intrinsic;

intrinsic ZeroCone(n::RngIntElt) -> TorCon
{The cone in an n-dimensional lattice supported at 0}
    require n ge 0: "Dimension must be non-negative";
    return ZeroCone(lattice_from_cache(n));
end intrinsic;

intrinsic FullCone(L::TorLat) -> TorCon 
{The full cone of then toric lattice L}
    return Dual(ZeroCone(Dual(L)));
end intrinsic;

intrinsic FullCone(n::RngIntElt) -> TorCon
{The full cone of an n-dimensional lattice}
    require n ge 0: "Dimension must be non-negative";
    return FullCone(lattice_from_cache(n));
end intrinsic;

intrinsic PositiveQuadrant(L::TorLat) -> TorCon
{The cone generated by the standard basis of the toric lattice L}
    C:=internal_positive_quadrant(L);
    D:=internal_positive_quadrant(Dual(L));
    C`dual:=D;
    D`dual:=C;
    return C;
end intrinsic;

intrinsic PositiveQuadrant(n::RngIntElt) -> TorCon
{The cone generated by the standard basis of an n-dimensional lattice}
    require n ge 0: "Dimension must be non-negative";
    return PositiveQuadrant(lattice_from_cache(n));
end intrinsic;

intrinsic RandomCone(L::TorLat,n::RngIntElt,k::RngIntElt) -> TorCon
{A random cone in the toric lattice L, generated by n points whose coefficients lie between -k and k}
    require n ge 0: "Argument 2 must be a non-negative integer";
    d:=Dimension(L);
    if k lt 0 then k:=-k; end if;
    return Cone([L | [Random(2 * k) - k : i in [1..d]] : j in [1..n]]);
end intrinsic;

intrinsic RandomCone(d::RngIntElt,n::RngIntElt,k::RngIntElt) -> TorCon
{A random cone in a d-dimensional toric lattice, generated by n points whose coefficients lie between -k and k}
    require d ge 1: "The dimension of the ambient toric lattice must be greater than zero";
    require n ge 0: "Argument 2 must be a non-negative integer";
    if n eq 0 then return ZeroCone(lattice_from_cache(d)); end if;
    if k lt 0 then k:=-k; end if;
    return Cone([PowerSequence(Integers()) |
                              [Random(2 * k) - k : i in [1..d]] : j in [1..n]]);
end intrinsic;

intrinsic RandomPositiveCone(L::TorLat,n::RngIntElt,k::RngIntElt) -> TorCon
{A random cone in the toric lattice L, generated by n points whose coefficients lie between 0 and k}
    require n ge 0: "Argument 2 must be a non-negative integer";
    d:=Dimension(L);
    if k lt 0 then k:=-k; end if;
    return Cone([L | [Random(k)  : i in [1..d]] : j in [1..n]]);
end intrinsic;

intrinsic RandomPositiveCone(d::RngIntElt,n::RngIntElt,k::RngIntElt) -> TorCon
{A random cone in a d-dimensional toric lattice, generated by n points whose coefficients lie between 0 and k}
    require d ge 1: "The dimension of the ambient toric lattice must be greater than zero";
    require n ge 0: "Argument 2 must be a non-negative integer";
    if n eq 0 then return ZeroCone(lattice_from_cache(d)); end if;
    if k lt 0 then k:=-k; end if;
    return Cone([PowerSequence(Integers()) |
                              [Random(k)  : i in [1..d]] : j in [1..n]]);
end intrinsic;


/////////////////////////////////////////////////////////////////////////
// Isomorphism of cones
/////////////////////////////////////////////////////////////////////////
/*
// THINK: Not working yet!
intrinsic AreExternallyIsomorphic(C1::TorCon,C2::TorCon)
        -> BoolElt, Map[TorLat,TorLat]
{True iff there exists an isomorphism of the ambient lattices of the cones C1 and C2, mapping C1 onto C2. If true, the isomorphism is also given.}
    if Dimension(Ambient(C1)) ne Dimension(Ambient(C2)) then
        return false,_;
    end if;
    if Dimension(C1) ne Dimension(C2) then 
        return false,_;
    end if;
    M1:=Transpose(Matrix(MinimalRGenerators(C1)));
    M2:=Transpose(Matrix(MinimalRGenerators(C2)));
    bool,M:=IsConsistent(M2,M1);
    if not bool then 
        return false,_;
    end if;
    if Determinant(M) in [1, -1] then 
        return true, LatticeMap(Ambient(C1), Ambient(C2), Transpose(M)); 
    end if;
    return false,_;
end intrinsic;

// THINK: Not working yet!
intrinsic AreIsomorphic(C1::TorCon,C2::TorCon) -> BoolElt, Map[TorLat,TorLat]
{True iff there exists a map of the ambient lattices of the cones C1 and C2 mapping C1 isomorphically onto C2. If true, the map is also given.}
    c1:=ConeInSublattice(C1);
    c2:=ConeInSublattice(C2);
    bool:=AreExternallyIsomorphic(c1,c2);
    if bool then 
        M1:=Transpose(Matrix(MinimalRGenerators(C1)));
        M2:=Transpose(Matrix(MinimalRGenerators(C2)));
        M:=Solution(M1,M2);
        return true, LatticeMap(Ambient(C1), Ambient(C2), Transpose(M));
    end if;
    return false, _;
end intrinsic;
*/
