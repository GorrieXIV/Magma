freeze;

/////////////////////////////////////////////////////////////////////////
// point.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Describes the elements (points) of the toric lattice and how to
// manipulate them.
/////////////////////////////////////////////////////////////////////////

import "../utilities/strings.m": seq_to_string;
import "lattice.m": lattice_from_cache, lattice_get_Zlattice, lattice_get_Qlattice;

declare type TorLatElt;
declare attributes TorLatElt:
    lattice,        // The parent lattice of this point
    row_matrix,     // This point as a row matrix
    elt_seq,        // This point as a sequence
    is_integral,    // True iff the point is integral in the lattice
    is_primitive,   // True iff the point is primitive
    primitive;      // If not primitive, this is the primitive vector

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Returns a row matrix M equal to the lattice point L. The coeficient ring
// of M will always be the rationals.
// NOTE: This function is intended for use outside this file to ensure a
// consistent way of accessing the row matrix of a lattice point.
function lattice_vector_to_row_matrix(L)
    return L`row_matrix;
end function;

// Converts the row matrix M into a lattice point in L. Note that NO checks
// are performed on the size of M to ensure that it is compatible with L.
function row_matrix_to_lattice_vector(L,M)
    // Create the point and assign its data
    v:=New(TorLatElt);
    v`lattice:=L;
    if Type(M) eq ModMatRngElt then
        v`is_integral:=true;
        v`row_matrix:=ChangeRing(M,Rationals());
    else
        v`row_matrix:=M;
    end if;
    return v;
end function;

// Returns a new lattice point equal to v but with the parent changed to L.
// Note that NO checks are performed that v and L are compatible.
function change_lattice_point_parent(v,L)
    // Is there anything to do?
    if v`lattice eq L then return v; end if;
    // Create the point and assign its data
    w:=New(TorLatElt);
    w`lattice:=L;
    w`row_matrix:=v`row_matrix;
    if assigned v`elt_seq then
        w`elt_seq:=v`elt_seq; end if;
    if assigned v`is_integral then
        w`is_integral:=v`is_integral; end if;
    if assigned v`is_primitive then
        w`is_primitive:=v`is_primitive; end if;
    return w;
end function;

// Returns true iff there exists an element v of S such that v * u == 0.
function is_orthogonal_element(u,S)
    for v in S do
        if IsZero(v * u) then return true; end if;
    end for;
    return false;
end function;

// Returns an arbitrary primitive form on which the given set of points S don't
// vanish. We assume that the origin is not in S.
// S can be a sequence of toric lattice elements,
//          a sequence of sequences of integers or rationals,
//          a sequence of row matrices.
// The resulting form is returned as a sequence and should be coerced into the
// dual lattice.
// Note: This function is essential for the lattice point counting
// algorithm. It's currently surprisingly slow considering that all we're
// trying to do is pick a random point not in a set of measure zero. Anything
// which can speed it up is worthwhile.
function nonvanishing_form(S)
    // Work out what the input is and standardise it to row matrices
    if Type(Universe(S)) eq TorLat then
        d:=Dimension(Universe(S));
        S:=[v`row_matrix : v in S];
    elif Type(Representative(S)) eq SeqEnum then
        d:=#Representative(S);
        S:=[Matrix(Rationals(),1,d,v) : v in S];
    else
        d:=NumberOfColumns(Representative(S));
    end if;
    // We assume that we are working with a sequence of row matrices
    for i in [0..d * (d - 1) * #S + 1] do
        coeffs:=[Integers() | i^j : j in [0..d - 1]];
        u:=Matrix(Rationals(),d,1,coeffs);
        if not is_orthogonal_element(u,S) then
            r:=GCD(coeffs);
            return [Integers() | coeffs[i] / r : i in [1..d]];
        end if;
    end for;
    assert false; // Impossible to get here
end function;

// Moves the points in the sequence S to the lattice L, where the dimension of
// L is >= the dimension of the points in S, by appending zeros to the
// coordinates if necessary.
// S can be a sequence of toric lattice elements,
//          a sequence of sequences of integers or rationals,
//          a toric lattice element,
//          a sequence of integers or rationals.
// If S represents a sequence of points, then a sequence of points will be
// returned. If S represents a single point, then a single point will be
// returned.
function move_points_to_lattice(S,L)
    if Type(S) eq TorLatElt then
        dif:=Dimension(L) - Dimension(Parent(S));
        if dif lt 0 then
            error "move_points_to_lattice: Incompatable dimension";
        end if;
        if dif eq 0 then
            return change_lattice_point_parent(S,L);
        end if;
        Z:=ZeroMatrix(Rationals(),1,dif);
        return row_matrix_to_lattice_vector(L,HorizontalJoin(S`row_matrix,Z));
    end if;
    if ExtendedCategory(S) eq SeqEnum[RngIntElt] or
       ExtendedCategory(S) eq SeqEnum[FldRatElt] then
        dif:=Dimension(L) - #S;
        if dif lt 0 then
            error "move_points_to_lattice: Incompatable dimension";
        end if;
        if dif eq 0 then
            return LatticeVector(L,S);
        end if;
        return LatticeVector(L,S cat ZeroSequence(Universe(L),dif));
    end if;
    if #S eq 0 then
        return [L|];
    end if;
    if ExtendedCategory(S) eq SeqEnum[SeqEnum[RngIntElt]] or
       ExtendedCategory(S) eq SeqEnum[SeqEnum[FldRatElt]] then
        u:=Representative(S);
        dif:=Dimension(L) - #u;
        if dif lt 0 then
            error "move_points_to_lattice: Incompatable dimension";
        end if;
        if dif eq 0 then
            return [L | v : v in S];
        end if;
        z:=ZeroSequence(Universe(u),dif);
        return [L | v cat z : v in S];
    elif ExtendedCategory(S) eq SeqEnum[TorLatElt] then
        dif:=Dimension(L) - Dimension(Universe(S));
        if dif lt 0 then
            error "move_points_to_lattice: Incompatable dimension";
        end if;
        if dif eq 0 then
            return [L | change_lattice_point_parent(v,L) : v in S];
        end if;
        z:=ZeroMatrix(Rationals(),1,dif);
        return [L | row_matrix_to_lattice_vector(L,
                                      HorizontalJoin(v`row_matrix,z)) : v in S];
    end if;
    error "move_points_to_lattice: Invalid arguments";
end function;

// Given a non-zero lattice vector v, returns a primitive vector u and a
// positive scalar k such that v = k * u.
// Note: This does NOT check whether v is zero.
function primitive_nonzero_lattice_vector(v)
    u_mat:=Denominator(v) * v`row_matrix;
    k:=GCD(ChangeUniverse(Eltseq(u_mat),Integers()));
    if not assigned v`primitive then
        u:=row_matrix_to_lattice_vector(Parent(v),u_mat / k);
        u`is_integral:=true;
        u`is_primitive:=true;
        v`primitive:=u;
    end if;
    return v`primitive,k;
end function;

// Returns -v, where v is a lattice element
function negate_lattice_point(v)
    w:=row_matrix_to_lattice_vector(Parent(v),-v`row_matrix);
    if assigned v`is_primitive then
        w`is_primitive:=v`is_primitive;
    end if;
    if assigned v`is_integral then
        w`is_integral:=v`is_integral;
    end if;
    return w;
end function;

// Multiplies the lattice element v by k
function multiply_lattice_point(k,v)
    if IsZero(v`row_matrix) then return v; end if;
    if k eq 0 then return Zero(Parent(v)); end if;
    if k eq 1 then return v; end if;
    if k eq -1 then return negate_lattice_point(v); end if;
    w:=row_matrix_to_lattice_vector(Parent(v),k * v`row_matrix);
    if assigned v`primitive and k gt 0 then
        w`primitive:=v`primitive;
    end if;
    if IsIntegral(k) and assigned v`is_integral and v`is_integral then
        w`is_integral:=v`is_integral;
        w`is_primitive:=false;
    end if;
    return w;
end function;

// Returns the index of sublattice generated by the rows of the matrix M.
function index_of_sublattice(M)
     M:=SmithForm(M);
     r:=Rank(M);
     ind:=Minor(M,[1..r],[1..r]);
     return Abs(ind);
end function;

// Returns -1 if v1 < v2, 0 if v1 = v2, and 1 if v1 > v2
// Assumes that v1 and v2 lie in the same lattice.
function lattice_element_cmp(v1,v2)
    if v1`row_matrix cmpeq v2`row_matrix then
        return 0;
    end if;
    return v1`row_matrix lt v2`row_matrix select -1 else 1;
end function;

// Raises x to the power of n.
// Assumes that n is an integer.
function raise_to_power(x,n)
    if n ge 0 then
        return x^n;
    else
        error if IsZero(x), "raise_to_power: Illegal zero denominator";
        return (1/x)^-n;
    end if;
end function;

/////////////////////////////////////////////////////////////////////////
// Printing, Parent, and Hash Value
/////////////////////////////////////////////////////////////////////////

intrinsic Print(v::TorLatElt,level::MonStgElt)
{A description of the point}
    if level eq "Maximal" then
        printf "%o in %o",seq_to_string(Eltseq(v`row_matrix),"(",","),
                                                           PrintName(Parent(v));
    elif level eq "Magma" then
        printf "Coordinates:\t%o\nLattice:\t%o",Eltseq(v`row_matrix),
                                                           PrintName(Parent(v));
    else
        printf "%o", seq_to_string(Eltseq(v`row_matrix),"(",",");
    end if;
end intrinsic;

intrinsic Parent(v::TorLatElt) -> TorLat
{The toric lattice containing v}
    return v`lattice;
end intrinsic;

intrinsic Hash(v::TorLatElt) -> RngIntElt
{The hash value of the point}
    return Hash(v`row_matrix);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Inequality Operations
/////////////////////////////////////////////////////////////////////////

intrinsic Compare(v1::TorLatElt, v2::TorLatElt) -> RngIntElt
{Negative, zero, or positive according to whether v1 is less than, equal to, or
greater than v2}
    require Parent(v1) eq Parent(v2):"Points must lie in the same lattice";
    if v1`row_matrix lt v2`row_matrix then
        return -1;
    elif v1`row_matrix gt v2`row_matrix then
        return 1;
    end if;
    return 0;
end intrinsic;

intrinsic 'eq'(v1::TorLatElt, v2::TorLatElt) -> BoolElt
{True iff v1 and v2 lie in the same toric lattice and v1 equals v2}
    return Parent(v1) eq Parent(v2) and v1`row_matrix cmpeq v2`row_matrix;
end intrinsic;

intrinsic 'le'(v1::TorLatElt, v2::TorLatElt) -> BoolElt
{True iff v1 le v2, however v1 and v2 must lie in the same toric lattice}
    require Parent(v1) eq Parent(v2):"Points must lie in the same lattice";
    return v1`row_matrix le v2`row_matrix;
end intrinsic;

intrinsic 'lt'(v1::TorLatElt, v2::TorLatElt) -> BoolElt
{True iff v1 lt v2, however v1 and v2 must lie in the same toric lattice}
    require Parent(v1) eq Parent(v2):"Points must lie in the same lattice";
    return v1`row_matrix lt v2`row_matrix;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Basis, Unitary and Binary Operations
/////////////////////////////////////////////////////////////////////////

intrinsic '.'(v::TorLatElt, i::RngIntElt) -> .
{The i-th coefficient of the toric lattice point v with respect to the standard basis}
    d:=NumberOfColumns(v`row_matrix);
    require i ge 1 and i le d:
        Sprintf("Value for basis element should be in the range [1..%o]",d);
    c:=v`row_matrix[1][i];
    return IsIntegral(c) select Integers() ! c else c;
end intrinsic;

intrinsic '+'(v1::TorLatElt,v2::TorLatElt) -> TorLatElt
{The sum of v1 and v2. The points must lie in the same lattice.}
    require Parent(v1) eq Parent(v2):"Points must lie in the same lattice";
    return row_matrix_to_lattice_vector(Parent(v1),v1`row_matrix+v2`row_matrix);
end intrinsic;

intrinsic '-'(v1::TorLatElt,v2::TorLatElt) -> TorLatElt
{The difference of v1 and v2. The points must lie in the same lattice.}
    require Parent(v1) eq Parent(v2):"Points must lie in the same lattice";
    return row_matrix_to_lattice_vector(Parent(v1),v1`row_matrix-v2`row_matrix);
end intrinsic;

intrinsic '-'(v::TorLatElt) -> TorLatElt
{The negation of v}
    return negate_lattice_point(v);
end intrinsic;

intrinsic '*'(v1::TorLatElt,v2::TorLatElt) -> FldRatElt
{The product of v1 and v2. The points must lie in lattices dual to each other.}
    require IsInDual(v1,Parent(v2)):
                "The lattices containing the points must be dual to each other";
    return (v1`row_matrix * Transpose(v2`row_matrix))[1][1];
end intrinsic;

intrinsic '*'(k::FldRatElt,v::TorLatElt) -> TorLatElt
{}
    return multiply_lattice_point(k,v);
end intrinsic;

intrinsic '*'(k::RngIntElt,v::TorLatElt) -> TorLatElt
{}
    return multiply_lattice_point(k,v);
end intrinsic;

intrinsic '*'(v::TorLatElt,k::FldRatElt) -> TorLatElt
{}
    return multiply_lattice_point(k,v);
end intrinsic;

intrinsic '*'(v::TorLatElt,k::RngIntElt) -> TorLatElt
{The point v scaled by k}
    return multiply_lattice_point(k,v);
end intrinsic;

intrinsic '*'(v::TorLatElt,M::Mtrx) -> TorLatElt
{The product v * M of the point v with a square matrix M}
    dim:=Dimension(v);
    require NumberOfRows(M) eq NumberOfColumns(M) and
            NumberOfRows(M) eq dim:
        Sprintf("Argument 2 must be a %o x %o (square) matrix",dim,dim);
    require CoefficientRing(M) cmpeq Integers() or
            CoefficientRing(M) cmpeq Rationals():
        "Argument 2 must have integral or rational entries";
    if dim eq 0 then return v; end if;
    if IsZero(v) then return v; end if;
    if CoefficientRing(M) cmpeq Integers() then
        M:=ChangeRing(M,Rationals());
    end if;
    return row_matrix_to_lattice_vector(Parent(v),v`row_matrix * M);
end intrinsic;

intrinsic '/'(v1::TorLatElt, v2::TorLatElt) -> FldRatElt
{The scalar k such that v1 = k*v2. The points must lie in the same lattice and be proportional.}
    bool,k:=AreProportional(v2,v1);
    require bool:"Points are not proportional";
    return k;
end intrinsic;

intrinsic '/'(v::TorLatElt,k::FldRatElt) -> TorLatElt
{}
    require not IsZero(k):"Cannot divide by zero";
    return multiply_lattice_point(1/k,v);
end intrinsic;

intrinsic '/'(v::TorLatElt,k::RngIntElt) -> TorLatElt
{The point v scaled by 1/k. k must be non-zero.}
    require not IsZero(k):"Cannot divide by zero";
    return multiply_lattice_point(1/k,v);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Creation
/////////////////////////////////////////////////////////////////////////

intrinsic LatticeVector(S::ModTupFldElt) -> TorLatElt
{}
    S:=Eltseq(S);
    type:=ExtendedCategory(S);
    require type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt]:
                           "The vector must contain integer or rational values";
    return LatticeVector(lattice_from_cache(#S),S);
end intrinsic;

intrinsic LatticeVector(L::TorLat,S::ModTupFldElt) -> TorLatElt
{}
    S:=Eltseq(S);
    type:=ExtendedCategory(S);
    require type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt]:
                           "The vector must contain integer or rational values";
    require #S eq Dimension(L):
             "The length of the vector must equal the dimension of the lattice";
    return LatticeVector(L,S);
end intrinsic;

intrinsic LatticeVector(S::ModTupRngElt) -> TorLatElt
{}
    S:=Eltseq(S);
    type:=ExtendedCategory(S);
    require type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt]:
                           "The vector must contain integer or rational values";
    return LatticeVector(lattice_from_cache(#S),S);
end intrinsic;

intrinsic LatticeVector(L::TorLat,S::ModTupRngElt) -> TorLatElt
{}
    S:=Eltseq(S);
    type:=ExtendedCategory(S);
    require type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt]:
                           "The vector must contain integer or rational values";
    require #S eq Dimension(L):
             "The length of the vector must equal the dimension of the lattice";
    return LatticeVector(L,S);
end intrinsic;

intrinsic LatticeVector(S::SeqEnum) -> TorLatElt
{}
    require not IsNull(S): "Illegal null sequence";
    return LatticeVector(lattice_from_cache(#S),S);
end intrinsic;

intrinsic LatticeVector(L::TorLat,S::SeqEnum) -> TorLatElt
{The toric lattice vector with coordinates S}
    require not IsNull(S): "Illegal null sequence";
    type:=ExtendedCategory(S);
    require type eq SeqEnum[RngIntElt] or type eq SeqEnum[FldRatElt]:
                         "The sequence must contain integer or rational values";
    require #S eq Dimension(L):
           "The length of the sequence must equal the dimension of the lattice";
    // Create the point and assign its data
    v:=New(TorLatElt);
    v`lattice:=L;
    if Universe(S) cmpeq Integers() then
        v`is_integral:=true;
        v`elt_seq:=S;
    end if;
    v`row_matrix:=Matrix(Rationals(),1,#S,S);
    return v;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Access Functions
/////////////////////////////////////////////////////////////////////////

intrinsic Vector(v::TorLatElt) -> ModTupFldElt
{The toric lattice point v as a vector}
    return v`row_matrix[1];
end intrinsic;

intrinsic Eltseq(v::TorLatElt) -> SeqEnum[FldRatElt]
{The coordinates of the toric lattice point v as a sequence}
    if not assigned v`elt_seq then
        v`is_integral,S:=CanChangeUniverse(Eltseq(v`row_matrix),Integers());
        v`elt_seq:=v`is_integral select S else Eltseq(v`row_matrix);
    end if;
    return v`elt_seq;
end intrinsic;

intrinsic Dimension(v::TorLatElt) -> RngIntElt
{The dimension of the toric lattice containing v}
    return Dimension(Parent(v));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Lattice Vector Operations
/////////////////////////////////////////////////////////////////////////

intrinsic AreProportional(v1::TorLatElt, v2::TorLatElt) ->BoolElt, FldRatElt
{True iff a * v1 = v2 for some rational number a. If so, then a is given as the second value.}
    require Parent(v1) eq Parent(v2):"Points must line in the same lattice";
    if IsZero(v2) then
        return true, 0;
    end if;
    w1:=PrimitiveLatticeVector(v1);
    w2:=PrimitiveLatticeVector(v2);
    if w1 eq w2 then
        s1:=Eltseq(v1`row_matrix);
        s2:=Eltseq(v2`row_matrix);
        while s1[#s1] eq 0 do
            Prune(~s1);
            Prune(~s2);
        end while;
        return true, s2[#s2]/s1[#s1];
    end if;
    return false,_;
end intrinsic;

intrinsic IsZero(v::TorLatElt) -> BoolElt
{True iff the toric lattice point v is 0}
    return IsZero(v`row_matrix);
end intrinsic;

intrinsic IsIntegral(v::TorLatElt) -> BoolElt
{True iff v has integral coordinates in the underlying toric lattice}
    if not assigned v`is_integral then
        v`is_integral,S:=CanChangeUniverse(Eltseq(v`row_matrix),Integers());
        v`elt_seq:=v`is_integral select S else Eltseq(v`row_matrix);
    end if;
    return v`is_integral;
end intrinsic;

intrinsic IsIntegral(S::SeqEnum[TorLatElt]) -> BoolElt
{}
    require not IsNull(S): "Illegal null sequence";
    for v in S do
        if not IsIntegral(v) then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic IsIntegral(S::{@TorLatElt@}) -> BoolElt
{}
    require not IsNull(S): "Illegal null ordered set";
    for v in S do
        if not IsIntegral(v) then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic IsIntegral(S::SetEnum[TorLatElt]) -> BoolElt
{True iff every element in S has integral coordinates in the underlying toric lattice}
    require not IsNull(S): "Illegal null set";
    for v in S do
        if not IsIntegral(v) then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic Denominator(v::TorLatElt) -> RngIntElt
{Smallest integer n, such that n * v is integral}
    return LCM([Integers() | Denominator(x) : x in Eltseq(v`row_matrix)]);
end intrinsic;

intrinsic IsPrimitive(v::TorLatElt) -> BoolElt
{True iff v is a primitive integral vector in the underlying toric lattice}
    if not assigned v`is_primitive then
        if not IsIntegral(v) then
            v`is_primitive:=false;
        elif not IsZero(v) then
            v`is_primitive:=GCD(Eltseq(v)) eq 1;
        else
            v`is_primitive:=true;
        end if;
    end if;
    return v`is_primitive;
end intrinsic;

intrinsic PrimitiveLatticeVector(v::TorLatElt) -> TorLatElt
{The first toric lattice point on the ray spanned by v}
    if IsPrimitive(v) then
        return v;
    end if;
    if assigned v`primitive then
        return v`primitive;
    end if;
    u:=primitive_nonzero_lattice_vector(v);
    return u;
end intrinsic;

intrinsic Norm(v::TorLatElt) -> FldRatElt
{The value of v*v}
    return (v`row_matrix * Transpose(v`row_matrix))[1,1];
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Useful Functions
/////////////////////////////////////////////////////////////////////////

intrinsic Form(L::TorLat,S::SeqEnum) -> TorLatElt
{The dual vector in the toric lattice dual to L with coordinates S}
    return LatticeVector(Dual(L),S);
end intrinsic;

intrinsic NonvanishingForm(S::SetEnum[TorLatElt]) -> TorLatElt
{}
    require not IsNull(S): "Illegal null sequence";
    require not Zero(Universe(S)) in S:
        "The origin must not be amongst the points";
    if #S eq 0 then return Zero(Dual(Universe(S))); end if;
    return Dual(Universe(S)) ! nonvanishing_form(S);
end intrinsic;

intrinsic NonvanishingForm(S::SeqEnum[TorLatElt]) -> TorLatElt
{A point u in the toric lattice dual to the universe of S such that u * v is non-zero for all v in S}
    require not IsNull(S): "Illegal null sequence";
    require not Zero(Universe(S)) in S:
        "The origin must not be amongst the points";
    if #S eq 0 then return Zero(Dual(Universe(S))); end if;
    return Dual(Universe(S)) ! nonvanishing_form(S);
end intrinsic;

intrinsic KernelBasis(v::TorLatElt) -> SeqEnum[TorLatElt]
{The basis of the dual sublattice anihilated by v}
    return [Dual(Parent(v)) | w : w in Basis(Kernel(Transpose(Matrix(
                                               [PrimitiveLatticeVector(v)]))))];
end intrinsic;

intrinsic LinearSpanEquations(S::SeqEnum[TorLatElt]) -> SeqEnum[TorLatElt]
{The sequence of equations of the minimal linear subspace containing the toric lattice points in the sequence S}
    require not IsNull(S): "Illegal null sequence";
    if IsEmpty(S) then
        return Basis(Dual(Universe(S)));
    end if;
    return [Dual(Universe(S)) | w : w in Basis(Kernel(Transpose(Matrix(
                                      [PrimitiveLatticeVector(v) : v in S]))))];
end intrinsic;

intrinsic LinearSpanGenerators(S::SeqEnum[TorLatElt]) -> SeqEnum[TorLatElt]
{The sequence of generators of the minimal linear subspace containing the toric lattice points in the sequence S}
    require not IsNull(S): "Illegal null sequence";
    if IsEmpty(S) then
        return S;
    end if;
    return [Universe(S) | w : w in Basis(Kernel(Transpose(Matrix(Basis(Kernel(
                 Transpose(Matrix([PrimitiveLatticeVector(v) : v in S]))))))))];
end intrinsic;

intrinsic LinearConeGenerators(S::SeqEnum[TorLatElt]) -> SeqEnum[TorLatElt]
{Non-destructively appends the point -\sum v, for all v in S, to the sequence of points S}
    require not IsNull(S): "Illegal null sequence";
    if IsEmpty(S) then
        return S;
    end if;
    return Append(S,-&+S);
end intrinsic;

intrinsic Index(S::SetEnum[TorLatElt]) -> RngIntElt
{}
    require not IsNull(S): "Illegal null set";
    return index_of_sublattice(Matrix(SetToSequence(S)));
end intrinsic;

intrinsic Index(S::SeqEnum[TorLatElt]) -> RngIntElt
{The index of the sublattice generatated by the toric lattice points in the sequence S}
    require not IsNull(S): "Illegal null sequence";
    return index_of_sublattice(Matrix(S));
end intrinsic;

intrinsic LatticeElementToMonomial(K::Rng,v::TorLatElt) -> RngMPolElt
{The Laurent monomial in the field of fractions of K corresponding to the integral toric lattice point v}
    require Rank(K) eq Dimension(Parent(v)):
        Sprintf("The ring must have %o indeterminates",Dimension(Parent(v)));
    require IsIntegral(v):
        "Argument 2 must be an integral lattive point";
    R:=FieldOfFractions(K);
    v:=Eltseq(v);
    return &*[R | Power(R.i,v[i]) : i in [1..#v] | v[i] ne 0];
end intrinsic;

intrinsic Matrix(S::SeqEnum[TorLatElt]) ->  ModMatRngElt
{The matrix with rows S}
    require not IsNull(S): "Illegal null sequence";
    if #S eq 0 then
        return Matrix(Integers(),0,Dimension(Universe(S)),[Integers()|]);
    end if;
    M:=VerticalJoin([v`row_matrix : v in S]);
    return IsIntegral(S) select Matrix(Integers(),M) else M;
end intrinsic;

intrinsic Matrix(R::Rng,S::SeqEnum[TorLatElt]) ->  ModMatRngElt
{The matrix over R with rows S}
    if IsNull(S) then return Matrix(R,0,0,[R|]); end if;
    if #S eq 0 then return Matrix(R,0,Dimension(Universe(S)),[R|]); end if;
    M:=&cat[PowerSequence(Rationals()) | Eltseq(v`row_matrix) : v in S];
    bool,M:=CanChangeUniverse(M,R);
    require bool: "Element of inner sequence not coercible into argument 1";
    return Matrix(R,#S,Dimension(Universe(S)),M);
end intrinsic;

intrinsic Sort(S::SeqEnum[TorLatElt]) -> SeqEnum[TorLatElt]
{Sorts the sequence S in increasing order determined by the toric lattice}
    require not IsNull(S): "Illegal null sequence";
    if IsIntegral(S) then
        SS:=[PowerSequence(Integers()) | Eltseq(v) : v in S];
    else
        SS:=[PowerSequence(Rationals()) | Eltseq(v) : v in S];
    end if;
    ParallelSort(~SS,~S);
    return S;
end intrinsic;

intrinsic Sort(~S::SeqEnum[TorLatElt])
{Sorts in place the sequence S in increasing order determined by the toric lattice}
    require not IsNull(S): "Illegal null sequence";
    if IsIntegral(S) then
        SS:=[PowerSequence(Integers()) | Eltseq(v) : v in S];
    else
        SS:=[PowerSequence(Rationals()) | Eltseq(v) : v in S];
    end if;
    ParallelSort(~SS,~S);
end intrinsic;

intrinsic Sort(S::{@TorLatElt@}) -> SetIndx[TorLatElt]
{Sorts the the indexed set S in increasing order determined by the toric lattice}
    require not IsNull(S): "Illegal null ordered set";
    if IsIntegral(S) then
        SS:=[PowerSequence(Integers()) | Eltseq(v) : v in S];
    else
        SS:=[PowerSequence(Rationals()) | Eltseq(v) : v in S];
    end if;
    Sort(~SS,~perm);
    return {@ Universe(S) | S[i] : i in Eltseq(perm) @};
end intrinsic;

intrinsic Sort(S::SetEnum[TorLatElt]) -> SeqEnum[TorLatElt]
{The sequence obtained by sorting the set S in increasing order determined by the toric lattice}
    require not IsNull(S): "Illegal null set";
    S:=SetToSequence(S);
    if IsIntegral(S) then
        SS:=[PowerSequence(Integers()) | Eltseq(v) : v in S];
    else
        SS:=[PowerSequence(Rationals()) | Eltseq(v) : v in S];
    end if;
    ParallelSort(~SS,~S);
    return S;
end intrinsic;
