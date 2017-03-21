freeze;

/////////////////////////////////////////////////////////////////////////
// coxring.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42161 $
// $Date: 2013-02-21 20:14:54 +1100 (Thu, 21 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Trivial data type as wrapper for Cox ring data.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": variables_of_ring, is_elmt_of, is_nonunitary_elmt_of, is_strict_subset_of, is_superset_of;
import "../utilities/strings.m": integer_weights_calc_widths, quotient_weights_calc_widths, quotient_weights_seq_to_aligned_string, integer_weights_seq_to_aligned_string, seq_to_string;
import "../lattice/lattice.m": lattice_get_Zlattice;
import "../lattice/map.m": lattice_map;

declare type RngCox;
declare attributes RngCox:
    poly_ring,                 // The underlying polynomaial ring
    integer_weights,           // Seq of int seqs of weights on vars of
                               // poly_ring
    rational_weights,          // Seq of rational seqs of weights on vars of
                               // poly_ring
    irrelevant_ideals,         // Seq of ideals
    is_prime_decomposition,    // True if the ideals are the prime decomp
    fan,                       // Associated toric fan (if known)
    summands,                  // A sequence of Ci if C = C1 x C2 x ...
    is_toric,                  // True if C is known to defined fan,
                               // false if C known not to define a fan.
    ray_lattice,               // Dual to lattice of Cox monomials
                               // i.e. (Z^#variables)
    one_parameter_subgroups_lattice, // Dual to lattice of monomials on the
                               // underlying toric variety
    ray_lattice_map,           // Map from ray_lattice to lattice of
                               // one-parameter subgroups
    divisor_class_group,       // RModule over Integers(), which represents
                               // the divisor class group.
    divisor_class_lattice,     // TorLat, which represents the Cl \otimes Q
    weil_to_class_groups_map,  // The surjective map of RModules from the
                               // underlying module of monomial lattice to
                               // the divisor class group
    weil_to_class_lattice_map; // The surjective map of TorLat from monomial
                               // lattice to the divisor class lattice

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Creates a new Cox ring and assignes the data. Does not attempt to reduce
// the weights, but does tidy up the irrelevant ideal components.
function cox_ring_create(R,B,Z,Q)
    CR := New(RngCox);
    // Calculating the prime decomposition is time consuming, so we try to
    // avoid doing it. However, if the number of gradings is small then it's
    // worth doing it now and getting it out of the way
    if #Z le 5 then
        CR`is_prime_decomposition:=true;
        B := Reverse(Sort(Setseq(Seqset(&cat[PowerSequence(Parent(R)) |
		                                PrimaryDecomposition(I): I in B]))));
    else
        CR`is_prime_decomposition:=false;
    end if;
    CR`irrelevant_ideals:=B;
    CR`poly_ring := R;
    CR`integer_weights := Z;
    CR`rational_weights := Q;
    return CR;
end function;

// Attempts to ensure all gradings are non-negative (if possible)
procedure cox_ring_clear_weights(~W)
    if not IsEmpty(W) then
        L := Universe(W);
        pos_cone := PositiveQuadrant(L);
        L2, phi := Sublattice(W);
        pos_cone2 := pos_cone @@ phi;
        if IsMaximumDimensional(pos_cone2) then
        	W := Sort(phi *  LatticeBasisInCone(pos_cone2));
        end if;
    end if;
end procedure;

// Recursive procedure used by combinatorial_fan() below.
procedure combinatorial_fan_internal(idxs, S, K, ~results)
    // Induct on the possible indices
    found := false;
    j := 1;
    for i in idxs do
        newS := Append(S,i);
        if not is_superset_of(newS, K) then
            found := true;
            $$(idxs[j+1..#idxs], newS, K, ~results);
        end if;
        j +:= 1;
    end for;
    // Did we find anything?
    if not found and not is_strict_subset_of(S, results) then
        Include(~results, Sort(S));
    end if;
end procedure;

// A combinatorial description of the maximal cones of the fan, given as a
// sequence of sequences listing the (indices of) the generating rays of each
// maximal cone. 'n' is the number of rays of the fan, which we label [1..n].
// 'K' is a sequence of sequences of (indices of) rays which describes the
// cones which do NOT occure in the fan.
function combinatorial_fan(K, n)
    // First get the free indices, since any maximal cone will contain them
    free := [Integers() | i : i in [1..n] | not is_elmt_of(i, K)];
    // Now calculate the list of possible additional indices
    idxs := [Integers() | i : i in [1..n] | is_nonunitary_elmt_of(i, K)];
    // Get the sequence containing the maximal cones
    results := [PowerSequence(Integers())|];
    combinatorial_fan_internal(idxs, free, K, ~results);
    return results;
end function;

// Returns a nicely formatted string describing the gradings and the quotient
// gradings.
function print_weights_and_quotient_weights(level,Z,Q,prefix)
    // Is there anything to do?
    len_Z:=#Z;
    len_Q:=#Q;
    if len_Z eq 0 and len_Q eq 0 then return ""; end if;
    // Check that the dimensions look like they'll match up
    if len_Z ne 0 and len_Q ne 0 then
        error if #Representative(Z) ne #Representative(Q),
                "print_weights_and_quotient_weights: Dimensions must match";
    end if;
    // Perhaps there is very little to do?
    if (len_Z gt 7 or len_Q gt 7) and level ne "Maximal" then
        if len_Q gt 0 then
            if len_Z eq 0 then
                if len_Q eq 1 then
                    S:="There is ";
                else
                    S:="There are ";
                end if;
            elif len_Z eq 1 then
                S:="There is one integer grading and ";
            else
                S:=Sprintf("There are %o integer gradings and ",len_Z);
            end if;
            if len_Q eq 1 then
                S cat:= "one quotient grading.";
            else
                S cat:= Sprintf("%o quotient gradings.",len_Q);
            end if;
        else
            S:=Sprintf("There are %o gradings.",len_Z);
        end if;
        return S;
    end if;
    // Build the strings describing the weights
    if len_Z ne 0 then
        prefix_Z:=prefix;
        widths:=integer_weights_calc_widths(Z);
        if len_Q ne 0 then
            d,widths_Q:=quotient_weights_calc_widths(Q);
            widths:=[Maximum(widths[i],widths_Q[i]):i in [1..#widths]];
            str_Q:=quotient_weights_seq_to_aligned_string(Q,d,widths,prefix);
            prefix_Z:=prefix cat "  " cat &cat[" ":i in [1..d]];
        end if;
        str_Z:=integer_weights_seq_to_aligned_string(Z,widths,len_Z ne 0,
                                                                   prefix_Z); 
    else
        d,widths:=quotient_weights_calc_widths(Q);
        str_Q:=quotient_weights_seq_to_aligned_string(Q,d,widths,prefix);
    end if;
    // Package it together in a literate way
    if len_Q eq 0 then
        if len_Z eq 1 then
            ZS:=Sprintf("The grading is:\n%o%o",prefix_Z,str_Z);
        elif len_Z gt 1 then
            ZS:=Sprintf("The %o gradings are:\n%o%o",len_Z,prefix_Z,str_Z);
        end if;
    else
        if len_Z eq 1 then
            ZS:=Sprintf("The integer grading is:\n%o%o",prefix_Z,str_Z);
        elif len_Z gt 1 then
            ZS:=Sprintf("The %o integer gradings are:\n%o%o",len_Z,prefix_Z,
                                                                      str_Z);
        end if;
        if len_Q eq 1 then
            QS:=Sprintf("The quotient grading is:\n%o%o",prefix,str_Q);
        elif len_Q gt 1 then
            QS:=Sprintf("The %o quotient gradings are:\n%o%o",len_Q,prefix,
                                                                      str_Q);
        end if;
    end if;
    if len_Z ne 0 then
        if len_Q ne 0 then
            return QS cat "\n" cat ZS;
        end if;
        return ZS;
    end if;
    return QS;
end function;

// Returns the known components of the irrelevant ideal of the Cox ring. Note
// that this does not attempt to decompose the irrelevant ideal -- it simply
// returns (as a sequence) whatever components have been calculated to date.
function cox_ring_irrelevant_ideals(C)
    return C`irrelevant_ideals;
end function;

/////////////////////////////////////////////////////////////////////////
// Creation Functions
/////////////////////////////////////////////////////////////////////////

intrinsic CoxRing( R::RngMPol, B::SeqEnum[RngMPol],
            Z::SeqEnum[SeqEnum[RngIntElt]], Q::SeqEnum[SeqEnum[FldRatElt]] :
            reduceZ:=true ) -> RngCox
{The Cox ring associated to the polynomial ring R, sequence of ideals (or sequence of their generators) B, sequence Z of integer weights on R, and a sequence Q of rational weights on R}
    // Sanity checks
    require IsField(BaseRing(R)): "The base ring must be a field";
    len := Rank(R);
    require &and[ #x eq len : x in Z ] and &and[ #x eq len : x in Q ]:
                "Each sequence of weights in Z and Q must have length equal " *
                "to the number of variables of the polynomial ring R";
    // Tidy up the torus action
    M0 := RModule(Integers(), len);
    M1,phi := sub< M0 | Z >;
    if reduceZ then
        Z := [PowerSequence(Integers()) | Eltseq(phi(g)) : g in Basis(M1)];
    else
        require Dimension(M1) eq #Z:
            "Integer gradings are not linearly independent. Set 'reduceZ' to " *
            "true to admit them";
    end if;
    // Tidy up the quotient action
    L := LCM([Integers()|Denominator(x) : x in &cat Q]);
    G0 := RModule(Integers(L), len);
    G1,phi1 := quo< G0 | Z >;
    G2,phi2 := sub< G1 | [phi1([L*x : x in q]) : q in Q] >;
    basis := [phi2(g) @@ phi1 : g in Generators(G2)];
    intbasis := [[Integers() | x : x in Eltseq(w)] : w in basis];
    Q := [PowerSequence(Rationals()) | [Rationals() | x / L : x in w] :
                                                                w in intbasis];
    // Create and return the Cox ring
    return cox_ring_create(R, B, Z, Q);
end intrinsic;

intrinsic CoxRing( R::RngMPol, B::SeqEnum[SeqEnum[RngMPolElt]],
            Z::SeqEnum[SeqEnum[RngIntElt]], Q::SeqEnum[SeqEnum[FldRatElt]] :
            reduceZ:=true ) -> RngCox
{}
    require IsField(BaseRing(R)): "The base ring must be a field";
    return CoxRing(R,[Parent(R) | ideal<R|f> : f in B],Z,Q : reduceZ:=reduceZ);
end intrinsic;

intrinsic CoxRing( k::Rng, F::TorFan : positive:=true ) -> RngCox
{The Cox over the field k associated to the fan F. Parameter positive (true by default) assures that the positive weights are going to be positive (if possible)}
    // Sanity check
    require IsField(k): "Argument 1 must be a field";
    // Create the polynomial ring and related lattices
    rays := AllRays(F);
    poly_ring := PolynomialRing(k, #rays);
    ray_lattice:=ToricLattice(#rays: name:="RayLattice");
    ray_map:=LatticeMap(ray_lattice, rays);
    L := Ambient(F);

    // now create the other data: irrelevant B, integer weights, quotient weight
    if Rank(poly_ring) eq 0 then
	    // If there is no variable, create the trivial data
        B := [Parent(poly_ring)|];
        Z := [PowerSequence(Integers())|];
        Q := [PowerSequence(Rationals())|];
    else
        // otherwise, calculate the data from fan 
        Z := KernelBasis(ray_map);
        if positive then 
          cox_ring_clear_weights(~Z);
        end if;
        Z := [PowerSequence(Integers()) | Eltseq(v) : v in Z];
        quotient,phi := quo<lattice_get_Zlattice(L) | [Eltseq(r) : r in rays]>;
        Q1 := [L | b : b in Basis(quotient) @@ phi];
        LL,psi := Sublattice(rays);
        dens:=[Integers() | Denominator(q) : q in Q1 @@ psi];
        Q := [ray_lattice | 1 / dens[i] * ((dens[i] * Q1[i]) @@ ray_map) :
                                                               i in [1..#dens]];
        Q := [PowerSequence(Rationals()) | [Rationals() | 
                                 FractionalPart(i) : i in Eltseq(q)] :  q in Q];
        B := [poly_ring|];
        cone_indices:=ConeIndices(F);
        if IsEmpty(cone_indices) then
            Append(~B, &*variables_of_ring(poly_ring));
        end if; 
        for cone in cone_indices do
            coneB := [poly_ring|poly_ring.i:i in {1..#rays} diff cone];
            Append(~B, &*coneB);
        end for;
        B := [Parent(poly_ring) | ideal<poly_ring|B> ];
    end if;
    // We don't need the weights checking, since by construction they're good.
    CR := cox_ring_create(poly_ring, B, Z, Q);
    CR`fan := F;
    CR`is_toric:=true;
    CR`ray_lattice:=ray_lattice;
    CR`ray_lattice_map:=ray_map;
    CR`one_parameter_subgroups_lattice:=L;
    return CR;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Printing function
/////////////////////////////////////////////////////////////////////////

intrinsic PrintNamed( C::RngCox,level::MonStgElt,name::MonStgElt )
{The description of the Cox ring C}
    if level eq "Minimal" then
        if name eq "$" then
            printf "Cox ring with ";
        else
            printf "Cox ring %o with ", name;
        end if;
        num_Z:=NumberOfGradings(C);
        num_Q:=NumberOfQuotientGradings(C);
        if num_Z ne 0 then
            if num_Q eq 0 then
                if num_Z eq 1 then
                    printf "one grading.";
                else
                    printf "%o gradings.", num_Z;
                end if;
            else
                if num_Z eq 1 then
                    printf "one integer grading";
                else
                    printf "%o integer gradings", num_Z;
                end if;
                if num_Q eq 1 then
                    printf " and one quotient grading.";
                elif num_Q gt 1 then
                    printf " and %o quotient gradings.", num_Q;
                end if;
            end if;
        elif num_Q eq 1 then
            printf "one quotient grading.";
        elif num_Q gt 1 then
            printf "%o quotient gradings.", num_Q;
        else
            printf "no gradings.";
        end if;
    else
        if name eq "$" then
            printf "Cox ring with underlying %o", UnderlyingRing(C);
        else
            printf "Cox ring %o with underlying %o", name, UnderlyingRing(C);
        end if;
        prefix:="    ";
        if #C`irrelevant_ideals eq 1 then
            B:=MinimalBasis(C`irrelevant_ideals[1]);
            if level eq "Maximal" or #B lt 15 then
                printf "\nThe irrelevant ideal is:\n%o%o", prefix,
                                                     seq_to_string(B,"(",",");
            end if;
        else
            B:=IrrelevantGenerators(C);
            if not IsEmpty(B) then 
                printf "\nThe components of the irrelevant ideal are:\n%o",
                                                                        prefix;
                for i in [1..#B-1] do
                    printf "%o, ", seq_to_string(B[i],"(",",");
                end for;
                printf "%o", seq_to_string(B[#B],"(",",");
            end if;
        end if;
        str:=print_weights_and_quotient_weights(level,Gradings(C),
                                                   QuotientGradings(C),prefix);
        if #str ne 0 then
                printf "\n%o", str;
        end if;
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Naming and Getting the Underlying Indeterminates
/////////////////////////////////////////////////////////////////////////

intrinsic AssignNames( ~C::RngCox, S::SeqEnum[MonStgElt] )
{Assigned the strings in S to be the names of the indeterminated of the underlying ring of the Cox ring C}
    len:=Rank(UnderlyingRing(C));
    require #S le len: "Argument 2 should have length at most ", len;
    AssignNames(~C`poly_ring,S);
end intrinsic;

intrinsic Name( C::RngCox, i::RngIntElt ) -> RngMPolElt
{The i-th indeterminate of the underlying ring of the Cox ring C}
    len:=Rank(UnderlyingRing(C));
    require i in [1..len]:
        Sprintf("Value for name index should be in the range [1..%o]",len);
    return Name(UnderlyingRing(C),i);
end intrinsic;

intrinsic '.'( C::RngCox, i::RngIntElt ) -> RngMPolElt
{The i-th indeterminate of the underlying ring of the Cox ring C}
    len:=Rank(UnderlyingRing(C));
    require i in [1..len]:
        Sprintf("Value for name index should be in the range [1..%o]",len);
    return UnderlyingRing(C).i;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Equality
/////////////////////////////////////////////////////////////////////////

intrinsic 'eq'( C1::RngCox, C2::RngCox ) -> BoolElt
{True iff the two Cox rings are defined by equal data}
    return UnderlyingRing(C1) cmpeq UnderlyingRing(C2) and
            Gradings(C1) eq Gradings(C2) and
            QuotientGradings(C1) eq QuotientGradings(C2) and
            IrrelevantComponents(C1) eq IrrelevantComponents(C2);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Attributes
/////////////////////////////////////////////////////////////////////////

intrinsic BaseRing( C::RngCox ) -> Fld
{The base field of the Cox ring C}
    return BaseRing(UnderlyingRing(C));
end intrinsic;

intrinsic UnderlyingRing( C::RngCox ) -> RngMPol
{The underlying polynomial ring of the Cox ring C}
    return C`poly_ring;
end intrinsic;

intrinsic Length( C::RngCox ) -> RngIntElt
{The rank of the underlying polynomial ring of the Cox ring C}
    return Rank(UnderlyingRing(C));
end intrinsic;

intrinsic IrrelevantIdeal( C::RngCox ) -> RngMPol
{The irrelevant ideal associated with the Cox ring C}
    return &meet cox_ring_irrelevant_ideals(C);
end intrinsic;

intrinsic IrrelevantComponents( C::RngCox ) -> SeqEnum[RngMPol]
{A sequence of components of the irrelevant ideal associated with the Cox ring C}
    if not assigned C`is_prime_decomposition or not C`is_prime_decomposition
        then
        C`is_prime_decomposition:=true;
        C`irrelevant_ideals:=Reverse(Sort(Setseq(Seqset(
                                &cat[PowerSequence(Parent(C`poly_ring)) |
                                PrimaryDecomposition(I) :
                                I in cox_ring_irrelevant_ideals(C)]))));
    end if;
    return C`irrelevant_ideals;
end intrinsic;

intrinsic IrrelevantGenerators( C::RngCox ) -> SeqEnum[SeqEnum[RngMPolElt]]
{A sequence of sequences of minimal generators of components of the irrelevant ideal associated with the Cox ring C}
    return [PowerSequence(UnderlyingRing(C)) | MinimalBasis(I) :
                                                I in IrrelevantComponents(C)];
end intrinsic;

intrinsic QuotientGradings( C::RngCox ) -> SeqEnum[SeqEnum[FldRatElt]]
{A sequence of sequences representing all of the rational weight gradings to be applied to the indeterminates of the polynomial ring of the Cox ring C}
    return C`rational_weights;
end intrinsic;

intrinsic NumberOfQuotientGradings( C::RngCox ) -> RngIntElt
{The number of rational weight gradings to be applied to the indeterminates of the polynomial ring of the Cox ring C}
    return #QuotientGradings(C);
end intrinsic;

intrinsic Gradings( C::RngCox ) -> SeqEnum[SeqEnum[RngIntElt]]
{A sequence of sequences representing all of the integer weight gradings to be applied to the indeterminates of the polynomial ring of the Cox ring C}
    return C`integer_weights;
end intrinsic;

intrinsic NumberOfGradings( C::RngCox ) -> RngIntElt
{The number of integer weight gradings to be applied to the indeterminates of the polynomial ring of the Cox ring C}
    return #Gradings(C);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic RayLattice( C::RngCox ) -> TorLat
{The lattice Z^d, where d is the number of monomials. It is dual to Cox Monomial Lattice}
    if not assigned C`ray_lattice then
        require IsField(BaseRing(C)): "Base ring must be a field";
        C`ray_lattice:=ToricLattice(Length(C): name:="RayLattice");
    end if;
    return C`ray_lattice;
end intrinsic;

intrinsic CoxMonomialLattice( C::RngCox ) -> TorLat
{The lattice whose elements represent monomials in C (or Weil Divisors on the underlying toric variety). It is dual to Ray Lattice.}
    return Dual(RayLattice(C));
end intrinsic;

// THINK: If we allow torsion in the lattice, then we can combine ClGroup and
// ClLattice into one object.
intrinsic DivisorClassGroup( C::RngCox ) -> ModED
{The Z-module representing the divisor class group}
    if not assigned C`divisor_class_group then
        require IsField(BaseRing(C)): "Base ring must be a field";
        C`divisor_class_group:=Codomain(WeilToClassGroupsMap(C));
    end if;
    return C`divisor_class_group;
end intrinsic;

intrinsic WeilToClassGroupsMap( C::RngCox ) -> Map[ModED, ModED]
{The surjective map of Z-modules from the underlying Cox monomial lattice to the divisor class group}
    if not assigned C`weil_to_class_groups_map then
        // Sanity check
        require IsField(BaseRing(C)): "Base ring must be a field";
        // Create the map
        weights:=Gradings(C);
        qweights:=QuotientGradings(C);
        R:=RModule(Integers(), #weights+#qweights);
        CML:=lattice_get_Zlattice(CoxMonomialLattice(C));
        qweights_dens:=[Integers() | LCM([Denominator(q) : q in qw]) :
                                                                qw in qweights];
        seq:=[PowerSequence(Integers()) | [q*qweights_dens[i]:q in qweights[i]]:
                                         i in [1.. #qweights_dens]] cat weights;
        if IsEmpty(seq) then 
            M:=[Integers() | 0 : i in [1..Length(C)]];
        else
            M:=RowSequence(Transpose(Matrix(seq)));
        end if;
        phi:=hom<CML -> R| M>;       
        Q:=HorizontalJoin(DiagonalMatrix(qweights_dens),ZeroMatrix(Integers(),
                                                     #qweights_dens, #weights));
        QR, pi:=quo<R| RowSequence(Q)>;
        C`weil_to_class_groups_map:=
                             hom<CML -> QR | [QR|pi(phi(b)) : b in Basis(CML)]>;
     end if;
    return C`weil_to_class_groups_map;
end intrinsic;

intrinsic WeilToClassLatticesMap( C::RngCox ) ->  Map[TorLat,TorLat]
{The surjective lattice map from the Cox monomial lattice to the divisor class lattice}
    if not assigned C`weil_to_class_lattice_map then
        require IsField(BaseRing(C)): "Base ring must be a field";
        weights:=Gradings(C);
        if IsEmpty(weights) then 
            C`weil_to_class_lattice_map:=ZeroMap(CoxMonomialLattice(C),
                                                        DivisorClassLattice(C));
        else 
            M:=Transpose(Matrix(weights));
            C`weil_to_class_lattice_map:=LatticeMap(CoxMonomialLattice(C),
                                                     DivisorClassLattice(C), M);
        end if;
    end if;
    return C`weil_to_class_lattice_map;
end intrinsic;

intrinsic DivisorClassLattice( C::RngCox ) -> TorLat
{The divisor class lattice of C (i.e. the lattice of Weil divisors modulo linear equivalence and modulo torsion)}
    if not assigned C`divisor_class_lattice then
        require IsField(BaseRing(C)): "Base ring must be a field";
        C`divisor_class_lattice:=ToricLattice(#Gradings(C):name:="Cl");
    end if;
    return C`divisor_class_lattice;
end intrinsic;
     
intrinsic RayLatticeMap( C::RngCox ) -> TorLat
{The lattice homomorphism from the ray lattice to the lattice of one-parameter subgroups}
    if not assigned C`ray_lattice_map then
        // Sanity check
        require IsField(BaseRing(C)): "Base ring must be a field";
        // If we know the fan, then we return the calculation from the rays
        if assigned C`fan then 
            C`ray_lattice_map:=LatticeMap(RayLattice(C), AllRays(Fan(C)));
        // If this has come from a product we create the fan now to ensure
        // we're in the correct lattice -- THINK: We really only need the
        // rays, so fan is overkill
        elif assigned C`summands then
            C`ray_lattice_map:=LatticeMap(RayLattice(C), AllRays(Fan(C)));
        // Otherwise we calculate the kernel of WeilToClassGroupsMap
        else 
            phi:=WeilToClassGroupsMap(C);
            K:=Kernel(phi);
            seq:=[Domain(phi)|b:b in Basis(K)];
            ChangeUniverse(~seq, Dual(RayLattice(C)));
            M, rlmd:=Sublattice( seq : name:="M", dual_name:="N" );
            C`ray_lattice_map:=Dual(rlmd);
        end if;
    end if;
    return C`ray_lattice_map;
end intrinsic;

intrinsic OneParameterSubgroupsLattice( C::RngCox ) -> TorLat
{The lattice of one-parameter subgroups of the underlying toric variety (i.e. the dual of the monomial lattice)}
    if not assigned C`one_parameter_subgroups_lattice then
        require IsField(BaseRing(C)): "Base ring must be a field";
        if assigned C`summands then
            C`one_parameter_subgroups_lattice:=DirectSum(
                           [OneParameterSubgroupsLattice(X) : X in C`summands]);
        else
            C`one_parameter_subgroups_lattice:=Codomain(RayLatticeMap(C));
        end if;
    end if;
    return C`one_parameter_subgroups_lattice;
end intrinsic;

intrinsic MonomialLattice( C::RngCox ) -> TorLat
{The lattice whose elements represent monomials on the underlying toric variety (i.e. the dual of the ray lattice)}
    require IsField(BaseRing(C)): "Base ring must be a field";
    return Dual(OneParameterSubgroupsLattice(C));
end intrinsic;

intrinsic Rays( C::RngCox ) -> SeqEnum[TorLatElt]
{The sequence of rays of the fan associated with the Cox ring C}
    require IsField(BaseRing(C)): "Base ring must be a field";
     // THINK: We shouldn't need the complete fan to only get the rays.
    return AllRays(Fan(C));
end intrinsic;

intrinsic Fan( C::RngCox ) -> TorFan
{The fan associated with the Cox ring C}
    require not assigned C`is_toric or C`is_toric:
        "The Cox ring is not defined by a fan";
    if not assigned C`fan then
        // Sanity check
        require IsField(BaseRing(C)): "Base ring must be a field";
        // If this comes from a direct product then we make use of the fans
        if assigned C`summands then
            F:=Fan([Fan(CC) : CC in C`summands]);
            delete C`summands;
        // Otherwise this is hard work
        else
            // Construct the ray lattice
            n:=Length(C);
            ray_lat:=RayLattice(C);
            // Construct the lattice the fan lives in
            RLM:=RayLatticeMap(C);
            R:=Image(RLM,Basis(ray_lat));
            // Check that the Cox data is compatible with what we're seeing
            bool:=&or[IsZero(r): r in R];
            if bool then 
                C`is_toric:=false;
                require false: "The Cox ring has redundant coordinates";
            end if;
            if not &and[IsPrimitive(r) : r in R] then 
                C`is_toric:=false;
                require false: "The Cox ring is not defined by a fan";
            end if;
            // Construct the maximal cones from the irrelevant ideal
            irrel:=[[Index(V, x) : x in irr | TotalDegree(x) eq 1 ] :
                            irr in IrrelevantGenerators(C)]
                            where V is variables_of_ring(UnderlyingRing(C));
            cone_indices:=combinatorial_fan(irrel,n);
            // Finally, attempt to construct the fan
            if assigned C`is_toric then
                define_fan:=true;
            else 
                define_fan:=false;
            end if;
            try 
                F:=Fan(R,cone_indices : define_fan:=define_fan);
            catch e
                C`is_toric:=false;
                require false: "The Cox ring is not defined by a fan";
            end try;
        end if;
        // If we're here then C is defined by a fan
        C`fan:=F;
        C`is_toric:=true;
    end if;
    return C`fan;
end intrinsic;
