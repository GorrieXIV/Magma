freeze;

intrinsic QuantumErrorGroup(Q::CodeQuantum) -> GrpPC
{ Return the abelian group representing all possible errors 
on the quantum system corrected by the quantum code Q.}
    return QuantumErrorGroup(#CoefficientRing(Q), Length(Q));
end intrinsic;


intrinsic QuantumBinaryErrorGroup(n::RngIntElt) -> GrpPC
{Return the abelian group of all possible errors on a length
n binary qbit system.}
    return QuantumErrorGroup(2, n);
end intrinsic;


intrinsic QuantumErrorGroup(p::RngIntElt, n::RngIntElt) -> GrpPC
{Return the abelian group representing all possible errors
on a length n p-ary qbit system, which 
is an extra special group with 2^n + 1 generators. 

The generators correspond to the qubit-flip operators X(i),
the phase-flip operators Z(i), and an overall phase multiplication W
by the p-th root of unity.
The generators appear in the order X(1),Z(1),...,X(n),Z(n),W.}

    return ExtraSpecialGroup(GrpPC, p, n);

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic StabilizerGroup(Q::CodeQuantum) -> GrpPC
{Return the abelian group of errors that defines the
quantum code Q, which is a subgroup of QuantumErrorGroup(Q)};
    return StabiliserGroup(Q, QuantumErrorGroup(Q));
end intrinsic;

intrinsic StabiliserGroup(Q::CodeQuantum) -> GrpPC
{Return the abelian group of errors that defines the
quantum code Q, which is a subgroup of QuantumErrorGroup(Q)};
    return StabiliserGroup(Q, QuantumErrorGroup(Q));
end intrinsic;

intrinsic StabilizerGroup(Q::CodeQuantum, G::GrpPC) -> GrpPC
{Return the abelian group of errors, a subgroup of G,
that defines the quantum code Q.
G should be an instance of the extraspecial group,
G = QuantumErrorGroup(Q).};
    return StabiliserGroup(Q, G);
end intrinsic;

intrinsic StabiliserGroup(Q::CodeQuantum, G::GrpPC) -> GrpPC
{Return the abelian group of errors, a subgroup of G,
that defines the quantum code Q.
G should be an instance of the extraspecial group,
G = QuantumErrorGroup(Q).};

    n := Length(Q);
    F := Alphabet(Q);
    p := Characteristic(F) ^ (Degree(F) div 2);


    require IsExtraSpecial(G) : "G must be the extra special group of errors";
    require Order(G) eq p^(2*n+1) : "G is the wrong size";

    M := StabiliserMatrix(Q : ExtendedFormat := true);
//M;
    n := Length(Q);
    k := Nrows(M);
    Z := Integers();
    
    gens := { &*[ G.( (j gt n) select 2*(j-n) else 2*j-1 ) ^ Z!M[i][j]   
				: j in Support(M[i])  ] : i in [1..k] };

    Include(~gens, G.(2*n+1));

    return sub< G | gens >;
end intrinsic;

    

