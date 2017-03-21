
// Markus' example.

// This example tests most of the functionality. 
// It has nontrivial (twosided) ideal classes and the
// two conjugacy classes of orders have F_5^* and F_25^* 
// as unit groups (these are the only possibilities).

SetVerbose("Quaternion", 1);

F<x>:= RationalFunctionField(GF(5));
Q:= QuaternionAlgebra< F | 2, x * (x+1) * (x+2) >;
assert IsDefinite(Q);

M:= MaximalOrder(Q);
I:= RightIdealClasses(M);
C:= ConjugacyClasses(M); 
assert #C eq 2;

T1:= TwoSidedIdealClasses(C[1]);
T2:= TwoSidedIdealClasses(C[2]);

U1:= UnitGroup(C[1]);
U2:= UnitGroup(C[2]);
assert {#U1, #U2} eq {4, 24};

