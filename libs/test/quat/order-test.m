
P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
F := FieldOfFractions(Z_F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3,b>;

// First type of constructor: Give algebra, a matrix representing the basis elements, 
// and coefficient ideals
M := MatrixAlgebra(F,4) ! 1;
I := [ideal<Z_F | 1> : i in [1..4]];
O := Order(A, M, I);
O;

// Second type of constructor: Give algebra and a pseudomatrix
P := PseudoMatrix(I, M);
O := Order(A, P);
O;

// Third type of constructor: Give a sequence of elements
O := Order([1,alpha,beta,alphabeta] : Check := false);
O := Order([alpha,beta]);

// Example of a sum
O1 := Order([1/3*alpha,beta], [ideal<Z_F | b^2+b+1>, ideal<Z_F | 1>]);
Discriminant(O1);
xi := (1 + alpha + (7+5*b+6*b^2)*beta + (3+b+6*b^2)*alphabeta)/2;
zeta := (-6-25*b-5*b^2)*alpha - 3*beta;
O2 := Order([xi,zeta]);
O := O1+O2;
Discriminant(O);

// Example of a left-multiplier
I := ideal<O | Algebra(O) ! Eltseq(xi), Algebra(O) ! Eltseq(zeta), 2>;
Op := MultiplicatorRing(I);
