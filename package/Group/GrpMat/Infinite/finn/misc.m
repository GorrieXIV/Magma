freeze;

function IndexProperty(seq, pred)
    for i in [1..#seq] do
        if pred(seq[i]) then
            return i;
        end if;
    end for;
    return 0;
end function;

function PandPPrimePart(m, p)
    a := p^Valuation(m, p);
    return a, m div a;
end function;

function MyIsQ(K)
    return (Type(K) eq FldRat) or (AbsoluteDegree(K) eq 1); // don't care about positive char
end function;

function MyIsNumberField(K)
    return Type(K) in {FldRat,FldQuad,FldCyc,FldOrd,FldNum};
end function;

function MyIsFunctionField(K)
    return Type(K) eq FldFunRat;
end function;

function MyAbsoluteField(K)
    return (Type(K) eq FldRat) select K else AbsoluteField(K);
end function;

function MyIsCollection(C)
    return Type(C) in {SeqEnum, SetEnum, List};
end function;

function MyRep(C)
    return Type(C) eq List select C[1] else Rep(C);
end function;

function CanHandleField(K)
    return MyIsNumberField(K)
           or
           ((Type(K) eq FldFunRat) and MyIsNumberField(BaseRing(K)));
end function;

function MyIsFormallyReal(K)
    k := MyIsFunctionField(K) select BaseRing(K) else K;
    return (Type(k) eq FldRat) select true else IsTotallyReal(k);
end function;

/*
 * Let A be an e-by-d matrix of rank e, where e <= d.
 * (In other words, A embeds K^d into K^e.)
 * Return a d-by-e matrix B such that A * B = 1
 */
function MatrixRightInverse(A)
    return
        Transpose(
          Matrix(
            Solution(Transpose(A), IdentityMatrix(R, e)[1..e])
            )
          )
        where R is BaseRing(A)
        where e is Nrows(A);
end function;

/*
 * InducedMatrixGroup
 *
 * INPUT:  M collection over GL(V), U<=V M-invariant
 * OUTPUT: the image of <M> in GL(U) w.r.t. Basis(U), 
 *         the matrix of the inclusion U --> V
 *
 * We do not require M to be a matrix group itself, since Magma's
 * matrix group constructor can be very expensive.
 */
function InducedMatrixGroup( M, U )
    A := BasisMatrix(U);
    B := MatrixRightInverse(A);
    H := MatrixGroup< Dimension(U), R |
                       [A * m * B : m in M] >
           where R is BaseRing(MyRep(M));
    return H, A;
end function;

function IsQ8(G)
    return (Order(G) ge 8) and (IdentifyGroup(G) eq <8,4>);
end function;

function ResidueClassOrder(a, m)
    return Order(Integers(m)!a);
end function;

/*
 * CyclotomicExtension(K,n) = K(zeta_n)
 */
function CyclotomicExtension(K, n)
    if Type(K) eq FldRat then
        return CyclotomicField(n);
    else
        return ext<K | Factorisation(phi)[1,1]>
            where phi is PolynomialRing(K)!CyclotomicPolynomial(n);
    end if;
end function;

function MyEvaluate(f, x)
    if Type(Parent(f).1) in {RngUPolElt,FldFunRatUElt} then
        return Evaluate(f,x[1]);
    else
        return Evaluate(f,x);
    end if;
end function;

// find point in k^n at which all elements of S evaluate to a
// non-zero value; we only look for integral points
function FindNonzeroPoint(k, S)
    n := Rank(Parent(MyRep(S)));
    bound := 2;
    // bias towards (0,...,0); we could be lucky!
    x := [0 : j in [1..n]];
    i := 0;
    repeat
        if i eq bound then
            bound *:= 2;
            i := 0;
        end if;
        if forall{<> : f in S | MyEvaluate(f,x) ne 0} then
            return x;
        end if;
        x := [Random(-bound,bound): j in [1..n]];
        i := i + 1;
    until false;
end function;

function ExtendToFractions(K, f)
    return
        pmap<K -> Codomain(f) | x :-> Numerator(x)@f / Denominator(x)@f>;
end function;

// retrieve the set of `entries' of x, optionally applying `fun'
// to each of them
function GetEntries(x : fun := func<x|x> )
    if (Type(x) eq GrpMatElt) or (Type(x) eq AlgMatElt) then
        S := {fun(e) : e in Eltseq(x)};
    elif Type(x) eq GrpMat then
        S := &join{{fun(e) : e in Eltseq(x.i)} : i in [1..Ngens(x)]};
    elif MyIsCollection(x) then
        S := &join{{fun(e) : e in Eltseq(y)} : y in x};
    end if;
    return S;
end function;

/*
 * ExponentElement
 *
 * INPUT:  a sequence G of generators of a finite group
 * OUTPUT: a sequence `exp' of length r such that G is cyclic if and only
 *         if prod(G.i^exp[i]) is a generator.
 */
function ExponentElement(G)
    vprintf Finn: "ExponentElement";

    if #G eq 1 then
        return [1];
    elif #G eq 0 then
        return [Integers()|];
    end if;

    orders := [ Order(G[i]) : i in [1..#G]];
    fac := [ Factorisation(o) : o in orders ];

   /*
    * S is the set of all primes dividing the order of <G>
    */
    S := { x[1] : x in e, e in fac };

    exp := [0 : i in [1..#G]];
    for p in S do
       /*
        * Cosntruct porders defined by nu_p(Order(G.i)) = porders[i]
        */
	porders := [];
	for f in fac do
	    if exists(i){x : x in f | x[1] eq p} then
		Append(~porders, i[2]);
	    else
		Append(~porders, 0);
	    end if;
	end for;
       /*
        * only incorporate the highest contribution
        */
	a, i := Maximum(porders);	
	exp[i] +:= (orders[i] div p^a);
    end for;
    vprintf Finn: "\n";
    return [exp[i] mod orders[i] : i in [1..#G]];
end function;

/*
 * MinimalPolynomialSemisimpleMatrix
 *
 * A cheap method to compute the minimal polynomial of a
 * semisimple matrix: Take the maximal square-free divisor of the
 * characteristic polynomial.
 *
 * Over function fields, the matrix should also have finite order OR
 * a suitable `point' such that evaluation at `point' preserves the
 * minimal polynomial should be provided.
 */
 
function MinimalPolynomialSemisimpleMatrix(g : denom := false, point := false)
    K := BaseRing(g);
    
   /*
    * Over function fields, compute the minimal polynomial after
    * evaluating at suitable points; this is correct for elts of the
    * k-span of a a FINITE abelian group if `point' is chosen carefully.
    * The user may specify a point for evaluation, or a list of denoms.
    */
    if MyIsFunctionField(K) then
        k := BaseRing(K);
        if point cmpeq false then
            S := denom cmpeq false
                 select { Denominator(i) : i in Eltseq(g)}
                 else denom;
            point := FindNonzeroPoint(k,S);
        end if;
        g := Evaluate(g,
              (Type(K.1) in {RngUPolElt,FldFunRatUElt})
              select point[1]
              else point
              );
    end if;
    f := CharacteristicPolynomial(g);
    ffp := Gcd(f, Derivative(f));
    return PolynomialRing(K) ! Eltseq(ExactQuotient(f, ffp)); 
end function;

