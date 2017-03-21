freeze;

/*
 * Functions related to the homogeneous decomposition of an abelian group.
 */
 
import "misc.m": MinimalPolynomialSemisimpleMatrix, MatrixRightInverse,
    ExponentElement, MyIsFunctionField, FindNonzeroPoint;
import "congruence.m": CongruenceObject, CongruenceField, Modp;
/*
 * The different modes of operation for `HomogeneousDecompositionAbelian'.
 */
ABELIAN_FULL   := 0;
ABELIAN_SEMI   := 1;
ABELIAN_DECIDE := 2;

/*
 * PrimEltEnvAlgAbCRMatGrp
 *
 * INPUT:  an abelian completely reducible G
 * OUTPUT: a primitive element of the enveloping algebra of G
 *         and its minimal polynomial
 */
function PrimitiveElementAbelianCR( G : thres := 1 )
    local g, x;
    
    vprint Finn: "PrimitiveElementAbelianCR";

   /*
    * Trivial case: G is generated by at most one element.
    */
    if Ngens(G) eq 1 then
	return G.1, MinimalPolynomialSemisimpleMatrix(G.1);
    elif Ngens(G) eq 0 then
	return Id(G), Polynomial(BaseRing(G), [-1,1]);
    end if;
    
    vprintf Finn: "\t getting dimension of enveloping algebra... ";
    A := sub< EndomorphismAlgebra(RSpace(G)) | Generators(G) >;
    d := Dimension(A);
    vprint Finn: d;
    
   /*
    * Once thres = max_thres, the probability of failure below is at
    * most 1/4; cf [Eberly 1991].
    */
    max_thres := 2 * d * (d-1);
    
    vprintf Finn: "\t maybe one of the generators suffices? ";
    if exists(x){ <g,f> :
                   g in Generators(G) |
                   Degree(f) eq d
                   where f is MinimalPolynomialSemisimpleMatrix(g)} then
                   
        vprint Finn: "yes";
        return x[1], x[2];
    end if;
    vprint Finn: "no";
        
   /*
    * Truly `random' elements can result in horrible matrices.
    * Therefore, first try something cheaper. This is just a heuristic! 
    */
    vprintf Finn: "\t first attempt: ";
    for i in [1..12] do
        cand := &+[Random(-2,2) * A!g : g in Generators(G) ];
        mu := MinimalPolynomialSemisimpleMatrix(cand);
        vprintf Finn: "*";
        if Degree(mu) eq d then
            vprint Finn: " (success)";
            return cand, mu;
        end if;
    end for;
    
    vprint Finn: " (failure)";
    vprintf Finn: "\t second attempt: ";
    i := 0;
    repeat
        if (i eq thres) and (thres le max_thres) then
            thres := Maximum(2 * thres, max_thres);
            vprintf Finn: "T";
            i := 0;
        end if;

        cand := &+[Random(-thres,thres) * b : b in Basis(A) ];
        i := i + 1;
        mu := MinimalPolynomialSemisimpleMatrix(cand);
        vprintf Finn: "*";
    until Degree(mu) eq d;
    vprintf Finn: "\n";
    return cand, mu;
end function;


/*
 * INPUT:  U, d-dim vector space (contained in K^sth)
 *         g, d-by-d matrix
 *         fac, factorisation of the minimal polynomial of g
 *         x, sequence of endos of U as d-by-d matrices w.r.t
 *            Basis(U)
 * OUTPUT: kernels of f(g) where `f' is a polynomial in `fac'
 */
function ChopAndInduce(U, g, fac, x)
    vprintf Finn: "ChopAndInduce";
    R := BaseRing(g);
    A := MatrixAlgebra(R, Nrows(g));
    
    mu := BasisMatrix(U);
    r := [* *];
    for f in fac do
        W := Kernel(Evaluate(f[1], A ! g));
       /*
        * abs(W) --> abs(U) is represented by T, hence
        * abs(W) --> abs(U) --> abs(V) = V is represented by T * mu
        */
        T := BasisMatrix(W);
        S := MatrixRightInverse(T);
        newx := [MatrixAlgebra(R,Dimension(W)) | T*x[i]*S : i in [1..#x]];
        Append(~r, <RowSpace(T * mu), newx>);
    end for;
    vprintf Finn: "\n";
    return r;
end function;

// just return the kernels, no induced action
function ChopButDontInduce(U, g, fac)
    return [ Kernel(Evaluate(f[1], A ! g)) * mu: f in fac ]
        where A is MatrixAlgebra( BaseRing(g), Nrows(g))
        where mu is Matrix(Basis(U));
end function;

/*
 * HomogeneousDecompositionAbelian
 *
 * Decompose the natural module of a *finite* completely reducible
 * abelian group over a field of char 0 into its homogeneous components.
 *
 * INPUT:  finite abelian c.r. G over field of char 0
 * PARAMS: primitive_element, a prim elt of the env alg
 *         minimal_polynomia, of prim elt 
 *         mode, ABELIAN_FULL (construct full decomp),
 *               ABELIAN_SEMI (decide whether G is homg, return one
 *                             component if it is not), or
 *               ABELIAN_DECIDE (only true of false).
 */

function HomogeneousDecompositionAbelian(G :
        primitive_element := false, minimal_polynomial := false,
        mode := ABELIAN_FULL, RandomThreshold := -1
        )

    vprint Finn: "HomogeneousDecompositionAbelian";
    
   /*
    * We use the randomised method if the degree is small or a
    * primitive element of K[G] is known.
    */
    if (Ngens(G) le 1) or (primitive_element cmpne false)
        or
        ((Type(BaseRing(G)) eq FldRat)
            and (Degree(G) le RandomThreshold)) then

        vprint Finn: "\t using randomised method",
            (primitive_element cmpne false) or (Ngens(G) le 1)
            select "(known prim elt)"
            else "(small degree)";
              
       /*
        * Get a primitive element.
        */
        if Ngens(G) le 1 then
            primitive_element := G.Ngens(G);
        elif primitive_element cmpeq false then
            primitive_element, minimal_polynomial
                := PrimitiveElementAbelianCR(G);
        end if;

       /*
        * Get its minimal polynomial.
        */ 
        if minimal_polynomial cmpeq false then
	    minimal_polynomial
                := MinimalPolynomialSemisimpleMatrix
                    (primitive_element);
        end if;

        if mode eq ABELIAN_DECIDE then
            //return #fac eq 1, _;
            return IsIrreducible(minimal_polynomial), _;
        end if;
            
        fac := Factorisation(minimal_polynomial);

        vprint Finn: "\t kernel computations";
        case mode:
        when ABELIAN_FULL:
            return ChopButDontInduce(RSpace(G), primitive_element, fac);
        when ABELIAN_SEMI:
            return #fac eq 1,
                   Kernel(Evaluate(fac[1,1], A ! primitive_element))
                   where A is EndomorphismAlgebra(RSpace(G));
        end case;
    end if;
    
   /*
    * Use the ``intrinsic'' method.
    */

    vprint Finn: "\t using intrinsic method";

    K := BaseRing(G);

   /*
    * We store pairs <U, x>, where U <= RSpace(G) and x is a sequence
    * of endos of U represented as matrices w.r.t Basis(U).
    */
    quasi := [* <RSpace(G), [G.i : i in [1..Ngens(G)]]> *];    
    homg  := [ PowerStructure(ModTupFld) | ];

    while not IsEmpty(quasi) do
        top := quasi[#quasi]; Prune(~quasi);
        U := top[1]; x := top[2];

       /*
        * Find potential generator for the action of `x' on `U'.
        */        
        p := CongruenceObject(x);
        xp := [ Modp(x[i],p) : i in [1..#x] ];
        coeff := ExponentElement(xp); 
        a := &*[x[i]^coeff[i] : i in [1..#x]]; 

       /*
        * If the potential generator is inhomogeneous, chop and continue;
        */
        fac := Factorisation(MinimalPolynomialSemisimpleMatrix(a));
        if #fac gt 1 then
            if mode eq ABELIAN_DECIDE then
                return false, _;
            end if;
            quasi cat:= ChopAndInduce(U, a, fac, x);
            continue;
        end if;

       /*
        * `a' acts homogeneously. Test whether <a> = <x[1], x[2], ...>
        */
        
        ap := Modp(a,p);
        Ap := MatrixGroup< Nrows(ap), CongruenceField(p)|ap>;
        
        if forall(i){i : i in [1..#x] | xp[i] in Ap} then
           /*
            * Groups acts cyclically with a homogeneous generator.
            * We found a homogeneous component!
            */
            Append(~homg, U);
            if #homg gt 1 then
                case mode:
                when ABELIAN_SEMI:
                    return false, homg[1];
                when ABELIAN_DECIDE:
                    return false, _;
                end case;
            end if;
            continue;
        end if;

       /*
        * b notin <a>
        */
        b := A ! x[i] where A is MatrixAlgebra(K, Dimension(U));
        e := Order(ap);

        if MyIsFunctionField(BaseRing(G)) then
            point := FindNonzeroPoint(BaseRing(BaseRing(G)),
                { Denominator(i) : i in (Eltseq(a) cat Eltseq(b)) }
                );
        else
            point := false;
        end if;
        
       /*
        * Final computation. X^e - 1 = prod(X - a^j) and `b' is a
        * root of this polynomial. Hence, b - a^j <> 0 is singular
        * for some j. In particular, some b - a^j acts inhomogeneously.
        */
        vprintf Finn: "\t looping: ";

       /*
        * Generate random powers b^j to find an inhomogeneous factor
        * in the product 0 = b^e - 1 = prod( b - a^j, j = 0..e-1 ).
        */
        exponents := {};
        repeat
           /*
            * Get *new* exponent.
            */
            j := Random(e-1);
            if j in exponents then
                continue;
            else
                Include(~exponents, j);
            end if;
            
            c := b - a^j;
            
            mip := MinimalPolynomialSemisimpleMatrix( c : point := point );
            fac := Factorisation(mip);
            if #fac gt 1 then
                if mode eq ABELIAN_DECIDE then
                    return false, _;
                end if;
                vprint Finn: ":)";
                quasi cat:= ChopAndInduce(U, c, fac, x);
                break;
            end if;
            vprintf Finn: ":( ";
        until false;
    end while;

   /*
    * NOTE: If `mode' is ABELIAN_SEMI or ABELIAN_DECIDE, then
    * we know that #homg = 1. Otherwise, we would have detected this
    * above.
    */
    case mode:
    when ABELIAN_FULL:
        return homg;
    when ABELIAN_SEMI:
        return true, homg[1];
    when ABELIAN_DECIDE:
        return true, _;
    end case;
end function;