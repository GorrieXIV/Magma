freeze;

/*
 * An oracle for finding solutions of a^2 + b^2 = -1.
 * This will never invoke a norm equation solver and only performs
 * cheap computations... it will thus in general fail.
 * There are two ingredients: (i) Real-time solutions if they are
 * theoretically known and (ii) a database of precomputed solutions.
 * The latter are stored as follows:
 *
 * Even type: <p, +1, a, b>, where a and b are the coefficients of
 * polynomials in a primitive p-th root of unity; ord(2 mod p) is even.
 * Note that we could also construct these entries on the fly.
 *
 * Odd type:  <p, -1, a, b>, where a = [a0, a1], b = [b0, b1] corr to
 * a = a0 + sqrt(2) * a1; the ai and bi are again coeff of polynomials;
 * ord(2 mod p) is odd.
 */
 
import "misc.m":  MyIsFunctionField, MyIsQ,
    MinimalPolynomialSemisimpleMatrix, PandPPrimePart, CyclotomicExtension;
 
SO2_solutions := [*
<7, -1, [[-1,-1,-1,0,-1,0], [1/2,1/2,1/2,0,1/2,0]], [[-1,0,0,0,0,0],[1/2,-1/2,-1/2,0,-1/2,0]]>
    *];

/*
 * The smallest missing entries are 23(176), 31(240) 47(368), 71(560).
 * The numbers in brackets denote the smallest corresponding dimensions for
 * which irreducibility testing then fails over the rationals.
 */

/*
 * SO2_retrieve
 *
 * If possible, either fetch a solution of a^2 + b^2 = -1 from the library
 * or construct it on the fly.
 *
 * If allow_sqrt2 = false, then only consider solutions in the p-th
 * (p a prime divisor of m) cyclotomic field; otherwise sqrt(2) may be
 * adjoined.
 *
 * For the construction, we use the formula given in
 *     Huppert: ``Character theory of finite groups'', Example 38.13d.
 * Explicitly, let e = zeta_p where r = ord(2 mod p) is even.
 * Let d = e^(-2^(r-1)). Then
 *     -1 = Norm(d * prod_(t=0)^(r-1) (d^(2^t) + i)).
 */

function SO2_retrieve(m, allow_sqrt2)
    S := PrimeDivisors(m);
    for sol in SO2_solutions do
        if (sol[1] in S) and ((sol[2] eq 1) or allow_sqrt2) then
            // Q: Why does `Explode' fail here?
            return true, sol[1], sol[2], sol[3], sol[4];
        end if;
    end for;
    for p in S do
        ord := Order(Integers(p)!2);
        if IsEven(ord) then
                K := CyclotomicField(p); e := K.1;
                r := ExactQuotient(ord, 2);
    
               /*
                * Represent F = K(i) as tuples; this is faster than
                * constructing F as a field via ext<...>.
                */
                d := e^(-2^(r-1));
                mul := func< x, y |
                    <x[1] * y[1] - x[2]*y[2], x[1] * y[2] + x[2] * y[1]>
                    >;
                x := <d,0>;
                for t in [0..r-1] do
                    x := mul(x, <d^(2^t),1>);
                end for;
                return true, p, +1, Eltseq(x[1]), Eltseq(x[2]);
        end if;
    end for;
    return false, _, _, _, _;
end function;


/*
 * A function for solving a^2 + b^2 = -1 for matrix reps of fields.
 *
 * INPUT:
 * A primitive order-th root of unity `z' over k; |k[z]:k| = phi.
 * Let order = 2^j m and z = x * y accordingly.
 * We assume that -1 is known to be a norm of k[z]/k[x + x^-1,y].
 *
 * OUTPUT:
 * An element of k[z] with norm -1 over k[x+x^-1,y], or `false' if
 * we failed to construct it.
 */
function SO2(z, order, k, phi : NeqnThreshold := Infinity())
   /*
    * (2,2')-decomposition z = x * y.
    */
    twoj, m := PandPPrimePart(order, 2);
    j := Valuation(twoj,2); // twoj = 2^j
    _, u, v := Xgcd(twoj, m);
    x := z^(v * m);
    y := z^(u * twoj);

   /*
    * First attempt: Ask the oracle.
    */
    repeat
        vprintf Finn: "\t does the oracle know a solution? ";
        // the field K[A] contains sqrt(2) if j >= 3
        // TODO: also include the case that sqrt(2) is in K 
        r, p, resord, seqa, seqb := SO2_retrieve(m, j ge 3);
        /* r := false; */ // use this to force use of norm eqn solver
        if r then
            vprintf Finn: "yea (prime = %o)\n", p;
        else
            vprintf Finn: "nay\n";
            break;
        end if;

        vprintf Finn: "\t decoding the oracle's answer... ";
        if j ge 3 then
            sqrti := x^(2^(j-3));
            i := sqrti^2;
        else
            i := x;
        end if;
        zeta := y^(ExactQuotient(m, p));
            
       /*
        * Construct solution.
        */
        case resord:
        when +1:
            a := Evaluate(Polynomial(seqa), zeta);
            b := Evaluate(Polynomial(seqb), zeta);
        when -1:
            // NOTE: only happens for j >= 3; sqrti is then defined
            sqrt2 := sqrti + sqrti^(-1);
            a := Evaluate(Polynomial(seqa[1]),zeta)
                + Evaluate(Polynomial(seqa[2]),zeta) * sqrt2;
            b := Evaluate(Polynomial(seqb[1]),zeta)
                + Evaluate(Polynomial(seqb[2]),zeta) * sqrt2;
        end case;
        vprint Finn: "done";
        return a + b * i;
    until true;
        
   /* 
    * Second attempt: Use a norm equation solver.
    * The computation will be aborted if the degree is too large.
    */
    // top degree = phi * AbsoluteDegree(k)
    if AbsoluteDegree(k) * phi gt NeqnThreshold then 
        vprintf Finn: "\
\t threshold for norm equation solver exceeded (top degree = %o) 

\t To force the computation of a solution, set `NeqnThreshold' to a
\t higher value and repeat the computation. This may take a long time...
\n", AbsoluteDegree(k) * phi;
        return false;
    end if;


    // Q: Maybe try to solve in k directly first?

    C<zeta> := CyclotomicExtension(k, 2^j * m);
    zeta_2  := zeta^(v * m);
    zeta_m  := zeta^(u * 2^j);
    F := sub<C | zeta_2 + zeta_2^(-1), zeta_m>;
    L := ext<F | Polynomial([1,0,1])>;
            
    vprintf Finn: "\t solving norm equation (degree = %o)... ", AbsoluteDegree(L);
    t0 := Cputime();
    r, s := NormEquation(L, F!(-1));
    vprintf Finn: "done [time: %o]\n", Cputime(t0);
    error if not r, "norm equation does not have a solution; this should never happen";
    
   /*
    * We have: a + b * i in L.
    * Get a, b in F, coerce into C so that they are polynomials
    * in zeta, hence in z.
    */
    seqa, seqb := Explode([C!x:x in Eltseq(s[1])]);
    a := Evaluate(Polynomial(Eltseq(seqa)),z);
    b := Evaluate(Polynomial(Eltseq(seqb)),z);
    return a + (x^(2^(j-2))) * b;
end function;

/*
 * IsIrrPrimANC
 *
 * Irreducibility and primitivity testing of non-abelian ANC groups
 * with homogeneous cyclic maximal subgroup and known structure.
 * The input will not be given as a `GrpMat'; MatrixGroup<..> is slow!
 *
 * INPUT:  G1^2 = theta, G2 generates a homogeneous cyclic subgroup of
 *         index 2; the `order' of <G1,G2>, `mu' and `DecideOnly'
 *         as usual
 * OUTPUT: see `IsIrreducibleRelative'
 */
 
function IsIrrPrimANC(G1, G2, order, theta 
           :  mu := false, DecideOnly := false,
              IrrTest := true, PrimTest := true,
              NeqnThreshold := Infinity())
    vprint Finn: "IsIrrPrimANC";
    d := Nrows(G1);
    vprintf Finn: "\t order = %o, theta = %o, degree = %o\n",
        order, theta, d;

    apply_mu := func<x | mu cmpeq false select x else x * mu>;
        
   /*
    * Get the `FldFunRat/FldNum/FldRat' decomposition.
    */        
    K := BaseRing(G1);

    k := MyIsFunctionField(K) select BaseRing(K) else K; // input is not user-generated!
    V := VectorSpace(K, d);
    A := EndomorphismAlgebra(V);
    g := A ! G1;
    z := A ! G2;
    
   /*
    * By working with reps of free groups, we avoid Magma's
    * MatrixGroup<...>  constructor. While this saves some time, setting
    * up the GModule-structure is still the major bottleneck here!
    */
    
    VG := GModule(FreeGroup(2), [G1,G2]);
    
   /*
    * Get dimension `phi' of the irreducible K[G]-module.
    */
    vprintf Finn: "\t getting degree of maximal subfield of K[G]: ";
    phi := Type(k) eq FldRat
             select EulerPhi(ExactQuotient(order,2))
             else Degree(MinimalPolynomialSemisimpleMatrix(G2));
    vprintf Finn: "%o\n", phi;

   /*
    * If the cyclic maximal subgroup is irreducible, then we are done
    * with irreducibility testing. Note that we do not actually need to
    * spin up any K[A]-submodule to detect this case.
    */           
    if d eq phi then
        vprint Finn: "\t the cyclic maximal subgroup is irreducible";
        if not PrimTest then return "irr", _; end if;
        
        vprintf Finn: "\t will now test primitivity\n";

       /*
        * The following is the interesting bit of primitivity testing.
        */

        vprintf Finn: "\t searching for a good odd prime... ";
        S := [p : p in PrimeBasis(order) | IsOdd(p) and (order mod p^2 eq 0)];

        if MyIsQ(k) then
           /*
            * We don't need to check degrees of cyclotomic fields over Q.
            */
            vprintf Finn: "[rational case] ";
            q := IsEmpty(S) select -1 else Rep(S);
            gq := G2^q;
        else
            q := -1; 
            for p in S do
                gq := G2^p;
                if p * Degree(MinimalPolynomialSemisimpleMatrix(gq)) eq d then // or maybe factorise the cyclotomic polynomial?
                    q := p;
                    break;
                end if;
            end for;
        end if;
        vprintf Finn: (q eq -1) select "failure\n" else "%o\n", q;

       /*
        * Only consider p = 2 when it's absolutely necessary.
        * (Tests can be more expensive.).
        */
        if q eq -1 then
            vprintf Finn: "\t checking 2... ";
            
            j := Valuation(order, 2);
            m := order div 2^j; // |G| = 2^j * m

            if MyIsQ(k) then
                vprintf Finn: "[rational case] ";
                
                if (j ge 5) or (theta eq 1) or ( (j eq 4) and (m gt 1) and IsEven(Order(Integers(m)!2)) ) then
                    q := 2;
                    gq := G2^2;
                end if;
            elif 2 * Degree(MinimalPolynomialSemisimpleMatrix(G2^2)) eq d then
                vprintf Finn: "looks promising... ";

                if ( (theta eq  1) or  (j ge 5) )
                   or
                   ( (theta eq -1) and (j eq 4) and
                     ( 
                       ( (m gt 1) and IsEven(Order(Integers(m)!2)) )
                       or
                       forall{1 : d in Decomposition(k,2) | IsEven(LocalDegree(v)) where v is d[1]}
                     )
                   ) then  // NOTE: If G_2 = Q_8, then p = 2 never works.
                    q := 2; gq := G2^2;
                end if;
            end if;

            vprint Finn: (q eq -1) select "failure" else "success";
        end if;
        
        if q eq -1 then
            vprintf Finn: "\t group is primitive\n";
            return "prim", _; 
        end if;

        vprintf Finn: "\t found block stabiliser\n";
        if DecideOnly then return "imp", _; end if;
        
        case theta:
        when 1:
            x := Kernel(g-1).1;
        when -1:
            vprintf Finn: "\t we need to solve a^2 + b^2 = -1\n";
            sol := SO2(z^q, order div (2*q), k, d div q);
            if sol cmpeq false then return "imp", _; end if;
            x := Kernel(g - sol).1;
        end case;
        
        vprintf Finn: "\t constructing sys of imp... ";

       /*
        * U := sub<V | [ x * gq^i : i in [0..(d div q)-1]]>;
        */
        bas := [V| x ];
        for i in [1.. (d div q)-1] do
            x *:= gq;
            Append(~bas, x);
        end for;
        U := VectorSpaceWithBasis(bas);

       /*
        * soi := [U * z^i : i in [0..q-1]];
        */
        soi := [ U ];
        for i in [1..q-1] do
            U *:= z;
            Append(~soi, U);
        end for;
        vprintf Finn: "done\n";

        return "imp", soi;
    end if;
    
   /*
    * Now the cyclic maximal subgroup is reducible but homogeneous.
    * Hence, if G is irreducible, then the group is of quaternion type, V = U (+) Ug,
    * where U is a 1-dim K[A]-subspace.
    */
    vprintf Finn: "\t the cyclic maximal subgroup is reducible\n";

    if not IrrTest then
        if DecideOnly then
            return "imp", _;
        else
            U := sub<V | [V.1 * G2^i : i in [0..d div 2 - 1] ]>;
            return "imp", [U, U * G1]; // this can only happen for e = 2!
        end if;
    end if;
    
   /*
    * Check if for U = V.1 * K[G2], we have V = U (+) U * G1 as required
    * by §6.2. In particular, we then have d = 2 * phi.
    */
    vprintf Finn: "\t attempting to construct system of imprimitivity... ";
    if Dimension(sub<VG|V.1>) lt Dimension(V) then
        vprint Finn: "failed; group is reducible";
        if DecideOnly then return "red", _; else return "red", apply_mu(V.1); end if;
    end if;
    vprint Finn: "success";

    case theta:
    when 1: // dihedral or semidihedral type

        if DecideOnly then return "red", _; else return "red", apply_mu(Kernel(A!G1 + 1).1); end if;

    when -1:// quaternion type

	twon, m := PandPPrimePart(order, 2);
        n := Valuation(twon,2);
        _, u, v := Xgcd(2^(n-1), m);
        	
       /*
        * Find the dimension of the faithful irreducible module.
        * In other words, decide whether a^2 + b^2 = -1 can be solved
        * in the associated cyclotomic extension of `k'.
        * If this is the case, then `e = 1', otherwise `e = 2'.
        */
        vprintf Finn: "\t getting dimension of the irreducible module: ";
        if MyIsQ(k) then
            e := (m gt 1) and ((n ge 4) or IsEven(Order(Integers(m)!2)))
                 select 1 else 2;
        else
            // cheap tests first!
            e :=
              ((m gt 1) or IsEmpty(RealPlaces(k)))
                 and
             (((m gt 1) and IsEven(Order(Integers(m)!2)))
                                or forall{<> : d in Decomposition(k,2)
                                             | IsEven(LocalDegree(v))
                                             where v is d[1]
                                           })
             select 1 else 2;                                           
        end if;
        vprint Finn: e * phi;

        if d eq e * phi then // dim nat mod = dim irr mod, ie: group is irreducible
            if PrimTest then
                if DecideOnly then
                    return "imp", _;
                else
                    U := sub<V | [V.1 * G2^i : i in [0..d div 2 - 1] ]>;
                    return "imp", [U, U * G1]; // this can only happen for e = 2!
                end if;
            end if;
            return "irr", _;
        end if;
        if DecideOnly then return "red", _; end if;
        
        vprint Finn: "\t we need to solve a^2 + b^2 = -1";
        
        sol := SO2(z, order div 2, k, phi : NeqnThreshold := NeqnThreshold);
        if sol cmpeq false then return "red", _; end if;
        
        vprintf Finn: "\t recovering generator of submodule... ";
        x := apply_mu(Kernel(g - sol).1);
        vprint Finn: "done";
        
        return "red", x;
    end case;
end function;
