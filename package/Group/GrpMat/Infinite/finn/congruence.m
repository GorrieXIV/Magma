freeze;

declare verbose Congruence, 1;

import "misc.m": MyIsCollection, MyRep, MyIsFunctionField,
                 MyIsNumberField, ExtendToFractions,
                 MyAbsoluteField, GetEntries, FindNonzeroPoint;
/*
 * Methods for congruence homomorphisms.
 *
 * `Users' should only care about the following:
 * CongruenceObject(x) returns a `congruence object', p say, associated
 * with `x'. Here, `x' can be a matrix or a matrix group.
 * The congruence image of `y' is then given by Modp(y,p).
 */

function CongruenceObject(x)
   /*
    * NOTE:
    * We don't consider inverses of generators. For possibly infinite
    * groups the code below would therefore have to be changed!
    */

    t0 := Cputime();

   /*
    * Get the base ring of `x'.
    */
    if MyIsCollection(x) then
        K := BaseRing(MyRep(x));
    else
        K := (Type(B) eq RngInt) select Rationals() else B
             where B is BaseRing(x);
    end if;

    //error if not CanHandleField(K),
    //    "no congruence object implemented for this field";
    
    // NOTE: We may apply `Denominator' directly to elts of k even
    // though we're really interested in the denoms of Eltseqs.

    // NOTE: We should really store most of the stuff below as attributes.
    //       A lot of things only depend on the field.
    if MyIsFunctionField(K) then
        vprint Congruence: "function field case";
        k := MyAbsoluteField(BaseRing(K));

        denoms := GetEntries(x : fun := Denominator);
        vprintf Congruence: "finding non-root... ";
        v := FindNonzeroPoint(BaseRing(K), denoms); // why not just use k?
        vprint Congruence: "done";

        // `Evaluate' does not allow [x] as input.
        v := (Type(K.1) in {RngUPolElt,FldFunRatUElt}) select v[1] else v;
        vprintf Congruence: "evaluating entries... ";
        if Type(x) eq GrpMat then
            X := [Evaluate(x.i,v) : i in [1..Ngens(x)]];
        elif MyIsCollection(x) then
            X := [Evaluate(q,v) : q in x];
        else
            X := Evaluate(x,v);
        end if;
        S := GetEntries(X : fun := Denominator);
        vprint Congruence: "done";
    else
        vprint Congruence: "pure number field case";
        vprintf Congruence: "getting absolute field... ";
        k := MyAbsoluteField(K);
        vprint Congruence: "done";
        vprintf Congruence: "getting denominators... ";
        S := GetEntries(x : fun := func<t | Denominator(k!t)>);
        vprint Congruence: "done";
    end if;
    
    gamma := k.1;
    // `DefiningPolynomial' will in general not return a monic polynomial!
    g := gg div LeadingCoefficient(gg) where gg is DefiningPolynomial(k);
    vprintf Congruence: "Irr(gamma) = %o\n", g;

    if IsIntegral(gamma) then
        vprint Congruence: "prim elt is integral";
        m := 1; theta := gamma;
        f := g;
        L := k; // L = Q(theta)
    else
        vprint Congruence: "prim elt needs scaling";
        coeff := Eltseq(g);
        m := LCM({Denominator(c) : c in coeff});
        vprintf Congruence: "\t m = %o\n", m;
        Include(~S,m);
        theta := m * gamma;
        f := m^N * Evaluate(g,1/m * Parent(g).1) where N is Degree(g);
        vprintf Congruence: "Irr(theta) = %o\n", f;
        L := NumberField(f : Check := false);
    end if;

   /*
    * Numbers to avoid:
    *   - |O_L : Z[theta]|
    *   - discriminant of L (= disc(k/Q))
    *   - the number m from above
    *   - denominators of entries in k (ie: wrt gamma; not theta!)
    */
    if Type(L) ne FldRat then
        R := Integers(L);
        E := EquationOrder(L);
        idx := Index(R,E);
        Include(~S, idx); // maybe only add the prime divisors of `idx'?
        vprintf Congruence: "index = %o\n", idx;
    
        dsc := Discriminant(R);
        Include(~S, Discriminant(R));
        vprintf Congruence: "discriminant = %o\n", dsc;
    else
        vprint Congruence: "index and discriminant trivial: rational case";
        idx := 1;
        dsc := 1;
        R := Integers();
    end if;

    p := 2;
    repeat
        p := NextPrime(p);
        if forall{-1 : s in S | not IsDivisibleBy(s,p)} then
            break;
        end if;
    until false;

    vprintf Congruence: "smallest admissable prime is %o\n", p;
    
    gbar := PolynomialRing(GF(p)) ! g;
    
    r, sigma := HasRoot(gbar);

    if r then
        vprintf Congruence: "gbar has a root in GF(%o): %o\n", p, sigma;
        F := GF(p);
    elif IsIrreducible(gbar) then
        vprint Congruence: "gbar is irreducible";
        F<sigma> := ext<GF(p) | gbar>;
    else
        vprint Congruence: "gbar is reducible w/o linear factors";
        vprintf Congruence: "factoring... ";
        w := Factorisation(gbar)[1,1];
        vprintf Congruence: "done (fdeg = %o)\n", Degree(w);
        F<sigma> := ext<GF(p) | w>;
    end if;
    
   /*
    * If m = 1, then we can work using the old method: decompose p in R
    * and partially extend R->R/P to K
    */
    if Type(k) eq FldRat then
        final := ExtendToFractions(k,f)
            where _, f is ResidueClassField(R,p*R);
    elif false and (m eq 1) and (idx eq 1) then
        final := ExtendToFractions(k, f)
            where _, f is ResidueClassField(R, Decomposition(R,p)[1,1]);
    else
        final := pmap<k -> F | x :-> Evaluate(P!Eltseq(x),sigma)>
            where P is PolynomialRing(GF(p));
    end if;
    vprintf Congruence: "TIME for CongruenceObject: %o\n", Cputime(t0);
    return (assigned v) select [* v, final *] else [* final *];
end function;

function CongruenceField(P)
    return Codomain(P[#P]);
end function;

function CongruencePrime(P)
    return Characteristic(Codomain(P[#P]));
end function;

/*
 * Modp
 *
 * Compute congruence images of matrices and matrix groups.
 * `p' can be `false' (in which case Modp(x,p) = x), a rational prime
 * or a `congruence object'.
 */
function Modp(x, p)
    // no type checking: this function is only used internally!
    //error if not Type(x) in {AlgMatElt, GrpMatElt, GrpMat},
    //"no congruence image implemented for this type";
    
    F := Codomain(p[#p]);
   /*
    * In the rational case, we can coerce directly into the target
    * structure w/o Eltseq'ing.
    */
    if Type(BaseRing(x)) eq FldRat then
        return case<Type(x) |
        AlgMatElt:  MatrixRing(F, Nrows(x)) ! x,
	GrpMatElt:  GL(Nrows(x), F) ! x,
	GrpMat:     G where G is
                    MatrixGroup<Degree(x), F 
                        | [ x.i : i in [1..Ngens(x)]]>,
        default:    false
            >;
    end if;
    
   /*
    * This seems to be the fastest way. However, it fails whenever
    * Eltseq(z) can be coerced into the domain of p[#p]
    */ 
    listp := func< z | Eltseq(z)@p[#p] >; 
    try                                          
        if #p gt 1 then
            return case< Type(x) |
                AlgMatElt:  MatrixRing(F, Nrows(x)) ! listp(Evaluate(x,p[1])),
                GrpMatElt:  GL(Nrows(x), F) ! listp(Evaluate(x,p[1])),
                GrpMat:     G where G is
                MatrixGroup<Degree(x), F 
                | [ listp(Evaluate(x.i,p[1])) : i in [1..Ngens(x)]]>,
                default:    false
                >;
        else
            return case< Type(x) |
                AlgMatElt:  MatrixRing(F, Nrows(x)) ! listp(x),
                GrpMatElt:  GL(Nrows(x), F) ! listp(x),
                GrpMat:     G where G is
                MatrixGroup<Degree(x), F 
                | [ listp(x.i) : i in [1..Ngens(x)]]>,
                default:    false
                >;
        end if;
        catch e // ugly, I know
            listp := func< z | [q@p[1] : q in Eltseq(z)] >;
        
            if #p gt 1 then
                return case< Type(x) |
                    AlgMatElt:  MatrixRing(F, Nrows(x)) ! listp(Evaluate(x,p[1])),
                    GrpMatElt:  GL(Nrows(x), F) ! listp(Evaluate(x,p[1])),
                    GrpMat:     G where G is
                    MatrixGroup<Degree(x), F 
                    | [ listp(Evaluate(x.i,p[1])) : i in [1..Ngens(x)]]>,
                    default:    false
                    >;
            else
                return case< Type(x) |
                    AlgMatElt:  MatrixRing(F, Nrows(x)) ! listp(x),
                    GrpMatElt:  GL(Nrows(x), F) ! listp(x),
                    GrpMat:     G where G is
                    MatrixGroup<Degree(x), F 
                    | [ listp(x.i) : i in [1..Ngens(x)]]>,
                    default:    false
                    >;
            end if;
    end try;
  
    error "we should never get here";

    //if MyIsNumberField(BaseRing(x)) then
    //    listp := func< z | Eltseq(z)@p >;
    //else
    //    listp := func< z | [q@p : q in Eltseq(z)] >;
    //end if;
    
    // return case< Type(x) |
    //     AlgMatElt:  MatrixRing(F, Nrows(x)) ! listp(x),
    //	GrpMatElt:  GL(Nrows(x), F) ! listp(x),
    //	GrpMat:     G where G is
    //                MatrixGroup<Degree(x), F 
    //                    | [ listp(x.i) : i in [1..Ngens(x)]]>,
    //	default:    false
    //	>;
end function;
