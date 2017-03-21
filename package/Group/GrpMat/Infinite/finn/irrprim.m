freeze;

/*
 * Irreducibility and primitivity testing of finite nilpotent
 * matrix groups.
 */

declare verbose Finn, 1;

import "fgrp.m": FGrp, FElt, FDot, MultFElt, InverseFElt, GroupifyFElt,
    FGrpToGrp, FGrpToFSub, OrderFElt,
    GrpToFGrp, IsAbelianFGrp, DoCommuteFElt, SylowSubgroupFSub,
    ExponentElementFSub;
import "anc.m": IsIrrPrimANC;
import "decomp.m": ABELIAN_FULL, ABELIAN_SEMI, ABELIAN_DECIDE,
    HomogeneousDecompositionAbelian;
import "noncyclic.m": HasNoncyclicAbelian;
import "congruence.m": CongruenceObject, Modp,
    CongruencePrime, CongruenceField;
import "misc.m": MyIsFormallyReal, IndexProperty, InducedMatrixGroup,
    CanHandleField, MinimalPolynomialSemisimpleMatrix, PandPPrimePart,
    ExponentElement;

/*
 * In the papers, the algorithm are described for a group acting on
 * an abstract vector space V. The reduction technique can replace V by a
 * subspace U. In this setting, if a vector which generates a proper
 * submodule is found, then it will be *contained* in the original
 * space V.
 * In the implementation, all the spaces are of the form V=K^d, whence
 * we need to keep track of the base changes underlying a transition
 * from V to U. For this purpose, many functions below take an extra
 * argument `mu' which should be a matrix which is applied to subspaces
 * returned by functions.
 *
 * This argument is ignored for primitivity testing, since for non-ANC
 * groups, we construct a system of imprimitivity from a non-cyclic
 * abelian normal subgroup of the original input group (not some
 * stabiliser which occurs after reduction).
 */

function IsIrrPrimAbelian( G : mu := false, DecideOnly := false,
                               RandomThreshold := -1,
                               IrrTest := true, PrimTest := true
                           )
    vprint Finn: "IsIrrPrimAbelian";

    /* if Degree(G) eq 1 then return (PrimTest select "prim" else "irr"), _; end if; */ // caught below

    apply_mu := func<x | mu cmpeq false select x else x * mu>;
    VG := GModule(G);
    V := RSpace(G);
    
    if IrrTest then
       /*
        * Test if G is homogeneous.
        */
        if DecideOnly then
            is_homg := HomogeneousDecompositionAbelian(G : mode := ABELIAN_DECIDE, RandomThreshold := RandomThreshold);
            if not is_homg then return "red", _; end if;
        else
           /*
            * If G is inhomogeneous, return one of the homogeneous components.
            */
            is_homg, M := HomogeneousDecompositionAbelian(G : mode := ABELIAN_SEMI, RandomThreshold := RandomThreshold);
            if not is_homg then return "red", apply_mu(M.1); end if;
        end if;
        
       /*
        * Now G is irred iff any vector <> 0 generates a proper submodule.
        */
        if Dimension(UG) lt Dimension(VG) where UG is sub<VG | V.1> then
            if DecideOnly then return "red", _; else return "red", apply_mu(V.1); end if;
        end if;
        if not PrimTest then return "irr", _; end if;            
    end if;
    
   /*
    * Test primitivity of G = <g>.
    * Below, G will be supplied to us in this form, so we don't bother
    * to construct g efficiently here.
    */
    vprintf Finn: "\t will now test primitivity\n";

    g := (Ngens(G) eq 1) select G.1 else ExponentElement([G.i : i in [1..Ngens(G)]]);
    n := (assigned G`Order) select G`Order else Order(g); // again, will be known below
    vprintf Finn: "\t order = %o\n", G`Order;
    d := Degree(G);
    
    vprintf Finn: "\t searching for good prime... ";
    S := [p : p in PrimeBasis(n) | n mod p^2 eq 0]; // Q: maybe permute S?
    for p in S do
        gp := g^p;
        if p * Degree(MinimalPolynomialSemisimpleMatrix(gp)) eq Degree(G) then
            vprintf Finn: "%o\n", p;
            if DecideOnly then
                return "imp", _;
            else
               /*
                * Create irred K[gp]-module U.
                * Then [U * g^i : i] is a sys of imp for G.
                */
                vprintf Finn: "\t cosntructing sys of imp... ";
                
               /*
                * U := sub<V| [V.1 * gp^i : i in [0..(d div p)-1]]>;
                */
                x := V.1;
                bas := [V| x ];
                for i in [1.. (d div p)-1 ] do
                    x *:= gp;
                    Append(~bas, x);
                end for;
                U := VectorSpaceWithBasis(bas);
                
               /*
                * soi := [U * g^j : j in [0..p-1]];
                */
                soi := [ U ];
                for i in [1..p-1] do
                    U *:= g;
                    Append(~soi, U);
                end for;
                vprintf Finn: "done\n";
                return "imp", soi;
            end if;
        end if;
    end for;
    vprintf Finn: "none\n";
    return "prim", _;
end function;

/*
 * ReduceDimension
 *
 * `res' will either be the mu-image of a proper submodule
 * for G, res = false (submodule exists but not constructed)
 * or res = true, signifying that G and mu have been updated
 */
procedure ReduceDimension(~G, F, ~mu, decomp, ~res : DecideOnly := false)
    vprint Finn: "ReduceDimension";

   /*
    * Find permutation rep for the action of G on decomp
    */
    gens := [FDot(F,i) : i in [1..F`ngens]];
    m := #gens;
    n := #decomp;

    orb := [1];
    tra := [FDot(F,0)]; // = Id(G)
    sta := [];
    
    vprintf Finn:
        "\t orbit stabiliser computations on %o points... ", n;
    i := 0;
    while i lt #orb do
        i +:= 1;
        for j in [1 .. m] do
           /*
            * We only need to test membership of ONE basis vector.
            */
            //w := Index(decomp, decomp[orb[i]] * G.j);
            w := IndexProperty(decomp, func<U| vec in U>)
                where vec is (decomp[orb[i]].1) * G.j;
            k := Index( orb, w );
            if k eq 0 then
                Append( ~orb, w );
                Append( ~tra, MultFElt(tra[i], FDot(F,j)));
            else
                s := MultFElt(MultFElt(tra[i],FDot(F,j)),
                    InverseFElt(tra[k]));
                pred := func<x|x`elt eq s`elt>;
                if IndexProperty(sta,pred) eq 0 then
                    Append(~sta, s);
                end if;
            end if;
        end for;
    end while;
    vprint Finn: "done";
    
    apply_mu := func<x | mu cmpeq false select x else x * mu>;
    if #orb lt n then
       /*
        * Action is intransitive.
        */
        vprintf Finn:
            "\t action is intransitive (#orbit = %o)\n", #orb;
        res := DecideOnly select false else apply_mu(decomp[1].1);
        return;
    else
       /*
        * Transitive action: Replace G and mu.
        */
        vprint Finn: "\t action is transitive";

        if n eq Degree(G) then
            vprint Finn: "\t monomial shortcut";
            G := MatrixGroup<1,BaseRing(G)|>;
            // we cheat and don't update `mu' at all!
            // this works since G is irreducible
            res := true;
            return;
        end if;

        vprintf Finn: "\t lifting stabiliser... ";
        sta := [GroupifyFElt(G,h) : h in sta];
        vprint Finn: "done";
        vprintf Finn:
        "\t generating new matrix group in degree %o on %o generators... ",
        Dimension(decomp[1]), #sta;
        
        G, lambda := InducedMatrixGroup( sta, decomp[1] );
        vprint Finn: "done";
        mu := lambda * mu;
        res := true;
        return;
    end if;
end procedure;

function IsIrrPrimNilpotentRelative
             (G, mu : DecideOnly := false, CheapTests := false,
                      IrrTest := true, PrimTest := true,
                      RandomThreshold := -1,
                      NeqnThreshold := -1)
    local res;

    vprint Finn: "IsIrrPrimNilpotentRelative";

   /*
    * Did we ever reduce to a smaller degree?
    * If so, we will not test primitivity any more.
    * The actual condition for primitivity testing below will thus
    * be ``PrimTest and (not ever_reduced)''.
    */
    ever_reduced := false;

   /*
    * Assuming that PrimTest = true and the group is irreducible,
    * sys_of_imp will be one of the following after execution of
    * the main loop:
    *     - false, if the input group is primitive,
    *     - true, if the input group is imprimitive but we did not
    *             succeed in constructing a sys of imp, or
    *     - a system of imprimitivity.
    */    
    sys_of_imp := false;
    
    repeat
        if Degree(G) eq 1 then
            if not PrimTest then return "irr", _; end if;
            r := true; // mark the group as irreducible
            break;
        end if;

        vprint Finn: "Current degree:", Degree(G);
        vprint Finn: "Number of generators:", Ngens(G);

        if (not PrimTest) and CheapTests and DecideOnly and IsOdd(Degree(G))
                 and MyIsFormallyReal(BaseRing(G)) then
               /*
                * If DecideOnly = false, we should be able to find a
                * submodule easily beause of the following:
                *   If G is finite nilpotent over a formally real field,
                *   and if G is homogeneous then G is scalar or
                *   Degree(G) is even. (Easy!)
                */
                return "red", _;
        end if;
        
        vprintf Finn: "\t getting congruence homomorphism... ";
        p := CongruenceObject(G);
        vprintf Finn: "codomain: GF(%o^%o)\n", 
            q, Valuation(#CongruenceField(p),q)
            where q is CongruencePrime(p);

       /*
        * SETUP CONGRUENCE HOMOMORPHISM
        */
        vprintf Finn: "\t setting up congruence image... ";
        if (not PrimTest) and CheapTests then
           /*
            * Computing the congruence image requires virtually no extra
            * work in addition to Modp'ing the G.i.
            * We might then as well use the Meat-Axe for this.
            */
            Gmodp := Modp(G,p);
            if IsIrreducible(Gmodp) then
                vprint Finn: "aborted";
                vprint Finn: "\t congruence image is irreducible";
                return "irr", _;
            end if;
            F := GrpToFGrp(Gmodp);
        else
            gens := [Modp(G.i,p) : i in [1..Ngens(G)]];
           /*
            * Inversion mod p seems to be faster than Modp(G.-i,p).
            * Not too surprising... at least it's polynomial time!
            */
            inv  := [x^(-1) : x in gens];
            F := rec<FGrp | ngens := Ngens(G),
                id := IdentityMatrix(CongruenceField(p),
                Degree(G)),
                gens := gens, inv := inv>;
        end if;
        vprintf Finn: "done\n";
        
       /*
        * ABELIAN CASE
        */
        vprintf Finn: "\t is the group abelian? ";
	if IsAbelianFGrp(F) then
            vprint Finn: "yes";
            
           /*
            * For primitivity testing of irreducible cyclic groups, we
            * need a generator so we might as well construct it now.
            * This is quite cheap since we have already set up the
            * cong hom machinery.
            */
            if PrimTest and (not ever_reduced) and IsCyclic(FGrpToGrp(F)) then
                a := ExponentElementFSub(FGrpToFSub(F));
                g := GroupifyFElt(G,a);
                G := MatrixGroup< Degree(G), BaseRing(G) | g >;
                G`Order := OrderFElt(a);
            end if;

            r,x := IsIrrPrimAbelian(
                       G : mu := mu,
                       IrrTest := IrrTest, PrimTest := PrimTest and (not ever_reduced),
                       DecideOnly := DecideOnly, RandomThreshold := RandomThreshold
                     );
                 
            if r eq "imp" then
                sys_of_imp := (assigned x) select x else true;
            end if;
            
            r := (r eq "red") select false else true; // if reducible, x will be a submod or unassigned
            break;
	end if;
        vprint Finn: "no";

       /*
        * EXCEPTIONAL CASE: DEGREE 2
        */
        if (not PrimTest) and (Degree(G) eq 2) then
            vprint Finn: "\t a non-abelian group of degree 2 is irreducible";
            return "irr", _;
        end if;

        r, A, H, H2_is_Q8 := HasNoncyclicAbelian(F : DecideOnly := (not IrrTest) and DecideOnly);
        if r then
            vprint Finn:
                "\t found non-cyclic abelian normal subgroup";
            
            if (not IrrTest) and DecideOnly then return "imp", _; end if;
            
            vprintf Finn:
                "\t lifting subgroup... ";
            A := sub<G|[GroupifyFElt(G,a) : a in A]>;
            vprint Finn: "done";
            
            decomp := HomogeneousDecompositionAbelian(A : RandomThreshold := RandomThreshold);
            
           /*
            * If we haven't already found a sys of imp, store this one.
            * However, only do this during the first round, i.e. not afte reduction.
            */
            if PrimTest and (not ever_reduced) then sys_of_imp := decomp; end if;
        else
            vprint Finn: "\t ANC group detected";

           /*
            * Find cyclic H < G of index 2.
            * Unless `H2_is_Q8', this has already been done
            * by `HasNoncyclicAbelian'
            */
            vprintf Finn: "\t finding cyclic maximal subgroup... ";
            if H2_is_Q8 then
                // H := < Hall 2'-subgroup, any non-central element >
                F2prime := SylowSubgroupFSub(F, -2);
                _ := exists(g){ g : i in [1..F`ngens] |
                    exists{j : j in [1..F`ngens] |
                    not DoCommuteFElt(g, FDot(F,j))}
                     where g is FDot(F,i)};
                H := F2prime cat [g];
            end if;
            vprint Finn: "done";

           /*
            * Find a generator of H.
            */
            h := ExponentElementFSub(H);
            vprintf Finn:
                "\t lifting generator (#bio = %o)... ", #h`bio;
            x := GroupifyFElt(G,h);
            vprint Finn: "done";
            
           /*
            * Make sure it's homogeneous (needed in §6)
            */
            vprintf Finn: "\t is it homogeneous? ";
            f := Factorisation(MinimalPolynomialSemisimpleMatrix(x));
            if #f gt 1 then
                vprint Finn: "no";
                
                if (not IrrTest) and DecideOnly then return "imp", _; end if;
                
                decomp := [ Kernel(Evaluate(g[1], A!x)) : g in f  ]
                    where A is MatrixAlgebra(BaseRing(x), Nrows(x));
                if PrimTest and (not ever_reduced) then sys_of_imp := decomp; end if;
                A := H;
            else
                vprint Finn: "yes";
              
                vprintf Finn: "\t setting up nice generators... ";
                xp := h`elt;
                _ := exists(i){i : i in [1..Ngens(G)]
                                 | not DoCommuteFElt(FDot(F,i),h)};
                g := G.i;
                gp := FDot(F,i)`elt;

                _, pp := PandPPrimePart( Order(gp), 2);
                g := g^pp;
                gp := gp^pp;
                
                order_G := 2 * Order(xp);

                _, pp := PandPPrimePart(Order(xp), 2);
                xp := xp^pp;
                
                I := (gp)^0; 
                if (xp * xp^gp eq -I) and (gp^2 ne I) then
                    g := x^pp * g;
                    gp := Modp(g,p);
                end if;
                eps := (gp^2 eq I) select 1 else -1;
                vprint Finn: "done";
                
                r, x := IsIrrPrimANC(g, x, order_G, eps :
                            IrrTest := IrrTest, PrimTest := PrimTest and not ever_reduced,
                            mu := mu, DecideOnly := DecideOnly,
                            NeqnThreshold := NeqnThreshold);
                        
                if r eq "imp" then
                    sys_of_imp := (assigned x) select x else true;
                end if;
                r := (r eq "red") select false else true;
                break;
            end if;
        end if;
        

       /*
        * A is definitely inhomogeneous at this stage and `decomp' is
        * the homogeneous decomposition of its natural module.
        */
        if (not IrrTest) then
            if DecideOnly or (sys_of_imp cmpeq true) then
                return "imp", _; 
            else
                return "imp", sys_of_imp;
            end if;
        end if;
        
        if Degree(G) eq 2 then
            vprint Finn: "\t stopping reduction in degree 2";
            r := true;
            break;
        end if;
        
       /*
        * Perform the actual reduction to smaller degree.
        */
        ever_reduced := true;
        ReduceDimension(~G, F, ~mu, decomp, ~res : DecideOnly := DecideOnly);
	if res cmpeq true then
            vprint Finn: "\t reduction performed, starting again";
	    continue; // start again
	else
            r := false; // reducible action; res generates a submodule
                        // or res = false
	    x := res;
	    break;
	end if;
    until false;

   /*
    * At this point `r' signifies irreducibility of G and x generates
    * a proper submodule of the original group. In other words, mu
    * has already been applied. This allows us to pass on control
    * to other functions (*Abelian, *ANC, *Meataxe)
    */

    if (not r) or (not PrimTest) then
        if r then
            return "irr", _;
        elif DecideOnly or (not assigned x) or (x cmpeq false) then
            return "red", _;
        else
            return "red", x;
        end if;
    else
        if ((sys_of_imp cmpne false) and DecideOnly) or (sys_of_imp cmpeq true) then
            return "imp", _;
        elif sys_of_imp cmpne false then
            return "imp", sys_of_imp;
        else
            return "prim", _;
        end if;
    end if;
end function;

function IsIrrPrimFiniteNilpotent( G :
        IrrTest       := true,
        PrimTest      := true,
        DecideOnly    := false,
        VectorMode    := false,
        CheapTests    := false,
        NeqnThreshold := Infinity()
    )
    
    t0:= Cputime();
    if (not (IrrTest or PrimTest)) or ((not IrrTest) and VectorMode) then
        return "gigo", _;
    end if;

   /*
    * The important cases of the trivial group.
    */
    if Ngens(G) eq 0 then
        case Degree(G):
        when 1:
            return PrimTest select "prim" else "irr", _;
        else:
            if DecideOnly then // NOTE: If IrrTest = false, then the input is bad. Not our problem then...
                return "red", _;
            else
                return "red", sub<V|V.1> where V is RSpace(G);
            end if;
        end case;
    end if;
    
    r, x := IsIrrPrimNilpotentRelative
              (G, IdentityMatrix(BaseRing(G),Degree(G)) :
              IrrTest := IrrTest, PrimTest := PrimTest,
              DecideOnly := DecideOnly, CheapTests := CheapTests,
              NeqnThreshold := NeqnThreshold,
              RandomThreshold := -1 // IOW: don't ever use the randomised
                                    // method; hard to debug and not even
                                    // much faster when it's fast (which
                                    // is not as often as one might think)
              );

    vprintf Finn: "\t TIME: main computation finished after %o\n",
        Cputime(t0);

    if DecideOnly or (r eq "irr") or (r eq "prim") then
        return r, _;
    elif assigned x then
        if (r eq "imp") or ((r eq "red") and VectorMode) then return r, x; end if;

        // group is reducible and we know a generator of a submodule
        vprintf Finn: "\t generating submodule... ";
        V := RSpace(G);
        MG := sub<GModule(G)|x>;
        vprint Finn: "done";
        
        vprintf Finn: "\t TIME: all done %o\n", Cputime(t0);
        return "red", MG;
    elif r eq "red" then
        vprint Finn: "WARNING: No submodule has been constructed.";
    elif r eq "imp" then
        vprint Finn: "WARNING: No system of imprimitivity has been constructed.";
    end if;
    return r, _;
end function;

// for compatibility with finn 0.4
intrinsic IsIrreducibleFiniteNilpotent( G::GrpMat :
        DecideOnly := false,
        Verify     := false
    ) -> BoolElt, .
    
{
  Test irreducibility of the finite nilpotent matrix group G defined
  over the rationals, a number field, or a rational function field over
  a number field. 
}
    require CanHandleField(BaseRing(G)):
    "Cannot handle groups over this base ring.";

    if Verify then
        require IsNilpotent(G): "G must be nilpotent";
        require IsFinite(G): "G must be finite";
    end if;
    
    r, x := IsIrrPrimFiniteNilpotent(G :
        IrrTest := true, PrimTest := false,
        DecideOnly := DecideOnly, VectorMode := false,
        CheapTests := true, NeqnThreshold := Infinity());
    r := r cmpeq "irr" select true else false;
    if assigned x then return r, x; else return r, _; end if;
end intrinsic;

intrinsic IsPrimitiveFiniteNilpotent( G::GrpMat :
        DecideOnly := false,
        Verify     := false
    ) -> BoolElt, .
    
{
  Test primitivity of the irreducible finite nilpotent matrix group G
  defined over the rationals, a number field, or a rational function
  field over a number field. 
}

    require CanHandleField(BaseRing(G)):
    "Cannot handle groups over this base ring.";

    if Verify then
        require IsNilpotent(G): "G must be nilpotent";
        require IsFinite(G): "G must be finite";
    end if;

    r, x := IsIrrPrimFiniteNilpotent(G :
        IrrTest := true, PrimTest := true,
        DecideOnly := DecideOnly, VectorMode := false,
        CheapTests := true, NeqnThreshold := Infinity());

    require r cmpne "red": "G must be irreducible";

    r := r cmpeq "prim" select true else false;
    if assigned x then return r, x; else return r, _; end if;
end intrinsic;
