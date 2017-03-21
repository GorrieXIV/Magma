freeze;

/*------------------------------------------------------------------------------------------------*/
/*  Computation of invariants related to the building block attached to a non-CM newform f.
/*  For weight 2 it is the simple variety B_f apearing in the absolute decomposition of
/*  the variety A_f attached by Shimura to f.
/*  For weight >2 the computations can be should be interpreted in terms of the motives
/*  M_f attached by Scholl to f.
/*  Written by Jordi Quer. April 2006.
/*  References:
/*  --- Pyle and Ribet papers in "Modular Curves and Abelian Varieties";
/*      Progress in Mathematics vol. 224 (Birkhäuser), 2004.
/*  --- J. Quer preprint "Field of definition of building blocks" (April 2006).
/*------------------------------------------------------------------------------------------------*/

/*******************      CHANGES LOG  --  PLEASE RECORD ALL CHANGES HERE       *******************    
                                             (Thanks  --Steve)

    2007-01, Steve: SystemOfEigenvalues has been changed to return elements in non-absolute FldNum's,
                    and this required a minor change here (converting back to an absolute field).

***************************************************************************************************/

import "inner_twists.m":
    InnerTwistCharacters;

import "misc.m":
    idxG0;

declare attributes ModSym: inner_twists, cm_twists, degmap, 
                           endomorphism_algebra_centre;

/*------------------------------------------------------------------------------------------------*/
//  Test for complex multiplication
/*------------------------------------------------------------------------------------------------*/

intrinsic HasCM(M::ModSym : Proof := false) -> BoolElt, RngIntElt
{Decides whether or not the modular abelian variety attached to the given 
modular symbols space has complex multiplication.}
   return IsCM(M : Proof:=Proof);
end intrinsic;

intrinsic IsCM(M::ModSym : Proof := false) -> BoolElt, RngIntElt
{Decides whether or not the modular abelian variety attached to the given 
modular symbols space has complex multiplication.}
    N := Level(M);
    k := Weight(M);
    if N le 100 or Proof then
        bound := Ceiling(k/12*idxG0(N^2));
    else
        bound := 15 + N div 2;
    end if;
    p := [n : n in [1..bound] | IsPrime(n)];
    ap := SystemOfEigenvalues(M,bound);
    cm_chi := [];
    for chi in [x : x in Elements(DirichletGroup(N)) | IsOdd(x)] do
        iscm := true;
        for i in [1..#p] do
            if Evaluate(chi,p[i]) eq -1 and ap[i] ne 0 then iscm := false; break; end if;
        end for;
        if iscm then Append(~cm_chi,-Conductor(chi)); end if;
    end for;
    require #cm_chi le 1 : "ERROR. More than one CM twist character";
    if #cm_chi eq 0 then
        return false, _;
    else
        return true, cm_chi[1];
    end if;
end intrinsic;

/*------------------------------------------------------------------------------------------------*/
//  Computation of the inner twists of a non-CM newform.
/*------------------------------------------------------------------------------------------------*/

intrinsic InnerTwists(M::ModSym : Proof := false) -> SeqEnum[GrpDrchElt]
{The inner twists characters of the non-CM newform corresponding to the modular symbols space M.
 For level larger than 100 uses by default a non-proved bound;
 this can be changed with the optional parameter Proof.
 WARNING: Even if Proof is True, the program does not prove that every twist returned
 is in fact an inner twist (though they are up to precision 0.00001).}

    if assigned M`inner_twists then return M`inner_twists; end if;

    N := Level(M);

    if Proof and N gt 100 then 
       print "WARNING: Even when Proof is true, the returned twists are only checked to be 
         inner twists up to precision 0.00001";
    end if;
 
    if N le 100 or Proof then
        Minner_twists, Mcm_twists := InnerTwistCharacters(M,true);
    else
        Minner_twists, Mcm_twists := InnerTwistCharacters(M,false);
    end if;
    if #Mcm_twists ne 0 then require false : 
      "The given modular symbols should have no complex multiplication";
    end if;
    M`inner_twists := Minner_twists;
    M`cm_twists := Mcm_twists;
    return M`inner_twists;

end intrinsic;

/*------------------------------------------------------------------------------------------------*/
//  Computation of the "degree map" attached to a non-CM newform:
//  a homomorphism of the absolute Galois group of Q into $F^*/F^{*2}$,
//  given by a list of pairs (t,d) with integer $t$ and $d\in F^*$ giving the degree component.
/*------------------------------------------------------------------------------------------------*/

//  Given nonzero elements of a number field F
//  this function returns a maximal subset of elements independent modulo squares.
function basis_for_bp_modulo_squares(bplist)
    F := Parent(bplist[1]);
    group := [F!1];
    basis := [];
    if F eq Rationals() then
        bplist := [Rationals()!SquarefreeFactorization(Integers()!x) : x in bplist];
        bplist := Sort(bplist);
    else
        bplist := Sort(bplist,func<x,y|Norm(x)-Norm(y)>);
    end if;
    for bp in bplist do
        belongs := false;
        for x in group do
            if IsSquare(bp/x) then belongs := true; end if;
        end for;
        if not belongs then
            Append(~basis,bp);
            for x in group do
                Append(~group,x*bp);
            end for;
        end if;
    end for;
    bpcos := [];
    for bp in basis do
        group := [F!1];
        for x in Exclude(basis,bp) do
            for y in group do
                Append(~group,x*y);
            end for;
        end for;
        Append(~bpcos,<bp,group>);
    end for;
    return bpcos;
end function;

//  Tests whether an element b of a number field belongs to a given group
//  of nonzero elements modulo squares
function belongs_mod_squares(b,group);
    for x in group do
        if IsSquare(b/x) then return true; end if;
    end for;
    return false;
end function;

//  Tests whether a given quadratic character psi is a degree character
function test_quadratic_twisting_character(psi,kernel,bplist)
    for x in bplist do
        p := x[1]; bp := x[2];
        if belongs_mod_squares(bp,kernel) then
            if Evaluate(psi,p) ne 1 then return false; end if;
        else
            if Evaluate(psi,p) ne -1 then return false; end if;
        end if;
    end for;
    return true;
end function;

intrinsic DegreeMap(M::ModSym) -> SeqEnum
{Data defining the map delta: G_Q -> F*/F*^2 associated to the given space of modular symbols,
which must be new and irreducible over Q. Returns a sequence of tuples <t,f>,
where t is in Q and f is in F.}
   
    if assigned M`degmap then 
       return M`degmap, M`endomorphism_algebra_centre; 
    end if;
   
    require IsCuspidal(M) : "The given space of modular symbols must be cuspidal.";
    require M`sign eq 1: 
       "The given space of modular symbols must have sign +1, for example ModularSymbols(N,2,1);";
    D := NewformDecomposition(M);
    require #D eq 1 : 
        "The given space of modular symbols must be spanned by a single Galois orbit of newforms.";
    
    QQ := PolynomialRing(Rationals()); x := QQ.1;
    eps := DirichletCharacter(M);
    N := Level(M);
    bound := 50 + N div 5;  // number of primes used in looking for generators of F.

    p := [n : n in [1..bound] | IsPrime(n)];
    ap := SystemOfEigenvalues(M,bound);

    E := Parent(ap[1]);
    if Type(E) eq RngUPolRes then
        f := Modulus(E);
        E := NumberField(f);
        phi := hom<Parent(f) -> E | E.1>;
        ap := [phi(x) : x in ap];
    end if;
    error if Type(E) cmpne FldNum, "SystemOfEigenvalues provided eigenvalues in the wrong type of field";
    
    if not IsAbsoluteField(E) then
        E := AbsoluteField(E);
        ap := [E!x : x in ap];
    end if;

    bp := [<p[i],ap[i]^2/Evaluate(eps,p[i])> : i in [1..#p] | N mod p[i] ne 0 and ap[i] ne 0]; 
    degF := Dimension(M)*Degree(BaseField(M)) div #InnerTwists(M);

    for x in bp do
        g := MinimalPolynomial(x[2]);
        if Degree(g) eq degF then
            F := NumberField(g);
            bpgen := x[2];
            break;
        end if;
    end for;
     
    require assigned F and Type(F) in {FldRat,FldCyc,FldNum} :
      "Something is wrong with the field degrees!  Check that the given space of 
       modular symbols is spanned by a single Galois orbit of newforms.";

    if Type(F) eq FldRat then
        bp := [<x[1],F!x[2]> : x in bp];
        EF := E;
    elif Degree(E) eq Degree(F) then
        F, phi := OptimisedRepresentation(E);
        bp := [<x[1],phi(x[2])> : x in bp];
        EF := F;
    else
        F := OptimisedRepresentation(F);
        f := PolynomialRing(F)!DefiningPolynomial(E);
        f_fac := [x[1] : x in Factorization(f) | x[2] eq 1];
        for fac in f_fac do
            EF := NumberField(fac);
            phi := hom<E -> EF|EF.1>;
            if IsCoercible(F,phi(bpgen)) then f := fac; break; end if;
        end for;
        require Degree(f) eq Degree(E) div Degree(F) : "Wrong degree of the polynomial of E/F";
        bp := [<x[1],F!phi(x[2])> : x in bp];
    end if;

    bpbas := basis_for_bp_modulo_squares([x[2] : x in bp]);
    psilist := [x : x in Elements(DirichletGroup(N)) | Order(x) gt 1];
    degmap := [];
    for x in bpbas do
        twist := [];
        for psi in psilist do
            if test_quadratic_twisting_character(psi,x[2],bp) then Append(~twist,psi); end if;
        end for;
        require #twist eq 1 : 
          "Something is wrong in the computation of quadratic twisting characters";
        psi := twist[1];
        t := Conductor(psi); if IsOdd(psi) then t := -t; end if;
        Append(~degmap,<t,x[1]>);
    end for;

    M`degmap := degmap;
    M`endomorphism_algebra_centre := F;
    return degmap,F;
end intrinsic;

/*------------------------------------------------------------------------------------------------*/
//  Computation of the Brauer class of the modular endomorphism algebra
//  and othe obstruction to descend a building block over the field K_P
/*------------------------------------------------------------------------------------------------*/

//  Ramified primes corresponding to the obstruction to find a square root
//  of a Dirichlet character eps
function ramified_places_eps_Q(eps)
    N := Modulus(eps);
    P := [p[1] : p in Factorization(N)];
    if N mod 4 eq 2 then Remove(~P,1); end if;
    e := Eltseq(eps);
    if N mod 8 eq 0 then Remove(~e,2); end if;
    ramified_primes := [P[i] : i in [1..#P] | IsOdd(e[i])];
    if IsOdd(eps) then Append(~ramified_primes,-1); end if;
    return Sort(ramified_primes);
end function;

//  ... and its restriction of the Brauer group of a number field F
function ramified_places_eps_F(eps,F)
    ramified_places := [];
    O := Integers(F);
    ramified_places_inQ := ramified_places_eps_Q(eps);
    if Type(F) eq FldRat then return Sort(ramified_places_inQ); end if;
    if -1 in ramified_places_inQ then
        ramified_places := [p : p in InfinitePlaces(F) | IsReal(p)];
    end if;
    for p in Exclude(ramified_places_inQ,-1) do
        for pi in Factorisation(ideal<O|p>) do
            if IsOdd(Degree(ResidueClassField(pi[1]))*pi[2]) then 
                Append(~ramified_places,Place(pi[1])); end if;
        end for;
    end for;
    return Sort(ramified_places);
end function;

//  2-adic Hilbert symbol
function two_adic_Hilbert_symbol(a,b)
    r := Valuation(a); s := Valuation(b);
    mu := a div 2^r; nu := b div 2^s;
    assert Precision(mu) ge 3 and Precision(nu) ge 3;
    if Valuation(s*((mu^2-1) div 8)+r*((nu^2-1) div 8)+((mu-1)*(nu-1) div 4)) eq 0 then
        return -1;
    end if;
    return 1;
end function;

//  Ramified places (of F) of the quaternion algebra (a,b) where a is a rational integer
//  and b is an element of a number field F
function ramified_places_quat_alg(a,b)
    ramified_places := [];
    F := Parent(b);
    if Type(F) eq FldRat then
        ramified_places := RamifiedPrimes(QuaternionAlgebra<Rationals()|a,b>);
        if a lt 0 and b lt 0 then Append(~ramified_places,-1); end if;
        return Sort(ramified_places);
    end if;
    O := Integers(F);
    a := O!a; b := O!b;
    odd_bad_primes := {p[1] : p in Factorisation(ideal<O|a>)} join {p[1] : p in Factorisation(ideal<O|b>)};
    odd_bad_primes := {p : p in odd_bad_primes | IsOdd(Norm(p))};
    odd_bad_primes := {p : p in odd_bad_primes | IsOdd(Valuation(a,p)) or IsOdd(Valuation(b,p))};
    for p in odd_bad_primes do
        pi := UniformizingElement(Place(p));
        r := Valuation(a,p); s := Valuation(b,p);
        mu := a/pi^r; nu := b/pi^s;
        _ , phi := ResidueClassField(O,p);
        modp := phi((-1)^(r*s)*mu^s*nu^r);
        if not IsSquare(modp) then Append(~ramified_places,Place(p)); end if;
    end for;
    even_bad_primes := {p[1] : p in Factorisation(ideal<O|2>)};
    for p in even_bad_primes do
        pi := UniformizingElement(Place(p));
        s := Valuation(b,p) div 2;
        _ , phi := Completion(F,p:Precision:=10*Degree(F));
        A := pAdicRing(2)!phi(a);
        B := phi(b/pi^(2*s));
        while Parent(B) ne pAdicField(2) do B := Norm(B); end while;
        if two_adic_Hilbert_symbol(A,B) eq -1 then Append(~ramified_places,Place(p)); end if;
    end for;
    infinite_bad_places := {p : p in InfinitePlaces(F) | IsReal(p)};
    for p in infinite_bad_places do
        if Evaluate(F!a,p) lt 0 and Evaluate(F!b,p) lt 0 then Append(~ramified_places,p); end if;
    end for;
    return Sort(ramified_places);
end function;

intrinsic BrauerClass(M::ModSym) -> SeqEnum
{Gives the Brauer class of the endomorphism algebra of the abelian variety A_f
 attached to the newform f corresponding to the modular symbols space M
 (resp. the motive M_f for weight larger than 2).
 It is given as the (possibily empty) list of the places of the centre F
 that ramify in the quaternion algebra representing this Brauer class.}
    degmap, F := DegreeMap(M);
    eps := DirichletCharacter(M);
    ram := Seqset(ramified_places_eps_F(eps,F));
    for x in degmap do
        ram := ram sdiff Seqset(ramified_places_quat_alg(x[1],x[2]));
    end for;

    ram := Sort(Setseq(ram));
    return ram;
end intrinsic;

intrinsic ObstructionDescentBuildingBlock(M::ModSym) -> SeqEnum
{For a modular symbols space M corresponding to a non-CM weight 2 newform f,
 this computes the obstruction to the existence of a building block over K_P
 isogenous to the building block B_f corresponding to the form f.
 This obstruction is given as a list of places of the polyquadratic field K_P.}
    QQ := PolynomialRing(Rationals()); x := QQ.1;
    degmap := DegreeMap(M);

    if #degmap eq 0 then
        L := Rationals();
    else
        qfs := [];
        for d in degmap do Append(~qfs,x^2-d[1]); end for;
        L := AbsoluteField(NumberField(qfs));
    end if;
    eps := DirichletCharacter(M);
    ram_L := ramified_places_eps_F(eps,L);
    return ram_L;
end intrinsic;

/*------------------------------------------------------------------------------------------------*/
/*  Computation of the subspace of modular symbols of given Nebentypus character
/*  and weight corresponding to non-CM newforms for which the field F has bounded degree over Q.
/*------------------------------------------------------------------------------------------------*/

//  Given a polynomial f and an element e of the field of coefficients of the polynomial,
//  this function outputs the polynomial g whose roots are the numbers a_p^2/e,
//  with a_p running over all the roots of the polynomial f.
function polynomial_of_ap2eps(f,e)
    K<T> := Parent(f);
    n := Degree(f);
    g := T^n;
    for i in [0..n-1] do
        x_i := K!0;
        for j in [Max(0,2*i-n)..Min(n,2*i)] do
            x_i +:= (-1)^(n+j)*Coefficient(f,j)*Coefficient(f,2*i-j);
        end for;
        g +:= (x_i/e^(n-i))*T^i;
    end for;
    return g;
end function;

intrinsic BoundedFSubspace(eps::GrpDrchElt, k::RngIntElt, range::SeqEnum[RngIntElt]) ->
    SeqEnum[ModSym]
{Returns the newform subspaces of weight k and Nebentypus character eps corresponding to
 non-CM newforms for which the field F has degree over Q in the given range.}

    eps := MinimalBaseRingCharacter(eps);
    N := Modulus(eps);

    M := CuspidalSubspace(NewSubspace(ModularSymbols(eps,k,1)));
    P := []; p:=1;
    while #P lt 5 do
        p := NextPrime(p);
        if N mod p ne 0 then Append(~P,p); end if;
    end while;

    for p in P do
        hecke_f := HeckePolynomial(M,p);
        deg := 0; for f in Factorisation(hecke_f) do deg := deg + Degree(f[1])*f[2]; end for;
        if deg ne Degree(hecke_f) then
            print "!!!!! Bug in polynomial factorisation !!!!!";
        else;
        pol := Parent(hecke_f)!1;
        for f in [x[1] : x in Factorisation(hecke_f)] do
            f2e := polynomial_of_ap2eps(f,Evaluate(eps,p));
            f2e := Factorisation(f2e)[1,1];
            deg := Max([Degree(MinimalPolynomial(x)) : x in Coefficients(f2e)]);
            if deg*Degree(f2e) le Max(range) then pol := pol*f; end if;
        end for;
        M := Kernel([<p,pol>],M);
        end if;
    end for;

    MM := NewformDecomposition(M);
    MM := [x : x in MM | not IsCM(x)];
    MM := [x : x in MM | Dimension(x)*Degree(BaseRing(x)) div #InnerTwists(x) in range];
    MM := SortDecomposition(MM);
    return MM;
end intrinsic;
