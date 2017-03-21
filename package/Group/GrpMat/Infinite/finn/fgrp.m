freeze;

/*
 * F-GROUPS, F-SEQUENCES AND F-ELEMENTS
 *
 * Suppose that we have an effective isomorphism f from a group G to
 * another group H such that (i) f^(-1) is not effective and
 * (ii) computations in H are cheapter than in G. If we want to lift
 * back structural information from H to G, we cannot use Magma's
 * standard functions since these don't store how elements can be
 * written as words in the generators.
 *
 * To address this problem, we replace H by an "f-group" F. The elements
 * of F ("f-elements") remember how they were built from the defining
 * generators of F (and hence H). It is then possible to evaluate such
 * f-elements efficiently in G provided G.i --> H.i is an isomorphism.
 * In particular, this is the case for suitable congruence images of
 * finite matrix groups.
 */

import "misc.m": IndexProperty, PandPPrimePart, ExponentElement,
    MyIsFunctionField;

/*
 * The hierarchy
 *
 * FGrp (f-groups, rarely used), FSub (f-subgroups), FElt (f-elements)
 *
 * In practice, we set up some ambient FGrp and then almost exclusively
 * compute with FSub`s and FElt`s.
 */
FGrp := recformat< ngens : Integers(), gens : SeqEnum,
                   inv : SeqEnum, id >;
FElt := recformat< bio : List, elt >;

/*
 * The biography of an f-elt is written as stack-encoded syntax tree.
 * Operators are multiplication, inversion, commutation, powering,
 * and conjugation. Integers correspond to stored generators
 * via i <-> F.i OR to exponents.
 *
 * Example: (F.i, F.j) * F.k is represented by [* i, j, COMM, k, MUL *]
 *
 * I tried using Magma's native GrpSLP, but it was noticeably slower.
 */
MUL := "x";
INV := "-";
COM := "[]";
POW := "^";
CON := "@";

/*
 * Create an f-group from a group.
 */
function GrpToFGrp(G)
    return rec< FGrp | ngens := Ngens(G),
                       gens  := [G.i : i in [1..Ngens(G)]],
                       inv   := [G.-i: i in [1..Ngens(G)]],
                       id    := Id(G) >;
end function;

/*
 * Magma's <G,i> :-> G.i for f-groups.
 */
function FDot(F, i)
    bio := [* i *];
    if i eq 0 then
        elt := F`id;
        bio := [* *];
    elif i gt 0 then
        elt := F`gens[i];
    else
        elt := F`inv[-i];
    end if;
    return rec<FElt | bio := bio, elt := elt>;
end function;

/*
 * Retrieve the underlying group of a (non-empty) FSub.
 */
function FSubToGrp(gens)
    return sub<Parent(gens[1]`elt) | [g`elt : g in gens]>;
end function;

/*
 * Retrieve the underlying group of an FGrp.
 */
function FGrpToGrp(F)
    return FSubToGrp([FDot(F,i) : i in [1..F`ngens]]);    
end function;

function FGrpToFSub(F)
    return [FDot(F,i) : i in [1..F`ngens]];
end function;

Push := Append;
procedure Pop(~stack, ~elt)
    elt := stack[#stack];
    Prune(~stack);
end procedure;

/*
 * Let x be an f-elt of the f-group F. Let G be group such that
 * phi: F.i --> G.i is an isomorphism. This function returns x^phi.
 */
forward GroupifyFElt_noinv, use_noinv_mode;
function GroupifyFElt(G, x)
    local a, b;

   /*
    * Catch simple cases first (not strictly necessary).
    */
    if #x`bio eq 0 then
        return Id(G);
    elif #x`bio eq 1 then
        return G.(x`bio[1]);
    end if;

   /*
    * In some situations, it may be VERY expensive to invert elements
    * of G. In these cases, we should to switch to `no-inverse'-mode;
    * see below.
    */
    if (Type(G) eq GrpMat) and use_noinv_mode(Degree(G), BaseRing(G)) then
        return GroupifyFElt_noinv(G,x);
    end if;

    stack := [* Id(G) *];
    
   /*
    * The following is optimised to make use of the known inverses
    * (G.i)^(-1) = G.(-i) whenever possible. This makes the code
    * somewhat ugly, though.
    */
    for t in x`bio do
        if Type(t) eq RngIntElt then
            Push(~stack, t);
        elif t cmpeq MUL then
            Pop(~stack, ~b);
            if Type(b) eq RngIntElt then b := G.b; end if;
            Pop(~stack, ~a);
            if Type(a) eq RngIntElt then a := G.a; end if;
            Push(~stack, a * b);
        elif t cmpeq COM then
            Pop(~stack, ~b);
            Pop(~stack, ~a);

            if (Type(a) eq RngIntElt) and (Type(b) eq RngIntElt) then
                Push(~stack, G.(-a) * G.(-b) * G.a * G.b);
            elif Type(a) eq RngIntElt then
                Push(~stack, G.(-a) * b^(-1) * G.a * b);
            elif Type(b) eq RngIntElt then
                Push(~stack, a^(-1) * G.(-b) * a * G.b);
            else
                Push(~stack, (a,b));
            end if;
        elif t cmpeq INV then
            Pop(~stack, ~a);
            if Type(a) eq RngIntElt then
                Push(~stack, G.(-a));
            else
                Push(~stack, a^(-1));
            end if;
        elif t cmpeq CON then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            if Type(a) eq RngIntElt then a := G.a; end if;
            if Type(b) eq RngIntElt then
                Push(~stack, G.(-b) * a * G.b);
            else                
                Push(~stack, a^b);
            end if;
        elif t cmpeq POW then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            if Type(a) eq RngIntElt then a := G.a; end if;
            Push(~stack, a^b);
        else
            error "invalid biography of f-element";
        end if;
    end for;
    Pop(~stack, ~a);
    if Type(a) eq RngIntElt then
        return G.a;
    else
        return a;
    end if;
end function;

/*
 * Determines whether we should evaluate in `no-inverse'-mode.
 * This should be refined using more experimental data.
 */
function use_noinv_mode(d,K)
    return 
       /*
        * We should probably balance the degree and the length of the
        * ``biography'' that we evaluate --- but then I don't know what
        * Magma really does behind the scenes...
        */
        (d ge 1000) // heuristic!
        or
       /*
        * For function fields over number fields, even matrix
        * multiplication is very slow. Inverting is virtually
        * impractical.
        */
        (MyIsFunctionField(K) and (Type(BaseRing(K)) ne FldRat));
end function;

/*
 * Alternate `evaluator' for f-elts. This one *never* inverts group
 * elements.
 * Disadvantage: All the remaining operations are performed twice and we
 *               need about twice as much memory.
 */
function GroupifyFElt_noinv(G, x)
    local a, b;
    stack := [* <Id(G),Id(G)> *];
    
   /*
    * The following is optimised to make use of the known inverses
    * (G.i)^(-1) = G.(-i) whenever possible. This makes the code
    * somewhat ugly, though.
    */
    for i in [1..#x`bio] do 
        t := x`bio[i];

        if Type(t) eq RngIntElt then
           /*
            * We use integers for generators and for exponents.
            * Look ahead to find the case we're in.
            */
            if (i lt #x`bio) and (x`bio[i+1] cmpeq POW) then
                Push(~stack, t);
            else
                Push(~stack, <G.t, G.(-t)>);
            end if;
        elif t cmpeq MUL then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            Push(~stack, <a[1] * b[1], b[2] * a[2]>);
        elif t cmpeq COM then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            Push(~stack, <a[2]*b[2]*a[1]*b[1], b[2]*a[2]*b[1]*a[1]>);
        elif t cmpeq INV then
            Pop(~stack, ~a);
            Push(~stack, <a[2],a[1]>);
        elif t cmpeq CON then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            Push(~stack, <b[2] * a[1] * b[1], b[2] * a[2] * b[1]>);
        elif t cmpeq POW then
            Pop(~stack, ~b);
            Pop(~stack, ~a);
            Push(~stack, <a[1]^b, a[2]^b>);
        else
            error "invalid biography of f-element";
        end if;
    end for;
    Pop(~stack, ~a);
    return a[1];
end function;

/*
 * The following functions implement basic computations in f-groups.
 */

// MultFElt(x,y) = x * y
function MultFElt(x, y)
    if x`elt eq (x`elt)^0 then
        return y;
    elif y`elt eq (y`elt)^0 then
        return x;
    else
        return 
            rec< FElt | bio := x`bio cat y`bio cat [* MUL *],
                        elt := x`elt * y`elt>;
    end if;
end function;

// MultFElt(x,k) = x^k
function PowerFElt(x, k)
    z := k eq 0 select
             rec< FElt | bio := [* *], elt := (x`elt)^0 >
         else
             rec< FElt | bio := x`bio cat [* k, POW *],
                         elt := (x`elt)^k >;
                     return z;                     
end function;

// &* [ li[i]^exp[i] : i in [1..n]] for f-elements, where #li ne 0
function PowerProductFElt(li, exp)
    a := PowerFElt(li[1],exp[1]);
    for i in [2..#li] do
        a := MultFElt(a, PowerFElt(li[i],exp[i]));
    end for;
    return a;
end function;

// InverseFElt(x) = x^(-1)
function InverseFElt(x)
    if x`elt eq (x`elt)^0 then
        return rec< FElt | bio := [* *], elt := (x`elt)^0 >;
    elif #x`bio eq 1 then
        return rec< FElt | bio := [* -x`bio[1] *], elt := (x`elt)^(-1) >;
    else
        return(
            rec< FElt | bio := x`bio cat [* INV *], 
                        elt := (x`elt)^(-1)> );
    end if;
end function;

// CommFElt(x,y) = (x,y)
function CommFElt(x,y)
    if (x`elt eq (x`elt)^0) or (y`elt eq (y`elt)^0) then
        return rec< FElt | bio := [* *], elt := (x`elt)^0 >;
    else
        return (
            rec< FElt | bio := x`bio cat y`bio cat [* COM *],
                        elt := (x`elt, y`elt)> );
    end if;
end function;

// ConjFElt(x,y) = x^y
function ConjFElt(x,y)
    if (x`elt eq (x`elt)^0) then
        return rec< FElt | bio := [* *], elt := (x`elt)^0 >;
    elif (y`elt eq (y`elt)^0) then
        return x;
    else
        return
            rec< FElt | bio := x`bio cat y`bio cat [* CON *],
                        elt := (x`elt)^(y`elt) >;
    end if;
end function;

/*
 * Try to find a better generating set for an FSub.
 *
 * We discard representations of the identity and make sure that distinct
 * f-elements represent distinct group elements.
 * Many improvements would be possible....
 */
function PurifyFSub(H)
    if IsEmpty(H) then
        return H;
    end if;
    
    id := (H[1]`elt)^0;
    res := [Universe(H)|];
    for h in H do
        pred := func<x|x`elt eq h`elt>;
        // Maybe we should take the shortest representation of an element
        // whenever there's a choice?
        if (h`elt ne id) and 0 eq IndexProperty(res,pred) then
            Append(~res, h);
        end if;            
    end for;
    return res;
end function;

function OrderFElt(x)
    return Order(x`elt);
end function;

// (x,y) = 1?
function DoCommuteFElt(x,y)
    return (x`elt) * (y`elt) eq (y`elt) * (x`elt);
end function;

// S subset Z(F)?
function IsCentralFSub(F,S)
    return forall{<> : f in F, s in S | DoCommuteFElt(f,s)};
end function;

// [F,F] = 1?
function IsAbelianFGrp(F)
    return forall{<> : j in [i+1..F`ngens], i in [1..F`ngens]
                     | F`gens[i] * F`gens[j] eq F`gens[j] * F`gens[i]};
end function;

// [seq,seq] = 1
function IsAbelianFSub(seq)
    return forall{<> : j in [i+1..#seq], i in [1..#seq]
                     | DoCommuteFElt(seq[i],seq[j])};
end function;

// For F:FSub, x:FElt, compute C_F(x) as an FSub; also return #(x^F)
function CentraliserFSub(F, x)
    orb := [ x ];
    tra := [ PowerFElt(F[1],0) ];
    sta := [ ];
    i := 0;
    while i lt #orb do
        i +:= 1;
	for j in [1 .. #F] do
            w := ConjFElt(orb[i], F[j]);
            k := IndexProperty( orb, func<x|x`elt eq w`elt> );
            if k eq 0 then
                Append( ~orb, w );
                Append( ~tra, MultFElt(tra[i], F[j]) );
            else
               /* `Include' doesn't work here because equality is
                * defined w.r.t. `elt!
                */
                s := MultFElt(MultFElt(tra[i],F[j]),InverseFElt(tra[k]));
                pred := func<x|x`elt eq s`elt>;
                if IndexProperty(sta,pred) eq 0 then
                    Append(~sta, s);
                end if;
	    end if;
        end for;
    end while;
    return sta, #orb;
end function;

// same as CentraliserFSub but F:FGrp
function CentraliserFGrp(F, x)
    return CentraliserFSub([FDot(F,i) : i in [1..F`ngens]], x);
end function;

// Compute the centre of an FSub and its index
function CentreFSub(F)
    Z := F;
    idx := 1;
    for f in F do
        Z, r := CentraliserFSub(Z, f);
        idx *:= r;
        if IsCentralFSub(F,Z) then
            return Z, idx;
        end if;
    end for;
end function;

/*
 * Compute the Sylow p-subgroup (p > 0) or Hall (-p)'-subgroup (p < 0)
 * of the FSub F as an FSub.
 */
function SylowSubgroupFSub(F, p)
    if p gt 0 then
        sylow := true;
    else
	sylow := false;
	p := -p;
    end if;

    ord := [ Order(F`gens[i]) : i in [1..F`ngens] ];
    fac := [ <pa, q> : o in ord | true where pa, q is PandPPrimePart(o,p) ];
    coe := [ <x,y> : t in fac | true where x, y is Xgcd(t[1], t[2]) ];

    if sylow then
	gens := [
            PowerFElt(FDot(F,i),((fac[i,2] * fac[i,2]) mod ord[i])) 
            : i in [1..F`ngens] ];
    else
	gens := [
            PowerFElt(FDot(F,i),((fac [i,1] * fac[i,1]) mod ord[i]))
            : i in [1..F`ngens] ];
    end if;
    return gens;
end function;

/*
 * Given an abelian FSub li, compute an f-elt x such that
 * Order(x) = Exponent(li).
 */
function ExponentElementFSub(li)
    return PowerProductFElt(li, ExponentElement([x`elt:x in li]));
end function;
