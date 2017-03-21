freeze;
/*
Created  28.9.2001   JK
*/

intrinsic 'subset'(F::FldFun, G::FldFun) -> BoolElt
{Whether F is a subfield of G}
    is_sub, _ := IsSubfield(F, G);
    return is_sub;
end intrinsic;

intrinsic AutomorphismGroup(F::FldFun, K::FldFunG) -> GrpFP, Map
{Return the automorphism group of the extension of the algebraic function field F over its rational base field K}
    A := Automorphisms(F, K);
    G, h := GenericGroup(
		A : Eq := func<a, b | a`Images eq b`Images>, 
		Mult := func<a, b | hom<F -> F | a`Images @ b>>
	   );
    return G, h, Aut(F);
end intrinsic;

declare verbose AutFldFun, 2;

intrinsic Specialization(f::RngUPolElt, a::RngIntElt) ->  RngUPolElt
    {Given f in k[t][x], returns f(a,x).}

    local   hom, coeff_hom, Rx;

    Rx:=Parent(f);
    R:=CoefficientRing(Rx);
    coeff_hom:=hom<R -> R |a>;
    hom:=hom<Rx-> R | coeff_hom, R.1>;

    return hom(f);
end intrinsic;


function FindSpec(f1,f2)
    local  i, g1, g2, Qxy;

    Qxy:=PolynomialRing(PolynomialRing(CoefficientRing(CoefficientRing(Parent(f1)))));
    f1:= Qxy ! f1;
    f2:= Qxy ! f2;
    i:=-1;
    repeat
	i:=i+1;
    until IsIrreducible(Specialization(f1,i)) and
    IsIrreducible(Specialization(f2,i));
    g1:=Specialization(f1,i);
    g2:=Specialization(f2,i);
    p:=CoefficientRing(Qxy) ! [-i,1];
    return g1, g2, p;
end function;

function ComputeDenBound(K)
    /*Computes muliple of the denominator of an integral element of o*/
    local disc, den, o;
    o:=EquationOrderFinite(K);
    disc:=Factorization(Discriminant(o));
    disc:=[x[1]^(x[2] div 2): x in disc];
    if #disc gt 0 then
        den:=&*(disc);
    else /* constant field extension of Q(t) */
        den := RingOfIntegers(BaseField(K))!1;
    end if;
    return den; 
end function;


intrinsic Automorphisms(F::FldFun, K::FldFunG) ->SeqEnum
    {Return the automorphisms of F over its rational base field K}
    local iss, o, L, A, w,  N, f, a, i, g, p, den;

    require ConstantField(F) eq RationalField():
      "Argument 1 must be a finite extension of Q(t)";
    require Characteristic(F) eq 0:
      "F must be a finite extension of Q(t)";
    
    require IsSimple(EquationOrderFinite(F)) : "Argument 1 must be simple";
    
    f:=DefiningPolynomial(EquationOrderFinite(F));
    
    require Degree(f) eq AbsoluteDegree(F):
      "Argument 1 must be an absolute extension";
    
    require K cmpeq BaseField(F) :
      "Argument 2 must be the base field of Argument 1";
    require IsRationalFunctionField(K) :
      "Argument 2 must be Q(t)";
    
    g,_,p:=FindSpec(f,f);
    N<w>:=NumberField(g);
    A:=Automorphisms(N);
    A:=[x(w): x in A];
    A:=[x: x in A |x ne w];
    den:=ComputeDenBound(F);

    B:=[F| F.1];

    for a in A do
        L:=Eltseq(a);
	b:=EquationOrderFinite(F) ! L;
	iss,b:=InternalLiftEmbedding(b, f, p, den); 
	if iss then
	    Append(~B,b);
	end if;
    end for;

    return [hom<F->F |b>: b in B];
end intrinsic;

intrinsic IsSubfield(K::FldFun, L::FldFun) ->  BoolElt, Map
    {True iff K is a subfield of L.}
    local f, g, ff, gg, p, den, issub, h, a, b, LL;

    require Characteristic(L) eq 0:
      "L must be a finite extension of Q(t)";
    require Characteristic(K) eq 0:
      "K must be a finite extension of Q(t)";
    require Degree(L) cmpne Infinity() : "L must be a finite extension of Q(t)";
    require Degree(K) cmpne Infinity() : "K must be a finite extension of Q(t)";

    require IsSimple(EquationOrderFinite(K)) : "Fields must be simple";
    require IsSimple(EquationOrderFinite(L)) : "Fields must be simple";
    require Type(BaseRing(L)) eq FldFunRat and
            CoefficientRing(BaseRing(L)) eq Rationals():
              "L must be a finite extension of Q(t)";

    require Type(BaseRing(K)) eq FldFunRat and
            CoefficientRing(BaseRing(K)) eq Rationals():
              "K must be a finite extension of Q(t)";

    f:=DefiningPolynomial(EquationOrderFinite(K));
    g:=DefiningPolynomial(EquationOrderFinite(L));

    require Degree(f) eq AbsoluteDegree(K):
      "K must be an absolute extension";
    require Degree(g) eq AbsoluteDegree(L):
      "L must be an absolute extension";

    ff,gg,p:=FindSpec(f,g);
    
    N1:=NumberField(ff);
    N2:=NumberField(gg);
    issub, h:=IsSubfield(N1,N2);

    if issub eq false then 
      return issub, _;
    end if;

    den:=ComputeDenBound(L);
    a:=h(N1.1);
    LL:=Eltseq(a);
    b:=EquationOrderFinite(L) ! LL;
    issub, b:=InternalLiftEmbedding(b, f, p, den); 
    if issub then 
	return issub, hom<K->L|b>;
    else
	return issub, _;
    end if;
end intrinsic;

intrinsic IsIsomorphicOverQt(K::FldFun, L::FldFun) ->  BoolElt, Map
    {True iff L is isomorphic to K as extensions of Q(t).}
    local issub, b;
    if Degree(K) ne Degree(L) then 
      return false, _;
    end if;

    require Characteristic(L) eq 0: "L must be a finite extension of Q(t)";
    require Characteristic(K) eq 0: "K must be a finite extension of Q(t)";
    require Degree(L) cmpne Infinity() : "L must be a finite extension of Q(t)";
    require Degree(K) cmpne Infinity() : "K must be a finite extension of Q(t)";

    require IsSimple(EquationOrderFinite(K)) : "Fields must be simple";
    require IsSimple(EquationOrderFinite(L)) : "Fields must be simple";

    issub,b:=IsSubfield(K,L);
    if issub then 
      return issub,b; 
    end if;
    return issub, _;
end intrinsic;

/* Simple examples:

Q:=Rationals();
Qt := PolynomialRing(Q); t := Qt.1;
Qtx := PolynomialRing(Qt); x := Qtx.1;

K:=FunctionField(x^4-t^3);
L:=Subfields(K);
assert #L eq 2;
L:=L[2][1]; //degree 2 subfield
assert IsSubfield(L,K);
LL:=FunctionField(x^2-t);
assert IsIsomorphic(LL,L); 

*/

/* More interesting ones: 

//This polynomial has Galois group C7.
Q:=Rationals();
Qt := PolynomialRing(Q); t := Qt.1;
Qtx := PolynomialRing(Qt); x := Qtx.1;

f:=x^7 + (t^3 + 2*t^2 - t + 13)*x^6 + (3*t^5 - 3*t^4 + 9*t^3 + 24*t^2 - 21*t + 54\
)*x^5 + (3*t^7 - 9*t^6 + 27*t^5 - 22*t^4 + 6*t^3 + 84*t^2 - 121*t + 75)*x^4 + (t^9 - 6*t^8 + 22*t^\
7 - 57*t^6 + 82*t^5 - 70*t^4 - 87*t^3 + 140*t^2 - 225*t - 2)*x^3 + (-t^10 + 5*t^9 - 25*t^8 + 61*t^\
7 - 126*t^6 + 117*t^5 - 58*t^4 - 155*t^3 + 168*t^2 - 80*t - 44)*x^2 + (-t^10 + 8*t^9 - 30*t^8 + 75\
*t^7 - 102*t^6 + 89*t^5 + 34*t^4 - 56*t^3 + 113*t^2 + 42*t - 17)*x + t^9 - 7*t^8 + 23*t^7 - 42*t^6\
+ 28*t^5 + 19*t^4 - 60*t^3 - 2*t^2 + 16*t - 1;
K:=FunctionField(f);
A:=Automorphisms(K, BaseField(K));
assert #A eq 7;
*/
