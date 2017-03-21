freeze;
//////////////////////////////////////////////////////////////////////////
/// intrinsic to produce an 'etale' stratification of scheme X used in ///
//////  the fix for IsLocallyFree on a sheaf /////////////////////////////

declare attributes Sch: EtaleStrat; // StratEltRec - the etale stratification
				    //   worked out below and stored.

import "normal.m": SmallQuotientBasis;

StratEltRec := recformat<
   X		: Sch,	      // the stratification scheme
   F		: RngElt,     // the element that defines X as a subscheme of its
			      // overscheme in the stratum (1 for the top level)
   xmap		: Map,        // hinv Noether normalising map
   xmapi	: Map,	      // h Noether normalising map
   lower_strat  : List        // sequence of closed components of substratum
>;

function relative_diffs(X,m)
// X <= P^(n-1) where projection to the last m coords P^(m-1) gives
// a finite map (k[x_(n-m+1),..x_n] -> k[x_1,..x_n]/IX is a Noether norm).
// returns a (non-saturated) module for the sheaf of relative differentials
// Omega_{X/P^(m-1)}

    R := CoordinateRing(Ambient(X));
    n := Rank(R);
    r := n-m;

    F := Module(R,[1: i in [1..n]]);
    mat := ZeroMatrix(R,Binomial(n,2)-Binomial(m,2),n);
    pairs := [[i,j] : j in [i+1..n],i in [1..r]];
    for i in [1..#pairs] do
	p := pairs[i];
	mat[i,p[1]] := -R.(p[2]); mat[i,p[2]] := R.(p[1]);
    end for;
    Saturate(~X);
    B := MinimalBasis(Ideal(X));

    F1 := Module(R,[2: i in [1..#pairs]]);
    M := quo<F|[F![Derivative(f,i) : i in [1..n]] : f in B] cat
		[b*F.i : i in [1..n], b in B] cat
		[(R.i)*(F.j)-(R.j)*(F.i) : j in [i+1..n],i in [r+1..n]]>;
    mp := Homomorphism(F1,M,mat);
    rels := Kernel(mp);
    Omega := quo<F1|rels>;
    return Omega;

end function;

// IX defines dimension d-1 scheme X in P^(n-1) s.t. x_(n-d+1), .. x_n
// gives a Noether normalisation for IX. Find a sequence of polynomials
// F_1,..F_r non-zero divisors for IX s.t. the finite projection X->P^(d-1)
// defined by the last variables is etale outside of the sub-locus
// given by the F_i 
function bad_locus_polynomials(IX,d)

    /*R := Generic(IX);
    B := RegularSequence(IX : Homogeneous := true);
    n := Rank(R);
    Jmat := Matrix([[Derivative(b,R.i) : i in [1..#B]] : b in B]);
    Jf := Determinant(Jmat);
    Fs := SmallQuotientBasis(IX+ideal<R|Jf>,ideal<R|B>);*/
    Om := relative_diffs(Scheme(Proj(Generic(IX)),IX),d);
    I1 := Saturation(Annihilator(Om));
    Fs := SmallQuotientBasis(I1,IX);
    Fs := &cat[[f[1] : f in SquareFreeFactorization(F)] : F in Fs];
    return Fs;

end function;

forward transform_node;

function transform_list(lst,h,hinv)
  return [* transform_node(n,h,hinv) : n in lst *];
end function;

function transform_node(n,h,hinv)
  R := Generic(n[1]);
  vs := [R.i : i in [1..Rank(R)]];
  I := ideal<R | [hinv(b) : b in Basis(n[1])]>;
  hn := hom<R->R|[m(v) : v in vs]> where m is h*n[2];
  hin := hom<R->R|[m(v) : v in vs]> where m is n[3]*hinv; 
  lst := n[4];
  if #lst gt 0 then lst := transform_list(lst,h,hinv); end if;
  return <I,hn,hin,lst,hinv(n[5])>; 
end function;

function inductive_strat(I,F)
   
    R := Generic(I);
    B := Basis(I);
    vars,h,hinv := NoetherNormalisation(I);
    d := #vars;
    n := Rank(R);
    change_vars := &or[vars[i] ne R.(n-d+i) : i in [1..d]];
    if change_vars then
	B1 := [h(b) : b in B];
	I1 := ideal<R|B1>;
    else
	B1 := B; I1 := I;
    end if;
    Fs := bad_locus_polynomials(I1,d);
    lst := [* *];
    for F in Fs do
	IF := Saturation(ideal<R|B1 cat [F]>);
	if d gt 2 then
	  nod := inductive_strat(IF,F);
	else
	  nod := <IF,i,i,[* *],F> where i is IdentityHomomorphism(R);
	end if;
	if change_vars then
	  nod := transform_node(nod,h,hinv);
	end if;
	Append(~lst,nod);
    end for;
    return <I,h,hinv,lst,F>;

end function;

function node_to_rec(X,nod)
    r := rec<StratEltRec | X := X, xmap := nod[3], xmapi := nod[2], F := nod[5] >;
    lst := [* *];
    for n in nod[4] do
	Append(~lst, node_to_rec(Scheme(Ambient(X),n[1] : Saturated := true),n));
    end for;
    r`lower_strat := lst;
    return r;
end function;

intrinsic EtaleStratification(X::Sch) -> Rec
{For internal use! Returns an etale stratification of the scheme X}

    if assigned X`EtaleStrat then return X`EtaleStrat; end if;
    Saturate(~X);
    nod := inductive_strat(Ideal(X),CoordinateRing(Ambient(X))!1);
    r := node_to_rec(X,nod);
    X`EtaleStrat := r;
    return r;

end intrinsic;

