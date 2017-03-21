freeze;

/////////////////////////////////////////////////////////////////////////
/*
	INFINITE PSL2 IMAGES OF TWO-GENERATOR GROUPS
	          mch - 09/09

 Provides functions to construct the scheme X over Q of representations of
 F(2)/<rels> into SL2(K) or PSL2(K) for characteristic zero fields K, where
 F(2) is the free group on two generators and rels is an arbitrary set of
 relations. Also determines the closed subschemes of X corr. to geometrically
 reducible images or dihedral,A4,S4,A5 images in PLS2. If the open complement
 U of these closed sets is non-empty, algebraic points of U give representations
 over a finite extension of Q with infinite image.

 Two possibilities:

 1) U non-empty, so have phi: F(2)/<rels> -> PSL2(K), K a number field with
    infinite image, so F<2>/<rels> is infinite itself.
    Further, for all but finitely many primes p, phi can be reduced mod v for
    any place v of characteristic p AND the reduction phi_v corresponds to
    a point in the analogue of U over the finite field, so the reductions
    give surjections of F<2>/<rels> onto a PSL2(k) [or maybe a PGL2(k)]
    for finite fields of any characteristic outside of a finite set.
 2) U is empty. Here, all the homomorphisms of F(2)/<rels> into (P)SL2(K)
    for char(K) = 0 have geom. red., dihedral, A4, S4 or A5 images and the
    same holds for K a field of characteristic p for all p outside of a
    finite set. F<2>/<rels> may or may not be infinite.

The algorithm is the L2-quotient algorithm of Plesken and Fabianska,
constructing X as a subscheme of affine 3-space given by the "trace ideal" of
the relations where the coordinate variables x1,x2,x3 correspond to the
traces of the SL2 images of g1,g2,g1g2 where g1,g2 are the generators of F(2).

NB: In case 2), there may be reps into PSL2(K) with INFINITE cyclic or
INFINITE dihedral images. The functions here currently don't check for this.

Main intrinsic:

HasInfinitePSL2Quotient(ws : signs, full)
 - ws is a sequence of words in a rank 2 free group F2. Determines whether
   F2/<ws> has an infinite PSL2(K) for K a number field as described above.

signs parameter:
- A homomorphism F2/<ws> -> PSL2(K) lifts to a homomorphism F2 -> SL2(K)
  where ws[i] |-> s[i]*I with s[i] = +/- 1. Conversely, any hm from
  F2 -> SL2(K) with ws[i] |-> s[i]*I for some choice of signs s[i], gives
  an hm F2/<ws> -> PSL2(K).

- HasInfinitePSL2Quotient considers the schemes X for  homomorphisms F2 -> SL2(K)
  with ws[i] |-> s[i]*I iterating over all 2^(#ws) possible choices
  of signs.

- However, it may be more efficient for the user to only consider maps for
  certain choices of signs.
  For example, if g1^2 is a relation in ws, g1^2 |-> I
  in SL2(K) means that g1 |-> identity in PSL2(K), so the PSL2(K) image
  would be (maybe infinitely) cyclic, and it is a waste of time to
  consider this possibility.
  Similarly, if g1^r, r odd, is a relation, wlog, in a PSL2 to SL2
  lift, g1^r |-> I and this can be specified.

- The signs parameter allows the user to specify that only certain sign
  combinations may be considered. signs should be a sequence of the
  same length as ws. An entry of 1/-1 means only consider maps with
  w |-> I/-I, and entry of 0 means consider both possibilities.

- For example, if ws is [g1^2,g2^3,(g1*g2)^5] and signs is [-1,1,0], then
  only the two possibilities g1^2 |-> -I, g2^3 |-> I, (g1*g2)^5 |-> I
  and g1^2 |-> -I, g2^3 |-> I, (g1*g2)^5 |-> -I under F2 -> SL2(K) will
  be considered, which involves analysing just two different representation
  spaces X.

- The default is that signs is [0,0,0...] 

full parameter:
- For each representation space X (corresponding to an allowable choice
  of signs s[i]), after removing positive dimensional components
  corresponding to geometrically reducible or dihedral type representations,
  there is often a zero-dimensional subscheme left. The existence of an
  infinite (non-cyclic or dihedral) image homomorphism to PSL2 then comes down
  to examining the finite set of closed points remaining and finding one that
  is not geom red, dihedral,A4,S4 or A5 type. Clearly, once one such is found
  the procedure can stop. However, it might be of interest for the user to
  see the types of ALL of the representations corr. to closed points, if
  the zero-dimensional analysis is performed.

- If full is set to true (default is false), the program will continue
  analysing all of the representations in the 0-dim locus, even after
  one corresponding to an infinite image is found. Furthermore a sequence
  of <signs,types> is also returned which gives, for each sign combination
  of maps considered, the sequence of types corresponding to the 0-dim locus
  [or empty if we don't reduce to 0-dim], given as strings:
  "infinite", "reducible","dihedral","A4","S4", and "A5".

verbose flag: IsInfGrp - values 0 and 1
*/
/////////////////////////////////////////////////////////////////////////

declare verbose IsInfGrp, 1;

function word_to_poly_map(F,P)
// get the map from F (= FreeGroup(2)) -> GL2 with the correct trace
// using "universal matrices"
    K := FieldOfFractions(P);
    R := PolynomialRing(K,1); T := R.1;
    S<a> := quo<R|T^2-K.1*T+1>;
    G := GL(2,S);
    i1 := G!Matrix(2,2,[a,K.2*(a-K.1)+K.3,0,K.1-a]);
    i2 := G!Matrix(2,2,[0,-1,1,K.2]);
    hm := hom<F->G|[i1,i2]>;
    return hm,K; 
end function;

function relations_to_ideal(ws,P)
    F := Parent(ws[1]);
    hm,K := word_to_poly_map(F,P);
    gs := [hm(F!1),hm(F.1),hm(F.2),hm(F.1*F.2)];
    seq := [P|];
    for w in ws do
	wmat := hm(w);
	seq cat:= [Numerator(K!Trace(g*wmat))-Numerator(K!Trace(g)) : g in gs];
    end for;
    return ideal<P|seq>;
end function;

function signed_relations_to_ideal(ws,P)
    F := Parent(ws[1][1]);
    hm,K := word_to_poly_map(F,P);
    gs := [hm(F!1),hm(F.1),hm(F.2),hm(F.1*F.2)];
    seq := [P|];
    for w in ws do
	wmat := hm(w[1]);
	seq cat:= [Numerator(K!Trace(g*wmat))-w[2]*Numerator(K!Trace(g)) : g in gs];
    end for;
    return ideal<P|seq>;
end function;

function types_to_string(types)
    strs := ["infinite","reducible","dihedral","A4","S4","A5"];
    return [strs[t+1] : t in types];
end function;

function ideal_type(I)
// for a prime trace ideal I of k[x,y,z] of dimension 0, return the
// type of the representation in PSL(2,k) as follows:
// 1 - absolutely reducible
// 2 - dihedral
// 3 - A4
// 4 - S4
// 5 - A5
// 0 - other

    P := Generic(I);
    k := BaseRing(I);
    x := P.1; y := P.2; z := P.3;

    // reducible case
    f := x^2+y^2+z^2-x*y*z-4;
    if f in I then return 1; end if;

    d := Degree(Scheme(AffineSpace(P),I));
    if d ge 3 then return 0; end if;

    if d eq 1 then // poss. dihedral or A4
        rxyz := [k!NormalForm(P.i,I) : i in [1..3]];
	n := #[r : r in rxyz | r eq k!0];
	if n ge 2 then return 2; end if;
	m := #[r : r in rxyz | (r eq k!1) or (-r eq k!1)];
	if ((n eq 1) and (m eq 2)) or (m eq 3) then return 3; end if;
    else // d=2 - poss. S4 or A5
        rxyz := [NormalForm(P.i,I) : i in [1..3]];
	rk := {k|r : r in rxyz | r in k};
	inds := [i : i in [1..3] | rxyz[i] in k];
	indsc := [j : j in [1..3] | j notin inds];
	zer := k!0; one := k!1; mone := k!(-1);
	case #inds:
	  when 0: // poss A5 case
	    if z^2+z-1 in I then
	      if ((x-z in I and y+z in I) or (x+z in I and y-z in I)) then
		return 5;
	      end if;
	    elif z^2-z-1 in I then
	      if ((x+z in I and y+z in I) or (x-z in I and y-z in I)) then
		return 5;
	      end if;
	    end if;
	  when 1: // poss S4 or A5
	    j := indsc[1]; k := indsc[2];
	    p1 := (P.k)^2-2; p2 := (P.k)^2+P.k-1; p3 := (P.k)^2-P.k-1;	    
	    case Representative(rk):
	      when zer:
		if p2 in I then
		  if ((P.j+P.k+1) in I) or ((P.j-P.k-1) in I) then
		    return 5;
		  end if;
		elif p3 in I then
		  if ((P.j+P.k-1) in I) or ((P.j-P.k+1) in I) then
		    return 5;
		  end if;
		end if;
	      when one:
		if p1 in I then 
		  if (P.j-P.k) in I then
		    return 4;
		  end if;
		elif p2 in I then
		  if ((P.j-P.k) in I) or ((P.j-P.k-1) in I) then
		    return 5;
		  end if;
		elif p3 in I then
		  if ((P.j-P.k) in I) or ((P.j-P.k+1) in I) then
		    return 5;
		  end if;
		end if;
	      when mone:
		if p1 in I then 
		  if (P.j+P.k) in I then
		    return 4;
		  end if;
		elif p2 in I then
		  if ((P.j+P.k) in I) or ((P.j+P.k+1) in I) then
		    return 5;
		  end if;
		elif p3 in I then
		  if ((P.j+P.k) in I) or ((P.j+P.k-1) in I) then
		    return 5;
		  end if;
		end if;
	    end case;
	  when 2: // poss S4 or A5
	    j := indsc[1];
	    p1 := (P.j)^2-2; p2 := (P.j)^2+P.j-1; p3 := (P.j)^2-P.j-1;	    
	    case rk:
	      when {zer,one}:
		if p1 in I then return 4;
		elif (p2 in I) or (p3 in I) then return 5; end if;
	      when {zer,mone}:
		if p1 in I then return 4;
		elif (p2 in I) or (p3 in I) then return 5; end if;
	      when {one,mone}:
		if p2 in I then return 5; end if;
	      when {one}://2 vars are 1!
		if p3 in I then return 5; end if;
	      when {mone}://2 vars are -1!
		if p3 in I then return 5; end if;
	    end case;
	end case;
    end if;
    return 0;

end function;

/* 
  Input ideal in R[x,y,z] where R is Z or Q giving the "trace ideal
  image" for an hm of a free 2-generator group into SL(2,S). Doesn't
  do the full check for an image which is all of PSL(2,F) for a finite
  field F of a certain char. Just eliminates the cyclic, dihedral, A4,S4
  and A5 cases in char 0. If the resulting scheme is non-empty, there is
  an image that is infinite in PSL(2,K) for K some #field, which is
  enough to say whether the original group is infinite or not. This
  non-emptiness or not is the true/false return value. 
*/
function IsInfiniteCharZero(I,bFull)

    P := Generic(I);
    assert Rank(P) eq 3;
    k := BaseRing(P);
    assert (k eq Integers()) or (k eq Rationals());
    if k eq Integers() then
	P := ChangeRing(P,Rationals());
	I := ideal<P|Basis(I)>;
    end if;
    types := [];

    // first remove the non-irreducible locus from X(I)
    x,y,z := Explode([P.i : i in [1..3]]);
    f := x^2+y^2+z^2-x*y*z-4;
    I := Saturation(I,f);
    d := Dimension(I);
    vprintf IsInfGrp: " Dimension after removing 'reducible components': %o\n",d;
    if d eq -1 then return false,types; end if;

    // now remove components lying in any of the three
    // 1-dimensional "dihedral" loci defined by <x,y>, 
    // <y,z>,<z,x>
      // first note that if dim X(I) is >= 2 we are done
    if d ge 2 then return true,types; end if;
    I1 :=  Saturation(I,x);
    I2 :=  Saturation(I,y);
    I3 :=  Saturation(I,z);
    I := (I1 meet I2) + (I2 meet I3) + (I3 meet I1);
    d := Dimension(I);
    vprintf IsInfGrp: " Dimension after removing 'dihedral components': %o\n",d;
    if d gt 0 then return true,types;
    elif d eq -1 then return false,types; end if;

    // final case: having removed cyclic & dihedral components
    //  X(I) is finite. Must check that not all remaining points
    //  corr. to A4,S4 or A5 reps (may also get V4).
    vprintf IsInfGrp: "Analysing zero-dimensional locus:\n";
    ps := RadicalDecomposition(I);
    for p in ps do
	Append(~types,ideal_type(p));
	vprintf IsInfGrp: "  Rep. type of closed point: %o\n",
			types_to_string([types[#types]]);
	if (not bFull) and (types[#types] eq 0) then
	    break;
	end if;
    end for;

    return (Index(types,0) ne 0), types;

end function;

/*
intrinsic HasInfinitePSL2Quotient(ws::SeqEnum : signs := 0, full := false)
		-> BoolElt, SeqEnum
{ ws is be a sequence of words in a 2-generator free group F2. Returns whether
  F2/<ws> has an infinite (non-cyclic, non-dihedral) image in PSL2(K) for a
  number field K.}
*/

intrinsic HasInfinitePSL2Quotient(G::GrpFP : signs := 0, full := false)
		-> BoolElt, SeqEnum
{ G is finitely presented 2-generator group. Returns whether G has an infinite 
(non-cyclic, non-dihedral) image in PSL2(K) for a number field K.}

    r := Relations(G);
    ws := [ LHS(r[i])*RHS(r[i])^-1 : i in [1..#r] ]; 

    if Type(signs) eq RngIntElt then
	signs := [signs : i in [1..#ws]];
    end if;

    require (Type(signs) eq SeqEnum) and (#signs eq #ws) and 
		(Universe(signs) eq Integers()) and &and[Abs(s) le 1 : s in signs] :
	"signs parameter should be 0,1 or -1 or", "a sequence of such integers of the same",
	"length as ws";

    P<x,y,z> := PolynomialRing(Rationals(),3);
    bInf := false;
    types := [];
    pair := [1,-1];
    sgn_combos := CartesianProduct([(s eq 0) select pair else [s] : s in signs]);
    for ss in sgn_combos do
	sseq := [s : s in ss];
	vprintf IsInfGrp: "Considering representations with signs: %o\n",sseq;
	vprintf IsInfGrp: "Getting the ideal of traces...\n";
	I := signed_relations_to_ideal([[*ws[i],sseq[i]*] : i in [1..#ws]],P);
	vprintf IsInfGrp: "Analysing representation types...\n";
	bRet,typs := IsInfiniteCharZero(I,full);
	bInf := bInf or bRet;
	if full then
	    typs := types_to_string(typs); 
	    Append(~types,[*sseq,typs*]);
	else
	    if bInf then break; end if;
	end if;
    end for;
    if full then return bInf,types;
    else return bInf,_; end if;
 
end intrinsic;

/*****
sgns := [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]];
hms := [hom<P->P|[s[i]*(P.(i^g)) : i in [1..3]]> :
		g in SymmetricGroup(3), s in sgns];
******/

