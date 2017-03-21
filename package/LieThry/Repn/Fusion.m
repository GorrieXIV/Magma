freeze;

/* 
Reference: Di Francesco, Mathieu, Sénéchal, Conformal Field Theory, Springer, 1997
  Section 16.2.

Implementation by Dan Roozemond, June/July 2011.
*/

declare verbose FusionRules, 3;

affine_nm := function(R)
	nm := CartanName(R);
	nm2 := "";
	for n in Eltseq(nm) do
		nm2 cat:= n;
		if Regexp("[A-Z]", n) then nm2 cat:= "~"; end if;
	end for;
	return nm2;
end function;
affine_cox_grp_fp := func<R | CoxeterGroup(GrpFPCox, affine_nm(R))>;
affine_cox_grp_mat := func<R | CoxeterGroup(GrpMat, affine_nm(R))>;

/* returns a sequence; entries 1..n are the finite ones, n+1 is the affine 0-node */
affine_reflection_matrices := function(R)
	F := Rationals();
	N := Rank(R);
	Gfp := affine_cox_grp_mat(R);
	
	mats := [ ChangeRing(Transpose(Matrix(Gfp.i)),F) : i in [1..N+1] ];
	return mats;
end function;
affine_reflection_functions := function(R)
	mats := affine_reflection_matrices(R);
	F := BaseRing(Universe(mats));
	N := Rank(R);
	rho := Vector([F|1 : i in [1..N+1]]);
	return [ func<v | (v+rho)*m-rho> : m in mats ];
end function;

/* checking/turning affine weight into finite weight (i.e., always return finite weight.)*/
function check_weight(R, fin2aff, aff2fin, v)
	assert ISA(Type(v), ModTupRngElt);
	N := Rank(R);
	if Ncols(v) eq N then 
		return v;
	elif Ncols(v) eq N+1 then
		fv := aff2fin(v);
		if fin2aff(fv) ne v then
			error Sprintf("Incorrect affine weight %o: should be %o", v, fin2aff(fv));
		end if;
		return fv;
	else
		error Sprintf("Weight (%o) should be given as vector with %o (finite) or %o (affine) entries", v, N, N+1);
	end if;
end function;

intrinsic WZWFusion(R::RootDtm, v::Any, w::Any, k::RngIntElt : ReturnForm := "Auto") -> SetMulti
{ Compute the fusion rules for weights v x w at level k using the Kac-Walton formula.
v,w may be given either as finite weights (vectors with Rank(R) entries) or
affine weights (vectors with Rank(R)+1 entries). affine weights out <=> affine weights in.
}
	require ReturnForm in {"Auto", "Affine", "Finite"} : "ReturnForm should be \"Auto\", \"Affine\", or \"Finite\"";

	F := Rationals();
	N := Rank(R);

	Cinv := ChangeRing(CartanMatrix(R), Rationals())^-1;
	theta := HighestRoot(R : Basis := "Weight");
	nrmtheta := RootNorm(R, RootPosition(R, HighestRoot(R)));
	lambda0 := func<wt | k - ((Matrix(Vector(wt))*Cinv*Transpose(Matrix(theta)))[1,1])>;
	fin2aff := func<wt | Vector(Eltseq(wt) cat [lambda0(wt)])>;
	aff2fin := func<wt | Vector(Eltseq(wt)[1..N])>;

	v := ChangeRing(Vector(v), F);
	w := ChangeRing(Vector(w), F);
	require Ncols(v) eq Ncols(w) : "v and w should be vectors with the same number of columns.";
	affine_weights_out := ((ReturnForm eq "Auto") and (Ncols(v) eq N+1)) or (ReturnForm eq "Affine");
	
	v := check_weight(R, fin2aff, aff2fin, v);
	w := check_weight(R, fin2aff, aff2fin, w);
	
	vprintf FusionRules, 1 : "v = %o = %o\nw = %o = %o\n", v, fin2aff(v), w, fin2aff(w);

	rho := Vector([F|1: i in [1..N+1]]);
	reflfns := affine_reflection_functions(R);
	
	/* Need to reorder gens of this grp */
	Gfp := affine_cox_grp_fp(R);
	gensfp := [ Gfp.i : i in [1..N+1] ];

	//return pair: weight, sign. 
	//Or false, in which case we ended up with a -1 as one of the entries and this one may be discarded.
	reflect_to_alcove := function(w)
		ws := AssociativeArray();
		ws[w] := Identity(Gfp);

		ln := 0;
		while true do
			newws := AssociativeArray();

			/* Go to the next level by reflecting */
			for w in Keys(ws) do
				g := ws[w];
				
				/* Find negative entries of the word, reflect. */
				fnd := false;
				for i in [1..N+1] do
					if w[i] ge 0 then continue; end if;
					if w[i] eq -1 then return <0,0>; end if;
					
					fnd := true;
					
					//Check whether this is "progress"
					gg := g*gensfp[i];
					if CoxeterLength(gg) ne ln+1 then continue; end if;
					
					//Reflect, store in the todo list.
					ww := (reflfns[i])(w);
					if not IsDefined(newws, ww) then newws[ww] := gg; end if;
				end for;
				
				/* No negative entries? We are done! */
				if not fnd then 
					assert CoxeterLength(g) eq ln;
					return <w, (-1)^(ln)>;
				end if;
			end for;
			
			ws := newws;
			ln +:= 1;
		end while;
	end function;


	if IsIrreducible(R) and CartanName(R)[1] eq "A" then
		tens := Multiset(LittlewoodRichardsonTensor(R, v, w));
	else
		tens := Multiset(Tensor(R, v, w));
	end if;
	vprintf FusionRules, 1 : "finite tensor = %o\n", tens;


	S := AssociativeArray();
	for w in MultisetToSet(tens) do S[fin2aff(w)] := Multiplicity(tens, w); end for;


	T := AssociativeArray();
	for w in Keys(S) do
		mp := S[w];
		vprintf FusionRules, 2 : "w = %o, mp = %o\n", w, mp;
	
		//Ignore those with -1 as affine entry
		if w[N+1] eq -1 then
			continue;
		end if;
	
		if w[N+1] ge 0 then
			/* By construction we know that the other entries are also >= 0 */
			w2 := w; mp2 := mp;
		else
			w2, mp2 := Explode(reflect_to_alcove(w));
			if w2 eq 0 then
				continue;
			end if;
			mp2 := mp*mp2;
		end if;

		b, n := IsDefined(T, w2);
		vprintf FusionRules, 2 : "  %o*%o ==> T +:= %o*%o\n", mp, w, mp2, w2;
		if b then 
			n +:= mp2;
			if IsZero(n) then Remove(~T, w2); else T[w2] := n; end if;
		else
			T[w2] := mp2;
		end if;
	
	end for;

	if affine_weights_out then
		return {* w^^(T[w]) : w in Keys(T) *};
	else
		return {* aff2fin(w)^^(T[w]) : w in Keys(T) *};
	end if;
end intrinsic;

intrinsic WZWFusion(D::LieRepDec, E::LieRepDec, k::RngIntElt) -> LieRepDec
{ Compute fusion rules for D x E at level k.}
	require RootDatum(D) eq RootDatum(E) : "D and E must have identical root data.";
	R := RootDatum(D);
	
	wt1, mp1 := WeightsAndMultiplicities(D);
	wt2, mp2 := WeightsAndMultiplicities(E);
	F := LieRepresentationDecomposition(R);
	
	for i in [1..#wt1] do for j in [1..#wt2] do
		r := WZWFusion(R, wt1[i], wt2[j], k);
		for w in MultisetToSet(r) do
			AddRepresentation(~F, w, mp1[i]*mp2[j]*Multiplicity(r, w));
		end for;
	end for; end for;
	
	return F;
end intrinsic;

/* Notes.
All cases seem to agree with Kac, except:
- Cn, where it seems the correct definition for lambda0 would be 
  lambda0 := k - wt*(C^-1)*theta/(|theta|^2))
  where |theta| is the norm of theta, in this case 2.
  However, the other non-simply-laced types *don't* need this.

- G2, where Kac seems to have its roots numbered the other way
  around, e.g., what Kac calls (0,2,1)  we would call (2,0,1).

*/

/* (Working) Examples:

(1) Example on page 682, A2, k = 3, [0,2,1] x [0,1,2] = [3,0,0] + [1,1,1]
> WZWFusion(RootDatum("A2" : Isogeny := "SC"), [2,1], [1,2], 3);
cf in Kac:
> Algebra A 2 3
> Display
> Fusion 7 4

(2) A2, k = 4, [1,2,1] x [1,1,2] (as p. 682), but this is [2,1,1]x[1,2,1] in Kac's terminology)
> WZWFusion(RootDatum("A2" : Isogeny := "SC"), [2,1], [1,2], 4);
cf in Kac:
> Algebra A 2 4
> Display
> Fusion 14 13

(3) B3, k = 3, Kac: (0,0,1,2) x (1,0,1,1); Book notation: [2,0,0,1]x[1,1,0,1]
> WZWFusion(RootDatum("B3" : Isogeny := "SC"), [0,0,1],[1,0,1], 3);
cf in Kac:
> Algebra B 3 3
> Display
> Fusion 2 12

4. F4, k = 5.Kac: (0,0,1,3,0) x (2,0,0,1,0); book: [0,0,0,1,3] x [0,2,0,0,1]
> WZWFusion(RootDatum("F4" : Isogeny := "SC"), [0,0,1,3], [2,0,0,1], 5);
cf in Kac:
> Algebra F 4 5
> Display
> Fusion 9 24

*/
