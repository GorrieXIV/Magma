freeze;

/////////////////////////////////////////////////////////////////////////////
//  Functions for the local resolution of surface singularities by blow-up //
//  and associated computations: intersection pairings of exceptional      //
//  divisors, multiplicities of functions at ex. divs., ex. div. conditions//
//  on linear systems, including the computation of multi-adjoint maps,    //
//  and geometric and arithmetic genera of a desingularisation.            //
//                                                                         //
//                         mch - 2015                                      //        
/////////////////////////////////////////////////////////////////////////////

declare verbose MultsAndInts, 1;
// Attribute for singularity resolution data of a surface. res_list is a list
// of triples <typ,lst1,not_adj_only> where lst1 is a resolution data list and
// typ is an integer with value 1 or 2 giving the type of lst1: 
// 1 for a formal desingularisation data list of the type produced by code in 
//    surface_resolution.m and
// 2 for a list of the more detailed DesingData objects below for a surface
//    with only point singularities.
// res_list contains at most one desingularisation pair of each type.
// not_adj_only is true/false depending on whether there is full
// desingularisation data or only that required to compute adjoint and
// multi-canonical linear systems/maps  
declare attributes Srfc: res_list;

// Structure for a node in the blow-up structure over a base affine patch Y
// of the surface that is being desingularised. Each node element is an
// affine variety with a birational morphism (prj_map) down to Y. 
// Only final blow-up patches that are non-singular and intersect the
// inverse image of the singular subscheme S of Y are kept. For each
// exceptional divisor lying above S, we keep more than just one "generic"
// patch, however, for intersection pairing computations: we need patches
// that cover the entire (complete) divisor.

NodeData :=  recformat<
    i		: RngIntElt,  	// Patch ID number
    i1		: RngIntElt,  	// Patch ID number of previous patch
    X		: Sch,  	// Patch as an affine scheme
    ex_cmpts	: SeqEnum,    	// Irreducible components of exceptional divisors
				// (ie lying over singular locus of Y) in the patch
    ex_links	: SeqEnum,	// Sequence containing a list of pairs <i,j> for each
				// element e of ex_cmpts containing the ID number i
				// and ex_cmpts index j (for patch i) for the component
				// in patch i that corresponds to e.
 				// Below - irreducible components of the singular subscheme
				// of X - temporary - will be empty for all final patches
    sing_cmpts	: SeqEnum,      // ones to be blown up
    sing_cmpts1 : SeqEnum,	// curve components NOT to be blown up (they have singular
				// points or intersect another singular curve)
    prj_map	: MapIsoSch,    // Birational blow-down map from X to the base patch Y
    prj_map1	: MapIsoSch     // Birational blow-down map from X to the previous patch
>;

// User type used to store final data about the resolution of singularity
// Y in affine surface X. Currently, Y must be a point component of the singular
// locus of X.

declare type DesingData;

declare attributes DesingData: main_dat, classes, div_leaf_dat, Y, pi, imat, mult_dat,
  mult_use_glob, w_mults;

/*DesingRec := recformat<
    main_dat	: List,		// Main data list containing tuples with info about
				// the leaf patches of the blow-up process and the
				// affine patches of the irreducible exceptional divisors
				// within these.
    classes	: SeqEnum,	// r sequences giving the indices of the elements in div_leaf_dat
				// representing the affine patches of the r exceptional divisors E1,..Er.
    div_leaf_dat : SeqEnum,	// Sequence of pairs [i,j] connecting patches of exceptional
				// divisors to curve data in main_dat. [i,j] means the jth element
				// of the sequence main_dat[i][1] of irreducible curves in the
				// ith leaf patch.
    Y		: Sch,		// The singular component of Sing(X) that this desingularisation
				// corresponds to. X is recoverable from main_dat
    pi		: RngIntElt,	// If X is an affine patch of a given projective surface, the patch
				// index. Otherwise 0.
    imat	: AlgMatElt,	// the r*r negative definite symmetric intersection matrix of
				// exceptional divisors (Ei.Ej). May initially be added with
				// the diagonal elements (Ei.Ei) given as 0. Since these must
				// all be negative, this is easily detected.
    mult_dat	: List,		// List of length r containing data for computing multiplicities
				// at the Ei. Entry is either 0 - meaning use global method - or
				// pair <fs,hm> as returned by the set_up_loc_mult_struct function.
    mult_use_glob : BoolElt,	// If true, use global method for all multiplicity computations.

    // Attributes currently only for the X=hypersurface case giving info about
    // differential 2-forms. Here, have a natural meromorphic 2-form, w, s.t.
    // +/- w = dx^dy/(dg/dz) = dy^dz/(dg/dx) = dz^dx/(dg/dy) on a standard affine patch
    // with local coords x,y,z, where g is the appropraitely dehomogenised defining poly
    // of X which gives a defining poly for the affine patch. w is holomorphic and non-vanishing
    // at all points except for singular points of X, so its associated divisor is supported
    // on exceptional divisors over the singular points.

    w_mults	: SeqEnum,	// Multiplicities of w at the r ex. divs. E1,..,Er.
>;*/

intrinsic Print(dsd::DesingData, L::MonStgElt)
{ Print resolution of surface singularity data object dsd at level L.}

    if L eq "Minimal" then
      printf "Object containing data about the exceptional divisors over a surface singularity.";
    else
      printf "Object containing data about the exceptional divisors over singularity\n" cat
	"%o\nof algebraic surface\n%o",dsd`Y,Codomain((dsd`main_dat[1])[3]);
    end if;
end intrinsic;

import "/magma/mch/package/Geometry/Sch/norm_form_of_sing.m": trunc_comp;

function inv_img(mp,Z)
// Z@@mp for mp:X->Y, Z<=Y. Don't use @@ here because it requires Z to be a subscheme
// of Y and then the equations of Y are added to those of Z. This is not useful
// in this situation, since we want schemes to be defined by as small a number
// of equations as possible since, for example, have to do many singularity checks.
// Here, X and Y will both be affine and mp defined by polys (and not rat fns).
 
    X := Domain(mp); Y := Codomain(mp);
    eqns := DefiningPolynomials(mp);
    B1 := [Evaluate(f,eqns) : f in DefiningPolynomials(Z)];
    B2 := [b : b in DefiningPolynomials(X) | b notin B1];
    B3 := GroebnerBasis(Ideal(X)+ideal<CoordinateRing(Ambient(X))|B1>);
    if #B3 lt (#B1+#B2) then
      return Scheme(Ambient(X),B3);
    else
      return Scheme(Ambient(X),B1 cat B2);
    end if;

end function;

function get_good_rat_fns(fs,IX,IC)
// Used by the the main resolution function and intersection_main.
// IX, IC are the (prime) ideals in R of an affine surface X and an
// irreducible curve C <= X. fs is a sequence of rational functions f/g in FOF(R)
// representing rat fns on X s.t. g notin IX but f,g in IC. If at least one f/g
// ISN'T a rational function on C (i.e. C <= its polar divisor on X) then return false.
// Otherwise, replace the f/g by u/v that give the same rat. fn. on X and C but with
// v notin IC.

    l := LCM([Denominator(e) : e in fs]);
    R := Generic(IX);
    I1 := ideal<R|Basis(IX) cat [l]>;
    new_dens := [];
    for f in fs do
      If := ColonIdeal(I1,ideal<R|R!(f*l)>);
      B := Reverse([b : b in Basis(If) | b notin IC]); //later elts better!
      if #B eq 0 then return false,_; end if;
      _,i := Min([TotalDegree(b) : b in B]);      
      Append(~new_dens,B[i]);
    end for;
    // now get the new numerators
    I1 := IdealWithFixedBasis(Basis(IX) cat [l]);
    new_nums := [c[#c] where c is Coordinates(I1,
		  R!(fs[i]*l*new_dens[i])) : i in [1..#fs]];
    return true,[new_nums[i]/new_dens[i] : i in [1..#fs]];

end function;

function get_blow_up_components(Sp_cmps)
// Sp_cmps are the irreducible components of the singular locus in a blow-up patch.
// Returns a collection of irreducible subvarieties (points and curves, since we are in the
// surface case) of the singular locus which are
//  1) pairwise disjoint
//  2) non-singular.
// These will be blown-up at the next stage.
// Also return any curve components of the sing. loc. NOT to be blown up

    // First, divide into connected components.
    N := #Sp_cmps;
    pairs := [];
    for i in [1..N], j in [i+1..N] do
      if not IsEmpty(Sp_cmps[i] meet Sp_cmps[j]) then
	Append(~pairs,{i,j});
      end if;
    end for;
    cmps := [];
    inds := {1..N};
    while #inds gt 0 do
      ExtractRep(~inds,~r);
      cmp := [r];
      repeat
	js := [j : j in inds | &or[{i,j} in pairs : i in cmp]];
	if #js gt 0 then
	  cmp cat:= js;
	  inds := inds diff Seqset(js);
	end if;
      until (#js eq 0);
      Sort(~cmp);
      Append(~cmps,cmp);
    end while;
    bup_cmps := [];
    non_bup_cmps := [];
    // for irreducible connected components, add the whole thing
    // unless it is a singular curve, in which case add the 
    // 0-dim (reduced) singular locus.
    for i in [c[1] : c in cmps | #c eq 1] do
      S := Sp_cmps[i];
      sng := SingularSubscheme(S);
      if IsEmpty(sng) then
	Append(~bup_cmps,S);
      else
	sng_pts := PrimeComponents(sng);
	bup_cmps cat:= sng_pts;
	Append(~non_bup_cmps,S);
      end if;
    end for;
    // for non-irreducible connected components (all irreducible
    // constituents of which must be curves) add the intersection
    // points.
    for c in [c : c in cmps | #c gt 1] do
      pc := [Setseq(p) : p in pairs | Representative(p) in c];
      ijs := Setseq(&join[Seqset(PrimeComponents(
		Sp_cmps[p[1]] meet Sp_cmps[p[2]])) : p in pc]);
      bup_cmps cat:= ijs;
      non_bup_cmps cat:= [Sp_cmps[i] : i in c];
    end for;
    return bup_cmps,non_bup_cmps;

end function;

function i1toi2patchmap(i1,i2,tree)
// returns the birational map from the index i1 patch to the
// index i2 patch.
    i1_prec := [i1];
    while i1_prec[#i1_prec] gt 1 do
      Append(~i1_prec,(tree[i1_prec[#i1_prec]])`i1);
    end while;
    i2_prec := [i2];
    while i2_prec[#i2_prec] notin i1_prec do
      Append(~i2_prec,(tree[i2_prec[#i2_prec]])`i1);
    end while;
    i1_prec := [i : i in i1_prec | i ge i2_prec[#i2_prec]];

    if #i1_prec gt 1 then
      mp1 := (tree[i1])`prj_map1;
      for j in [2..#i1_prec-1] do
	mp1 := Expand(mp1*(tree[i1_prec[j]])`prj_map1);
      end for;
    else
      mp1 := IdentityMap((tree[i1])`X);
    end if;

    if #i2_prec gt 1 then
      mp2 := (tree[i2])`prj_map1;
      for j in [2..#i2_prec-1] do
	mp2 := Expand(mp2*(tree[i2_prec[j]])`prj_map1);
      end for;
    else
      mp2 := IdentityMap((tree[i2])`X);
    end if;

    return Expand(mp1*Inverse(mp2));
end function;

/*
function new_sings(tree,leaves)
// Group together the set of singularities over leaf nodes to be blown up.
// For dimension 0 sings, only want to blow up one copy from the different patches.
// For dimension 1, want to keep track of which divisors of the various patches
// correspond to the same irreducible component of the singular locus

    sings_tot := [* <i,j>: j in (tree[i])`sing_cmpts, i in leaves *];
    // divide into 0- and 1-dimensional components
    inds0 := [i : i in [1..#sings_tot] | Dimension(sings_tot[i][2]) eq 0];
    sings0 := [* sings_tot[i] : i in inds0 *];
    sings1 := [* sings_tot[i] : i in [1..#sings_tot] | i notin inds0 *];
    sings01 := [* sings0,sings1 *];
    //compute maps and base-schemes between patches
    inds0 := Sort(Setseq(Seqset([s[1] : s in sings0])));
    inds1 := Sort(Setseq(Seqset([s[1] : s in sings1])));
    pairs := Setseq(Seqset(&cat[[<inds[i1],inds[i2]> : i2 in [i1+1..#inds],
		i1 in [1..#inds]] : inds in [inds0,inds1]]));
    idata := [* <mp12,BaseScheme(mp12)> where
	mp12 is i1toi2patchmap(p[1],p[2],tree) : p in pairs *];

    sing_sets01 := [**];
    for j in [1,2] do
      sings := sings01[j];
      inds := (j eq 1) select inds0 else inds1;
      sing_sets := [**];
      while #sings gt 0 do
	k,ind := Min([s[1] : s in sings]);
	s1 := sings[ind];
	gp := [* s1 *]; Remove(~sings,ind);
	for i in [ i : i in inds | i gt k] do
	  dat := idata[u] where u is Index(pairs,<k,i>);
	  if s1[2] subset dat[2] then continue; end if;
	  s1_img := Restriction(dat[1],s1[2],Codomain(dat[1]) :
				Check := false, Inverse := false)(s1[2]);
	  for l in [l : l in [1..#sings] | (sings[l])[1] eq i] do
	    if (sings[l])[2] eq s1_img then
	      Append(~gp,sings[l]); Remove(~sings,l);
	      break;
	    end if;
	  end for;
	end for;
	Append(~sing_sets,gp);
      end while;
      Append(~sing_sets01,sing_sets);
    end for;

    // for dimension 0 components, just take the first of equivalent sets
    ss0 := [* ss[1] : ss in sing_sets01[1] *];

    // for dimension 1 components, discard patches which are covered by the others
    ss1 := [**];
    for j in [1..#(sing_sets01[2])] do
      ss := sing_sets01[2][j];
      while #ss gt 2 do
	js := [s[1] : s in ss];
	rem := false;
	for k := #js to 1 by -1 do
	  ind := js[k];
	  bss := [(i1 lt ind) select BaseScheme(Inverse((idata[u])[1])) else
		(idata[u])[2] where u is Index(pairs,(i1 lt ind) select <i1,ind>
		else <ind,i1>) : i1 in js | i1 ne ind];
	  if IsEmpty(ss[k][2] meet &meet(bss)) then //kth patch is superfluous
	    Remove(~ss,k); rem := true; break;
	  end if;
	end for;
	if not rem then break; end if;
      end while;
      Append(~ss1,ss);
    end for;

    return ss0,ss1;

end function;
*/

function new_sings(tree,leaves)
// Group together the set of singularities over leaf nodes to be blown up.
// For dimension 0 sings, only want to blow up one copy from the different patches.
// For dimension 1, want to keep track of which divisors of the various patches
// correspond to the same irreducible component of the singular locus

    sings_tot := [* [i,j] : j in [1..#((tree[i])`sing_cmpts)], i in leaves *];
    // divide into 0- and 1-dimensional components
    inds0 := [i : i in [1..#sings_tot] | Dimension(((tree[s[1]])`sing_cmpts)[s[2]]) eq 0
			where s is sings_tot[i]];
    sings0 := [* sings_tot[i] : i in inds0 *];
    sings1 := [* sings_tot[i] : i in [1..#sings_tot] | i notin inds0 *];
    sings01 := [* sings0,sings1 *];
    //compute maps and base-schemes between patches
    inds0 := Sort(Setseq(Seqset([s[1] : s in sings0])));
    inds1 := Sort(Setseq(Seqset([s[1] : s in sings1])));
    pairs := Setseq(Seqset(&cat[[<inds[i1],inds[i2]> : i2 in [i1+1..#inds],
		i1 in [1..#inds]] : inds in [inds0,inds1]]));
    idata := [* <mp12,BaseScheme(mp12)> where
	mp12 is i1toi2patchmap(p[1],p[2],tree) : p in pairs *];

    sing_sets01 := [**];
    for j in [1,2] do
      sings := sings01[j];
      inds := (j eq 1) select inds0 else inds1;
      sing_sets := [**];
      while #sings gt 0 do
	k,ind := Min([s[1] : s in sings]);
	s1 := sings[ind];
	gp := [* s1 *]; Remove(~sings,ind);
	for i in [ i : i in inds | i gt k] do
	  dat := idata[u] where u is Index(pairs,<k,i>);
	  s1s := ((tree[s1[1]])`sing_cmpts)[s1[2]];
	  if s1s subset dat[2] then continue; end if;
	  s1_img := Restriction(dat[1],s1s,Codomain(dat[1]) :
				Check := false, Inverse := false)(s1s);
	  for l in [l : l in [1..#sings] | (sings[l])[1] eq i] do
	    if sls eq s1_img where sls is ((tree[sings[l][1]])`sing_cmpts)[sings[l][2]] then
	      Append(~gp,sings[l]); Remove(~sings,l);
	      break;
	    end if;
	  end for;
	end for;
	Append(~sing_sets,gp);
      end while;
      Append(~sing_sets01,sing_sets);
    end for;

    // for dimension 0 components, just take the first of equivalent sets
    ss0 := [* ss[1] : ss in sing_sets01[1] *];

    // for dimension 1 components, discard patches which are covered by the others
    ss1 := [**];
    for j in [1..#(sing_sets01[2])] do
      ss := sing_sets01[2][j];
      while #ss gt 2 do
	js := [s[1] : s in ss];
	rem := false;
	for k := #js to 1 by -1 do
	  ind := js[k];
	  bss := [(i1 lt ind) select BaseScheme(Inverse((idata[u])[1])) else
		(idata[u])[2] where u is Index(pairs,(i1 lt ind) select <i1,ind>
		else <ind,i1>) : i1 in js | i1 ne ind];
	  if IsEmpty(((tree[ss[k][1]])`sing_cmpts)[ss[k][2]] meet &meet(bss)) then
		//kth patch is superfluous
	    Remove(~ss,k); rem := true; break;
	  end if;
	end for;
	if not rem then break; end if;
      end while;
      Append(~ss1,ss);
    end for;

    return ss0,ss1;

end function;

function relate_new_divs(new_divs,m,tree)
// identify the new divisor components (over different patches) which are the last m
// entries in new_divs and arise from blowing up a singular component.

    divs := new_divs[r-m+1..r] where r is #new_divs;
    tinds := Sort(Setseq(Seqset([d[2] : d in divs])));
    done := {}; div_sets := [];
    while #done lt #divs do
      div_sets1 := [[i : i in [1..#divs] | (divs[i][2] eq j) and (i notin done)] : j in tinds];
      nd_max,j := Max([#ds : ds in div_sets1]);
      if nd_max gt 1 then
	ds := [[i] : i in div_sets1[j]];
	mpj := Inverse(tree[tinds[j]]`prj_map1);
	done join:= Seqset(div_sets1[j]);
	for k in [1..#tinds] do
	  if (k eq j) or (#(div_sets1[k]) eq 0) then continue; end if;
	  mp := Expand((tree[tinds[k]]`prj_map1)*mpj);
	  for i in div_sets1[k] do
	    // if divs[i][1] is in the base scheme of mp then it doesn't
	    // correspond to any component of Codomain(mp). We have to do a
	    // proper check for the TRUE base scheme, though!
	    defs := DefiningPolynomials(mp);
	    if LCM([Denominator(e) : e in defs]) in Ideal(divs[i][1]) then
	      bad_is := [e : e in [1..#defs] | Denominator(defs[e]) in Ideal(divs[i][1])];
	      if not &and[Numerator(defs[e]) in Ideal(divs[i][1]) : e in bad_is] then
		continue;
	      end if;
	      boo,grs := get_good_rat_fns([defs[e] : e in bad_is],Ideal(Domain(mp)),
						Ideal(divs[i][1]));
	      if not boo then continue; end if;
	      for e in [1..#bad_is] do defs[bad_is[e]] := grs[e]; end for;
	      mp := map<Domain(mp)->Codomain(mp)|defs,InverseDefiningPolynomials(mp):
				Check := false, CheckInverse := false>;
	    end if; 
	    div_im := Restriction(mp,divs[i][1],Codomain(mp) : Check := false,
				Inverse := false)(divs[i][1]);
	    for l in [1..#ds] do
	      if div_im eq (divs[ds[l][1]])[1] then
		ds[l] := Append(ds[l],i); Include(~done,i); break;
	      end if;
	    end for;
	  end for;
	end for;
      else
	ds := [&cat(div_sets1)];
	done join:= Seqset(ds[1]);
      end if;
      div_sets cat:= ds;
    end while;
    return [[d+i : i in ds] : ds in div_sets] where d is (#new_divs)-m;

end function;

function relate_d1_div_classes(cls,dps,new_divs,tree)
// cls is a sequence of sequences of sequences. The ith sequence of sequences
// correspond to distinct exceptional divisors resulting from the blowup
// of a curve singularity referenced by dps[i]. The dps singularities are
// different patches of a complete curve singularity and this function
// merges the classes in the different cls[i] which correspond to the
// same complete exceptional divisor.

    div_sets := [];
    m,ind := Max([#c : c in cls]);
    // ?? should the below always complete in one pass without the while loop ??
    // Should do no harm having the extra loop, anyway.
    while m gt 0 do
      if &and[#(cls[i]) eq 0 : i in [1..#cls] | i ne ind] then
	div_sets cat:= cls[ind];
	break;
      /*elif m eq 1 then
	Append(~div_sets, Sort(&cat[ c[1] : c in cls | #c gt 0]));
	break;*/
      else
	dss := cls[ind];
	cls[ind] := [];
	for ds in dss do
	  nd := new_divs[ds[1]];
	  ds1 := ds;
	  for j in [j : j in [1..#cls] | (j ne ind) and (#(cls[j]) gt 0)] do
	    inds := [c[1] : c in cls[j]];
	    for i in [1..#inds] do
	      i2 := inds[i];
	      mp := i1toi2patchmap(nd[2],new_divs[i2][2],tree);
	      //NB: if nd[1] is in the base scheme of mp below, the image
	      //call will work and give the empty scheme - which is fine!
	      if new_divs[i2][1] eq Image(Restriction(mp,nd[1],Codomain(mp) : 
			Check := false,Inverse := false)) then
		ds1 cat:= cls[j][i];
		cls[j] := Remove(cls[j],i); break;
	      end if;
	    end for;	    
	  end for;
	  Append(~div_sets,Sort(ds1));
	end for;
      end if;
      m,ind := Max([#c : c in cls]);
    end while;

    return div_sets;

end function;

function full_relns(rels,rels1,lnks,bcat)
// rels is a sequence of integer sequences giving a partial equivalence on
// a set S of integers.
// rels1 is a list/sequence of subsets of T, giving an equivalence
// between elements of a set T.
// lnks is a sequence giving an element of T for each partial equivalence class in rels.
// Compute and return the sequence of full equivalence classes of rels
// formed by joining existing classes that are linked to pairs in T that
// are related via rels1.
// If bcat is false then rather than concatenating the newly joined
// classes, return the full classes as a sequence of joined

    inds := [];
    for p in lnks do
      for i in [1..#rels1] do
	if p in rels1[i] then
	  Append(~inds,i); break;
	end if;
      end for;      
    end for;
    assert #inds eq #lnks;
    indset := Setseq(Seqset(inds));
    rels2 := [[] : i in [1..#indset]];
    for i in [1..#inds] do
      j := Index(indset,inds[i]);
      rels2[j] := Append(rels2[j],i);
    end for;
    if bcat then 
      return [Sort(&cat([rels[i] : i in r])) : r in rels2];
    else
      return [[rels[i] : i in r] : r in rels2];
    end if;

end function;

/////////////////////////////////////////////////////

function intersection_main(ints,degs,dat,js,pis,cis,bbad)
// does the main work in intersections of 2 divisors which is over
// >= 2 leaf blow-up patches. Can be two irreducible exceptional
// divisors or an irreducible exceptional divisor and a non-exceptional
// divisor D.

    // have non-empty intersections over >= 2 patches. Will use function
    // field methods to reconcile things, cutting out repeats.
    dmax,imax := Max([degs[i] : i in js]);
    res := dmax;
    pi := pis[imax];
    Ca := Curve((dat[pi][1])[cis[imax]]);
    C := ProjectiveClosure(Ca);
    K := FunctionField(C);
    coord_fns := [K!(A.i) : i in [1..Length(A)]] where A is Ambient(Ca);
    coord_fns := [f : f in coord_fns | not IsZero(f)];
    pl_done := {}; bad_pls := {};
    // Some of the pi patch intersection might lie in the singular locus of the patch.
    // Note that this can happen for some patch but, for a given intersection point,
    // cannot occur over all patches in which the point lies! If it happens for
    // the pi patch, record the places of C over these points in bad_pls.
    if bbad[imax] then
	S := ints[imax] meet SingularSubscheme(dat[pi][2]);
	if not IsEmpty(S) then
	  bad_pls := Seqset(Support(Divisor(Ca,Ideal(S))));
	  //adjust res to get rid of the current 'bad place' contribution
	  res := Degree(Complement(ints[imax],S));
	end if;
    end if;

    for j in [j : j in js | j ne imax] do
	i := pis[j];
	mp_pi_to_i := Expand(dat[pi][3]*Inverse(dat[i][3]));
	// Possible problem in some cases (rare, I think) is that one or 
        // more of the defining (rational) equations of the (rational) map
	// from patch pi to patch i may be of the form f/g where f and g
	// are polynomials that both vanish on Ca. As Ca doesn't lie in 
	// the base scheme of the map, can replace f/g by u/v on the surface
	// so that v doesn't vanish on Ca. Need to do this computation.
	defs := DefiningEquations(mp_pi_to_i);
	if LCM([Denominator(e) : e in defs]) in Ideal(Ca) then
	  bad_is := [k : k in [1..#defs] | Denominator(defs[k]) in Ideal(Ca)];
	  boo,grs := get_good_rat_fns([defs[k] : k in bad_is],Ideal(Ca),Ideal(dat[pi][2]));
	  assert boo;
	  for k in [1..#bad_is] do defs[bad_is[k]] := grs[k]; end for;
	end if;
	cmps := PrimaryComponents(ints[j]);
	for c in cmps do
	  // first check that c doesn't lie in the singular subscheme
	  // of the patch - if it does, it should be ignored
	  if bbad[j] then
	    if not IsEmpty(c meet SingularSubscheme(dat[i][2])) then
	      continue;
	    end if;
	  end if;
	  c_eqns := [K!f : f in [Evaluate(g,defs) : g in Basis(Ideal(c))]];
	  c_eqns := [f : f in c_eqns | not IsZero(f)];
	  assert #c_eqns gt 0;
	  // c <-> the simultaneous zeroes of the rational functions in c_eqns
	  c_pls := CommonZeros(C,c_eqns);
	  // firstly ignore any places that lie over Ca and are not in bad_pls
	  c_pls := [p : p in c_pls | (p in bad_pls) or
			not &and[Valuation(f,p) ge 0 : f in coord_fns]];
	  // then get rid of infinite or bad places already considered
	  c_pls := [p : p in c_pls | p notin pl_done];
	  // get the multiplicity of the new places and add the contribution
	  // to the intersection number
	  if #c_pls gt 0 then
	    m_pls := [Min([Valuation(f,p) : f in c_eqns]) : p in c_pls];
	    res +:= &+[m_pls[i]*Degree(c_pls[i]) : i in [1..#c_pls]];
	    pl_done join:= Seqset(c_pls);
	  end if;
	end for;
    end for;

    return res;
 
end function;

function intersection_num(cl1,cl2,dat)
// the intersection number of two distinct irreducible exceptional divisors
// given by the classes cl1 and cl2 giving full sets of patches
// covering a complete exceptional divisor. The elements of
// cli are index pairs into the exceptional graph data contained
// in dat.

    pis := [[c[1] : c in cl] : cl in [cl1,cl2]];
    cis := Setseq(&meet[Seqset(p) : p in pis]); // common patch indices
    if #cis eq 0 then return 0; end if;
    Sort(~cis);
    dis := [[cl1[Index(pis[1],i)][2],cl2[Index(pis[2],i)][2]] : i in cis];

    // first compute intersections in common patches - these will possibly
    // contain repeats if there are multiple common patches.
    ints := [* arr[dis[i][1]] meet arr[dis[i][2]] 
	where arr is dat[cis[i]][1] : i in [1..#cis] *];
    degs := [Degree(X) : X in ints]; //each intersection X is empty or a cluster
    js := [i : i in [1..#degs] | degs[i] ne 0];
    if #js eq 0 then return 0; end if;
    if #js eq 1 then return degs[js[1]]; end if;

    // have non-empty intersections over >= 2 patches. Will use function
    // field methods to reconcile things, cutting out repeats.
    bbad := [b[dis[i][1]] and b[dis[i][2]] where b is dat[cis[i]][4] : i in [1..#cis]];
    return intersection_main(ints,degs,dat,js,cis,[d[1] : d in dis],bbad);

end function;

function intersection_num_Dcl(cl1,cl2,dat)
// As above except that now cl1 represents an irreducible exceptional
// divisor and cl2 a non-exceptional effective divisor D represented
// by a list of pairs <E,i> where E is the subscheme of the ith patch
// giving D in that patch. These pairs should run over at least the
// patches where E is non-empty or maybe the patches where E is
// non-empty that occur for cl1.

    pis := [[c[1] : c in cl1],[c[2] : c in cl2]];
    cis := Setseq(&meet[Seqset(p) : p in pis]); // common patch indices
    if #cis eq 0 then return 0; end if;
    Sort(~cis);
    dis := [cl1[Index(pis[1],i)][2] : i in cis];

    // first compute intersections in common patches - these will possibly
    // contain repeats if there are multiple common patches.
    ints := [* (dat[cis[i]][1])[dis[i]] meet
			cl2[Index(pis[2],cis[i])][1] : i in [1..#cis] *];
    degs := [Degree(X) : X in ints]; //each intersection X is empty or a cluster
    js := [i : i in [1..#degs] | degs[i] ne 0];
    if #js eq 0 then return 0; end if;
    if #js eq 1 then return degs[js[1]]; end if;

    // have non-empty intersections over >= 2 patches. Will use function
    // field methods to reconcile things, cutting out repeats.
    bbad := [(dat[cis[i]][4])[dis[i]] : i in [1..#cis]];
    return intersection_main(ints,degs,dat,js,cis,dis,bbad);

end function;

/////////// Functions to compute the multiplicities of exceptional /////////////
/////// divisors in pullbacks and the linear conditions that exceptional ///////
/////// divisors place on linear systems. //////////////////////////////////////

function naive_multiplicity(Z,p,X)
// p is a (generically nonsingular) prime divisor of affine surface X and
// Z is an effective divisor. Compute the multiplicity of p in Z, as divisors,
// using naive powering method

    IZ := Ideal(Z); Ip := Ideal(p); IX := Ideal(X);
    n := 0; I := Ip;
    while IZ subset I do
      I := EquidimensionalPart(Ip*I+IX);
      n +:= 1;
    end while;
    return n;

end function;

function naive_multiplicity_F(F,p,X)
// As above except for a principal effective divisor given by
// polynomial F. We can speed up by factoring F.
    A := Ambient(X);
    fact := Factorisation(F);
    m := 0;
    for f in fact do
      m +:= f[2]*naive_multiplicity(Scheme(A,f[1]),p,X);
    end for;
    return m;
end function;

function naive_multiplicity_I(Z,p,X)
// As above except we try to speed up by factoring out a
// GCD polynomial F from the defining equations of Z and
// using naive_multiplicity_F to deal with that bit.
    defs := DefiningPolynomials(Z);
    F := GCD(defs);
    if TotalDegree(F) gt 0 then
      Z1 := Scheme(Ambient(X),[s div F : s in defs]);
      return naive_multiplicity_F(F,p,X)+
		naive_multiplicity(Z1,p,X);
    else
      return naive_multiplicity(Z,p,X);
    end if;
end function;

function set_up_loc_mult_struct(X,D,p)
// X is an affine surface, D is an irreducible divisor on it and p
// is a point on D, in D(K), that is non-singular on both D and X.
// Linear transform p to the origin in such a way that under the
// transformation, a local minimal basis for I(X) is f0,..,f(n-3)
// where fi = x_(n-i)+... and for I(D) is f0,..,f(n-2) where
// f_(n-2)=x_2+O(deg2). Return the linear transformation and the
// local minimal basis f0,..,f(n-2). Note that we do not even
// need to do a Groebner basis computation here although the
// fi give minimal standard bases for I(X) and I(D) in the local
// ring at O for the lgrevlex ordering!

    A := Ambient(X);
    R := CoordinateRing(A);
    n := Length(A);
    k := BaseRing(R);
    K := Ring(Parent(p));
    if not IsIdentical(K,k) then
      A := BaseChange(A,K); X := BaseChange(X,K); D := BaseChange(D,K);
      p := A!ChangeUniverse(Eltseq(p),K);
    else
      p := A!Eltseq(p);
    end if;
    R1 := CoordinateRing(A);
    tr := [(R1.i)+p[i] : i in [1..n]];
    Xeqns := [Evaluate(f,tr) : f in DefiningPolynomials(X)];
    Deqns := [Evaluate(f,tr) : f in DefiningPolynomials(D) | 
			f notin DefiningPolynomials(X)];
    if n gt 2 then
      Tmat := Matrix([[MonomialCoefficient(f,R1.i) : i in [1..n]] :
                f in Xeqns]);
      Tmat,M := EchelonForm(Tmat);
      inds := [Min(Support(Tmat[i])) : i in [1..Nrows(Tmat)] |
			not IsZero(Tmat[i])];
    else // X is the whole ambient!
      inds := [];
    end if;
    i1 := [i : i in [1..n] | i notin inds];
    assert #i1 eq 2;
    fDs := [f : f in Deqns | &or[not IsZero(
		MonomialCoefficient(f,R1.i)) : i in i1]];
    assert #fDs gt 0;
    fD := [f : f in fDs | TotalDegree(f) eq m][1] where m is
		Min([TotalDegree(f) : f in fDs]);
    // get indices of new order for vars s.t. the tangent space
    // of X at O is x3=x4=..xn=0 after further lin trans
    isub := Reverse(inds cat i1);
    isubi := [Index(isub,j) : j in [1..n]];
    fs := [&+[M[i,j]*Xeqns[j] : j in [1..#Xeqns]] : i in [1..n-2]];
    tr1 := [R1.j : j in isubi];
    fs := [Evaluate(f,tr1) : f in fs];
    fD := Evaluate(fD,tr1);
    tr := [Evaluate(f,tr1) : f in tr];
    cs := [MonomialCoefficient(fD,R1.i) : i in [1..2]];
    if IsZero(cs[2]) then
      tr1 := [R1.2,R1.1] cat [R1.i : i in [3..n]];
      fD := (1/cs[1])*fD;
    else
      if not (K cmpeq Rationals()) or IsZero(cs[1]) or
	(Height(cs[1]) ge Height(cs[2])) then
	tr1 := [R1.1,R1.2-(cs[1]/cs[2])*R1.1] cat [R1.i : i in [3..n]];
	fD := (1/cs[2])*fD;
      else
	tr1 := [R1.2-(cs[2]/cs[1])*R1.1,R1.1] cat [R1.i : i in [3..n]];
	fD := (1/cs[1])*fD;
      end if;
    end if;
    fs := [Evaluate(f,tr1) : f in fs];
    fD := Evaluate(fD,tr1);
    tr := [Evaluate(f,tr1) : f in tr];
    tr1 := [R1.1,R1.2] cat [R1.i - MonomialCoefficient(fs[n+1-i],R1.1)*R1.1 -
		MonomialCoefficient(fs[n+1-i],R1.2)*R1.2 : i in [3..n]];
    fs := [Evaluate(f,tr1) : f in fs];
    fD := Evaluate(fD,tr1);
    tr := [Evaluate(f,tr1) : f in tr];
    fs cat:= [fD];
    Rl := LocalPolynomialRing(K,n,"lgrevlex");
    fs := [Rl!f : f in fs]; tr := [Rl!f : f in tr];
    return fs,hom<R->Rl|tr>;
    
end function;

function local_multiplicity(Z,fs,hm)
// Computation of the mutiplicity of irreducible divisor D in
// effective divisor Z on affine surface X, working with local
// Groebner bases. fs and hm represent X and D as in the preceding
// function.
    Rl := Generic(Parent(fs[1]));
    IZ := ideal<Rl|[hm(f) : f in DefiningPolynomials(Z)]>;
    n := 0;
    fn := fs[#fs];
    while IZ subset ideal<Rl|fs[1..#fs-1] cat [fn]> do
      n +:= 1;
      fn *:= fs[#fs];
    end while;
    return n;
end function;

function local_multiplicity_F(F,fs,hm)
// As above except for a principal effective divisor given by
// polynomial F. We can speed up by factoring F.
    R := Generic(Parent(F));
    AR := Spec(R);
    fact := Factorisation(F);
    m := 0;
    for f in fact do
      m +:= f[2]*local_multiplicity(Scheme(AR,f[1]),fs,hm);
    end for;
    return m;
end function;

function local_multiplicity_I(Z,fs,hm)
// As above except we try to speed up by factoring out a
// GCD polynomial F from the defining equations of Z and
// using naive_multiplicity_F to deal with that bit.
    defs := DefiningPolynomials(Z);
    F := GCD(defs);
    if TotalDegree(F) gt 0 then
      Z1 := Scheme(Ambient(Z),[s div F : s in defs]);
      return local_multiplicity_F(F,fs,hm)+
		local_multiplicity(Z1,fs,hm);
    else
      return local_multiplicity(Z,fs,hm);
    end if;
end function;

function extn_pt(p,D)
// convert a (reduced and) irreducible 0-D subscheme p of affine scheme
// D to a point in D(K) where K is a finite extension field of the
// (perfect) base field k.

    I := Ideal(p);
    if not MonomialOrder(I)[1] eq "lex" then
      I := ChangeOrder(I,"lex");
    end if;
    GB := GroebnerBasis(I);
    n := Rank(I);
    assert #GB eq n;
    K := BaseRing(I);
    P := PolynomialRing(K);
    seq := [K|];
    for i := n to 1 by -1 do
      f := Evaluate(GB[i],[P!0 : j in [1..i-1]] cat [P.1] cat
	    ChangeUniverse(seq,P));
      assert Degree(f) gt 0;
      if Degree(f) eq 1 then
	Insert(~seq,1,-Coefficient(f,0)/Coefficient(f,1));
      else
	K := ext<K|f>;
	ChangeUniverse(~seq,K);
	Insert(~seq,1,K.1);
	P := PolynomialRing(K);
      end if;
    end for;
    return D(K)!seq;

end function;

function good_extn_point(ls,D,Z,boo)
// Pick a good point p of affine curve D/k over a small degree extension
// K of k which is scheme-theoretically a component of D meet l, where
// l is one of the k-linear forms in the base variables from the
// sequence ls of such forms, s.t. p doesn't lie in 'bad' subscheme Z.
// If no such point exists, return false.

    // if boo, know that D doesn't lie in any l-plane, l in ls.
    ints := boo select [D meet Scheme(Ambient(D),l) : l in ls]
	else [D meet Scheme(Ambient(D),l) : l in ls | l notin Ideal(D)];
    degs := [Degree(i) : i in ints];
    ks := [j : j in [1..#ints] | degs[j] ne 0];
    while #ks gt 0 do
      _,k := Min([degs[i] : i in ks]);
      ps := PrimeComponents(ints[ks[k]]);
      Remove(~ks,k);
      degs1 := [Degree(p) : p in ps];
      if #ps gt 1 then
	Sort(~degs1,~prm);
      else
	prm := 1; //works as identity permutation on 1 element!
      end if;
      for j in [1..#ps] do
	p := ps[j^prm];
	if IsEmpty(Z meet p) then
	  return true,extn_pt(p,D);
	end if;
      end for;
    end while;
    return false,_;

end function;

function good_point(D,X,boo)
    A := Ambient(X);
    k := BaseRing(A);
    Z := SingularSubscheme(D);
    if boo then Z := Z join SingularSubscheme(X); end if;
    if Type(k) cmpeq FldFin then
      my_h := func<s| #[0 : u in s| not IsZero(u)]>;
      pts := Setseq(RationalPointsByFibration(D:Max := 1000));
    elif Type(k) cmpeq FldRat then
      my_h := func<s| &+[Abs(u*l) : u in s]+l where l is LCM([Denominator(e) : e in s])>;
      pts := PointSearch(D,10);
    else
      pts := [];
    end if;
    cmp := func<s,t|my_h(Eltseq(s))-my_h(Eltseq(t))>;
    if #pts ne 0 then
      Sort(~pts,cmp);
      for p in pts do
	if A!Eltseq(p) notin Z then return p; end if;
      end for;
    end if;
    // Will have to choose a point possibly over an extension field.
    // Take a component of a non-empty small degree intersection l meet D
    // with l a linear form. Begin trying the xi, then +/-1 linear combs of
    // the xi with increasing numbers of terms, then random (for FFs) or
    // increasing (char 0) linear combinations of the xi.
    js := [j : j in [1..Length(A)] | A.j notin Ideal(D)];
    b,p := good_extn_point([A.j : j in js],D,Z,true);
    if b then return p; end if;
    sgns := (Characteristic(k) eq 2) select [1] else [1,-1];
    for i in [2..#js] do
      sti := [Setseq(s) : s in Subsets({1..#js},i)];
      cps := CartesianPower(sgns,i-1);
      ls := [A.(s[1])+&+[c[j]*A.(s[j+1]): j in [1..i-1]] : c in cps, s in sti];
      b,p := good_extn_point(ls,D,Z,false);
      if b then return p; end if;
    end for;
    if Type(k) cmpeq FldFin then
      if #k gt 3 then
	ls := [&+[Random(k)*(A.j) : j in js] : i in [1..20]];
	b,p := good_extn_point(ls,D,Z,false);
	if b then return p; end if;
      end if;
    else
      error if Characteristic(k) ne 0, "Point choice on divisor needs base field",
	"to be finite or have characteristic 0.";
      // Should never really get to this point unless VERY unlucky! So, it's not
      // been made especially efficient.
      for d in [2..5] do
	cp := CartesianPower([-d..d],#js);
	cp := [c : c in cp | Max([Abs(c[i]) : i in [1..#js]]) eq d];
	ls := [&+[c[j]*(A.j) : j in js] : c in cp];
        b,p := good_extn_point(ls,D,Z,false);
	if b then return p; end if;
      end for;
    end if;
    error "Failed to find a good point (over an extension field) on a divisor after",
		"many attempts";
      
end function;

function test_mults_loc(f,dat,cls,ld)

    // first get the data for the local mult comp for each divisor
    ms := [];
    for c in cls do
      pi,i := Explode(ld[c[1]]);
      f1 := Evaluate(f,DefiningPolynomials(dat[pi][3]));
      // get the data for the local mult comp for the c divisor
      X := dat[pi][2];
      D := dat[pi][1][i];
      p := good_point(D,X,dat[pi][4][i]);
      fs,hm := set_up_loc_mult_struct(X,D,p);
      // do the comp.
      Append(~ms,local_multiplicity_F(f1,fs,hm));
    end for;
    return ms;
   
end function;

function test_mults_naive(f,dat,cls,ld)

    ms := [];
    for c in cls do
      pi,i := Explode(ld[c[1]]);
      f1 := Evaluate(f,DefiningPolynomials(dat[pi][3]));
      Append(~ms,naive_multiplicity_F(f1,dat[pi][1][i],dat[pi][2]));
    end for;
    return ms;
   
end function;

function mults(f,dsd,boo)
// Overall function for computing multiplicities of poly f/ideal f
// (if boo true/false) on the base patch of the singularity.

// NB: Currently don't have top level functionality to set choice
// to use local rather than global intersection method. However,
// this function is written so as to allow that possibility in future.

    dat := dsd`main_dat; cls := dsd`classes; ld := dsd`div_leaf_dat;
    b_glob := dsd`mult_use_glob or (not assigned dsd`mult_dat);
    if not b_glob then m_dat := dsd`mult_dat; end if;
    if boo then
      fs := [*Evaluate(f,DefiningPolynomials(d[3])) : d in dat*];
    else
      fs := [*ideal<CoordinateRing(Ambient(d[2]))| [Evaluate(e,DefiningPolynomials(d[3])):
			e in Basis(f)]> : d in dat*];
    end if;
    ms := [];
    for j in [1..#cls] do
      pi,i := Explode(ld[(cls[j])[1]]);
      X := dat[pi][2];
      if (not b_glob) and Type(m_dat[j]) cmpne RngIntElt then
	fs,hm := Explode(m_dat[j]);
	if boo then
	  m := local_multiplicity_F(fs[pi],fs,hm);
	else
	  m := local_multiplicity_I(Scheme(Ambient(X),Basis(fs[pi])),fs,hm);
        end if;
      else
	if boo then
	  m := naive_multiplicity_F(fs[pi],dat[pi][1][i],X);
	else
	  m :=naive_multiplicity_I(Scheme(Ambient(X),Basis(fs[pi])),
				dat[pi][1][i],X);
        end if;
      end if;
      Append(~ms,m);
    end for;
    return ms;

end function;

function mults_and_ints(f,dat,cls,ld,boo)
// Return the multiplicities [m1,..,mr] of the exceptional divisors Di in the
// effective divisor Df given by polynomial f/ideal f (if boo true/false)
// on the base patch of the singularity and also return the intersections
// [n1,...,nr] with Ef:=Df-(m1*D1+..mr*Dr) (i.e. ni = Ef.Di)

    if boo then
      fs := [*Evaluate(f,DefiningPolynomials(d[3])) : d in dat*];
    else
      fs := [*ideal<CoordinateRing(Ambient(d[2]))| [Evaluate(e,DefiningPolynomials(d[3])):
			e in Basis(f)]> : d in dat*];
    end if;
    ms := [];
    vprintf MultsAndInts : "Computing multiplicities...\n";
    for c in cls do
      pi,i := Explode(ld[c[1]]);
      X := dat[pi][2];
      if boo then
	Append(~ms,naive_multiplicity_F(fs[pi],dat[pi][1][i],X));
      else
	Append(~ms,naive_multiplicity_I(Scheme(Ambient(X),Basis(fs[pi])),
				dat[pi][1][i],X));
      end if;
    end for;
    // construct the divisor for Ef in the various leaf patches
    vprintf MultsAndInts : 
      "Constructing the strict transform Ef on %o patches...\n Doing patch ",#dat;
    Ef := [**];
    for i in [1..#dat] do
      vprintf MultsAndInts : "%o ",i;
      X := dat[i][2];
      /*ps := { Ideal(c) : c in dat[i][1] };
      Dfi := ideal<CoordinateRing(Ambient(X))| Basis(Ideal(X)) cat [fs[i]]>;
      pcs,psf := PrimaryDecomposition(Dfi);
      js := [j : j in [1..#pcs] | (psf[j] notin ps) and 
		(Dimension(psf[j]) eq 1)];
      if #js gt 0 then
	Efi := Scheme(Ambient(X),&meet[pcs[j] : j in js]);
	Append(~Ef,<Efi,i>);
      end if;*/
      Dfi := ideal<CoordinateRing(Ambient(X))| Basis(Ideal(X)) cat 
		(boo select [fs[i]] else Basis(fs[i]))>;
      ps := [ Ideal(c) : c in dat[i][1] ];
      for e in ps do Dfi := Saturation(Dfi,e); end for;
      //Dfi := EquidimensionalPart(Dfi); - unnecessary!
      if Dimension(Dfi) gt 0 then
	Append(~Ef,<Scheme(Ambient(X),Dfi),i>);
      end if;
    end for;
    vprintf MultsAndInts : "\nComputing intersections of Ef with blow-up divisors...\n";
    if #Ef eq 0 then
      ns := [0: i in [1..#cls]];
    else
      ns := [intersection_num_Dcl([ld[i] : i in d],Ef,dat) : d in cls];
    end if;
    return ms,ns;

end function;

function self_ints(f,mat,dat,cls,ld)
// Use polynomial f on the base scheme that vanishes on the singular component
// Y and the matrix mat of Ei.Ej intersections to compute the self-intersections
// Ei.Ei where E1,..Er are the exceptional divisors over Y.

    ms,ns := mults_and_ints(f,dat,cls,ld,true);
    //(f)= R+D where R is a +ive linear combination of the Ei=sum ms[i]*Ei
    // and D is an effective divisor with no Ei component and Ei.D=ns[i]
    assert &and[m gt 0 : m in ms] and &and[n ge 0 : n in ns] and
	&or[n gt 0 : n in ns];
    // sequence of ((f)-ms[i]Ei).Ei
    seq := Eltseq((Vector(ms)*mat)+Vector(ns));
    assert &and[IsDivisibleBy(seq[i],ms[i]) : i in [1..#seq]];
    return [-(seq[i] div ms[i]) : i in [1..#seq]];

end function;


function expand_to_prec(Fs,subs,prec : d := 0, subsx2 := false)
// Used by function below to expand polynomials Fs in x1,..xn as
// power series in 'Y' (if subsx2) or x2 and x1 mod O(deg prec+1)
// (& O(Y/x2^d) if d > 0) where Y=x2+O(deg 2) is the local equation
// for D in X. If subsx2 is true then subs[2] should be the expansion
// (O(deg prec+1)) of x2 purely as a Y and x1 poly.
    P := Generic(Parent(Fs[1]));
    n := Rank(P);
    Gs := [&+[P|e : e in Terms(f) | LeadingTotalDegree(e) le prec] : f in Fs];
    is_good := func<f | IsZero(f) or &and[&and[e eq 0 : e in es] where es
	is Exponents(t)[3..n] : t in Terms(f)]>;
    bad_is := [i : i in [1..#Fs]];
    P := Generic(Universe(subs));
    seq := Setseq(MonomialsOfDegree(P,prec+1));
    if d gt 0 then
      seq := [m : m in seq | Exponents(m)[2] le d] cat [(P.2)^d];
    end if;
    Sort(~seq); Reverse(~seq);
    P1 := quo<P|seq>;
    s1 := [P1!e : e in subs];
    if subsx2 then
      s := [P1.1,s1[2]] cat [P1.i : i in [3..n]];
      Gs := [P!Evaluate(Gs[i],s) : i in bad_is];
      s1 := [P1.1,P1.2] cat [Evaluate(e,s) : e in s1[3..n]];
    end if;
    while #bad_is gt 0 do
      Gs1 := [P!Evaluate(Gs[i],s1) : i in bad_is];
      for i in [1..#bad_is] do Gs[bad_is[i]] := Gs1[i]; end for;
      bad_is := [i : i in bad_is | not is_good(Gs[i])];
    end while;
    return Gs;
end function;

function lin_sys_restriction_loc(B,r,d,ds)
// B is the basis of a linear system of polynomials in the affine
// patch containing singularity Y. Compute the linear subsystem
// given by the subspace that vanishes to multiplicity at least
// d>0 on the rth exceptional divisor D over Y. This version uses
// local methods and two-var power series expansions

    dat := ds`main_dat; cls := ds`classes; ld := ds`div_leaf_dat;
    pi,i := Explode(ld[(cls[r])[1]]);
    Bpi := [Evaluate(f,DefiningPolynomials(dat[pi][3])) : f in B];
    if not assigned ds`mult_dat or (Type(ds`mult_dat[r]) cmpeq RngIntElt) then
      p := good_point(dat[pi][1][i],dat[pi][2],dat[pi][4][i]);
      if not assigned ds`mult_dat then ds`mult_dat := [*0 : j in [1..#cls]*]; end if;
      fs,hm := set_up_loc_mult_struct(dat[pi][2],dat[pi][1][i],p);
      (ds`mult_dat)[r] := <fs,hm>;
    end if;
    fs,hm := Explode((ds`mult_dat)[r]);
    Pl := Parent(fs[1]);
    n := Rank(Pl); K := BaseRing(Pl);
    // convert back to non-local poly ring for power series comps
    P := PolynomialRing(K,n,"grevlex");
    fsP := [P!f : f in fs];
    subs1 := [P.1,2*P.2-fsP[n-1]] cat [P.i-fsP[n+1-i] : i in [3..n]];
    Bloc := [P!hm(b) : b in Bpi];
    prec := Max(5,2*d);
    mat := IdentityMatrix(K,#B);
    Vdone := []; Id := 0;
    while true do
      // first, letting Y=fsP[n-1]=x2+O(deg 2) - the local equation for D,
      // expand to get substitution x2=p(x1,Y) mod O(deg prec+1)
      R := PolynomialRing(K,n+1,"grevlex");
      s := [R.1] cat [R.i : i in [3..n+1]];
      v := R.2-Evaluate(P.2-fsP[n-1],s);
      subs := [R.1,R.2,v] cat [Evaluate(P.i+a*P.2-fsP[n+1-i],s)-a*v where
		a is MonomialCoefficient(fsP[n+1-i],P.2) : i in [3..n]];
      x2p := expand_to_prec([R.3],subs,prec)[1];
      x2p := Polynomial(Coefficients(x2p),[Monomial(P,Exponents(m)[1..n]) : m in
			Monomials(x2p)]);
      // now expand the elements of B as x1,Y power series up to degree prec
      subs := [P.1,x2p] cat [P.i+a*P.2-fsP[n+1-i]-a*x2p where 
		a is MonomialCoefficient(fsP[n+1-i],P.2) : i in [3..n]];
      Bexp := expand_to_prec(Bloc,subs,prec : d := d, subsx2 := true);
      if &and[IsZero(b) : b in Bexp] then
	mat1 := IdentityMatrix(K,#Bloc);
      else
        j := Max(&cat[[Exponents(t)[1] : t in Terms(b)] : b in Bexp | not IsZero(b)]);
	Mcs := Matrix([[MonomialCoefficient(b,Monomial(P,[i,k] cat s)) : i in [0..j],
			k in [0..d-1]] : b in Bexp]) where s is [0:i in [3..n]];
	V := Kernel(Mcs);
	mat1 := Matrix(Basis(V));
      end if;
      if Nrows(mat1) eq 0 then break; end if; //empty subspace 
      // check which basis elements of the subspace actually satisfy the condition
      B1 := Eltseq(ChangeRing(mat1,P)*Matrix(#Bloc,1,Bloc));
      Id := (Type(Id) cmpeq RngIntElt) select ideal<Pl|Prune(fs) cat [fs[#fs]^d]> else
		Id;
      good_is := [i : i in [1..#B1] | Pl!(B1[i]) in Id];
      if #good_is gt 0 then
        Vdone cat:= RowSequence(Matrix([mat1[i] : i in good_is])*mat);
      end if;
      if #good_is eq #B1 then break; end if;
      // recompute with higher precision for 'ambiguous' elements of B1;
      bad_is := [i :i in [1..#B1] | i notin good_is]; 
      Bloc := [B1[i] : i in bad_is];
      mat := Matrix([mat1[i] : i in bad_is])*mat;
      prec +:= 5;
    end while;
    if #Vdone eq 0 then
      return Matrix(K,0,#B,[]);
    else
      return Matrix(Vdone);
    end if;

end function;

function lin_sys_restriction_glob(B,d,dat,cl,ld)
// B is the basis of a linear system of polynomials in the affine
// patch containing singularity Y. Compute the linear subsystem
// given by the subspace that vanishes to multiplicity at least
// d>0 on the exceptional divisor D over Y of class cl. This version
// uses global Groebner basis computations

    pi,i := Explode(ld[cl[1]]);
    Bpi := [Evaluate(f,DefiningPolynomials(dat[pi][3])) : f in B];
    gcd := GCD(Bpi);
    if TotalDegree(gcd) gt 0 then
      //pullback of the Bs have a non-trivial gcd on patch pi.
      mg := naive_multiplicity_F(gcd,dat[pi][1][i],dat[pi][2]);
      if mg ge d then
	return IdentityMatrix(BaseRing(Universe(B)),#B);
      end if;
      d -:= mg;
      Bpi := [b div gcd : b in Bpi];
    end if;
    ID := Ideal(dat[pi][1][i]); IX := Ideal(dat[pi][2]);
    Id := ID;
    for j in [2..d] do
      Id := EquidimensionalPart(ID*Id+IX);
    end for;
    Bn := [NormalForm(b,Id) : b in Bpi];
    if &and[IsZero(b) : b in Bn] then 
      return IdentityMatrix(BaseRing(Universe(B)),#B);
    end if;
    mons := Setseq(&join[Seqset(Monomials(b)) : b in Bn | not IsZero(b)]);
    mat := Matrix([[MonomialCoefficient(b,m) : m in mons] : b in Bn]);
    V := Kernel(mat);
    return Matrix(Basis(V));

end function;

function full_lin_sys_res_general(B,mults,dat,cls,ld,bmon)
// B is the basis of a linear system of polynomials in the affine
// patch containing singularity Y. IT IS BEST HERE if B is the full
// O(d) linear system of all monomials of degree <=d. Here we compute
// the subsytem given by the set of restriction conditions on all
// exceptional divisors of vanishing to order >= mults[i] on the ith.
//
// As we want to cover cases where some of mults[i] are quite large,
// we use a filtration by order method on successive divisors starting
// with ones where mults[i] is largest. The idea is that, in practise,
// for the high multiplicity divisors, there will only be a few members
// of B with any given multiplicity and the pullbacks to the relevant
// blow-up patch will often have a big common factor, especially if B is
// pure monomials. Taking out the common factor,
// we solve a restriction problem on the few members to a much lower order -
// namely up to the next highest multiplicity of members of B - the mult. of
// the gcd.

    R := Generic(Universe(B));
    // first compute multiplicities of B elements at each exceptional div.
    if bmon then // B consists of monomials
      mxs := Matrix([test_mults_naive(R.i,dat,cls,ld) : i in [1..Rank(R)]]);
      mmat := Matrix([Exponents(b) : b in B])*mxs;
    else
      mmat := Matrix([test_mults_naive(b,dat,cls,ld) : b in B]);
    end if;
    resmat := IdentityMatrix(BaseRing(R),#B);

    while &or[Min(rs[i]) lt mults[i]: i in [1..#mults]] where rs is
		RowSequence(Transpose(mmat)) do
      d,r := Max(mults);
      Bmr := [mmat[i,r] : i in [1..#B]];
      Bmr1 := Sort(Setseq(Seqset(Bmr)));
      while (#Bmr1 gt 0) and (Bmr1[1] lt d) do
	m1 := Bmr1[1];
	m2 := (#Bmr1 eq 1) select d else Min(Bmr1[2],d);
	js := [j : j in [1..#Bmr] | Bmr[j] eq m1];
	Remove(~Bmr1,1);
	if #js gt 1 then
	  mat1 := lin_sys_restriction_glob([B[i] : i in js],m2,dat,cls[r],ld);
	end if;	 
	if (#js eq 1) or (Nrows(mat1) eq 0) then
	  for i in Reverse(js) do
	    Remove(~B,i);
	    Remove(~Bmr,i);
	    RemoveRow(~resmat,i);
	    RemoveRow(~mmat,i);
	  end for;
	else
	  // Expect this case to not happen often! Don't want it too often
	  // for large m2 as multiplicities have to be recomputed - OK, though
	  // if the linear combiations of B in B1 still pullback to to elements
	  // that are highly factorable.
	  B1 := Eltseq(ChangeRing(mat1,R)*Matrix(#js,1,[B[i] : i in js]));
	  mmat1 := Matrix([test_mults_naive(b,dat,cls,ld) : b in B1]);
	  resmat1 := mat1*Matrix([resmat[j] : j in js]);
	  for i in [1..#B1] do
	    B[js[i]] := B1[i];
	    Bmr[js[i]] := mmat1[i,r];
	    resmat[js[i]] := resmat1[i];
	    mmat[js[i]] := mmat1[i];
	  end for;
	  Bmr1 := Sort(Setseq(Seqset(Bmr1 cat [mmat1[i,r] : i in [1..#B1]])));
	  for i in Reverse(js[(#B1)+1..#js]) do
	    Remove(~B,i);
	    Remove(~Bmr,i);
	    RemoveRow(~resmat,i);
	    RemoveRow(~mmat,i);
	  end for;
	end if;
	if #B eq 0 then break; end if;
      end while;
      Remove(~mults,r);
      if (#B eq 0) or (#mults eq 0) then break; end if;
      RemoveColumn(~mmat,r);
      Remove(~cls,r);
//printf "d:%o\nr:%o\nB:%o\n",d,r,B;
    end while;
    return resmat;

end function;

///// Functions to deal with differential forms on affine surfaces ///////

function diff_pullback(phi,f,i,j)
// phi is a morphism X -> Y of affine surfaces and w is the
// differential f*(dy_i^dy_j) where f is a rational function
// on (the ambient of) Y and the y_k are the coord fns of the ambient.
// Return the pullback by phi of w as a sequence [<g,l,m>] where
// <g,l,m> represents g*(dx_l^dx_m) and phi^*(w) is the sum of these terms.

    defs := DefiningPolynomials(phi);
    gstar := Evaluate(f,defs);
    ijp := [Evaluate(A.k,defs) : k in [i,j]] where A is 
                Ambient(Codomain(phi));
    n := Length(Ambient(Domain(phi)));
    dijp := [[Derivative(e,k) : k in [1..n]] : e in ijp];
    wstar := [<gstar*(dijp[1][l]*dijp[2][m]-dijp[2][l]*dijp[1][m]),l,m>:
                m in [l+1..n],l in [1..n-1]];
    return wstar;

end function;

function get_l12_bad_case(eqns,R,n)
// used by good_diff_form in the unlikely cases where no dxi^dxj work.

    k := BaseRing(R);
    booff := (Type(k) cmpeq FldFin);
    rand := func<|booff select Random(k) else k!Random(-5,5)>;
    // first try l1=xi
    i0 := 0;
    for i in [1..n] do
      seq := [0 : j in [1..n]]; seq[i] := 1;
      eqnsi := [*Evaluate(e,[R.j : j in [1..n]] cat [R!s : s in seq])
		where R is Parent(e) : e in eqns*];
      if not &or[IsZero(e) : e in eqnsi] then
	i0 := i; break;
      end if;
    end for;
    if i0 eq 0 then
      bdone := false;
      for j in [1..20] do
	vec := [rand() : i in [1..n]];
	eqnsi := [*Evaluate(e,[R.j : j in [1..n]] cat [R!v : v in vec])
		where R is Parent(e) : e in eqns*];
	if not &or[IsZero(e) : e in eqnsi] then
	  bdone := true; break;
	end if;
      end for;
      error if not bdone, "Failed to fine a good auxilliary patch differential",
		"after 20 random tries.";
    end if;
    // now try random vectors for l2
    bdone := false;
    for j in [1..20] do
      vec1 := [rand() : i in [1..n]];
      evals := [*Evaluate(e,vec1) : e in eqnsi*];
      if not &or[IsZero(e) : e in evals] then
	  bdone := true; break;
      end if;
    end for;
    error if not bdone, "Failed to fine a good auxilliary patch differential",
		"after 20 random tries.";
    //now get a linear transform tr that takes l1 -> x1 and l2 -> x2
    //and its inverse tri
    seq := [R.i:i in [1..n]];
    if i0 ne 0 then
      i1 := [i : i in [1..n] | (i ne i0) and not IsZero(vec1[i])][1];
      tri := [R.i0,Polynomial(vec1,seq)] cat
		[R.j : j in [1..n] | (j ne i0) and (j ne i1)];
    else
      mat := Matrix([vec,vec1]);
      assert Rank(mat) eq 2;
      mat := EchelonForm(mat);
      supp := [Min(Support(mat[i])) : i in [1..2]];
      tri := [Polynomial(vec,seq),Polynomial(vec1,seq)] cat
		[R.j : j in [1..n] | j notin supp];
    end if;
    mat := Matrix([[MonomialCoefficient(f,s) : s in seq]:f in tri])^-1;
    tr := [Polynomial(r,seq) : r in RowSequence(mat)];
    return tr,tri;

end function;

function good_diff_form(X,Ds,Ddat)
// X an affine surface and Ds a sequence (assumed non-empty here) of
// irreducible curves in X, none of which lie in Sing(X).
// Find linear forms l1,l2 (preferably coordinate functions) in the
// coordinate functions s.t. d(l1)^d(l2) is non-zero differential
// on X which doesn't vanish along the whole of any Ds[i].
// Return a sequence [[g1,h1],..[gn,hn]] of pairs of rational functions
// s.t. coord fn xi sats. dxi=gi*d(l1)+hi*d(l2) on X.

    A := Ambient(X);
    n:= Length(A);
    R := CoordinateRing(A); K := FieldOfFractions(R);
    if n eq 2 then
      //dx1^dx2 works
      return [[K!1,K!0],[K!0,K!1]];
    end if;
    if n eq 3 then
      F := DefiningPolynomial(X);
      DF := [Derivative(F,i) : i in [1..3]];
      error if &and[IsZero(e) : e in DF], "Surface is not geometrically reduced";
      for i := 3 to 1 by -1 do
	if (not IsZero(DF[i])) and &and[DF[i] notin Ideal(D) : D in Ds] then
	  seq := [[K!1,K!0],[K!0,K!1]];
	  Insert(~seq,i,[-DF[j]/DF[i] : j in [1..3] | j ne i]);
	  return seq;
	end if;
      end for;
    end if;
    //Choose a point (maybe over a finite extension of the base field) on
    //each D which is non-singular on X and choose l1,l2 s.t. d(l1)^d(l2)
    //doesn't vanish at any of these points. Ddat will already contain the
    //relevant data for some of the Ds.
    Dd := Ddat;
    for i in [1..#Ds] do
      if Type(Dd[i]) cmpeq RngIntElt then
	p := good_point(Ds[i],X,true);
	fs,hm := set_up_loc_mult_struct(X,Ds[i],p);
	Dd[i] := <fs,hm>;
      end if;
    end for;
    //If l1=a1*x1+..+an*xn, l2=b1*x1+..bn*xn, set up the relevant bilinear
    //polynomials in the ai,bi (over various extensions of the base field)
    //whose vanishing gives vanishing of d(l1)^d(l2) at the chosen points.
    eqns := [**];
    for i in [1..#Ds] do
      hm := Dd[i][2];
      Rl := Codomain(hm);
      PK := PolynomialRing(BaseRing(Rl),2*n);
      vecs := [[MonomialCoefficient(hm(R.i),Rl.j):i in [1..n]] : j in [1,2]];
      Append(~eqns,&+[vecs[1][i]*PK.i:i in [1..n]]*&+[vecs[2][i]*PK.(i+n):i in [1..n]]-
		&+[vecs[2][i]*PK.i:i in [1..n]]*&+[vecs[1][i]*PK.(i+n):i in [1..n]]);
    end for;
    // Now choose ai,bj in the base field k s.t. none of eqns vanish. Try combinations
    // with the li = coordinate functions first.
    k := BaseRing(R);
    seq := [k!0 : i in [1..2*n]];
    i0 := 0;
    for i in [1..n-1], j in [i+1..n] do
      vec := seq; bgood := true;
      vec[i] := k!1; vec[n+j] := k!1;
      for f in eqns do
	if IsZero(Evaluate(f,ChangeUniverse(vec,BaseRing(Parent(f))))) then
	  bgood := false; break;
	end if;
      end for;
      if bgood then i0 := i; j0 := j; break; end if;
    end for;
    if i0 eq 0 then
      tr,tri := get_l12_bad_case(eqns,R,n);
      i0 := 1; j0 := 2; btr := true;
      defs := [Evaluate(e,tr) : e in DefiningPolynomials(X)];
    else
      defs := DefiningPolynomials(X); btr := false;
    end if;
    // now get expressions for the dxi as gi*d(l1)+hi*d(l2);
    inds := [i : i in [1..n] | (i ne i0) and (i ne j0)];
    mat1 := Matrix(K,[[Derivative(f,i) : i in inds] : f in defs]);
    mat2 := Matrix(K,[[Derivative(f,i) : i in [i0,j0]] : f in defs]);
    E,trE := EchelonForm(mat1);
    assert RowSubmatrix(E,1,n-2) eq IdentityMatrix(K,n-2);
    E := trE*mat2; 
    gs := [-E[i,1] : i in [1..n-2]];
    hs := [-E[i,2] : i in [1..n-2]];
    Insert(~gs,i0,K!1); Insert(~gs,j0,K!0);
    Insert(~hs,i0,K!0); Insert(~hs,j0,K!1);
    if btr then // linearly transform back the results
      gs := [Evaluate(g,tri) : g in gs];
      hs := [Evaluate(h,tri) : h in hs];
      A := Matrix([[MonomialCoefficient(tri[j],R.i) : i in [1..n]]:
			j in [1..n]])^-1;
      gs,hs := Explode([Eltseq(ChangeRing(A,R)*Matrix(n,1,v)) :
			v in [gs,hs]]);
    end if;
    // If, unluckily, any of the rational functions gi or hi are of the
    // form a/b with a,b in Ideal(X), we have to work them out using
    // R-modules. Check this.
    bad_i := []; pairs := [[K!0,K!0]:i in [1..n]];
    I := Ideal(X);
    for i in [1..n] do
      n1 := Numerator(gs[i]); d1 := Denominator(gs[i]);
      if d1 in I then
	assert n1 in I;
	Append(~bad_i,i);
	continue;
      end if;
      n2 := Numerator(hs[i]); d2 := Denominator(hs[i]);
      if d2 in I then
	assert n2 in I;
	Append(~bad_i,i);
      else
	pairs[i] := [gs[i],hs[i]];
      end if;
    end for;
    if #bad_i gt 0 then
      I := ideal<R|defs>;
      matz := ZeroMatrix(R,#defs,n);
      matc := Matrix(#defs,1,defs);
      mat := Matrix([[Derivative(f,i) : i in [1..n]] : f in defs]);
      for i in [1..n] do
	mat := VerticalJoin(mat,InsertBlock(matz,matc,1,i));
      end for;
      matz := ZeroMatrix(R,2,n);
      matz[1,i0] := R!1; matz[2,j0] := R!1;
      mat := VerticalJoin(matz,mat);
      F := Module(R,n);
      vecs := [F!r : r in RowSequence(mat)];
      for i in bad_i do
	if btr then
	  vec := [R!MonomialCoefficient(tr[i],R.j) : j in [1..n]];
	else
	  vec := [R!0:j in [1..n]]; vec[i] := R!1;
	end if;
	M := sub<F|[F!vec] cat vecs>;
	B := Basis(SyzygyModule(M));
	b0 := 0;
	for b in B do
	  if b[1] notin I then b0:=b; break; end if;
	end for;
	assert Type(b0) cmpne RngIntElt;
	pr := [K!(-b0[2]/b0[1]),K!(-b0[3]/b0[1])];
	if btr then pr := [Evaluate(e,tri) : e in pr]; end if;
	pairs[i] := pr;	
      end for;
    end if;

    return pairs;

end function;

function diff_to_loc_fns(f,i,j,dsY)
// w = f dxi^dxj is a rational differential form on the base scheme. Return
// a sequence(list) of rational functions fk on the affine blow-up
// packages Xk containing the chosen reps of the exceptional divisors
// over Y s.t. the pull back of w on Xk is fk *(dl1^dl2) where l1 and l2
// are linear forms on the patch s.t. the holomorphic differential dl1^dl2
// doesn't vanish on any of the exceptional curves in Xk.

    dat := dsY`main_dat;  
    clr := [c[1] : c in dsY`classes];
    ldr := [(dsY`div_leaf_dat)[k] : k in clr];
    pis := Sort(Setseq(Seqset([l[1] : l in ldr]))); //relevant patch indices
    inds := [[l[2] : l in ldr | l[1] eq k] : k in pis];
    fs := [**];
    for k in [1..#pis] do
      datk := dat[pis[k]];
      if assigned dsY`mult_dat then
	Ddat := [*(dsY`mult_dat)[Index(ldr,[pis[k],l])] : l in inds[k]*];
      else
	Ddat := [*0 : l in [1..#(inds[k])]*];
      end if;
      pairs := good_diff_form(datk[2],[(datk[1])[l] : l in inds[k]],Ddat);
      wstar := diff_pullback(datk[3],f,i,j);
      fk := &+[e[1]*(pairs[e[2]][1]*pairs[e[3]][2]-pairs[e[3]][1]*pairs[e[2]][2]) :
		e in wstar];
      Append(~fs,fk);
    end for;
    return fs;

end function;

function diff_mults_hyp(f,i,j,dsY)
// w = f dxi^dxj is a rational differential form on the base scheme.
// Return the sequence of multiplicities of the exceptional divisors
// over Y in the divisor of w. Version particularly adapted to (though not
// strictly limited to) hypersurfaces where the 'natural' differential form is
// directly expressed as f dxi^dxj.

    vprintf MultsAndInts : "Getting good local differentials on blow-up patches.\n";
    fs := diff_to_loc_fns(f,i,j,dsY);

    dat := dsY`main_dat;  
    clr := [c[1] : c in dsY`classes];
    ldr := [(dsY`div_leaf_dat)[k] : k in clr];
    pis := Sort(Setseq(Seqset([l[1] : l in ldr]))); //relevant patch indices
    if dsY`mult_use_glob or not assigned dsY`mult_dat then
      bglob := [true : i in [1..#clr]];
    else
      bglob := [Type(d) cmpeq RngIntElt select true else false:
			d in dsY`mult_dat];
    end if;
    mults := [];
    vprintf MultsAndInts : "Computing multiplicities...\n";
    for i in [1..#clr] do
      pi := ldr[i][1]; j := ldr[i][2];
      X := dat[pi][2]; D := dat[pi][1][j];
      fk := fs[Index(pis,pi)];
      n := Numerator(fk); d := Denominator(fk);
      if bglob[i] then
	mlt := naive_multiplicity_F(n,D,X)-naive_multiplicity_F(d,D,X);
      else
	fp,hm := Explode(dsY`mult_dat[i]);
	mlt := local_multiplicity_F(n,fp,hm)-local_multiplicity_F(d,fp,hm);
      end if;
      Append(~mults,mlt);
    end for;
    return mults;

end function;

/////////////////////////////////////////////////////
 
function linear_elim_B(B)
// B generates an ideal I in R=k[x1,..xn]. Eliminate vars 
// (highest index first) by using relations
// in B of the form xi+F(x1,..,xn) where F doesn't involve xi.
// Apply this iteratively to get a new generic ring R1 and
// transformed B, Bn, generating I1<=R1 with R1/I1 = R/I.
// Return whether an elimination was performed and, if so,
// the elimination map R->R1, the inclusion map R1->R and Bn.

    R := Generic(Universe(B));
    n := Rank(R);
    subs := [R.i : i in [1..n]];
    if #B eq 0 then
      phi := hom<R->R|subs>;
      return false,phi,phi,B;
    end if;
    bchange := false;
    B1 := [b : b in B | &or[TotalDegree(t) eq 1 : t in Terms(b)]];
    while #B1 gt 0 do
      js := [j : j in [1..n] | subs[j] eq R.j];
      bdone := true;
      for j in js do
	for b in [e : e in B1 | not IsZero(MonomialCoefficient(e,R.j))] do
	  c := MonomialCoefficient(b,R.j);
	  b1 := b-c*(R.j);
	  if &and[Exponents(t)[j] eq 0 : t in Terms(b1)] then
	    subs[j] := -(1/c)*b1;
	    for k in [k : k in [1..n] | (k ne j) and k notin js] do
	      subs[k] := Evaluate(subs[k],subs);
	    end for;
	    B := [Evaluate(e,subs) : e in B];
	    B := [e : e in B | not IsZero(e)];
	    B1 := [e : e in B | &or[TotalDegree(t) eq 1 : t in Terms(e)]];
	    bdone := false; bchange := true; break;
	  end if;
	end for;
	if not bdone then break; end if;
      end for;
      if bdone then break; end if;
    end while;

    if bchange then
      inds := [i : i in [1..n] | subs[i] eq R.i];
      R1 := PolynomialRing(BaseRing(R),#inds,"grevlex");
      i := 1; prj := [R1|];
      for j in [1..n] do
	if j in inds then
	  Append(~prj,R1.i);
	  i +:= 1;
	else
	  Append(~prj,R1!0);
	end if;
      end for;
      subs := [Evaluate(s,prj) : s in subs];
      B := [Evaluate(b,prj) : b in B];
      mp1 := hom<R->R1|subs>;
      mp2 := hom<R1->R|[R.i : i in inds]>;
      return true,mp1,mp2,B;
    else
      return false,phi,phi,B where phi is hom<R->R|subs>;
    end if;
end function;

function linear_elim(I,b_use_GB)
// I is an ideal in k[x1,..xn]. Try to eliminate vars 
// (highest index first) simplistically by using relations
// in I of the form xi+F(x1,..,xn) where F doesn't involve xi.
// Apply this iteratively, making the substitutions
// xi -> -F(x1,..,xn) R-> k[x1,..,x(i-1),x(i+1),..xn]=R1,
// I -> image in R1. Tries an elimination using the original
// basis of I first and then, if b_use_GB is true, sees if
// the Groebner basis of I provides other possibilities.
// Return is as for linear_elim_B above.

    R := Generic(I);
    K := BaseRing(R);
    n := Rank(R);
    // first try initial basis relations
    B := Basis(I);
    boo,mp1,mp2,B1 := linear_elim_B(B);
    if b_use_GB and not (B eq GroebnerBasis(I)) then
	GB := GroebnerBasis(I);
	if boo then
	  GB := [mp1(b) : b in GB];
	  GB := [b : b in GB | not IsZero(b)];
	end if;
	boo1,mp3,mp4,_ := linear_elim_B(GB);
	if boo1 then
	  B1 := [mp3(b) : b in B1];
	  mp1 := 
	   hom<R->Codomain(mp3)|[mp3(mp1(R.i)) : i in [1..Rank(R)]]>;
	  mp2 := hom<R1->R|[mp2(mp4(R1.i)) : i in [1..Rank(R1)]]>
		where R1 is Domain(mp4);
	  boo := boo1;
	end if;
    end if;

    if boo and (#B1 gt 0) then
      B1 := GroebnerBasis(ideal<Universe(B1)|B1>);//good??
    end if;
    return boo,mp1,mp2,B1;
end function;

function local_blow_ups(I,B,b_use_GB)
// I <= R = k[x1,..,xn], I an ideal and B = [f1,..,fr],
// a collection of r polynomials in not lying in I and
// not zero-divisors of R/I.
// Compute the r local affine patches of the blow-up
// of X = Spec(R/I) by the closed subscheme Y=Spec(R/J)
// where J=I+ideal<R|B>. Let A = R/I.
//
// B(X,Y) is given projectively by 
//  Proj(A[X1,..Xr]/(<fj*Xi-fi*Xj|1<=i,j<=r>:<f1,..fr>))
//  where (I1:J1) denotes the saturation of ideal I1 by ideal J1
//  and the grading on A[X1,..,Xr] has deg(Xi)=1 and the fi
//  are identified with their images in A.
//
// B(X,Y) is covered by the r affine patches
// B(X,Y,i) = B(X,Y)_(Xi)
//  Spec(A[y1,..,y(i-1),y(i+1),..yr]/(<fj-fi*yj|1<=j<=r, j!=i>:<fi>))
//  for 1 <= i <= r, where yj <-> Xj/Xi
//
// Computes each B(X,Y,i) and tries to eliminate variables from
// the x1,..,xn,y1,..,y(i-1),y(i+1),..yr using linear relations.
// If b_use_GB is true, uses a Groebner Basis in the eliminate
// variables phase.
//
// Returns a sequence of r triples <Ii,seqi,inv_seqi> where the Ii of the
// ith pair is the ideal defining B(X,Y,i) [i.e. B(X,Y,i)=
//  Spec(Generic(Ii)/Ii)], the seqi defines the images of
//  x1,..,xn in Generic(Ii)/Ii corr. to prj_i: B(X,Y,i) -> X, and
//  inv_seqi are rational functions in the xi that the coordinate
//  functions of Generic(Ii) correspond to under the inverse map.

    R := Generic(I);
    K := BaseRing(R);
    n := Rank(R);
    r := #B;

    patches := [**];
    for i in [1..r] do
      Ri := PolynomialRing(K,n-1+r);
      seqi := [Ri.j : j in [1..n]];
      mpi := hom<R->Ri|seqi>;
      fji := [mpi(b) : b in B];
      Bi := [mpi(b) : b in Basis(I)] cat [fji[j]-fji[i]*(Ri.(n+j)) : j in [1..i-1]]
		cat [fji[j]-fji[i]*(Ri.(n+j-1)) : j in [i+1..r]];
      inv_seqi := [R.j : j in [1..n]] cat [B[j]/B[i] : j in [1..r] | j ne i];
      Ii := Saturation(ideal<Ri|Bi>,fji[i]);
      // try to eliminate linear relations
      boo,mp1,mp2,B2 := linear_elim(Ii,b_use_GB);
      if boo then
	seqi := [mp1(s) : s in seqi];
	inv_seqi := [inv_seqi[k] where k is Index(seq,mp2(S.j)) : j in [1..Rank(S)]]
	   where S is Codomain(mp1) where seq is [Ri.j : j in [1..n+r-1]];
	Ii := ideal<Codomain(mp1)|B2>;
      end if;
      Append(~patches,<Ii,seqi,inv_seqi>);
    end for;
    return patches;
end function;

intrinsic LocalBlowUp(X::Sch,Y::Sch) -> SeqEnum
{ Computes and returns local patches for the blow-up of affine variety
  X by subscheme Y. }

    defs := [f : f in DefiningPolynomials(Y) | f notin Ideal(X)];
    patch_Is := local_blow_ups(Ideal(X),defs,false);
    patches := [<X1,iso<X1->X|e[2],e[3]:Check := false>> where X1 is
		Scheme(Spec(Generic(e[1])),e[1]) : e in patch_Is];
    return patches;

end intrinsic;

intrinsic ResolveSingByBlowUp(X::Sch,Y::Sch) -> DesingData
{ X is an affine variety and Y is an isolated singular point (may be extended to
  an irreducible curve in the singular locus later) of X. Computes
  the tree of blowups to resolve the singularity at Y. }

    // Create record for "base-patch" X (to be removed later)
    rec0 := rec<NodeData|i := 1, X := X, ex_cmpts := [],ex_links := [], sing_cmpts1 := []>;
    tree := [rec0];
    leaves := [1]; // list of 'leaf' patches
    // List of (irreducible) exceptional divisors arising. Stored as a list
    // consisting of <I,i> where I is the defining ideal in the ambient of
    // patch i. i is the index of the first patch in which the divisor appears.
    // cmp1_sets, onedrels and div_preims are used to identify divisors resulting from
    // the blow-ups of 1-dim components of singular loci and cmp0_sets is for
    // the same thing for 0-dim component blow-ups.
    new_divs := [**]; onedrels := [**]; div_preims := [**]; cmp0_sets := []; cmp1_sets := [];
    idx := 2;
    sings := [* <1,Y> *]; //singular blow-up patches with singular locus
    while #sings ne 0 do
      for dat in sings do
	j := dat[1]; S := dat[2];
	BS := Basis(Ideal(S));
	bood0 := (Dimension(S) eq 0); //otherwise S is of dimension 1
	if bood0 then new_ind0 := []; end if;
	vprintf Resolve : "Blowing up singular component of dimension %o ...\n",
				(bood0 select 0 else 1);
	nnd := #new_divs;
	pj := [p : p in tree | p`i eq j][1];
	// get the irreducible exceptional divisors of patch pj
	// and divide into those that intersect the current blow-up
	// locus S and those that don't
	//
	// Also, at this stage, pj`ex_links contains just the index
	// into the list of new_divs rather than index pairs, which
	// will be constructed at the end
	pj_cmps := pj`ex_cmpts;
//printf "pj_cmps:%o\n",pj_cmps;
	inds := [i : i in [1..#pj_cmps] | IsEmpty(pj_cmps[i] meet S)];
	pj_cmps1 := [pj_cmps[i] : i in inds];
	pj_inds1 := [(pj`ex_links)[i] : i in inds];
	pj_cmps2 := [pj_cmps[i] : i in [1..#pj_cmps] | i notin inds];
	pj_inds2 := [(pj`ex_links)[i] : i in [1..#pj_cmps] | i notin inds];
//printf "pj_cmps1:%o\n,pj_cmps2:%o\n",pj_cmps1,pj_cmps2;
        // the non-blow-up singular components that meet S
	sing_old := [c : c in pj`sing_cmpts1 | not IsEmpty(c meet S)];

	Exclude(~leaves,j);	
	new_patches := LocalBlowUp(pj`X,S);
	for p in new_patches do
	  Xp := p[1];
	  mpp := p[2];
	  mppt := (j eq 1) select mpp else Expand(mpp*(pj`prj_map));
	  ex_p := [inv_img(mpp,c) : c in pj_cmps1];
//printf "ex_p:%o\n",ex_p;
	  exl_p := pj_inds1 cat pj_inds2;
	  // to get the STRICT TRANSFORM of components in pj_cmps2
	  // need to saturate the inverse image w.r.t an appropriate
	  // (pullback of) an element in the basis of Ideal(S)
	  elts := [];
	  for c in pj_cmps2 do
	    I := Ideal(c); i := 1;
	    while i le #BS do
	      if BS[i] notin I then break; end if;
	      i := i+1;
	    end while;
	    assert i le #BS; //nothing listed in the ex_cmpts should
			     // lie entirely in the singular locus!
	    Append(~elts,BS[i]);
	  end for; 
	  ex_p cat:= [Scheme(Ambient(Xp),Saturation(Ideal(inv_img(mpp,pj_cmps2[i])),
			(elts[i])@@mpp)) : i in [1..#pj_cmps2]];
	  // some pull-backs of old exceptional cmpts might not intersect all patches
          // leading to 'empty' cmpts in ex_p. Remove these empty ones here.
	  good_ex_inds := [i : i in [1..#ex_p] | not IsEmpty(ex_p[i])];
	  if #good_ex_inds lt #ex_p then
	    ex_p := [ex_p[i] : i in good_ex_inds];
	    exl_p := [exl_p[i] : i in good_ex_inds];
	  end if;
	  // now deal with new exceptional cmpts over S and the new sing locus
	  ex_loc_p := inv_img(mpp,S);
	  if IsEmpty(ex_loc_p) then
	    new_cmps_p := [];
	  else
	    new_cmps_p := PrimeComponents(ex_loc_p);
	  end if;
	  Sp := SingularSubscheme(Xp) meet ex_loc_p;
	  if IsEmpty(Sp) then
	    Sp_cmps := [];
	  else
	    Sp_cmps := PrimeComponents(Sp);
	  end if;
	  // add in any non-blow-up singular curve cmpts from the blow-up patch
	  // that meet the new exceptional locus
	  Sp_cmps cat:= [Complement(c@@mpp,ex_loc_p) : c in sing_old];
//printf "Sp_cmps:%o\n",Sp_cmps;
	  if (#ex_p eq 0) and (#Sp_cmps eq 0) and (#new_cmps_p eq 0) then
	    continue; //no useful data in this patch!
	  end if;
	  new_cmps_p := [c : c in new_cmps_p | c notin Sp_cmps];
	  vprintf Resolve : "%o new blow-up components patches not in singular locus\n",
				#new_cmps_p;
	  if #new_cmps_p ne 0 then
	    ex_p cat:= new_cmps_p;
	    //exl_p cat:= [idx : i in [1..#new_cmps_p]];
	    for c in new_cmps_p do 
		Append(~new_divs,<c,idx>);
		Append(~exl_p,#new_divs);
	    end for;
	    if bood0 then Append(~new_ind0,idx); end if;
	  end if;
	  Append(~tree, rec<NodeData|i := idx, i1 := j, X := Xp, ex_cmpts := ex_p,
			ex_links := exl_p, prj_map := mppt, prj_map1 := mpp>);
	  if #Sp_cmps gt 0 then
	    Sp1,Sp2 := get_blow_up_components(Sp_cmps);
//printf "new blow_up_cmps: %o\n%o\n",idx,Sp1;
	    //for s in Sp1 do Append(~sings,<idx,s>); end for;
	  else
	    Sp1 := []; Sp2 := [];
	  end if;
	  (tree[#tree])`sing_cmpts := Sp1;
	  (tree[#tree])`sing_cmpts1 := Sp2;
	  Append(~leaves,idx);
	  idx := idx+1;
	end for;
	//find relations between the new divisors over the different new patches
        // and update cmp0 or cmp1 structures appropriately
	if #new_divs gt nnd then
	  vprintf Resolve : "Getting relations between new component patches...\n"; 
	  patch_div_rels := relate_new_divs(new_divs,(#new_divs)-nnd,tree);
	  vprintf Resolve : "%o blow-up components found.\n",#patch_div_rels;
	  if bood0 then
	    cmp0_sets cat:= patch_div_rels;
	    preim_dat := 0;
	  else
	    cmp1_sets cat:= patch_div_rels;
	    // If we are blowing up a 1D locus, want to record the exact singular 
	    // component that lies under the new divisor classes, given by the
	    // index into the blow-up patches sing_cmpts list. Currently, we are
	    // only blowing up irreducible components, so this can be read off.
	    // If that changes, will need to compute the projection image of an element
	    // of each relation class to see which of the sing_cmpts it lies over.
	    ind := Index(pj`sing_cmpts,S);
	    preim_dat := [j,ind]; 
	  end if;
	  for l in [1..(#new_divs)-nnd] do Append(~div_preims,preim_dat); end for;
	end if;
      end for;
      // get new singularities to be blown up from leaf nodes. For 0-dimensional
      // components, make sure we only blow them up in one patch. For 1-dimensional
      // components that will span several patches in total, make sure we know which
      // ones correspond and simplify if possible.
      vprintf Resolve : "Identifying singular locus components over different patches...\n";
      sings0,sings1 := new_sings(tree,leaves);
      // record the correspondences of 1-D components in order to identify new divisors
      // lying above them at a later stage.
      onedrels cat:= [* {s : s in ss} : ss in sings1 | #ss gt 1 *];
      // then get new list of sings to be blown up
        //sings := sings0;
        //for ss in sings1 do sings cat:= ss; end for;
      sings := [* <s[1],((tree[s[1]])`sing_cmpts)[s[2]]> : s in sings0 *];
      for ss in sings1 do 
	sings cat:= [* <s[1],((tree[s[1]])`sing_cmpts)[s[2]]> : s in ss *];
      end for;
    end while;

    // Now must work out the final equivalence relation between the exceptional
    // (irreducible over the base field) divisors in new_divs - ie, which ones
    // are open patches of the same complete exceptional divisor. The
    // full set of complete (projective) exceptional divisors correspond
    // to the equivalence classes of new_divs.
    //
    // The equivalence classes of divisors which occur as blow-up cmpts of a
    // point singularity are already fully computed in cmp0_sets.
    //
    // cmp1_sets contains partial equivalence classes for divisors which
    // occur as blow-up cmpts of (irreducible) curve singularities. It remains
    // to use div_preims and onedrels to check which of these curve singularities
    // are equivalent and identify the corresponding partial equivalence classes.
    vprintf Resolve : "Identifying new components arising from blowing up\n";
    vprintf Resolve : "   1-D singular components over different patches...\n";	
    cmp1_tmp := full_relns(cmp1_sets, onedrels,
			[div_preims[c[1]] : c in cmp1_sets],false);
    cmp1_sets := [];
    for cls in cmp1_tmp do
	dps := Setseq(Seqset([div_preims[c[1]] : c in cls]));
	cmp1_sets cat:= relate_d1_div_classes( 
	  [[c : c in cls | div_preims[c[1]] eq dp] : dp in dps],dps,new_divs,tree);
    end for; 

    // Now use the full equivalence between patch divisors in new_divs to
    // compute the full equivalence between (irreducible) exceptional divisors
    // in the leaf nodes of the blow-up tree.
    leaf_divs := []; ld_to_nd := [];
    for i in leaves do
	ld_to_nd cat:= (tree[i])`ex_links;
	leaf_divs cat:= [[i,j] : j in [1..#((tree[i])`ex_links)]];
    end for;
    lds_per_nd := [[] : i in [1..#new_divs]];
    for i in [1..#leaf_divs] do
	Append(~(lds_per_nd[ld_to_nd[i]]),i);
    end for;
      // 'non-concatenated' classes of leaf exceptional divisors
    //ld_cls_nc := full_relns(lds_per_nd, [Seqset(c) : c in cmp0_sets cat cmp1_sets],
			//[1..#new_divs],false);
    // classes of leaf exceptional divisors
    ld_cls := full_relns(lds_per_nd, [Seqset(c) : c in cmp0_sets cat cmp1_sets],
			[1..#new_divs],true);
    vprintf Resolve : "Found %o complete irreducible blow-up divisors in total.\n",
			#ld_cls;
    // ignore leaf patches with no useful divisor data (can there be any at this stage??)
    // and renumber
    leaves1 := leaves;
    leaves := Sort(Setseq(Seqset([l[1] : l in leaf_divs])));
    leaf_divs := [[Index(leaves,l[1]),l[2]] : l in leaf_divs];

    //return tree,new_divs,cmp0_sets,cmp1_sets,lds_per_nd,ld_cls_nc;
    dat := [*<t`ex_cmpts,t`X,t`prj_map,[not IsEmpty(c meet S) : c in t`ex_cmpts]> 
	where S is SingularSubscheme(t`X) where t is tree[l] : l in leaves *];
    //return dat,ld_cls_nc,leaf_divs,tree,leaves1;
    dsd := New(DesingData);
    dsd`main_dat := dat; dsd`classes := ld_cls; dsd`div_leaf_dat := leaf_divs; dsd`Y := Y;
    dsd`mult_use_glob := false; dsd`pi := 0;
    return dsd;		

end intrinsic;

function int_mat_nd(dat,cls,ld)
// Computes the non-diagonal entries of the intersection product matrix for the irreducible
// exceptional divisors and returns this matrix (with 0 for the diagonal terms)

    n := #cls;
    cls1 := [[ld[i] : i in c] : c in cls];
    seq := [(i eq j) select 0 else intersection_num(cls1[i],cls1[j],dat) :
		j in [1..i], i in [1..n]];
    return SymmetricMatrix(seq);

end function;

intrinsic IntersectionMatrix(dsd::DesingData : get_self_ints := true) -> Mtrx
{ Returns the intersection matrix of the irreducible exceptional divisors
  in the resolution of surface singularity Y represented by dsd. If parameter
  get_self_ints is false (default:true), only compute the non-diagonal entries
  leaving the diagonal ones (self-intersections) as 0.}

    dat := dsd`main_dat; cls := dsd`classes; ld := dsd`div_leaf_dat;
    if assigned dsd`imat then
      mat := dsd`imat;
    else
      vprintf MultsAndInts: "Computing the non-diagonal part...\n";
      time mat := int_mat_nd(dat,cls,ld);
    end if;
    if (mat[1,1] ne 0) or not get_self_ints then
      if not assigned dsd`imat then dsd`imat := mat; end if;
    else
      B := Basis(Ideal(dsd`Y));
      _,i := Min([TotalDegree(f) : f in B]);
      vprintf MultsAndInts: "Computing the diagonal part...\n";
      time sis := self_ints(B[i],mat,dat,cls,ld);
      dsd`imat := mat+DiagonalMatrix(sis);
    end if;
    return dsd`imat;

end intrinsic;

intrinsic DifferentialMultiplicities(dsd::DesingData) -> SeqEnum
{ For a hypersurface surface, returns the sequence of multiplicities of
  the 'natural' meromorphic differential 2-form at the irreducible
  exceptional divisors in the resolution of surface singularity Y represented
  by dsd.}

    R := CoordinateRing(Ambient(dsd`Y));
    require Rank(R) eq 3:
      "Intrinsic currently only available for singularities of a hypersurface";
    if not assigned dsd`w_mults then
      f := DefiningPolynomial(Codomain((dsd`main_dat[1])[3]));
      i := 4;
      repeat
	i -:= 1;
	dfi := Derivative(f,i);
      until (not IsZero(dfi)) or (i eq 1);
      require not IsZero(dfi): "Surface is not geometrically reduced";
      i,j := Explode([k : k in [1..3] | k ne i]);
      dsd`w_mults := diff_mults_hyp(1/dfi,i,j,dsd);
    end if;
    return dsd`w_mults;

end intrinsic;

intrinsic DesingulariseSurfaceByBlowUp(X::Srfc : AdjComp := false) -> List
{ Computes singularity resolution data for surface X via blowing up. X must have
  only point singularities but may lie in any ambient for which the singular points
  are in definable affine patches. Return value (which is also stored) is a list of
  DesingData objects for each set of conjugate singular points. If parameter
  AdjComp is set to true (default:false) simple singularities on X are left unresolved
  since they are not needed for multi-adjoint and multi-canonical computations.}

    rl := [**];
    rl2 := [**];
    bAdjOnly := false;
    if (assigned X`Nonsingular) and X`Nonsingular then
      return rl;
    end if;
    if assigned X`res_list then
      rl := X`res_list;
      for r in rl do
	if (r[1] eq 2) then
	  if AdjComp or r[3] then return r[2]; end if;
	  rl2 := r[2]; bAdjOnly := true; break;
	end if;
      end for;
    end if;
    S := SingularSubscheme(X);
    require Dimension(S) le 0: 
	"Blow-up desingularisation is currently only available for surfaces with",
	"isolated point singularities";
    if IsEmpty(S) then return [**]; end if; //X non-singular
    sngs := PrimeComponents(S);
    R := CoordinateRing(Ambient(X));
    for spt in sngs do
      pi := 0;
      if IsAffine(X) then
	Xa := X; sp := spt;
      else
        for i in [1..NumberOfAffinePatches(X)] do
	  if not HasAffinePatch(X,i) then continue; end if;
	  Xa := AffinePatch(X,i);
	  pcm := ProjectiveClosureMap(Ambient(Xa));
	  den := LCM([Denominator(e) : e in InverseDefiningPolynomials(pcm)]);
	  if not (den in Ideal(spt)) then
	    pi := i; break;
	  end if;
	end for;
	require pi gt 0: "All singular points must lie in creatable affine patches";
	seq := [Evaluate(e,DefiningPolynomials(pcm)): e in MinimalBasis(Ideal(spt))];
	seq := Reverse(Sort(Setseq(Seqset([e : e in seq | not IsZero(e)]))));
	sp := Scheme(Ambient(Xa),seq);
      end if;
      if AdjComp or bAdjOnly then
	p := extn_pt(sp,Xa);
	try //simple singularity test might fail in some char 2&3 cases
	  bss := IsSimpleSurfaceSingularity(p);
	catch e
	  bss := false;
	end try;
	if (bss and AdjComp) or ((not bss) and bAdjOnly) then
	  continue;
	end if; 
      end if;
      vprintf Resolve : "Beginning resolution of singular point by blow-up.\n\n";
      dsd := ResolveSingByBlowUp(Xa,sp); dsd`pi := pi;
      vprintf Resolve : "\n";
      // Case where sp is known to be a conjugate set of simple singular
      // points. Can fill in useful data in the hypersurface case.
      if bAdjOnly and IsOrdinaryProjective(X) and (Length(X) eq 4) then
	dsd`w_mults := [0 : i in [1..#dsd`classes]];
      end if;
      Append(~rl2,dsd);
    end for;
    Append(~rl,<2,rl2,not AdjComp>);
    X`res_list := rl;
    return rl2;

end intrinsic;

intrinsic ResolveSingularSurface(S::Srfc :  AdjComp := false, UseFormalDesing := false) -> List, RngIntElt
{ Compute the resolution of singularities of a surface either by blowing-up
  or computing a formal desingularisation. Blowing-up is the preferred method but currently only 
  works for point singularities. Formal desingularisation only works for ordinary projective
  hypersurfaces (in P^3) in characteristic 0 but can handle curve singularities. The
  parameter can be set to true to force the formal method to be used. The return
  values (which are also stored) are a list of data objects of the appropriate type
  and an integer (1 for formal, 2 for blow-up desingularisation)}

    if (assigned S`Nonsingular) and S`Nonsingular then
      return [**],2;
    end if;
    booP3 := IsOrdinaryProjective(S) and (Length(S) eq 4) and
		(Characteristic(BaseRing(S)) eq 0);
    if not booP3 then
      require not UseFormalDesing: 
	"Can only compute formal desingularisation for surfaces in P^3 of char. 0";
      res_lst := DesingulariseSurfaceByBlowUp(S : AdjComp := AdjComp);
      return res_lst,2;
    end if;
    if assigned S`res_list then
      rl := S`res_list; boo2adj := false;
      rlac := [1..#rl];
      if not AdjComp then
	boo2adj := (#rl gt 0) and &or[r[1] eq 2 : r in rl];
	rlac := [i : i in [1..#rl] | rl[i][3] eq true];
      end if;
      if #rlac gt 0 then
	j := Index([rl[i][1] : i in rlac],2);
	if j ne 0 then
	  return rl[j][2],2;
	else
	  return rl[1][2],1;
	end if;
      elif boo2adj then
	res_lst := DesingulariseSurfaceByBlowUp(S : AdjComp := AdjComp);
	return res_lst,2;
      end if;
    end if;
    if (not UseFormalDesing) and (Dimension(SingularSubscheme(S)) le 0) then
      res_lst := DesingulariseSurfaceByBlowUp(S : AdjComp := AdjComp);
      typ := 2;
    else
      res_lst := FormallyResolveProjectiveHypersurface(S : AdjComp := AdjComp);
      typ := 1;
    end if;
    return res_lst,typ;
    
end intrinsic;

//// Adjoints for surfaces in P^3 using blow-up resolutions ////

function MultiAdjointLS(m,n,S,dsds)
// S a surface in P^3 and dsds a full or canonical set of resolution data
// objects. Computes and returns a basis for K(S)^m(n) as a subspace of
// polynomials of degree  n+m*(Degree(S) - 4)
// NB: only indep. of desingularisation if m >= 0!

    d := n+m*(Degree(S)-4);
    if d lt 0 then return []; end if;
    R := CoordinateRing(Ambient(S));
    mons := Setseq(MonomialsOfDegree(R,d));
    if d ge Degree(S) then
      // mons -> basis for degree d monomials mod F where
      // F is the defining polynomial of S.
      expl := Exponents(LeadingMonomial(Equation(S)));
      mons := [m : m in mons | &or[e[i] lt expl[i] : i in [1..4]]
                                where e is Exponents(m)];
    end if;
    V := VectorSpace(BaseRing(S),#mons); W := V; 
    for dsd in dsds do
      dms := DifferentialMultiplicities(dsd);
      ams := [Max(-m*s,0) : s in dms];
      if IsZero(Vector(ams)) then continue; end if;
      R1 := CoordinateRing(Ambient(dsd`Y));
      js := [i : i in [1..4]| i ne 5-dsd`pi];
      restr_mat := full_lin_sys_res_general(
        [Monomial(R1,(Exponents(b))[js]) : b in mons],ams,dsd`main_dat,
          dsd`classes,dsd`div_leaf_dat,true);
      W meet:= sub<V|RowSequence(restr_mat)>;
      if Dimension(W) eq 0 then return [R|]; end if;
    end for;
    if Dimension(W) eq #mons then return mons; end if;
    return [Polynomial(Eltseq(w),mons) : w in Basis(W)];

end function;

intrinsic FirstChernClassOfDesingularization(S::Srfc) -> RngIntElt
{ Returns the first Chern class, K^2, of the Magma desingularisation of S.
  Note that this depends on the precise desingularisation. Currently, S
  must be an ordinary projective hypersurface with only point singularities.
  If a desingularisation data object of blow-up type has not already been
  stored for S, that is first computed. }

    boo := IsOrdinaryProjective(S) and (Length(S) eq 4);
    if boo then
	boo := Dimension(SingularSubscheme(S)) le 0;
    end if;
    require boo:
      "Currently, S must be a hypersurface in P^3 with only point singularities";
    if (not assigned S`res_list) or &and[s[1] ne 2 : s in S`res_list] then
      dsds := DesingulariseSurfaceByBlowUp(S : AdjComp := true);
    else
      dsds := [s[2] : s in S`res_list | s[1] eq 2][1];
    end if;
    imats := [* IntersectionMatrix(dsd) : dsd in dsds *];
    dms := [DifferentialMultiplicities(dsd) : dsd in dsds];
    // The canonical class K on the desingularisation is equivalent
    // to (d-4)*H + sum_{i,j} d_{i,j}*D_{i,j} where d is the degree of H,
    // H is the hypersurface section, and for each i, D_{i,j} runs over
    // the exceptional divisors for dsds[i], which have intersection
    // matrix imats[i], and d_{i,j} runs over the multiplicities (<=0)
    // of D_{i,j} in the 'natural differential': dms[i]=[d_{i,j} : j].
    i2 := &+[(m*imats[i]*Transpose(m))[1,1] where m is Matrix(Vector(dms[i])) :
		i in [1..#dsds]];
    d := Degree(S);
    return i2+d*(d-4)^2;

end intrinsic;

///////////////////////////////////////////////////////////////////////
/// Intrinsics to export the mults and ints functionality and also  ///
/// for the restriction of a linear system w.r.t. some mults at     ///
///              exceptional blow-up divisors.                      ///
///////////////////////////////////////////////////////////////////////

intrinsic Multiplicities(S::Srfc, dsd::DesingData, D::Sch) -> SeqEnum
{ dsd should be a desingularisation data object of blow-up type for a singular point
  p of surface S and D a subscheme of S giving an effective divisor. Returns
  the multiplicities with respect to the irreducible exceptional divisors over p of
  the pullback of D to the desingularisation of S. }

    require (D subset S) and Dimension(D) eq 1: "D is not a divisor on S";
    if IsAffine(S) then
	D1 := D;
    else
	D1 := AffinePatch(D,dsd`pi);
    end if;
    if IsEmpty(D1 meet dsd`Y) then
      m := [0 : i in [1..#(dsd`classes)]];
      return m;
    else
      //check whether we can reduce to single polynomial
      defs := [f : f in DefiningPolynomials(D) | f notin Ideal(S)];
      if #defs eq 1 then
	f := IsAffine(S) select defs[1] else DefiningEquation(AffinePatch(
		Scheme(Ambient(S),defs[1]),dsd`pi));
	return mults(f,dsd,true);
      else
	return mults(Ideal(D1),dsd,false);
      end if;
    end if;

end intrinsic;

intrinsic Multiplicities(S::Srfc, D::Sch) -> SeqEnum
{ For effective divisor D on singular surface S with only point singularities, returns
  a sequence of sequences. These are sequences of multiplicities with respect to the
  irreducible exceptional divisors over each singular point of the pullback of D to the
  desingularisation. The order of singular points is that in the singularity resolution
  object of S. If S doesn't have a resolution object of blow-up type already stored, this
  is computed first. }

    require (D subset S) and Dimension(D) eq 1: "D is not a divisor on S";
    if (not assigned S`res_list) or &and[s[1] ne 2 : s in S`res_list] then
      sng := SingularSubscheme(S);
      require Dimension(sng) lt 1:
	"Can only compute for surfaces with only point singularities";
      dsds := DesingulariseSurfaceByBlowUp(S);
    else
      dsds := ([s : s in S`res_list | s[1] eq 2][1])[2];
    end if;
    //check whether we can reduce to single polynomial
    defs := [f : f in DefiningPolynomials(D) | f notin Ideal(S)];
    if #defs eq 1 then D := Scheme(Ambient(S),defs[1]); end if;
    m_seq := [];
    for dsd in dsds do
      if IsAffine(S) then
	D1 := D;
      else
	D1 := AffinePatch(D,dsd`pi);
      end if;
      if IsEmpty(D1 meet dsd`Y) then
	ms := [0 : i in [1..#(dsd`classes)]];
      else
	if #DefiningEquations(D1) eq 1 then
	  ms := mults(DefiningEquations(D1)[1],dsd,true);
	else
	  ms := mults(Ideal(D1),dsd,false);
	end if;
      end if;
      Append(~m_seq,ms);
    end for;
    return m_seq;

end intrinsic;

intrinsic Multiplicities(S::Srfc, D::DivSchElt) -> SeqEnum
{ For divisor D on singular surface S with only point singularities, returns
  a sequence of sequences. These are sequences of multiplicities with respect to the
  irreducible exceptional divisors over each singular point of the pullback of D to the
  desingularisation. The order of singular points is that in the singularity resolution
  object of S. If S doesn't have a resolution object of blow-up type already stored, this
  is computed first. }

    require IsIdentical(S,Variety(D)):
      "S is not the parent variety of D";
    if IsIntegral(D) then //easy integral case
      return Multiplicities(S,Scheme(Ambient(S),Ideal(D)));
    end if;
    num,den := SignDecomposition(D);
    ms_num := Multiplicities(S,Scheme(Ambient(S),Ideal(num)));
    ms_den := Multiplicities(S,Scheme(Ambient(S),Ideal(den)));
    ms := [Eltseq(Vector(ms_num[i])-Vector(ms_den[i])) : i in [1..#ms_num]];
    return ms;

end intrinsic;

intrinsic MultiplicitiesAndIntersections(S::Srfc, dsd::DesingData, D::Sch) -> SeqEnum, SeqEnum
{ dsd should be a desingularisation data object of blow-up type for a singular point
  p of surface S and D a subscheme of S giving an effective divisor. Returns
  two sequences. The first contains the multiplicities with respect to the irreducible
  exceptional divisors over p of the pullback of D to the desingularisation of S
  and the second contains the intersection numbers of the residual of the pullback
  (ie after subtracting off exceptional divisors with multiplicty) with each exceptional
  divisor.}

    require (D subset S) and Dimension(D) eq 1: "D is not a divisor on S";
    if IsAffine(S) then
	D1 := D;
    else
	D1 := AffinePatch(D,dsd`pi);
    end if;
    if IsEmpty(D1 meet dsd`Y) then
      m := [0 : i in [1..#(dsd`classes)]];
      return m,m;
    else
      //check whether we can reduce to single polynomial
      defs := [f : f in DefiningPolynomials(D) | f notin Ideal(S)];
      if #defs eq 1 then
	f := IsAffine(S) select defs[1] else DefiningEquation(AffinePatch(
		Scheme(Ambient(S),defs[1]),dsd`pi));
	return mults_and_ints(f,dsd`main_dat,
			dsd`classes,dsd`div_leaf_dat,true);
      else
	return mults_and_ints(Ideal(D1),dsd`main_dat,dsd`classes,
			dsd`div_leaf_dat,false);
      end if;
    end if;

end intrinsic;

intrinsic MultiplicitiesAndIntersections(S::Srfc, D::Sch) -> SeqEnum, SeqEnum
{ For effective divisor D on singular surface S with only point singularities, returns
  two sequences of sequences. The first sequence contains the sequence of multiplicities
  with respect to the irreducible exceptional divisors over each singular
  point of the pullback of D to the desingularisation and the second contains the
  intersection numbers of the residual of the pullback (ie after subtracting off 
  exceptional divisors with multiplicty) with each exceptional divisor. The
  order of singular points is that in the singularity resolution object of
  S. If S doesn't have a resolution object of blow-up type already
  stored, this is computed first. }

    require (D subset S) and Dimension(D) eq 1: "D is not a divisor on S";
    if (not assigned S`res_list) or &and[s[1] ne 2 : s in S`res_list] then
      sng := SingularSubscheme(S);
      require Dimension(sng) lt 1:
	"Can only compute for surfaces with only point singularities";
      dsds := DesingulariseSurfaceByBlowUp(S);
    else
      dsds := ([s : s in S`res_list | s[1] eq 2][1])[2];
    end if;
    //check whether we can reduce to single polynomial
    defs := [f : f in DefiningPolynomials(D) | f notin Ideal(S)];
    if #defs eq 1 then D := Scheme(Ambient(S),defs[1]); end if;
    m_seq := []; i_seq := [];
    for dsd in dsds do
      if IsAffine(S) then
	D1 := D;
      else
	D1 := AffinePatch(D,dsd`pi);
      end if;
      if IsEmpty(D1 meet dsd`Y) then
	m := [0 : i in [1..#(dsd`classes)]]; i := m;
      else
	if #DefiningEquations(D1) eq 1 then
	  m,i := mults_and_ints(DefiningEquations(D1)[1],dsd`main_dat,
			dsd`classes,dsd`div_leaf_dat,true);
	else
	  m,i := mults_and_ints(Ideal(D1),dsd`main_dat,dsd`classes,
			dsd`div_leaf_dat,false);
	end if;
      end if;
      Append(~m_seq,m); Append(~i_seq,i);
    end for;
    return m_seq,i_seq;

end intrinsic;

intrinsic MultiplicitiesAndIntersections(S::Srfc, D::DivSchElt) -> SeqEnum, SeqEnum
{ For divisor D on singular surface S with only point singularities, returns two
  sequences of sequences. The first sequence contains the sequence of multiplicities
  with respect to the irreducible exceptional divisors over each singular
  point of the pullback of D to the desingularisation   and the second contains the
  intersection numbers of the residual of the pullback (ie after subtracting off 
  exceptional divisors with multiplicty) with each exceptional divisor. The
  order of singular points is that in the singularity resolution object of
  S. If S doesn't have a resolution object of blow-up type already
  stored, this is computed first. }

    require IsIdentical(S,Variety(D)):
      "S is not the parent variety of D";
    if IsIntegral(D) then //easy integral case
      return MultiplicitiesAndIntersections(S,Scheme(Ambient(S),Ideal(D)));
    end if;
    num,den := SignDecomposition(D);
    m_num, i_num := MultiplicitiesAndIntersections(S,Scheme(Ambient(S),Ideal(num)));
    m_den, i_den := MultiplicitiesAndIntersections(S,Scheme(Ambient(S),Ideal(den)));
    m := [Eltseq(Vector(m_num[i])-Vector(m_den[i])) : i in [1..#m_num]];
    i := [Eltseq(Vector(i_num[i])-Vector(i_den[i])) : i in [1..#i_num]];
    return m,i;
   
end intrinsic;

intrinsic CanonicalIntersection(S::Srfc, D::Sch) -> RngIntElt
{ For effective divisor D on singular hypersurface S in P^3 with only point singularities,
  returns the intersection of the strict transform of D on S1 with the canonical divisor of
  S1, where S1 is Magma's blow-up resolution of S. The strict transform is the pullback
  of D with any blow-up divisor components lying over singular points removed.
  If S doesn't have a resolution object of blow-up type already stored, this
  is computed first. }

    boo := IsOrdinaryProjective(S) and (Length(S) eq 4);
    if boo then
	boo := Dimension(SingularSubscheme(S)) le 0;
    end if;
    require boo:
      "Currently, S must be a hypersurface in P^3 with only point singularities";
    if (not assigned S`res_list) or &and[s[1] ne 2 : s in S`res_list] then
      dsds := DesingulariseSurfaceByBlowUp(S);
    else
      dsds := [s[2] : s in S`res_list | s[1] eq 2][1];
    end if;
    dms := [DifferentialMultiplicities(dsd) : dsd in dsds];
    js := [i : i in [1..#dsds]| not IsZero(Vector(dms[i]))];
    
    // On the desingularisation S1, K (can div) = (d-4)H+some components
    // of the blow-up divisors whose multiplicities are in dms (H=hyperplane div)
    // The strict transform of D, Dr = D-some components of b.u. divs and the
    // intersection of Dr with the b.u. divs comes from mults_and_ints
    i1 := 0;
    for i in js do
      _,dris :=  MultiplicitiesAndIntersections(S,dsds[i],D);   
      i1 +:= (Vector(dris)*Transpose(Matrix(Vector(dms[i]))))[1];
    end for;
    return ((Degree(S)-4)*Degree(D))+i1;

end intrinsic;

intrinsic CanonicalIntersection(S::Srfc, D::DivSchElt) -> RngIntElt
{ For divisor D on singular hypersurface S in P^3 with only point singularities,
  returns the intersection of the strict transform of D on S1 with the canonical divisor of
  S1, where S1 is Magma's blow-up resolution of S. The strict transform is the pullback
  of D with any blow-up divisor components lying over singular points removed.
  If S doesn't have a resolution object of blow-up type already stored, this
  is computed first. }

    require IsIdentical(S,Variety(D)):
      "S is not the parent variety of D";
    if IsIntegral(D) then //easy integral case
      return CanonicalIntersection(S,Scheme(Ambient(S),Ideal(D)));
    end if;
    num,den := SignDecomposition(D);
    i1 := CanonicalIntersection(S,Scheme(Ambient(S),Ideal(num)));
    i2 := CanonicalIntersection(S,Scheme(Ambient(S),Ideal(den)));
    return i1-i2;

end intrinsic;

intrinsic CanonicalIntersection(dsd::DesingData, i::RngIntElt) -> RngIntElt
{ For singular hypersurface S with only point singularities and dsd the
  data object for the desingularisation by blow-up of S over
  a singular point p, return the intersection number of the i-th blow-up
  divisor over p with the canonical divisor on the desingularisation.}

    require (i ge 1) and (i le #(dsd`classes)):
	"i must be a positive integer <=",#(dsd`classes);
    require Length(dsd`Y) eq 3:
      "Intrinsic currently only available for singularities of a hypersurface";
    dms := DifferentialMultiplicities(dsd);
    imat := IntersectionMatrix(dsd);
    return (imat[i]*Transpose(Matrix(Vector(dms))))[1];

end intrinsic;

function lin_indep_basis(B,S)
// B is a sequence of homogeneous polynomials (of the same multi-degree) on
// the ambient of surface S. Return a subseq of B that generates the same
// linear space of polynomials mod Ideal(S) [The polys in B are not
// assumed to be lin indep mod <0>]
    R := Generic(Universe(B));
    B1 := [NormalForm(b,Ideal(S)) : b in B];
    if &and[IsZero(b) : b in B1] then return [R|]; end if;
    mons := Reverse(Sort(Setseq(&join([Seqset(Monomials(b)) :
			b in B1 | not IsZero(b)]))));
    mat := Matrix([[MonomialCoefficient(b,m) : b in B1] : m in mons]);
    E := EchelonForm(mat);
    inds := [Min(Support(E[i])) : i in [1..Nrows(E)] |
			not IsZero(E[i])];
    return [R|B[i] : i in inds];
end function;

intrinsic LinearSystemDivisorRestriction(S::Srfc, B::SeqEnum[RngMPolElt], ms::SeqEnum[SeqEnum] :
		CheckB := true) -> SeqEnum
{ S should be a singular surface with only point singularities and B a sequence of
  polynomials on the ambient of S, homogeneous of the same degree for all gradings,
  which can be thought of as a basis for the sections of a linear system on S. ms
  is a sequence of sequences of multiplicities for the irreducible exceptional divisors
  over the singular points of S that occur in singularity resolution by blow-up.
  Returns a basis for the linear subsystem of sections that vanish to at least the
  given multiplicity at each exceptional divisor. Parameter CheckB can be set to false
  to avoid the initial check that no non-zero section in the linear span of B vanishes
  on S and choice of an appropriate subset of B if so. The singularities of S must have
  been resolved by the blow-up method before this function is called.}

    require (assigned S`res_list) and &or[s[1] eq 2 : s in S`res_list]:
	"S must have had singularities resolved by ResolveSingularSurface";
    dsds := [s[2] : s in S`res_list | s[1] eq 2][1];
    require (Universe(ms) cmpeq Parent([0])) and (#ms eq #dsds) and
	 &and[#(ms[i]) eq #(dsds[i]`classes) : i in [1..#ms]] :
	"Number or size of sequences in ms does not match singularity data for S";
    R := Generic(Universe(B));
    require IsIdentical(CoordinateRing(Ambient(S)),R):
	"Polynomials in B must lie in the coordinate ring of the ambient of S";
    if CheckB and (#B gt 0) then
      B := lin_indep_basis(B,S);
    end if;
    if #B eq 0 then return B; end if;
    V := VectorSpace(BaseRing(S),#B); W := V;
    boo := &and[#Terms(b) eq 1 : b in B]; // monomial case? 
    for i in [1..#dsds] do
      dsd := dsds[i];
      md := [Max(m,0) : m in ms[i]];
      if IsZero(Vector(md)) then continue; end if;
      if dsd`pi ne 0 then
	seq := DefiningPolynomials(ProjectiveClosureMap(AffinePatch(Ambient(S),dsd`pi)));
	B1 := [Evaluate(b,seq) : b in B];
      else
        B1 := B;
      end if;
      restr_mat := full_lin_sys_res_general(B1,md,dsd`main_dat,
          dsd`classes,dsd`div_leaf_dat,boo);
      W meet:= sub<V|RowSequence(restr_mat)>;
      if Dimension(W) eq 0 then return [R|]; end if;
    end for;
    if Dimension(W) eq #B then return B; end if;
    if boo then
      return [Polynomial(Eltseq(w),B) : w in Basis(W)];
    else
      return Eltseq(Vector(B)*ChangeRing(Transpose(Matrix(Basis(W))),R));
    end if;

end intrinsic;

///// Some intrinsics to return more information about the exceptional /////
///              divisors over a singular point                          ///

intrinsic NumberOfBlowUpDivisors(dsd::DesingData) -> RngIntElt
{ Number of irreducible divisors lying over a singular point in the desingularisation
  of a surface by blow-up. dsd is the desingularisation data object corresponding
  to that point. }

    return #(dsd`classes);

end intrinsic;

intrinsic SingularPoint(dsd::DesingData) -> Sch
{ The singular point on surface S of which dsd is the blow-up desingularisation object.
  Here, point mean scheme-theoretic point and it is a reduced, irreducible, 0-dimensional
  subscheme of the singular locus of S representing a conjugate set of singular points of
  S over the algebraic closure of the base field. It is returned as a subscheme of S.}

    p := dsd`Y; // point on an affine patch
    if dsd`pi ne 0 then // projective case
      pcm := ProjectiveClosureMap(Ambient(p));
      p := Image(Restriction(pcm,p,Codomain(pcm))); 
    end if;
    return p;

end intrinsic;

intrinsic BlowUpDivisor(S::Srfc, dsd::DesingData, i::RngIntElt) -> Crv, Sch, MapSch
{ For desingularisation data object dsd representing the desingularisation by blow-up
  of a surface S over a singular point p, return an affine curve C giving one patch of
  the i-th irreducible divisor lying over p and the surface blow-up affine patch Sa in
  which it lies along with the blow-down map of Sa to S.}

    require (i ge 1) and (i le #(dsd`classes)):
	"i must be a positive integer <=",#(dsd`classes);
    di,j := Explode((dsd`div_leaf_dat)[((dsd`classes)[i])[1]]);
    dat := dsd`main_dat;
    C := Curve(((dat[di])[1])[j]);
    mp_eqns := DefiningPolynomials(dat[di][3]);
    if dsd`pi ne 0 then
      mppc := ProjectiveClosureMap(AffinePatch(Ambient(S),dsd`pi));
      mp_eqns := [Evaluate(e,mp_eqns) : e in DefiningPolynomials(mppc)];
    end if;
    return C,dat[di][2],map<dat[di][2]->S|mp_eqns : Check := false>;

end intrinsic;

intrinsic BlowUpDivisorAllPatches(dsd::DesingData, i::RngIntElt) -> List, RngIntElt
{ dsd is the desingularisation data object for the resolution of surface S at singular
  point p. Returns a list of affine blow-up patches that completely cover the i-th
  irreducible blow-up divisor over p. The list consists of 4-tuples containing i)
  an affine curve C giving the divisor patch, ii) the affine surface blow-up patch
  Sa in which C lies, iii) the birational blow-down map of Sa to an affine patch of S in which
  p lies and iv) the index of Sa in the list of all blow-up patches of dsd. The
  patch index of the affine patch of S which is the codomain of all of the maps in iii)
  is the second return value (0 if S is affine). }

    require (i ge 1) and (i le #(dsd`classes)):
	"i must be a positive integer <=",#(dsd`classes);
    cl := (dsd`classes)[i];
    dat := dsd`main_dat;
    ret_lst := [**];
    for k in cl do
      di,j := Explode((dsd`div_leaf_dat)[k]);
      Append(~ret_lst,<Curve(((dat[di])[1])[j]),dat[di][2],dat[di][3],di>);
    end for;
    return ret_lst,dsd`pi;

end intrinsic;
