freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspcLH, recompute_eigenvectors;

function ChangeBasisLie(L, NewBasis : Rep := "Dense") //-> AlgLie, AlgMatElt, UserProgram, UserProgram
/* Changes basis for structure constant Lie algebra L. 
Returns: (1) The new Lie algebra L', (2) the transformation matrix, (3) map L' -> L, (4) map L -> L'. */
	local dim,VNewBasis, tups, Lnw, transf, transfinv,
		dist_to_orig, orig_to_dist,
		i, j, k, v, t0, whichrep;
		
	Lnw := ChangeBasis(L, Matrix(NewBasis) : Rep := Rep);

	//Construct maps.
	transf := Matrix(NewBasis);
	transfinv := transf^-1;
	dist_to_orig := map<Lnw -> L | x :-> L!(Vector(x)*transf)>;
	orig_to_dist := map<L -> Lnw | x :-> Lnw!(Vector(x)*transfinv)>;

	return Lnw, transf, dist_to_orig, orig_to_dist;
end function;

procedure ChangeBasisLie_CBD( ~CBD, T : RefOldL := false, RefOldH := false )
/* Changes the entries of the ChevBasData structure */
	local Lnw, Hnw, phi;

	Lnw, _, _, phi := ChangeBasisLie(CBD`L, T);
	Hnw := sub<Lnw | [ Lnw!Vector(phi((CBD`L)!h)) : h in Basis(CBD`H)]>;

	if RefOldL cmpeq false then CBD`L := Lnw; else CBD`L := RefOldL; end if;
	if RefOldH cmpeq false then CBD`H := Hnw; else CBD`H := RefOldH; end if;
	
	if assigned CBD`EigenSpaces then
		CBD`EigenSpaces := [ CBD`L | Vector(phi(x)) : x in CBD`EigenSpaces ];
		CBD`SCSAVectors := [ CBD`L | Vector(phi(x)) : x in CBD`SCSAVectors ];
		recompute_eigenvectors(~CBD);
	end if;

	if assigned CBD`BasisPos then
		CBD`BasisPos :=  [ CBD`L | Vector(phi(x)) : x in CBD`BasisPos ];
		CBD`BasisNeg :=  [ CBD`L | Vector(phi(x)) : x in CBD`BasisNeg ];
		CBD`BasisCart := [ CBD`L | Vector(phi(x)) : x in CBD`BasisCart ];
	end if;
end procedure;


function ChangeBasisLie_SparseWrtH(L, H) //-> AlgLie, AlgLie, AlgMatElt, UserProgram, UserProgram
/* Returns L and H with respect to another basis, consisting of the 
  eigenspaces of L with respect to H.

  In these newer algebras multiplication may be quicker, as it should be more sparse. 

  Third return value is the basis transformation matrix, fourth and fifth
  are maps from new to old basis and back, respectively. 
*/
	
	local es, ev, t0,
		LNew, HNew, transf, dist_to_orig, orig_to_dist;

	t0 := Cputime();
	vprintf ChevBas, 3: "[ChangeBasisLie_SparseWrtH]: findeigenspc...\n";
	es, ev := findeigenspcLH(L,H);

	vprintf ChevBas, 3: "[ChangeBasisLie_SparseWrtH]: Precomputing new basis...\n";

	LNew, transf, dist_to_orig, orig_to_dist := ChangeBasisLie(L, Matrix(es) : Rep := "Sparse");
	HNew := sub<LNew | [ LNew!Vector(orig_to_dist(L!h)) : h in Basis(H)]>;

	vprintf ChevBas, 3: "[ChangeBasisLie_SparseWrtH]: Done (%o s).\n", Cputime()-t0;

	return LNew, HNew, transf, dist_to_orig, orig_to_dist;
end function;

