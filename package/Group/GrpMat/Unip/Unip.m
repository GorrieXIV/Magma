freeze;

/* 
 * Computing a cleaned and rearranged set of PC generators for
 *   a unipotent matrix group. Algorithm by JF Carlson.
 * 
 * Dan Roozemond, Oct. 2010.
 */
intrinsic PCGenerators(G::GrpMatUnip[FldFin] : GensAreKnownPCSet := false, Check := true) -> SeqEnum, SeqEnum, GrpMatElt
{Compute a rearranged and cleaned up PC set of generators for a unipotent matrix group.
Such a set is computed automatically when needed, so it should not be necessary to call
this function explicitly unless there is a need to change some of the parameters.}

	k := GensAreKnownPCSet select 1 else 0;
	gens, trace := InternalUnipPCGensCleaned(G, k, Check);
	conj := G`Conjugator;

	return gens, trace, conj;
end intrinsic;

function WordMapPC(G) //WordMapPC(::GrpMat[FldFin]) -> Map
/* The word map sending elements of G to elements of the GrpSLP corresponding
   to its PC generators. */

	/* Ensure generators are computed */
	_ := InternalUnipPCGensCleaned(G, 2, true);
	
	/* The groups */
	Hpc := G`GrpSLPPC;
	
	/* The map to the pc gens */
	function mat_to_slp(x)
		b, c := InternalUnipPCWordProblem(G, x);
		if not b then error "Element not in group"; end if;
		return c;
	end function;
	wmp := map<GL(Degree(G), CoefficientRing(G)) -> Hpc | x:->mat_to_slp(x)>;
	
	/* Done. */
	return wmp;
end function;

intrinsic WordMap(G::GrpMatUnip[FldFin]) -> Map
{ The word map sending elements of G to elements of the GrpSLP corresponding
 to the original generators.}

	/* The WordMapPC, the groups, the traces for the gens. */
	wmp := WordMapPC(G);
	Hpc := G`GrpSLPPC;
	H := G`GrpSLPOrig;
	trace := G`PCGensTrace;

	/* Compose with the trace to map pc-gens to the original gens */
	phi := hom<Hpc -> H | trace>;
	return map<Domain(wmp) -> H | x:->phi(wmp(x))>;
end intrinsic;

intrinsic PCPresentation(G::GrpMatUnip[FldFin]) -> GrpPC, Map, Map
{ Construct a PC group H from G. 2nd return value is the map
  from G to H, 3rd return value is the map from H to G.}

	/* Construct the GrpPC */
	H := InternalUnipPCPresentation(G);
	gens := G`PCGens;
	assert #gens eq NumberOfPCGenerators(H);

	/* Construct the map from G to H */
	wmp := WordMapPC(G);
	phi := map<G -> H | x :-> Evaluate(wmp(x), H)>;

	/* Construct the map from H to G */
	c := G`Conjugator;
	if IsIdentity(c) then
		psi := hom<H -> G | gens>;
	else
		cinv := c^-1;
		psi := hom<H -> G | [ g^cinv : g in gens]>;
	end if;
	
	return H, phi, psi;
end intrinsic;

intrinsic UnipotentMatrixGroup(G::GrpMat[FldFin]) -> GrpMatUnip
{ Construct a known-unipotent matrix group from G. }

  return UnipotentMatrixGroup<Degree(G), CoefficientRing(G) | [ G.i : i in [1..Ngens(G)] ]>;
end intrinsic;




