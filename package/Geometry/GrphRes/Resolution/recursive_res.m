freeze;

///////////////////////////////////////////////////////////////////////
// recursive_res.m
//	Contents:
//		A routine which recursively calls itself after calculating
//		and analysing the initial main spine of the resolution;
//		it does not test for singularity of p.
//		Auxilliary functions for building graph portions and
//		finding unresolved germs on graph portions.
///////////////////////////////////////////////////////////////////////


forward make_res_graph;
forward find_new_germs;
intrinsic RecursiveGrphRes(C::Crv,p::Pt) -> GrphRes
{Internal function}
    require IsOrdinaryProjective(Ambient(C)):
	"Argument must be a curve in an ordinary projective space";
    t := Cputime();
    G := ResolutionSpine(C!p);
    U := find_new_germs(G);	// These are the germs along G which where the
				// recursion will happen: their resolution
				// graphs will get glued to G.
    // run through the unresolved germs in turn
    for i in [1..#U] do
	germ := U[i][1];
	gal := U[i][3];
	verts := U[i][4];
	require #verts eq 1: "too many vertices";   // unused design feature

	// retrieve the resolution data of germ
	pi,Ci := ProjectiveRepresentative(germ);
	Gi := RecursiveGrphRes(Ci,pi);

	// update the resolution graph
	for jj in [1..gal] do
	    G := make_res_graph(G,Gi,verts[1]);
	end for;
    end for;

    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Auxilliary functions
///////////////////////////////////////////////////////////////////////

make_res_graph := function(G,T,vert)
// glue the vertex number 1 of the resolution graph T to the resolution
// graph G at vertex of index 'vert' of G.
    ng := Size(G);
    // calculate the new sequence of uncomposed patch maps.
    ppmG := PrePatchMaps(G);
    ppmT := PrePatchMaps(T);
    extra_map := ppmG[vert];
    ppmT_new := [];	// the prepatch maps on ppmT including the extra_map
    for i in [1..#ppmT] do
	if IsDefined(ppmT,i) then
	    ppmT_new[i] := extra_map cat ppmT[i];
	end if;
    end for;
    ppm_new := ppmG;
    /* mch - 04/05 - change universe to remove problem of germ patch maps
       being defined over different fields [when the Universe for the
       sequence of maps comprising a single patch map to the base germ
       will be the Power Structure of MapSch]                             */
    if not IsNull(ppmT_new) and not IsNull(ppm_new) and                        
		not (Universe(ppmT_new) cmpeq Universe(ppm_new)) then
	ChangeUniverse(~ppm_new,Universe(ppmT_new));
    end if;
    for i in [1..#ppmT_new] do
	if IsDefined(ppmT_new,i) then
	    ppm_new[ng+i] := ppmT_new[i];
	end if;
    end for;
    G1 := G;
    vt1 := T ! 1;
    v := G1 ! vert;
    b := BaseBlowupContribution(T);
    ModifySelfintersection(~v,b);
    G1 := Connect(v,vt1);
    SetPrePatchMaps(~G1,ppm_new);
    // fix the base blowup contribution
    G1`base_blowup_contribution := BaseBlowupContribution(G);
    // fix the base germ
    g := BaseGerm(G);
    SetBaseGerm(~G1,g);
    return G1;
end function;

///////////////////////////////////////////////////////////////////////

find_new_germs := function(G)
// locate the partially resolved germs along G and put them in a sequence
// together with associated data.
    U := [];
    newgerms := NeighbouringGerms(G);
    gals := GaloisMultiplicities(G);
    for j in [1..Size(G)] do
	if not IsDefined(newgerms,j) then
	    continue;
	end if;
	jth_germs := newgerms[j];
	jth_gals := gals[j];
	jth_len := #jth_germs;
	for jj in [1..jth_len] do
	    Uelt := [* jth_germs[jj],"junk" *];
	    Append(~Uelt,jth_gals[jj]);
	    Append(~Uelt,[(j)]);
	    Append(~U,Uelt);
	end for;
    end for;
    return U;
end function;

///////////////////////////////////////////////////////////////////////

