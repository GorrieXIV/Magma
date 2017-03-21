freeze;

///////////////////////////////////////////////////////////////////////
// spine_res.m
//
// This is the main calculation for the resolution routine.
// It calculates and sets the field_extension, resolution_spine, base_blowups
// and newton_fan attributes for the germ p.
// The routine is
//	1. calculate the newton polygon of a representative of p;
//	2. calculate the projective patch maps used for pullbacks;
//	3. calculate the necessary birational pullbacks of p;
//	4. build the partial resolution graph;
// The parameter PatchMaps should usually be set to 0: in that case
// only maps at significant patches will be calculated.
//
///////////////////////////////////////////////////////////////////////


forward get_linear_map;
forward get_newton;
forward get_spine_maps;
forward remove_axis_components;
forward excl_factors;
forward extend_field;

function Reversion(S,n)
    // The sequence S reversed and translated so that the 
    // last term is in the n-th position
    /* require #S le n:
       "Sequence is longer than the integer argument";  */
    Snew := [ Universe(S) | ];
    for i in [1..#S] do
	if IsDefined(S,i) then
	    Snew[n+1-i] := S[i];
	end if;
    end for;
    return Snew;
end function;

intrinsic ResolutionSpine(p::Pt: PatchMaps:=0) -> GrphRes
{The initial linear graph, the spine, and the associated data of the
resolution of the germ p and its associated data}

    require IsGerm(p): "Point is not a germ";
    tt := Cputime();
    field := Ring(Parent(p));
    require IsField(field):
        "Base ring must admit polynomial factorisation";


///////////////////////////////////////////////////////////////////////
//			Step 0
// fix notation; position the germ at the origin; count axis factors.
// vars:	C	-- affine curve with 'germ' at the origin
//		A	-- its ambient affine plane
///////////////////////////////////////////////////////////////////////

    pt,C0 := ProjectiveRepresentative(p);
    P2 := Ambient(C0);
    linear_map := get_linear_map(pt);	// moves the germ to [0,0,1] 
    C1 := C0@@linear_map;

    // make an affine patch at the origin
    C := AffinePatch(C1,1);
    A := Ambient(C);
    fC := Polynomial(C);
    // record the multiplicity of the axes (x=0) and (y=0) in C --- these are
    // lost in the resolution process when 'remove_axis_components' is called.
    _,xmult := RemoveFactor(fC,1);
    _,ymult := RemoveFactor(fC,2);

//////////////////////////////////////////////////////////////////////
//			Step 1
// calculate the newton polygon (n.p.) and resolve it.
// vars:	newton		-- the resolved dual fan of the n.p.
//		key_faces	-- those rays of 'newton' corr to faces of n.p.
//		base_blowup	-- number of times x-axis has been blownup
///////////////////////////////////////////////////////////////////////

    newton,key_faces,base_blowup := get_newton(C);
    ng := #newton;
	    vprint Resolution,2: "\ttime =",Cputime(tt);
	    vprint Resolution,2: "\tResolved newton polygon:",newton;


///////////////////////////////////////////////////////////////////////
//			Step 2
// Make the projective maps which will be the closure of maps from patches
// on the resolution corresponding to rays of the newton polygon down to
// the original curve. I only make maps at the significant patches, those
// where the resolution graph branches or has intersection with C.
// These maps are stored as a sequence of blowups and coordinate changes
// which are composed later if needed.
///////////////////////////////////////////////////////////////////////	

    spine_maps := get_spine_maps(newton,key_faces,P2,PatchMaps);
    patch_maps := [];
    for i in [1..#spine_maps] do
	if IsDefined(spine_maps,i) then
	    patch_maps[i] := [linear_map,spine_maps[i]];
	end if;
    end for;
	    vprint Resolution,2: "\tCalculated patch maps\ttime =",Cputime(tt);


///////////////////////////////////////////////////////////////////////
//			Step 3
// Find the intersections of the birational preimage of C with the
// exceptional loci and return germs of the birational preimage of C at
// those points.
///////////////////////////////////////////////////////////////////////

    // make germs of the intersections
    neigh_germs := [];  // a sequence of unresolved germs for each excl curve
    galdata := [];      // a corr seq galois mults
    axismult := [];	// a corr seq of tangency mults to excl curve
    trans_ints := [ 0 : i in [1..ng] ];
			// a corr seq: # of smooth transverse intersections
    fields := [* *];

    // run through the patches in turn; the final origin is checked later
    for i in key_faces do
	// calculate the germs of the birational pullback of p here
        ngerms := 0;
        neigh_germs[i] := [* *];
        galdata[i] := [];
	axismult[i] := [];
// THINK: next line is the slowest around
// This is where axis factors are lost since I don't decide in advance
// how many factors to remove.
// bool is true if there is a curve here --- if eqn is say x*y
// the intersections will have been completely accounted for already.
// THINK: interesting: the following two lines have exactly the same result.
// However, in different circumstances they take very different times.
// The 'if' condition is a guess which works well in some cases.
//if 3*#Terms(Polynomial(C0)) lt 2*#Terms(Polynomial(C1)) then
// THINK: they are actually different --- the first one fails in g5
// bool,newcurve :=
// remove_axis_components(C0@@(patch_maps[i][1]*patch_maps[i][2]));
	bool,newcurve := remove_axis_components(C1@@patch_maps[i][2]);
	if not bool then
	    // The poly of C0 was of the form x^*y^*z^*. ?? THINK
	    Append(~fields,field);
	    continue;
	end if;
	factors := excl_factors(newcurve);

	// extend field by those roots of mult >= 2 (where more work is needed)
	// THINK: facterms := [ fac[1] : fac in factors | fac[2] gt 1];
	// mch - 04/05 - implemented the above thought!
	facterms := [fac[1] : fac in factors | fac[2] gt 1];
	if #facterms gt 0 then
	  if Type(field) in {FldRat,FldNum,FldAC} then
	    tempfield,temproots := extend_field(field,facterms);
	  elif Type(field) eq FldFin then
            if &*[Degree(fac): fac in facterms] gt 1 then
                tempfield := SplittingField(SequenceToSet(facterms));
            else
                tempfield := field;
            end if;
	    temproots := [ Roots(PolynomialRing(tempfield)!fac)[1][1] :
					fac in facterms ];
	  else
	    require false:
		"Illegal field type";
	  end if;
	else
	  tempfield := field;
	end if;
	Append(~fields,tempfield);

	// If there was a field extension, move everything there THINK:
	if field cmpne tempfield then
	    tempcurve := BaseChange(newcurve,tempfield);
	    vprint Resolution,2: "\tField extension to",tempfield;
	else
	    tempcurve := newcurve;
	end if;

	// Run through the factors --- the intersections of the curve with
	// the i-th exceptional curve --- and decide what to do with each.
        for fac in factors do
            f := fac[1];
	    if fac[2] eq 1 then
		// These are transverse intersections; just record that fact.
		trans_ints[i] +:= Degree(f);
		continue fac;
	    else
		// The germ needs further resolution; record a new germ here.
		ngerms +:= 1;
		neigh_germs[i][ngerms] := Germ(repP,tempcurve) where repP is
	    	     Ambient(tempcurve) ! [tempfield| temproots[ngerms],0,1 ];
		galdata[i][ngerms] := Degree(f);
		axismult[i][ngerms] := fac[2];
	    end if;
        end for;
    end for;
    vprint Resolution,2: "\ttime =",Cputime(tt);
    vprint Resolution,2: "\tDone birational pullbacks";


///////////////////////////////////////////////////////////////////////
//			Step 4
// make the data so far look like a resolution graph portion
///////////////////////////////////////////////////////////////////////


    si := [ newton[i][3] : i in [1..ng] ];
    Reverse(~si);
    // reinclude arrows that were lost in 'remove_axis_components'
    trans_ints[1] +:= xmult;
    trans_ints[ng] +:= ymult;
    trans_ints := Reversion(trans_ints,ng);
    neigh_germs := Reversion(neigh_germs,ng);
    patch_maps := Reversion(patch_maps,ng);
    axismult := Reversion(axismult,ng);
    galdata := Reversion(galdata,ng);
    g := LinearGraph(ng);
    G := MakeResolutionGraph(g,si);
    SetNeighbouringGerms(~G,neigh_germs);
    SetProjectivePatchMaps(~G,patch_maps);
    // setup the uncomposed patch maps: be careful with undefined seq elts.
    Gppm := [];
    for i in [1..#patch_maps] do
	if IsDefined(patch_maps,i) then
	    Gppm[i] := patch_maps[i];
	end if;
    end for;
    G`pre_patch_maps := Gppm;
    SetTransverseIntersections(~G,trans_ints);
    SetAxisMultiplicities(~G,axismult);
    SetGaloisMultiplicities(~G,galdata);
    G`base_blowup_contribution := base_blowup;
    G`base_germ := p;

    return G;

end intrinsic;



///////////////////////////////////////////////////////////////////////
//		Auxilliary functions
///////////////////////////////////////////////////////////////////////


get_newton := function(curve);
    NP := NewtonPolygon(Polynomial(curve));
    // If, say, curve = (x*y = 0) NP will be trivial.
    // I assume here that i do need to blow up something.
    if #Faces(NP) eq 0 then
	NP := NewtonPolygon(curve.1+curve.2);
	// This ensures a single blowup to make (x+y=0) transverse to the axes.
    end if;
    newton := ResolvedDualFan(NP);
    ng := #newton;
    /* the base blowup number is collected before deleting the ends of newton */
    base_blowup_contribution := newton[ng][3];
    /* remove the first and last terms of the sequence --- these correspond
     * to the x and y axes of the plane of p rather than exceptional curves
     * of the resolution. */
    Remove(~newton,ng);
    Remove(~newton,1);
    /* figure out which rays meet the birational transform of curve */
    ng := #newton;
    key_faces := [];
    for j in [1..ng] do
	vect := newton[j];
	if IsFace(NP,<vect[1],vect[2],vect[4]>) then
	    Append(~key_faces,j);
	end if;
    end for;
    return newton,key_faces,base_blowup_contribution;
end function;

remove_axis_components := function(curve)
// given curve = (f(x,y,z) = 0) this removes factors of x,y,z from f.
// it returns true,(f1=0) or false,_ as f1:=f/factors is nontrivial or not.
    P := Ambient(curve);
    f := Polynomial(curve);
    for i in [1..3] do
	f,nnn := RemoveFactor(f,i);
    end for;
    if TotalDegree(f) le 0 then
	return false,_;
    end if;
    newcurve := Curve(P,f);
    return true,newcurve;
end function;

excl_factors := function(curve)
// given curve = (f(x,y,z) = 0) this calculates f(t,0,1) and factorises it.
    k := BaseField(Ambient(curve));
    R := PolynomialRing(k);
    var := R.1; zero := R ! 0; one := R ! 1;
    poly := Polynomial(curve);
    evalu := hom< Parent(poly) -> R | var,zero,one >;
    upoly := evalu(poly);
    factors := Factorisation(upoly);
    return factors;
end function;

get_spine_maps := function(newton,key_faces,projspace,param);
    // calculate the weighted blowup matrixes at exceptional curves
    // if param == 1 then calculate them all else only calculate the
    // essential ones.
    spine_maps := [];
    ng := #newton;
    faces_set := SequenceToSet(key_faces);
    for i in [1..ng] do
        // first find the two relevant rays of the newton fan
        vl := newton[i];
	if param eq 0 then
	    if not i in faces_set then
		continue i;
	    end if;
	end if;
        if i ge 2 then
            vr := newton[i - 1];
        else
            vr := <1,0,0,0>;
        end if;
        // now make the matrix, homogenising properly
        rowsum1 := vr[1]+vl[1];
        rowsum2 := vr[2]+vl[2];
        deg := Maximum([rowsum1,rowsum2]);
        entries := [vr[1],vl[1],deg-rowsum1,vr[2],vl[2],deg-rowsum2,0,0,deg];
        M_blowup := Matrix(3,entries);
        // make the birl transfm from to get to this patch using M_blouwp
        tr_blowup := ToroidalAutomorphism(projspace,M_blowup);
	spine_maps[i] := tr_blowup;
    end for;
    return spine_maps;
end function;

get_linear_map := function(point)
    P2 := Ambient(Scheme(point));
    coords := Coordinates(point);
    xco := point[1];
    yco := point[2];
    zco := point[3];
    if zco ne 0 then
        linear_map := map< P2 -> P2 | [P2.1 + xco*P2.3,P2.2 + yco*P2.3,P2.3] >;
    elif yco ne 0 then
        linear_map := map< P2 -> P2 | [P2.1 + xco*P2.3,P2.3,P2.2] >;
    else
        linear_map := map< P2 -> P2 | [P2.3,P2.1,P2.2] >;
    end if;
    return linear_map;
end function;

forward den,extanf;
extend_field := function(field,polyseq)
// polyseq a list of polys (not nec monic) irred over field (== FldRat|FldNum).
// make a big field containing the roots of them all, together with a
// seq of representative roots.
    bigfield := field;
    reps := [ bigfield | ];
    polyseq := [ f/LeadingCoefficient(f) : f in polyseq ];
    for f in polyseq do

	if Degree(f) eq 1 then
	    // This poly is linear: record its root and don't extend the field
	    ccc := Coefficients(f);
	    Append(~reps,bigfield!(-ccc[1]/ccc[2]));
	    continue;
	end if;

	// Make a field extension of 'field' by adjoining a root of the poly.
	tempk,root := extanf(field,f);
	// Extend 'bigfield' to include this new root.
	if Type(bigfield) eq FldRat then
	    bigfield := tempk;
	elif Type(bigfield) eq FldNum then
	    bigfield := CompositeFields(tempk,bigfield)[1];
	else
	    error "Illegal field type";
	end if;
	ChangeUniverse(~reps,bigfield);
	Append(~reps,bigfield!root);
    end for;
    return bigfield,reps;
end function;

den := function(x)
    if Type(x) ne FldNumElt then
	return Denominator(x);
    end if;
    return LCM([ den(t) : t in Eltseq(x) ]);
end function;

extanf := function(K,f)
    L := ext< K | f >;
    return L, L.1;
end function;

intrinsic RemoveFactor(f::RngMPolElt,i::RngIntElt) -> RngMPolElt,RngIntElt
{The polynomial f with all i-th variable factors removed;
also returns the number of factors removed}
    R := Parent(f);
    n := -1;
    more := true;
    while more do
        more,f1 := IsDivisibleBy(f,R.i);
        if more then
            f := f1;
        end if;
        n +:= 1;
    end while;
    return f,n;
end intrinsic;


