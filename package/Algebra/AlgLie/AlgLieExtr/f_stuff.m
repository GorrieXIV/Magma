freeze;

/*
 * Computing with Lie algebras generated by extremal elements.
 *
 * This file contains code to investigate the structure of the f-variety
 * associated to such a Lie algebra.
 *
 * Dan Roozemond, 2010.
 */

function checkPadInstance(L, inst)
	local brd, R, U, e;

	if Type(BaseRing(L)) eq RngMPol then
		brd := Rank(BaseRing(L));
	else
		brd := 0;
	end if;
	
	if #inst gt brd then 
		error Sprintf("Instance should have length at most %o\n", brd); 
	elif #inst eq brd then
		/* We are happy, regardless */
		return Universe(inst), inst;
	else
		/* #inst < brd --> padding and possibly universe changes */
		try
			U := Universe(inst);
			if Rank(U) eq brd then
				R := U;
			else 
				vprintf AlgLieExtr,1: "[Universe of Instance changed to BaseRing(L)]\n";
				R := BaseRing(L);
				inst := ChangeUniverse(inst, R);
			end if;
			while #inst lt Rank(R) do 
				Append(~inst, R.(#inst+1)); 
			end while;
			vprintf AlgLieExtr,1:"[Instance padded to %o]\n", inst;
			return R, inst;
		catch e
			error Sprintf("Instance sequence has incorrect length (%o, should be %o) and could not be sensibly padded.", #inst, brd);
		end try;
	end if;
end function;

/* chooses dense/sparse depending on whether MT contains 4-tuples or not */
function lie_algebra_by_mt(R, dim, MT)
	assert Type(MT) eq SeqEnum;
	
	if #MT eq 0 then
		return AbelianLieAlgebra(R, dim : Rep := "Sparse");
	else 
		rep := (Type(MT[1]) eq Tup) select "Sparse" else "Dense";
		return LieAlgebra<R, dim | MT : Check := false, Rep := rep>;
	end if;
end function;
	

function mtinstance(L, inst, limit, skipjac, rep, return_alglie)
/* Almost directly calls InternalMTInstance, but takes care of throwing
   away the first argument if it isn't required. Returns base ring
   R as third return value. */
	local S, MT, R;
	
	/* Ensure at least part of MT is computed */
	MultiplicationTable(~L : HowMuch := "Top");
	
	/* Check & fix the arguments */
	if limit cmpeq Infinity() then limit := 0; end if;
	
	if inst cmpeq false then
		//Goes to the above case
		R := BaseRing(L);
		inst := [R|];
	else 
		R, inst := checkPadInstance(L, inst);
	end if;
	
	/* See alg_lie_extr.h for these constants */
	case rep:
		when "Auto": repi := 0;
		when "Dense": repi := 1;
		when "Sparse": repi := 2;
		else error "Invalid rep: " cat rep;
	end case;
	
	if (return_alglie) then
		MT,S := InternalMTInstance(L, R, inst, limit, skipjac, repi);
	else
		_,S := InternalMTInstance(L, R, inst, limit, skipjac, repi);
		MT := false;
	end if;
	return MT, S, R;
end function;


//Set up the map from the free Lie algebra to M (and back)
function instance_map(L, R, M)
	dimM := Dimension(M); ng := L`NumGens;
	FL := FreeLieAlgebra(R, ng);
	gensFL := [ FL.i : i in [1..ng] ]; compFL := func<x,y | x*y>;
	basFL := [ f(gensFL, compFL) : f in (L`BasisUP) ];
	m_to_fl := map< M -> FL | v :-> &+[ FL | v[i]*basFL[i] : i in [1..dimM] ] >;
	fl_to_m := hom< FL -> M | [ M.i : i in [1..ng] ]>;
	phi := map<M -> FL | v :-> m_to_fl(v), x :-> fl_to_m(x) >;
	return phi;
end function;


intrinsic Instance(L::AlgLieExtr, Q::SeqEnum : Check := true, Rep := "Auto") -> AlgLie, Map
{ Create an instance of L as a structure constant Lie algebra L' by evaluating 
  the f-variety in Q. L' will be defined over the ring Universe(Q).
  The second value returned is an invertible map from L to L'.
  An error is thrown if Check is set to true and the resulting multiplication table 
  does not satisfy  the Jacobi identity.

  Rep ("Auto", "Dense", or "Sparse") controls the type of multiplication table used.
}

	local S, MT, LL, R, phi1, phi2;

	MT, S, R := mtinstance(L, Q, 1, not Check, Rep, true);
	if #S ne 0 then
		error "Jacobi identity not satisfied";
	else
		M := lie_algebra_by_mt(R, Dimension(L), MT);
		return M, instance_map(L, R, M);
	end if;
end intrinsic;


intrinsic MultiplicationTable(L::AlgLieExtr : Check := true, Rep := "Auto") -> SeqEnum
{ Create a multiplication table for L as a structure constant Lie algebra L', over BaseRing(L).
  An error is thrown if Check is set to true and the resulting multiplication table
  does not satisfy the Jacobi identity.

  Rep ("Auto", "Dense", or "Sparse") controls the type of multiplication table used.

}

	local S, MT, LL, R, phi1, phi2;

	MT, S, R := mtinstance(L, false, 1, not Check, Rep, true);
	if #S ne 0 then error "Jacobi identity not satisfied"; end if;
	
	return MT;
end intrinsic;

intrinsic Instance(L::AlgLieExtr : Check := true, Rep := "Auto") -> AlgLie
{ Create an instance of L as a structure constant Lie algebra L', over BaseRing(L).
  The second value returned is an invertible map from L to L'.
  An error is thrown if Check is set to true and the resulting multiplication table
  does not satisfy the Jacobi identity.

  Rep ("Auto", "Dense", or "Sparse") controls the type of multiplication table used.
}
	
	MT := MultiplicationTable(L : Check := Check, Rep := Rep);
	R := BaseRing(L);
	M := lie_algebra_by_mt(R, Dimension(L), MT);
	return M, instance_map(L, R, M);
end intrinsic;


function bigtopfactordim(M)
	local Z, Mp, CS;
	
	Mp := M*M;
	//Z := Centre(M);
	//Mp := quo<M | Z>;
	if Dimension(Mp) eq 0 then return 0; end if;

	CS := CompositionSeries(Mp);
	if #CS eq 1 then return Dimension(Mp); end if;
	
	return Dimension(CS[#CS]) - Dimension(CS[#CS-1]);
end function;


intrinsic DimensionsEstimate(L::AlgLieExtr, g::UserProgram : NumSamples := Infinity(), Check := true, Rep := "Auto") -> SeqEnum, SetMulti
{ Estimate the dimensions of the subvarieties of the parameter space X of L giving rise to
  irreducible Lie algebra modules of different dimensions. 

  This procedure repeatedly (at most NumSamples times) invokes Instance(L, g()) to produce
  a Lie algebra M. The composition series of M are computed, and the dimension e of its
  simple factor is stored. Then, for each of these e encountered, the dimension of the 
  subvariety (inside the algebraic variety X) that contains Lie algebras whose top factor
  has dimension e is estimated using the dimension d of the full f-variety that the
  user provides. 

  The estimate is printed as a sequence of triples (e, n, s): n is the number of times
  dimension e was encountered, and s the estimate for the dimension of the subvariety.

  Note that this procedure assumes that X itself is an affine variety (which is proved to
  be true if Gamma(L) is a connected simply laced Dynkin diagram of finite or affine type)
  and that g() produces uniformly random elements of X. If either of these two is not the 
  case, the estimates produced are likely wrong. Moreover, g() must produce a sequence of
  elements of a finite field.
}

	local dimest, ecount, printinfo, MT, M, e, U, rels;
	
	U := Universe(g());
	d := #FreefValues(L);
	dimest := func<p | d + Log(p)/Log(#U)>;
	printinfo := func<ecount | [ <e, Multiplicity(ecount, e), Sprintf("%.2o", dimest(Multiplicity(ecount,e)/#ecount))> : e in MultisetToSet(ecount) ]>;
	ecount := {* *};
	while (NumSamples cmpeq Infinity() or #ecount lt NumSamples) do
		MT, rels := mtinstance(L, g(), 0, not Check, Rep, true);
		if #rels ne 0 then printf "WARNING: Invalid instance returned by g()\n"; continue; end if;
		M := lie_algebra_by_mt(U, Dimension(L), MT);
		vprintf AlgLieExtr, 4: "Computing size of big top factor...\n";
		e := bigtopfactordim(M);
		Include(~ecount, e);
		vprint AlgLieExtr, 3 : printinfo(ecount);
	end while;
	
	return printinfo(ecount), ecount;
end intrinsic;


intrinsic InstancesForDimensions(L::AlgLieExtr, g::UserProgram, ds::SetEnum[RngIntElt] : Check := true) -> Assoc
{ By randomly generating instances of L (using g()) try to find instances for each of the
  "top factor dimensions" in ds.
}
	local v, M, phi, ret;
	
	ret := AssociativeArray(Integers());
	todo := ds;
	if #ds eq 0 then return ret; end if;
	
	repeat
		v := g();
		M, phi := Instance(L, v : Check := Check);
		vprintf AlgLieExtr, 3: "Computing size of big top factor...\n";
		e := bigtopfactordim(M);
		if e in todo then
			ret[e] := <v, M, phi>;
			Exclude(~todo, e);
		end if;
		vprintf AlgLieExtr, 3 : "   e = %o; todo = %o\n", e, todo;
	until #todo eq 0;
	
	return ret;
end intrinsic;


