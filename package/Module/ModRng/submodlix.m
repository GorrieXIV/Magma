freeze;
 

intrinsic LowDimSubmodules(M::ModRng, limit::RngIntElt) -> SeqEnum
{A sequence containing all submodules of M having dimension less
than or equal to limit}

    /*
    Return all submodules of M having dimension <= limit.
    Allan Steel, Oct 2001.
    */

    vprint SubmoduleLattice: "Get constituents";
    vtime SubmoduleLattice:
	CM := ConstituentsWithMultiplicities(M);

    C := [t[1]: t in CM];
    E := [t[2]: t in CM];
    k := #C;

    L := <<M, E, <>, 0>>;
    R := {sub<M|>};

    OM := M;

    while #L gt 0 do

	M, E, H, d := Explode(L[#L]);
	Prune(~L);

	vprintf SubmoduleLattice:
	    "%o left: M: dim %o, d: %o\n", #L + 1, Dimension(M), d;

	for i := 1 to k do
	    if E[i] ne 0 then
		di := Dimension(C[i]);
		if d + di gt limit then
		    continue;
		end if;
		IS := IsomorphicSubmodules(M, C[i]);
		vprintf SubmoduleLattice:
		    "    Constituent %o [%o]: %o submodule(s)\n",
		    i, Dimension(C[i]), #IS;

		if #IS gt 0 then
		    EE := E;
		    EE[i] -:= 1;
		    for S in IS do
			SS := S;
			for i := #H to 1 by -1 do
			    SS := SS @@ H[i];
			end for;
			Include(~R, SS);

			//Q, Qf := quo<M | S>;
			Q, Qf := M / S;
			Append(~L, <Q, EE, Append(H, Qf), d + di>);
		    end for;
		end if;
	    end if;
	end for;
    end while;

    R := Setseq(R);
    Sort(~R, func<x, y | Dimension(x) - Dimension(y)>);
    return R;

end intrinsic;

intrinsic LowIndexSubmodules(M::ModRng, limit::RngIntElt) -> SeqEnum
{A sequence containing all submodules of M having codimension less
than or equal to limit}

    /*
    Return all submodules of M having dimension >= Dim(M) - limit.
    Allan Steel, Oct 2001.
    */

    T := Transpose(M);
    R := LowDimSubmodules(T, limit);

    vprint SubmoduleLattice: "Convert";
    vtime SubmoduleLattice:
	R := [
	    sub<M |
		NullspaceOfTranspose(Matrix(Morphism(S, T))): Check := false>:
	    S in R
	];

    return R;

end intrinsic;

