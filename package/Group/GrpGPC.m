freeze;

intrinsic CentreGrpGPC(G::GrpGPC) -> GrpGPC
{For internal use}
    F := FittingSubgroup(G);
    C := Centre(F); /* F is nilpotent - special algorithm used */
    A, toA := AbelianGroup(C);
    B := A;
    for i := NPCgens(G) to 1 by -1 do
	g := G.i;
	if g notin F then
	    f := hom<B->B|[B!((((B.j)@@toA)^g)@toA)-B.j: j in [1..Ngens(B)]]>;
	    B := Kernel(f);
	end if;
    end for;
    return B@@toA;
end intrinsic;
