freeze;

orb_stab := function(G, f, x)
    relative_orders := PCPrimes(G);
    orbit := {@ G | x @};
    stab_gens := [ G | ];
    orbit_nos := [];
    for i := NPCgens(G) to 1 by -1 do
        g := G.i;
        pos := Position(orbit, f(<x, g>));
        orbit_len := #orbit;
        if pos eq 0 then
            for k := 1 to relative_orders[i]-1 do
                for j := 1 to orbit_len do
                    Include(~orbit, f(<orbit[j], g>));
                end for;
                g *:= G.i;
            end for;
            assert #orbit eq orbit_len * relative_orders[i];
            Append(~orbit_nos, i);
        else
            /* move to 0-index arrays for modulo arithmetic */
            pos -:= 1;
            for j := #orbit_nos to 1 by -1 do
                if pos eq 0 then break; end if;
                t := orbit_nos[j];
                orbit_len div:= relative_orders[t];
                pow := pos div orbit_len;
                g *:= G.t^-pow;
                pos -:= pow * orbit_len;
            end for;
            assert f(<x ,g>) eq x;
            Append(~stab_gens, g);
        end if;
    end for;
    stab := sub< G | stab_gens >;
    return orbit, stab, orbit_nos;
end function;

intrinsic OrbitStabilizer(G::GrpPC, f::Map, x::Any) -> SetIndx, GrpPC, SeqEnum
{Return orbit, stabiliser of x as subgroup of G, and
generator numbers in G that were used to build up orbit, where f : S x G -> S
gives the G-action}

    return orb_stab(G, f, x);

end intrinsic;

intrinsic OrbitStabilizer(G::GrpPC, f::UserProgram, x::Any) -> SetIndx, GrpPC, SeqEnum
{Return orbit, stabiliser of x as subgroup of G, and
generator numbers in G that were used to build up orbit, where f : S x G -> S
gives the G-action}

    return orb_stab(G, f, x);

end intrinsic;

intrinsic OrbitStabilizer(G::GrpPC, f::Intrinsic, x::Any) -> SetIndx, GrpPC, SeqEnum
{Return orbit, stabiliser of x as subgroup of G, and
generator numbers in G that were used to build up orbit, where f : S x G -> S
gives the G-action}

    return orb_stab(G, f, x);

end intrinsic;

orb_stab_mat_mult := function(G, act, x)
    ng := NPCgens(G);
    ords := PCPrimes(G);
    orb := {@ x @};
    stabgens := [G|];
    orbnos := [];
    for i := ng to 1 by -1 do
	ga := act[i];
	im := x*ga;
	pos := Position(orb, im);
	lo := #orb;
	if pos eq 0 then
	    for k := 1 to ords[i]-1 do
		for j := 1 to lo do
		    Include(~orb, orb[j]*ga);
		end for;
		ga *:= act[i];
	    end for;
	    assert #orb eq lo*ords[i];
	    Append(~orbnos, i);
	else
	    g := G.i;
	    for j := #orbnos to 1 by -1 do
		if pos eq 1 then break; end if;
		t := orbnos[j];
		lo := lo div ords[t];
		pow := (pos-1) div lo;
		g *:= G.t^-pow;
		assert t gt i; // so act[t] is inverse of original value
		im *:= act[t]^pow;  // not -pow
		pos := Position(orb, im);
		assert pos ne 0;
	    end for;
	    assert im eq x;
	    Append(~stabgens, g);
	end if;
	act[i] := act[i]^-1; // invert this action matrix
    end for;
    stab := sub<G | stabgens>;
    return orb, stab, orbnos;
end function;

intrinsic OrbitStabilizer(G::GrpPC, f::SeqEnum, x::Any) -> SetIndx, GrpPC, SeqEnum
{Return orbit, stabiliser of x as subgroup of G, and
generator numbers in G that were used to build up orbit}

    return orb_stab_mat_mult(G, f, x);

end intrinsic;

PCActGIsCon_mat := function(G,f,orb,orbnos,impt)
//orb, orbnos should be as returned by PCOSG on (G,f,pt)
//Determine if impt is in orb, and if so return conjugating element from G
      pos := Position(orb,impt);
      if pos eq 0 then return false,_; end if;
      ng := NPCgens(G);
      g := Id(G);
      lo := #orb;
      ords := PCPrimes(G);
      for i := #orbnos to 1 by -1 do
        if pos eq 1 then break; end if;
	t := orbnos[i];
        lo := lo div ords[t];
        pow := (pos-1) div lo;
       	h := G.t^-pow;
        g *:= h;
	m := f[t]^-1;
	for j := 1 to pow do
	    impt := impt * m;
	end for;
        pos := Position(orb,impt);
      end for;
      assert pos eq 1;
      return true, g^-1;
end function;

intrinsic IsConjugate(G::GrpPC, f::SeqEnum, O::SetIndx, N::SeqEnum[RngIntElt], x::Any) -> BoolElt, GrpPCElt
{Use the data returned by OrbitStabilizer(G, f, b) to determine if x is in the
G-orbit of b}

    return PCActGIsCon_mat(G,f,O,N,x);

end intrinsic;

PCActGIsCon := function(G,f,orb,orbnos,impt)
//orb, orbnos should be as returned by PCOSG on (G,f,pt)
//Determine if impt is in orb, and if so return conjugating element from G
      pos := Position(orb,impt);
      if pos eq 0 then return false,_; end if;
      ng := NPCgens(G);
      g := Id(G);
      lo := #orb;
      ords := PCPrimes(G);
      for t in Reverse(orbnos) do
        if pos eq 1 then break; end if;
        lo := lo div ords[t];
        pow := (pos-1) div lo;
       	h := G.t^-pow;
        g *:= h;
        impt := f(<impt, h>);
        pos := Position(orb,impt);
      end for;
      assert pos eq 1;
      return true, g^-1;
end function;

intrinsic IsConjugate(G::GrpPC, f::Map, O::SetIndx, N::SeqEnum[RngIntElt], x::Any) -> BoolElt, GrpPCElt
{Use the data returned by OrbitStabilizer(G, f, b) to determine if x is in the
G-orbit of b}

    return PCActGIsCon(G,f,O,N,x);

end intrinsic;

intrinsic IsConjugate(G::GrpPC, f::UserProgram, O::SetIndx, N::SeqEnum[RngIntElt], x::Any) -> BoolElt, GrpPCElt
{Use the data returned by OrbitStabilizer(G, f, b) to determine if x is in the
G-orbit of b}

    return PCActGIsCon(G,f,O,N,x);

end intrinsic;

intrinsic IsConjugate(G::GrpPC, f::Intrinsic, O::SetIndx, N::SeqEnum[RngIntElt], x::Any) -> BoolElt, GrpPCElt
{Use the data returned by OrbitStabilizer(G, f, b) to determine if x is in the
G-orbit of b}

    return PCActGIsCon(G,f,O,N,x);

end intrinsic;
