freeze;

intrinsic CommutatorGroup(H::Grp, K::Grp) -> Grp
{The commutator group [H, K] = <(h,k): h in H, k in K>}
    require IsCompatible(Id(H), Id(K)): "H and K must be compatible groups";
    G := Parent(Id(H) * Id(K));
    Hgens := [H.i: i in [1 .. Ngens(H)]];
    Kgens := [K.i: i in [1 .. Ngens(K)]];
    combgens := Hgens cat Kgens;
    gens := [G | ];
    HK := sub<G | gens>;
    for h in Hgens, k in Kgens do
	if (h, k) notin HK then
	    Append(~gens, (h, k));
	    HK := sub<G | gens>;
	end if;
    end for;
    i := 0;
    while i lt #gens do
	i +:= 1;
	y := gens[i];
	for x in combgens do
	    if y^x notin HK then
		Append(~gens, y^x);
		HK := sub<G | gens>;
	    end if;
	end for;
    end while;
    return HK;
end intrinsic;
