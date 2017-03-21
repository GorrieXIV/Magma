freeze;

///////////////////////////////////////////////////////////////////////
// These functions are now an interface to all the machinery in Magma,
// via appropriate calls to MordellWeilShaInformation.
// Previously they were internal and only used internal ec code.
// (The internal code will be used via MordellWeilShaInformation
// when a way to access certain bits of internal data is provided.) 
// 
// 'Bound' is now ignored
// 'Effort' is new (and currently very primitive)
// 
// Dec 2014, SRD
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
// Group

intrinsic MordellWeilGroup(E::CrvEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> GrpAb, Map, BoolElt, BoolElt

{The Mordell-Weil group of the elliptic curve E
(or possibly a subgroup if one of the returned booleans is false)}

    F := BaseRing(E);
    EF := E(F);

    require t eq FldRat or ISA(t, FldAlg) where t is Type(F) :
        "The base ring of the curve must be Q or a number field";

    T, mT := TorsionSubgroup(E);
    t := Ngens(T);

    rank, gens := MordellWeilShaInformation(E : HeightBound:=HeightBound,
                                                Effort:=Effort,
                                                Silent:=GetVerbose("MWSha") eq 0);
    r := #gens;

    G := AbelianGroup(Invariants(T) cat [0 : i in [1..r]]);

    /* TO DO inverse map
    function toG(P)
        bool, v := IsLinearlyDependent(Append(gens, P));
        if v[r+1] eq -1 then v := -v; end if;
        error if not bool or v[r+1] ne 1, 
            "Point is not in the calculated Mordell-Weil group";
        v1 := [v[i] : i in [1..r]];
        P1 := &+ [EF | v[i] * gens[i] : i in [1..r]];
        P0 := P - P1;
        v0 := Eltseq(P0 @@ mT);
        return G! (v0 cat v1);
    end function;
    */

    mG := map< G -> EF |
               g :-> mT(T! e[1..t]) +
                     &+ [EF | e[t+i] * gens[i] : i in [1..r]]
                     where e is Eltseq(g) >;

    return G, mG, r eq rank[2], E`MWProof;

end intrinsic;

intrinsic AbelianGroup(E::CrvEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> GrpAb, Map, BoolElt, BoolElt
{"} // "

    return MordellWeilGroup(E : HeightBound:=HeightBound, Effort:=Effort);
end intrinsic;

intrinsic Generators(E::CrvEll : Bound:=0, HeightBound:=15, Effort:=1)
  -> SeqEnum, BoolElt, BoolElt
{The generators of MordellWeilGroup(E) returned as points on E}

    G, mG, b1, b2 := MordellWeilGroup(E : HeightBound:=HeightBound, Effort:=Effort);

    return [E| G.i @ mG : i in [1..Ngens(G)]], b1, b2;
end intrinsic;

intrinsic NumberOfGenerators(E::CrvEll : Bound:=0, HeightBound:=15, Effort:=1)
  -> RngIntElt, BoolElt, BoolElt
{NumberOfGenerators(MordellWeilGroup(E))}

    G, mG, b1, b2 := MordellWeilGroup(E : HeightBound:=HeightBound, Effort:=Effort);

    return Ngens(G), b1, b2;
end intrinsic;


/////////////////////////////////////////////////////////////////////////
// Rank

intrinsic Rank(E::CrvEll : Bound:=0, Effort:=1) -> RngIntElt, BoolElt

{The Mordell-Weil rank of the elliptic curve E
(or possibly a lower bound if the returned boolean is false)}

    require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
        "The base ring of the curve must be Q or a number field";

    rank := MordellWeilShaInformation(E : RankOnly, Effort:=Effort,
                                          Silent := GetVerbose("MWSha") eq 0);

    return rank[1], rank[1] eq rank[2];

end intrinsic;

intrinsic MordellWeilRank(E::CrvEll : Bound:=0, Effort:=1) -> RngIntElt, BoolElt
{"} // "

    require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
        "The base ring of the curve must be Q or a number field";

    return Rank(E : Effort:=Effort);

end intrinsic;

intrinsic RankBound(E::CrvEll : Bound:=0, Effort:=1, Isogeny:=0) -> RngIntElt, BoolElt
{"} // "
// Isogeny vararg obselete

    require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
        "The base ring of the curve must be Q or a number field";

    return Rank(E : Effort:=Effort);

end intrinsic;


intrinsic RankBounds(E::CrvEll : Bound:=0, Effort:=1) -> RngIntElt, RngIntElt

{Upper and lower bounds on the Mordell-Weil rank of the elliptic curve E}

    require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
        "The base ring of the curve must be Q or a number field";

    rank := MordellWeilShaInformation(E : RankOnly, Effort:=Effort,
                                          Silent := GetVerbose("MWSha") eq 0);

    return Explode(rank);

end intrinsic;

intrinsic MordellWeilRankBounds(E::CrvEll : Bound:=0, Effort:=1) -> RngIntElt, RngIntElt
{"} // "

    require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
        "The base ring of the curve must be Q or a number field";

    return RankBounds(E : Effort:=Effort);

end intrinsic;


/////////////////////////////////////////////////////////////////////////
// SetPtEll signatures

intrinsic MordellWeilGroup(E::SetPtEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> GrpAb, Map, BoolElt, BoolElt
{Returns MordellWeilGroup(Curve(E))}
    return MordellWeilGroup(Curve(E) : HeightBound:=HeightBound, Effort:=Effort);
end intrinsic;

intrinsic AbelianGroup(E::SetPtEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> GrpAb, Map, BoolElt, BoolElt
{"} // "
    return MordellWeilGroup(Curve(E) : HeightBound:=HeightBound, Effort:=Effort);
end intrinsic;

intrinsic Generators(E::SetPtEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> SeqEnum
{Returns Generators(Curve(E))}
    return Generators(Curve(E) : HeightBound:=HeightBound, Effort:=Effort);
end intrinsic;

intrinsic NumberOfGenerators(E::SetPtEll : Bound:=0, HeightBound:=15, Effort:=1)
       -> RngIntElt
{Returns NumberOfGenerators(Curve(E))}
    return NumberOfGenerators(Curve(E) : HeightBound:=HeightBound, Effort:=Effort);
end intrinsic;

intrinsic Rank(E::SetPtEll : Bound:=0, Effort:=1) -> RngIntElt, BoolElt
{Returns Rank(Curve(E))}
    return Rank(Curve(E) : Effort:=Effort);
end intrinsic;

intrinsic MordellWeilRank(E::SetPtEll : Bound:=0, Effort:=1) -> RngIntElt, BoolElt
{Returns MordellWeilRank(Curve(E))}
    return Rank(Curve(E) : Effort:=Effort);
end intrinsic;

intrinsic RankBounds(E::SetPtEll : Bound:=0, Effort:=1) -> RngIntElt, RngIntElt
{Returns RankBounds(Curve(E))}
    return RankBounds(Curve(E) : Effort:=Effort);
end intrinsic;

intrinsic MordellWeilRankBounds(E::SetPtEll : Bound:=0, Effort:=1) -> RngIntElt, RngIntElt
{Returns MordellWeilRankBounds(Curve(E))}
    return RankBounds(Curve(E) : Effort:=Effort);
end intrinsic;

