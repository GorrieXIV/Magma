freeze;

/*************************************************************************
    
  Script for running all available machinery for MW and Sha 
  for elliptic curves over Q or over number fields
       
  Steve Donnelly

*************************************************************************/

declare verbose MWSha, 1;

declare attributes CrvEll : MWRankBounds, // [rl, ru]
                            MWGens,       // independent points
                            MWProof,      // true if MWGens generate E(K)/tors
                            ShaBounds;    // see below

debug := false;

/************************************************************************/
// CACHE

intrinsic StorePoints(P::SeqEnum[PtEll])
{Include the given points in the group of known points on their parent 
elliptic curve.}

  if IsEmpty(P) then return; end if;

  E := Curve(Universe(P));
  K := BaseRing(E);

  require ISA(Type(K), FldRat) or ISA(Type(K), FldAlg):
    "The base field must be Q or a number field";
  require IsIdentical(K, Ring(Universe(P))):
    "The point must be defined over the base field of the curve";

  if assigned E`MWGens then
    if forall{pt : pt in P | pt in E`MWGens or -pt in E`MWGens} then
      return;
    end if;
    B := E`MWGens cat P;
    s := #E`MWGens + 1;
  else
    B := P;
    s := 1;
  end if;

  E`MWGens := IndependentGenerators(B : Start:=s);

  bool, r := HasAttribute(E, "MWRankBounds");
  if bool then
    assert r[2] ge #E`MWGens;
    r[1] := Max(r[1], #E`MWGens);
  end if;
end intrinsic;

intrinsic StoredPoints(E::CrvEll) -> SeqEnum[PtEll]
{Return generators of the group of known points on the elliptic curve E}

  bool, pts := HasAttribute(E, "MWGens");
  if bool then
    return pts;
  else
    return [E(BaseRing(E))| ];
  end if;
end intrinsic;

/************************************************************************/
// FUNCTIONS

procedure Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,
               heightbound 
              : final:=false)

  assert rl ge #MWgens and ru ge #MWgens;
  if ranal ge 0 then  // known
    assert rl le ranal and #MWgens le ranal and ru ge ranal; 
  end if;
  if debug then
    assert forall{P : P in MWgens | Order(P) eq 0};
  end if;
  
  done_rank := rl eq ru;
  done_gens := RankOnly or #MWgens eq ru;
  done_sha := {n : n in {2,4,8,3,9} | Sha mod n eq 0} subset Keys(sha);
  done := done_rank and done_gens and done_sha; 

  if done or final then
    if not RankOnly and #MWgens gt 0 then
      MWgens, MWproof := Saturation(MWgens : Check:=false, TorsionFree,
                                             HeightBound:=heightbound);
    end if;
    E := Curve(Universe(MWgens));
    E`MWGens := MWgens;
    E`MWRankBounds := [rl, ru];
    E`MWProof := ru eq 0 or ru eq #MWgens and assigned MWproof and MWproof;
    E`ShaBounds := sha;
    // sha1 = old format for sha
    sha1 := [<n,sha[n]> : n in Sort(Setseq(Keys(sha)))];
    vprintf MWSha: "\n"; 
    SetVerbose("MWSha", verbosity);   // restore original value
  end if;  
end procedure;

procedure add_points(E, ~MWgens, pts, ~rl, ru)
  r0 := #MWgens;
  MWgens := IndependentGenerators(MWgens cat pts : Start := r0+1);
  assert r0 le #MWgens;
  assert ru ge #MWgens;
  rl := Max(rl, #MWgens);
  if r0 lt #MWgens then
    if #pts eq 1 then
      vprintf MWSha: "New point of infinite order (x = %o)\n", pts[1,1];
    else
      vprintf MWSha: "Infinite rank now %o\n", #MWgens;
    end if;
  end if;
end procedure;

procedure refine_sha_bounds(~sha, n, l, u)
  if IsDefined(sha, n) then
    l0, u0 := Explode(sha[n]);
    sha[n] := [Max(l,l0), Min(u,u0)];
  else
    sha[n] := [l, u];
  end if;
  assert l ne u or IsEven(l); // Sha is square
end procedure;

function get_sha_bounds(sha, n)
  bool, bounds := IsDefined(sha, n);
  if bool then
    return Explode(bounds);
  else 
    return 0, Infinity();
  end if;
end function;

procedure print_sha_bounds(sha)
  L := "";  
  U := "";

  function plus(s)
    return #s eq 0 select "" else " + ";
  end function;

  bool, bounds8 := IsDefined(sha, 8);
  if bool then
    if bounds8[1] gt 0 then
      L *:= plus(L) * "(Z/8)^"*IntegerToString(bounds8[1]); end if;
    if bounds8[2] gt 0 then
      U *:= plus(U) * "(Z/8)^"*IntegerToString(bounds8[2]); end if;
  else 
    bounds8 := [0,0];
  end if;

  bool, bounds4 := IsDefined(sha, 4);
  if bool then
    b1 := bounds4[1] - bounds8[1];
    b2 := bounds4[2] - bounds8[2];
    if b1 gt 0 then
      L *:= plus(L) * "(Z/4)^"*IntegerToString(b1); end if;
    if b2 gt 0 then
      U *:= plus(U) * "(Z/4)^"*IntegerToString(b2); end if;
  else 
    bounds4 := [0,0];
  end if;

  bool, bounds2 := IsDefined(sha, 2);
  if bool then
    b1 := bounds2[1] - bounds4[1];
    b2 := bounds2[2] - bounds4[2];
    if b1 gt 0 then
      L *:= plus(L) * "(Z/2)^"*IntegerToString(b1); end if;
    if b2 gt 0 then
      U *:= plus(U) * "(Z/2)^"*IntegerToString(b2); end if;
  end if;

  bool, bounds9 := IsDefined(sha, 9);
  if bool then
    if bounds9[1] gt 0 then
      L *:= plus(L) * "(Z/9)^"*IntegerToString(bounds9[1]); end if;
    if bounds9[2] gt 0 then
      U *:= plus(U) * "(Z/9)^"*IntegerToString(bounds9[2]); end if;
  else 
    bounds9 := [0,0];
  end if;

  bool, bounds3 := IsDefined(sha, 3);
  if bool then
    b1 := bounds3[1] - bounds9[1];
    b2 := bounds3[2] - bounds9[2];
    if b1 gt 0 then
      L *:= plus(L) * "(Z/3)^"*IntegerToString(b1); end if;
    if b2 gt 0 then
      U *:= plus(U) * "(Z/3)^"*IntegerToString(b2); end if;
  end if;

  n := LCM(Keys(sha)); assert 72 mod n eq 0;

  if #U eq 0 then 
    vprintf MWSha: "    Sha(E)[%o] is trivial\n", n;
  elif #L eq 0 then
    vprintf MWSha: "    Sha(E)[%o] <= %o\n", n, U;
  else
    vprintf MWSha: "    %o <= Sha(E)[%o] <= %o\n", L, n, U;
  end if;
end procedure;

/*************************************************************************/
// MAIN

intrinsic DescentInformation(E::CrvEll :
                             RankOnly:=false, ShaInfo:=false, Sha:=1,
                             Effort:=1, HeightBound:=Infinity(),
                             Silent:=false) 
       -> SeqEnum[RngIntElt], SeqEnum[PtEll], SeqEnum[Tup]

{Print and return all obtainable information about the Mordell-Weil group and
the Tate-Shafarevich group of the elliptic curve E (over Q or a number field).
Returns:
a sequence containing a lower and upper bound on the Mordell-Weil rank,
a sequence of generators for the known subgroup of the Mordell-Weil group modulo torsion,
and a sequence specifying all known lower and upper bounds on Sha[n] for integers n.}

  require t eq FldRat or ISA(t, FldAlg) where t is Type(BaseRing(E)) :
         "The curve must be over the rationals or a number field";

  require Type(RankOnly) eq BoolElt : "Optional parameter 'RankOnly' should be a boolean";
  require Type(ShaInfo) eq BoolElt : "Optional parameter 'ShaInfo' should be a boolean";
  require Type(Sha) eq RngIntElt : "Optional parameter 'Sha' should be an integer";

  return MordellWeilShaInformation(E :
                                   RankOnly:=RankOnly, ShaInfo:=ShaInfo, Sha:=Sha,
                                   Effort:=Effort, HeightBound:=HeightBound,
                                   Silent:=Silent);

end intrinsic;

intrinsic MordellWeilShaInformation(E::CrvEll :
                                    RankOnly:=false, ShaInfo:=false, Sha:=1,
                                    Effort:=1, HeightBound:=Infinity(),
                                    Silent:=false) 
       -> SeqEnum[RngIntElt], SeqEnum[PtEll], SeqEnum[Tup]
{"} // "

  type := Type(BaseRing(E));
  require type eq FldRat or ISA(type, FldAlg) : 
         "The curve must be over the rationals or a number field";

  require Type(RankOnly) eq BoolElt : "Optional parameter 'RankOnly' should be a boolean";
  require Type(ShaInfo) eq BoolElt : "Optional parameter 'ShaInfo' should be a boolean";
  require Type(Sha) eq RngIntElt : "Optional parameter 'Sha' should be an integer";

  require Effort ge 1 : "Optional paramter 'Effort' should be a positive integer";

  // default behaviour is to print information (the original purpose of the function)
  verbosity := GetVerbose("MWSha");
  SetVerbose("MWSha", Silent select 0 else 1);

  if ShaInfo then
    Sha := 0; // all possible Sha info
  end if;

  vprintf MWSha: "\n";

  // STORED DATA
  if assigned E`MWGens then
    MWgens := E`MWGens; // must be independent (mod torsion)
    if debug then
      assert #MWgens eq #IndependentGenerators(MWgens);
    end if;
  else
    MWgens := [E(BaseRing(E)) | ];
  end if;

  if assigned E`MWRankBounds then
    rl, ru := Explode(E`MWRankBounds);
    rl := Max(rl, #MWgens);
  else
    rl := #MWgens;
    ru := Infinity();  
  end if;
  assert rl ge #MWgens and ru ge #MWgens;

  // sha stores known bounds on the n-rank of sha, where n is a prime power
  // sha[n] = [lower bound, upper bound]
  if assigned E`ShaBounds then
    sha := E`ShaBounds;
  else
    sha := AssociativeArray(Integers()); 
  end if;

  ranal := -1; // unknown so far

  Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
  if done then return [rl,ru], MWgens, sha1; end if; 

  // TORSION
  tors := TorsionSubgroup(E);  
  t2 := Ilog(2, #TwoTorsionSubgroup(E));
  if #Invariants(tors) eq 0 then
    tors_string := "is trivial";
  elif #Invariants(tors) eq 1 then
    tors_string := "= Z/"*IntegerToString(Invariants(tors)[1]);
  else 
    tors_string := "= Z/"*IntegerToString(Invariants(tors)[1])*
                  " x Z/"*IntegerToString(Invariants(tors)[2]);
  end if;
  vprintf MWSha: "Torsion Subgroup %o\n", tors_string;

  // ANALYTIC RANK 
  // TO DO: can we increase this to 10^12 ?
  // TO DO: is anything proved for FldNum ?
  if type eq FldRat and Conductor(E) le 10^10 then
    ranal := AnalyticRank(E);
    assert rl le ranal;
    assert ru ge ranal;
    vprintf MWSha: "Analytic rank = %o\n", ranal;
    if ranal le 1 then
      rl := ranal;
      ru := ranal;
      vprintf MWSha: "     ==> Rank(E) = %o\n", ranal;
    end if;

    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if;

  /*
  // SEARCH E 
  // TO DO: when and how much?
  doEsearch := IsFinite(ru) and (rl lt ru or not RankOnly and #MWgens lt ru);
  if doEsearch and type eq FldRat then
    pts := Points(E : Bound:=50); 
    if #pts gt 0 then
      // TO DO: too slow when there are several points
      add_points(E, ~MWgens, Setseq(pts), ~rl, ru);
      Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
      if done then return [rl,ru], MWgens, sha1; end if; 
    end if;
  elif type ne FldRat then // TO DO
  end if;
  */
  
  // TWO DESCENT
  // TO DO: get TwoCover's only as needed
  doTD :=  rl lt ru or not RankOnly and #MWgens lt ru or IsEven(Sha);
  if doTD and type eq FldRat then
    S2, S2map := TwoSelmerGroup(E : RemoveTorsion);
    S2elts := [s : s in S2 | not IsIdentity(s)];
    TD := [];
    TDmaps := [* *];
    for s in S2elts do 
      C2, C2toE := TwoCover(s @@ S2map : E:=E);
      Append(~TD, C2);
      Append(~TDmaps, C2toE); 
    end for;
  elif doTD then 
    // TO DO: TwoCover
    TD, TDmaps, TDsel := TwoDescent(E : RemoveTorsion);
    S2 := Domain(TDsel);
    S2elts := [C2@@TDsel : C2 in TD];
  end if;
  ruTD := Ilog(2, 1+#TD);  assert 2^ruTD eq 1+#TD;
  ru := Min(ru, ruTD);
  refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl);
  vprintf MWSha: "The 2-Selmer group has rank %o\n", ruTD+t2;

  procedure search_on_TDs( TD, ~pts_on_TDs, ~MWgens, ~rl, ru, Bs, ~usedB : TDsubset:=0);
    inds := (TDsubset cmpeq 0) select [1..#TD]
                                else  [i : i in [1..#TD] | TD[i] in TDsubset];
    for B in Bs do 
      usedB := B;
      for i in inds do 
        if IsEmpty(pts_on_TDs[i]) then
          pts := type eq FldRat select Points(TD[i] : Bound:=B)
                                 else  Points(TD[i] : Bound:=B, Max:=1);
          if not IsEmpty(pts) then
            pt := Rep(pts);
            pts_on_TDs[i] := [pt];
            add_points(E, ~MWgens, [pt@TDmaps[i]], ~rl, ru);
            if #MWgens eq ru then break B; end if;
          end if;
        end if;
      end for;
    end for;
  end procedure;

  // quick search for points on the TDs
  // TO DO: initialize pts_on_TDs using pts on E
  // TO DO: keep track of subgroup on which pts are known (use TDsubset?)
  pts_on_TDs := [* [] : i in TD *];
  doTDsearch := rl lt ru or not RankOnly and #MWgens lt ru;
  if doTDsearch then
    Bs := (type eq FldRat) 
             select [10^2, 10^3, 10^4] 
              else  [2^4];
    search_on_TDs( TD, ~pts_on_TDs, ~MWgens, ~rl, ru, Bs, ~B);
  end if;
  refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl); 
  vprintf MWSha: "After 2-descent: \n    %o <= Rank(E) <= %o\n", rl,ru;
  print_sha_bounds(sha);
  if doTDsearch then
    vprintf MWSha: "(Searched up to height %o on the 2-coverings.)\n", B;
  end if;
  
  Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
  if done then return [rl,ru], MWgens, sha1; end if; 

  // TO DO: make full use of pts_on_TDs

  // CASSELS-TATE (quicker than FourDescent!)
  // Do this if (i) don't know rank 
  //         or (ii) need more MWgens and don't know that all TDs lift 
  //         or (iii) need sha and don't know that all TDs lift
  // Note: we assume all TDs lift when ranal = ruTD, however we check this is true when we do 4-descent.
  //   (ie we use this assumption ONLY to save time now, then prove it before using it in the results.)
  if ranal ne -1 then
    rl_conjectural := ranal;
  else
    rl_conjectural := rl;
    if IsOdd(rl_conjectural - ruTD) then
      rl_conjectural +:= 1;
    end if;
  end if;
  if (rl_conjectural lt ruTD) and  
     (rl lt ru or (not RankOnly and #MWgens lt ru) or IsEven(Sha))
  then
    n := Ngens(S2);
    inds := [Index(S2elts, S2.i) : i in [1..n]];
    CTmat := ZeroMatrix(GF(2), n, n);
    for i in [1..n], j in [1..i-1] do 
      ii := inds[i];
      jj := inds[j];
      if IsEmpty(pts_on_TDs[ii]) and IsEmpty(pts_on_TDs[jj]) then
        CTij := CasselsTatePairing(TD[ii], TD[jj]);
        CTmat[i,j] := CTij;  
        CTmat[j,i] := CTij;
      end if;
    end for; 
    vprintf MWSha: "The Cassels-Tate pairing on Sel(2,E)/E[2] is\n";
    IndentPush();
    vprintf MWSha: "%o\n", CTmat;
    IndentPop();
    error if not IsEven(Rank(CTmat)), "CasselsTatePairing failed the parity check";

    kernel := [v : v in Kernel(CTmat) | not IsZero(v)];
    kernel_inds := [Index(S2elts, S2!Eltseq(v)) : v in kernel];
    S2_4 := [S2elts[ii] : ii in kernel_inds]; // used in 8-descent
    TDCT := [TD[ii] : ii in kernel_inds];
    ruTDCT := Ilog(2, 1+#kernel);  assert 2^ruTDCT eq 1+#kernel;
    ru := Min(ru, ruTDCT);
    refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl); 
    refine_sha_bounds(~sha, 4, ruTDCT-ru, ruTDCT-rl); 
    vprintf MWSha: "After using Cassels-Tate: \n    %o <= Rank(E) <= %o\n", rl,ru;
    print_sha_bounds(sha);

    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if; 
 
  if type ne FldRat then
    // long search for points on the TDs (there's nothing else to do)
    doTDsearch := rl ne ru or not RankOnly and #MWgens lt ru; 
    if doTDsearch then
      // choose bounds B such that B ^ (deg + 0.5) <= 10^6*Effort
      deg := Degree(BaseRing(E));
      Bmax := Round( (10^6*Effort) ^ (1/(deg+0.5)) );
      b := deg eq 2 select 4 else 2;
      Bs := Reverse([Bmax div b^i : i in [0..Ilog(b,Bmax)] | Bmax div b^i ge 2^5]);

      search_on_TDs( TD, ~pts_on_TDs, ~MWgens, ~rl, ru, Bs, ~B :
                     TDsubset := assigned TDCT select TDCT else 0);
      refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl); 
      vprintf MWSha: "After more searching:\n    %o <= Rank(E) <= %o\n", rl,ru;
      print_sha_bounds(sha);
      vprintf MWSha: "(Searched up to height %o on the 2-coverings.)\n", B;
    end if;
    
    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if;


//////////////////////
if type eq FldRat then

  // FOUR DESCENT
  if not assigned TDCT then  // we skipped Cassels-Tate because all TD's will lift
    assert rl eq ruTD or rl_conjectural eq ruTD;  // double check
    S2_4 := S2elts;
    TDCT := TD; 
    ruTDCT := ruTD; 
  end if;

  doFD := #MWgens lt ru or (Sha mod 8 eq 0 and ruTDCT ne ru);
  doHEEGNER := Conductor(E) le 5*10^6 and ranal eq 1;

  if doFD then
    // TO DO: omit 4-covers that correspond to known points
    FDs := [FourDescent(C2 : RemoveTorsion) : C2 in TDCT];
    assert forall{FD: FD in FDs | not IsEmpty(FD)}; 
    // we MUST check this, otherwise our answers are only conjectural.
    // (We used ranal above to decide whether to skip Cassels-Tate.) 

    FDmaps := [];
    for i := 1 to #TDCT do 
      Append(~FDmaps, [* *]);
      for j := 1 to #FDs[i] do 
        _,C4toE := AssociatedEllipticCurve(FDs[i][j] : E:=E);
        Append(~FDmaps[i], C4toE);
      end for;
    end for;

    pts_on_FDs := [*[* [] : j in [1..#FDs[i]]*] : i in [1..#FDs]*];  // store points found

    if #MWgens lt ru then
      // Search for points on 4-coverings
      // TO DO: where appropriate, try three descent before searching with large B 
      for b := 1 to (doHEEGNER select 6 else 7) do 
        B := 10^b;
        for i := 1 to #TDCT do 
          for j := 1 to #FDs[i] do
            if IsEmpty(pts_on_FDs[i][j]) then
              pts := PointsQI(FDs[i][j], B : OnlyOne);
              if not IsEmpty(pts) then
                pts_on_FDs[i][j] := pts;
                add_points(E, ~MWgens, [pts[1]@FDmaps[i][j]], ~rl, ru);
                if #MWgens eq ru then break b; end if;
              end if;
            end if;
          end for;
        end for; 
      end for;

      refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl);  // rl may have increased during point-searching
      refine_sha_bounds(~sha, 4, ruTDCT-ru, ruTDCT-rl); 
      vprintf MWSha: "After 4-descent: \n    %o <= Rank(E) <= %o\n", rl,ru;
      print_sha_bounds(sha);
      vprintf MWSha: "(Searched up to height 10^%o on the 4-coverings.)\n", Ilog(10,B);
    end if;

    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if; 

  // HEEGNER
  if doHEEGNER and #MWgens eq 0 then
    // First guess whether using covers is likely to help
    // (Note: the non-cover case is faster code!)
    // TO DO: also use HeegnerIndex for the number of cosets (though occasionally,
    // if the twisting discriminant is large, this may actually be time-dominant)
    cover := 1;
    terms1 := HeegnerPointNumberOfTerms(E);
    if terms1 gt 10^7 then 
      terms2 := (#TDCT eq 1) 
                select HeegnerPointNumberOfTerms(E : Cover:=TDCT[1])
                 else  Infinity();
      terms4 := (#FDs eq 1 and #FDs[1] eq 1) 
                select HeegnerPointNumberOfTerms(E : Cover:=FDs[1][1])
                 else  Infinity();
      if Min(terms2, terms4) lt terms1 div 100 then 
        cover := (terms2 lt terms4) select 2 else 4;
      end if;
    end if;
    vprintf MWSha: "Finding a Heegner point"; 
    if cover gt 1 then
      vprintf MWSha: " (using a %o-cover)", cover;
    end if;
    vprintf MWSha: "\n";

    case cover:
      when 1: bool, pt := HeegnerPoint(E :                  NaiveSearch:=0);
      when 2: bool, pt := HeegnerPoint(E : Cover:=TDCT[1],  NaiveSearch:=0);
      when 4: bool, pt := HeegnerPoint(E : Cover:=FDs[1,1], NaiveSearch:=0);
    end case;

    if bool then 
      vprint MWSha: "Found Heegner point of height", Height(pt);
      MWgens := [P : P in Saturation([pt], 10 : TorsionFree)]; 
    else 
      vprint MWSha: "Failed to find a Heegner point!";
    end if;
        
    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if;
 
end if; // FldRat
//////////////////////////////////////
if type eq FldRat and Effort gt 1 then

  // EIGHT DESCENT
  if #MWgens lt ru or (Sha mod 8 eq 0 and ruTDCT ne ru) then
    
    // Do all 4-coverings where we didn't already find points.
    // (Note: it's not advantageous to quotient by the known MW group;
    //  must still try all candidates because only one candidate has
    //  the point with small height.  TO DO: should mod out torsion.)
    EDs        := [ [] : i in [1..#FDs] ];
    EDmaps     := [ [] : i in [1..#FDs] ];
    pts_on_EDs := [[ [] : j in [1..#FDs[i]] ] : i in [1..#FDs] ];

    // The sequences FDs, TDCT and S2_4 match up with eachother.
    // Let S2_8 be the elements of S2 known to have at least one 8-covering
    // and S2_not8 the elements of S2 known to have no 8-coverings
    S2_not8 := {S2| }; 
    S2_8 := sub< S2 | [S2_4[i] : i in [1..#FDs]
                               | exists{j : j in [1..#FDs[i]] | not IsEmpty(pts_on_FDs[i,j])}] >;
    S2_8done := #S2_8 + #S2_not8 eq #S2_4 + 1;
    if S2_8done then
      r8 := Ilog(2, #S2_8);
      ru := Min(ru, r8); // refine rank bound
    end if;
   
    searchedB := 0;
    for b in [2 .. 20 by 2] do
      B := 10^b;
      for i in [1..#FDs], j in [1..#FDs[i]] do
        if #MWgens eq ru and (Sha mod 8 ne 0 or S2_8done) then 
          break b; 
        end if;
        if S2_4[i] in S2_not8 then
          continue i;
        elif IsEmpty(pts_on_FDs[i,j]) then
          if not IsDefined(EDs[i],j) then
            EDs[i,j], EDmaps[i,j] := EightDescent(FDs[i,j]);
            if not IsEmpty(EDs[i,j]) then
              S2_8 := S2_8 + sub< S2 | S2_4[i] >;
            elif forall{jj : jj in [1..#FDs[i]] | IsDefined(EDs[i],jj) and IsEmpty(EDs[i,jj])} then
              Include(~S2_not8, S2_4[i]);
            end if;
            S2_not8 := {S2| s+n : s in S2_8, n in S2_not8}; // S2_not8 = union of cosets of S2_8
            S2_8done := #S2_8 + #S2_not8 eq #S2_4 + 1;
            if S2_8done then
              r8 := Ilog(2, #S2_8);
              ru := Min(ru, r8); // refine rank bound
            end if;
          end if;

          for k := 1 to #EDs[i,j] do
            if #MWgens eq ru then 
              break k;
            end if;
            // TO DO: probably should skip when a pt has been found on *any* of the EDs[i,j]
            if not IsDefined(pts_on_EDs[i,j], k) then
              searchedB := B;
//printf "Search (B = 10^%o): ", b; time
              pts := PointSearch(EDs[i,j,k], B : OnlyOne);
              if not IsEmpty(pts) then
                pts_on_EDs[i,j,k] := pts[1];
                add_points(E, ~MWgens, [pts[1] @EDmaps[i,j,k] @FDmaps[i,j]], ~rl, ru);
              end if;
            end if;
          end for;

        end if;
      end for;
    end for;

    refine_sha_bounds(~sha, 2, ruTD-ru, ruTD-rl);
    refine_sha_bounds(~sha, 4, ruTDCT-ru, ruTDCT-rl); 
    if S2_8done then
      refine_sha_bounds(~sha, 8, r8-ru, r8-rl);
    end if;
    vprintf MWSha: "After 8-descent: \n    %o <= Rank(E) <= %o\n", rl,ru;
    print_sha_bounds(sha);
    if searchedB gt 0 then
      vprintf MWSha: "(Searched up to height 10^%o on the 8-coverings.)\n", Ilog(10,searchedB);
    end if;

    Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound);
    if done then return [rl,ru], MWgens, sha1; end if; 
  end if;

  // THREE DESCENT (not useful for finding points: better to search on FDs)
  if rl lt ru or Sha mod 3 eq 0 then
    t3 := (#tors mod 3 eq 0) select 1 else 0;
    S3 := ThreeSelmerGroup(E);
    ruD3 := Ilog(3, #S3) - t3;  assert 3^(ruD3+t3) eq #S3;
    ru := Min(ru, ruD3);
    refine_sha_bounds(~sha, 3, ruD3-ru, ruD3-rl);
    vprintf MWSha: "The 3-Selmer group has rank %o\n", ruD3+t3;
    vprintf MWSha: "After 3-descent: \n    %o <= Rank(E) <= %o\n", rl,ru;
    print_sha_bounds(sha);
  end if;

end if; // FldRat
/////////////////


  // Now tried everything (TO DO: search longer according to desired Effort)

  assert forall{P : P in MWgens | Order(P) eq 0};
  if #MWgens lt rl then
    vprint MWSha: "Didn't find generators for the full Mordell-Weil group\n"; 
  end if;

  Done(~done,rl,ru,ranal,~MWgens,sha,~sha1,RankOnly,Sha,verbosity,HeightBound : final);
  return [rl,ru], MWgens, sha1;

end intrinsic;


//////////////////////////////////////////////////////////////////////////////
// Miscellaneous interface stuff
//////////////////////////////////////////////////////////////////////////////

// Partly extracted from main routine above

intrinsic FourDescent(E::CrvEll : CT:=false, D8:=false) -> SeqEnum
{Return all locally solvable 4-coverings of the elliptic curve E over Q,
modulo equivalence by E_tors(Q).  When CT or D8 is given, return only
the 4-coverings that have a locally solvable 8-covering.}
 
  K := BaseRing(E);
  type := Type(K);

  require type eq FldRat or ISA(type, FldAlg) :
          "Implemented only for curves over Q and number fields";

  // TO DO : FldNum case
  
  if type eq FldRat then
    S2, S2map := TwoSelmerGroup(E : RemoveTorsion);
    S2elts := [s : s in S2 | not IsIdentity(s)];
    TD := [];
    TDmaps := [* *];
    for s in S2elts do 
      C2, C2toE := TwoCover(s @@ S2map : E:=E);
      Append(~TD, C2);
      Append(~TDmaps, C2toE); 
    end for;
  else
    // TO DO: TwoCover
    TD, TDmaps, TDsel := TwoDescent(E : RemoveTorsion);
    S2 := Domain(TDsel);
    S2elts := [C2@@TDsel : C2 in TD];
  end if;
  vprintf MWSha: "Sel(2,E)/E[2] has rank %o\n", Ilog(2, #S2);

  n := Ngens(S2);
  inds := [Index(S2elts, S2.i) : i in [1..n]];
  CTmat := ZeroMatrix(GF(2), n, n);
  for i in [1..n], j in [1..i-1] do 
    ii := inds[i];
    jj := inds[j];
    CTij := CasselsTatePairing(TD[ii], TD[jj]);
    CTmat[i,j] := CTij;  
    CTmat[j,i] := CTij;
  end for; 
  vprintf MWSha: "The Cassels-Tate pairing on Sel(2,E)/E[2] is\n";
  IndentPush();
  vprintf MWSha: "%o\n", CTmat;
  IndentPop();
  error if not IsEven(Rank(CTmat)), "CasselsTatePairing failed the parity check";

  kernel := [v : v in Kernel(CTmat) | not IsZero(v)];
  kernel_inds := [Index(S2elts, S2!Eltseq(v)) : v in kernel];
  S2_4 := [S2elts[ii] : ii in kernel_inds];
  TDCT := [TD[ii] : ii in kernel_inds];

  FD := [FourDescent(C2 : RemoveTorsion) : C2 in TDCT];

  if type eq FldRat and # &cat FD gt 1 then

    require not CT or not D8 : "Parameters 'CT' and 'D8' should not both be true";

    if CT then
      vprint MWSha: "Cassels-Tate pairings (4 x 2) :";

      // TO DO !!!

      FD := &cat FD;
      fdct := [1..#FD];
      for i in [1..#TD], j in fdct do if TD[i] in TDCT then continue; end if;
        vtime MWSha:
        if CasselsTatePairing(FD[j], TD[i]) ne 0 then
          Exclude(~fdct, j);
        end if;
      end for;

      return [FD[j] : j in fdct];

    elif D8 then
      vprint MWSha: "EightDescent :";

      FD8 := [];
      for C4 in &cat FD do
        vtime MWSha:
        if not IsEmpty(EightDescent(C4)) then
          Append(~FD8, C4);
        end if;
      end for;

      return FD8;

    end if;

  end if;
  
  return &cat FD;

end intrinsic;

