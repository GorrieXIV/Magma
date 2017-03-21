freeze;

eval_wrap := function(str)
    return eval str;
end function;

read_file_eval := function(path)
    fullpath := Sprintf("%o/data/TrnGps/Trn32IdData/%o", GetLibraryRoot(), path);
    x := Read(fullpath);
    y := eval_wrap(x);
    return y;
end function;

read_file_split := function(path)
    fullpath := Sprintf("%o/data/TrnGps/Trn32IdData/%o", GetLibraryRoot(), path);
    x := Read(fullpath);
    y := Split(x, "X");
    return y;
end function;

classes_invar := function(G)
    local cl, m2, m4, inv, i, x;
    cl := ClassesData(G);
    m2 := {* *};
    m4 := {* *};
    for i := 1 to #cl do
	if cl[i,1] eq 2 then
	    Include(~m2, #Fix(ClassRepresentative(G,i))^^cl[i,2]);
	elif cl[i,1] eq 4 then
	    Include(~m4, #Fix(ClassRepresentative(G,i))^^cl[i,2]);
	end if;
    end for;
    inv := [#cl, &+[c[1]:c in cl]];
    x := Sort(SetToSequence(MultisetToSet(m2)));
    for a in x do
	Append(~inv, a);
	Append(~inv, Multiplicity(m2, a));
    end for;
    Append(~inv, 0);
    x := Sort(SetToSequence(MultisetToSet(m4)));
    for a in x do
	Append(~inv, a);
	Append(~inv, Multiplicity(m4, a));
    end for;
    return inv;
end function;

BlocksIsConjugate16 := function(G1,G2)
  BW := WreathProduct(Sym(16), Sym(2));
  proj := hom<BW -> Sym(2) | Sym(2).1, Id(Sym(2)), Id(Sym(2)) >;
  K := Kernel(proj);

  oG1 := G1;
  G1K := G1 meet K; G2K := G2 meet K;
  G11 := sub<Sym(16) | [ [Eltseq(G1K.i)[j] : j in [1..16]] :
                                                  i in [1..Ngens(G1K)] ] >;
  G12 := sub<Sym(16) | [ [Eltseq(G1K.i)[j]-16 : j in [17..32]] :
                                                  i in [1..Ngens(G1K)] ] >;
  G21 := sub<Sym(16) | [ [Eltseq(G2K.i)[j] : j in [1..16]] :
                                                  i in [1..Ngens(G2K)] ] >;
  G22 := sub<Sym(16) | [ [Eltseq(G2K.i)[j]-16 : j in [17..32]] :
                                                  i in [1..Ngens(G2K)] ] >;
  isc, x1 := IsConjugate(Sym(16), G11, G21);
  if not isc then return false, _; end if;
  isc, x2 := IsConjugate(Sym(16), G12, G22);
  if not isc then return false, _; end if;
  x := Sym(32)!(Eltseq(x1) cat [Eltseq(x2)[i]+16: i in [1..16]]);
  G1 := G1^x;
  NG21 := Normaliser(Sym(16), G21);
  NG22 := Normaliser(Sym(16), G22);
  NG2 := sub< Sym(32) | [Eltseq(NG21.i) cat [17..32] : i in [1..Ngens(NG21)]]
               cat  [[1..16] cat [x+16: x in Eltseq(NG22.i)] :
                                                 i in [1..Ngens(NG22)]] >;
  if G2K ne G2 then
    y := [ G2.i : i in [1..Ngens(G2)] | not G2.i in K][1];
    NG2 := sub< BW | NG2, y >;
  else isc, u := IsConjugate(Sym(16), NG21, NG22);
    if isc then
       y := Sym(32)!([Eltseq(u)[i]+16 : i in [1..16]] cat
                     [Eltseq(u^-1)[i] : i in [1..16]] );
       NG2 :=sub< BW | NG2,y >;
    end if;
  end if;
  isc,z := IsConjugate(NG2,G1,G2);
  if isc then
    assert oG1^(x*z) eq G2;
    return true, x*z;
  else return false, _;
  end if;
end function;

BlocksIsConjugate8 := function(G1,G2)
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S8, S4);
  proj := hom<BW -> S4 | S4.1, S4.2, Id(S4), Id(S4) >;
  K :=sub< Sym(32) | (1,2,3,4,5,6,7,8), (1,2),
                     (9,10,11,12,13,14,15,16), (9,10),
                     (17,18,19,20,21,22,23,24), (17,18),
                     (25,26,27,28,29,30,31,32), (25,26) >;
  assert K eq Kernel(proj);
  i1 := hom< S8->K | K!(1,2,3,4,5,6,7,8), K!(1,2) >;
  i2 := hom< S8->K | K!(9,10,11,12,13,14,15,16), K!(9,10) >;
  i3 := hom< S8->K | K!(17,18,19,20,21,22,23,24), K!(17,18) >;
  i4 := hom< S8->K | K!(25,26,27,28,29,30,31,32), K!(25,26) >;
  e:=Id(S8);
  p1 := hom< K->S8 | S8.1, S8.2, e,e,e,e,e,e >;
  p2 := hom< K->S8 | e,e, S8.1, S8.2, e,e,e,e >;
  p3 := hom< K->S8 | e,e,e,e, S8.1, S8.2, e,e >;
  p4 := hom< K->S8 | e,e,e,e,e,e, S8.1, S8.2 >;
  //in hard cases projections onto S8xS8 are useful
  S82 := DirectProduct(S8,S8);
  e2:=Id(S82);
  pp1 := hom< K->S82 | S82.1, S82.2, S82.3, S82.4, e2,e2,e2,e2 >;
  pp2 := hom< K->S82 | e2,e2,e2,e2, S82.1, S82.2, S82.3, S82.4 >;
  ii1 := hom< S82->K | K!(1,2,3,4,5,6,7,8), K!(1,2),
                       K!(9,10,11,12,13,14,15,16), K!(9,10) >;
  ii2 := hom< S82->K | K!(17,18,19,20,21,22,23,24), K!(17,18),
                       K!(25,26,27,28,29,30,31,32), K!(25,26) >;

  isc, w := IsConjugate(S4, proj(G1), proj(G2) );
  if not isc then return false, _; end if;
  w := w@@proj;
  oG1 := G1;
  G1 := G1^w;
  NP := Normaliser(S4,proj(G2));
  NPI := NP@@proj;

  G1K := G1 meet K; G2K := G2 meet K;
  //NG21 := Normaliser(S8, p1(G2K));
  //NG22 := Normaliser(S8, p2(G2K));
  //NG23 := Normaliser(S8, p3(G2K));
  //NG24 := Normaliser(S8, p4(G2K));
  //NG2K := sub< K | i1(NG21), i2(NG22), i3(NG23), i4(NG24) >;

  NNG21 := Normaliser(S82, pp1(G2K));
  NNG22 := Normaliser(S82, pp2(G2K));
  NNG2K := sub< K | ii1(NNG21), ii2(NNG22) >;

  KIsConj := function(S1,S2) //S1,S2 <= K
    oS1 := S1;
    isc, x1 := IsConjugate(S8, p1(S1), p1(S2) );
    if not isc then return false, _; end if;
    isc, x2 := IsConjugate(S8, p2(S1), p2(S2) );
    if not isc then return false, _; end if;
    isc, x3 := IsConjugate(S8, p3(S1), p3(S2) );
    if not isc then return false, _; end if;
    isc, x4 := IsConjugate(S8, p4(S1), p4(S2) );
    if not isc then return false, _; end if;

    x := i1(x1) * i2(x2) * i3(x3) * i4(x4);
    S1:=S1^x;

    isc, xx1 := IsConjugate(S82, pp1(S1), pp1(S2) );
    if not isc then return false, _; end if;
    isc, xx2 := IsConjugate(S82, pp2(S1), pp2(S2) );
    if not isc then return false, _; end if;

    xx := ii1(xx1) * ii2(xx2);
    S1:=S1^xx;
    isc, y := IsConjugate(NNG2K, S1, S2);
    //isc, y := IsConjugate(NG2K, S1, S2);
    if not isc then return false, _; end if;
    assert oS1^(x*xx*y) eq S2;
    return true, x*xx*y;
  end function;
 
  isc,x := KIsConj(G1K,G2K);

  if isc then
    G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
    if G1 eq G2 then assert oG1^(w*x) eq G2; return true, w*x; end if;
  end if;
  Q, nproj := quo< NP | proj(G2) >;
  if not isc then //look for element in Q mapping G1K to G2K
   found := false;
   for q in Q do if not IsIdentity(q) then
    iq := q @@ nproj @@ proj;
    cG1K := G1K^iq;
    isc,c := KIsConj(cG1K,G2K);
    if isc then
      x := iq*c;
      G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
      found := true; break;
    end if;
   end if; end for;
   if not found then return false,_; end if;
  end if;

  //now must generate subgroup containing normaliser of G2K.
  NKG2K := Normaliser(NNG2K, G2K);
  //NKG2K := Normaliser(NG2K, G2K);
  nelts := [];
  S := sub< Q | >;
  for q in Q do if not q in S then
    iq := q @@ nproj @@ proj;
    cG2K := G2K^iq;
    isc,c := KIsConj(cG2K,G2K);
    if isc then
      Append(~nelts,iq*c);
      S := sub<Q | S,q>;
    end if;
  end if; end for;

  NG2K := sub< BW | G2, NKG2K, nelts >; 
  isc,y := IsConjugate(NG2K,G1,G2);
  if not isc then return false, _; end if;
  assert oG1^(w*x*y) eq G2;
  return true, w*x*y;
end function;

BlocksNormaliser4 := function(G: sgp:=0, nsub:=G)
//normaliser in subgroup sgp of BW of G. nsub is known subgroup of normaliser
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  if sgp cmpeq 0 then sgp:=BW; end if;
  proj := hom<BW -> S8 | S8.1, S8.2, Id(S8), Id(S8) >;
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  S42 := DirectProduct(S4,S4);
  i1 := hom< S42->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6) >;
  i2 := hom< S42->K | K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >;
  i3 := hom< S42->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22) >;
  i4 := hom< S42->K | K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  e:=Id(S42);
  p1 := hom< K->S42 | S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e,e,e,e,e >;
  p2 := hom< K->S42 | e,e,e,e, S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e >;
  p3 := hom< K->S42 | e,e,e,e,e,e,e,e,S42.1, S42.2, S42.3, S42.4, e,e,e,e >;
  p4 := hom< K->S42 | e,e,e,e,e,e,e,e,e,e,e,e, S42.1, S42.2, S42.3, S42.4 >;
  //in hard cases projections onto S8xS8 are useful
  S42 := DirectProduct(S4,S4);
  S44 := DirectProduct(S42,S42);
  e2:=Id(S44);
  pp1 := hom< K->S44 | S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8,
                                           e2,e2,e2,e2,e2,e2,e2,e2 >;
  pp2 := hom< K->S44 | e2,e2,e2,e2,e2,e2,e2,e2,
            S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8 >;
  ii1 := hom< S44->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6), 
                       K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >; 
  ii2 := hom< S44->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22), 
                     K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  
  NP := Normaliser(S8,proj(G)) meet proj(sgp);
  GK := G meet K;

  NNG1 := Normaliser(S44, pp1(GK));
  NNG2 := Normaliser(S44, pp2(GK));
  NNGK := sub< K | ii1(NNG1), ii2(NNG2) >;
  KIsConj := function(S1,S2) //S1,S2 <= K
    oS1 := S1;
    isc, x1 := IsConjugate(S42, p1(S1), p1(S2) );
    if not isc then return false, _; end if;
    isc, x2 := IsConjugate(S42, p2(S1), p2(S2) );
    if not isc then return false, _; end if;
    isc, x3 := IsConjugate(S42, p3(S1), p3(S2) );
    if not isc then return false, _; end if;
    isc, x4 := IsConjugate(S42, p4(S1), p4(S2) );
    if not isc then return false, _; end if;

    x := i1(x1) * i2(x2) * i3(x3) * i4(x4);
    S1:=S1^x;

    isc, xx1 := IsConjugate(S44, pp1(S1), pp1(S2) );
    if not isc then return false, _; end if;
    isc, xx2 := IsConjugate(S44, pp2(S1), pp2(S2) );
    if not isc then return false, _; end if;

    xx := ii1(xx1) * ii2(xx2);
    S1:=S1^xx;
    isc, y := IsConjugate(NNGK, S1, S2);
    if not isc then return false, _; end if;
    assert oS1^(x*xx*y) eq S2;
    return true, x*xx*y;
  end function;
 
  reg := #proj(G) ne 1;
  if reg then Q, nproj := quo< NP | proj(G) >;
  else Q := NP;
  end if;
  //now must generate subgroup containing normaliser of GK.
  nelts := [ Sym(32) | g : g in Generators(nsub) | not g in K ];
  if not reg then EQ := {@ Id(Q) @} join {@ q: q in Q | q ne Id(Q) @}; end if;
  oQ := #Q;
  //do clever search through Q
  S := reg select sub< Q | [nproj(proj(g)):g in nelts] >
             else sub< Q | [proj(g):g in nelts] >;
  if #S eq 1 then
    reps := {2..oQ};
  else
    reps := reg select
    { 1^t : t in DoubleCosetRepresentatives(Q,S,S) } diff {1}
    else { Position(EQ,t): t in DoubleCosetRepresentatives(Q,S,S) } diff {1};
  end if;

  larger := true;
  while larger do
   larger := false;
   for i in reps do
    if not reg then q := EQ[i];
    else isc, q := IsConjugate(Q,1,i);
    end if;
    iq := reg select q @@ nproj @@ proj else q @@ proj;
    cGK := GK^iq;
    isc,c := KIsConj(cGK,GK);
    if isc then
      Append(~nelts,iq*c);
      S := sub<Q | S,q>;
      reps := reg select
           { 1^t : t in DoubleCosetRepresentatives(Q,S,S) } diff {1}
      else  { Position(EQ,t): t in DoubleCosetRepresentatives(Q,S,S) } diff {1};
      larger := true;
      break;
    end if;
   end for;
  end while;

  NKGK := Normaliser(NNGK, GK);
  NG2K := sub< BW | G, NKGK, nelts >; 
  return Normaliser(NG2K, G);
end function;

BlocksIsConjugate4 := function(G1,G2 : sgp:=0, nsub1:=G1, nsub2:=G2 )
//subgroups of BW - decide if conjugate in subgroup sgp of BW
//(sgp should only be used when G1,G2 <= K)
//nsub1, nsub2 are known subgroups of normalisers of G1,G2
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  if sgp cmpeq 0 then sgp:=BW; end if;
  mainp := MinimalPartitions(BW)[1];
  proj := hom<BW -> S8 | S8.1, S8.2, Id(S8), Id(S8) >;
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  S42 := DirectProduct(S4,S4);
  i1 := hom< S42->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6) >;
  i2 := hom< S42->K | K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >;
  i3 := hom< S42->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22) >;
  i4 := hom< S42->K | K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  e:=Id(S42);
  p1 := hom< K->S42 | S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e,e,e,e,e >;
  p2 := hom< K->S42 | e,e,e,e, S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e >;
  p3 := hom< K->S42 | e,e,e,e,e,e,e,e,S42.1, S42.2, S42.3, S42.4, e,e,e,e >;
  p4 := hom< K->S42 | e,e,e,e,e,e,e,e,e,e,e,e, S42.1, S42.2, S42.3, S42.4 >;
  //in hard cases projections onto S8xS8 are useful
  S42 := DirectProduct(S4,S4);
  S44 := DirectProduct(S42,S42);
  e2:=Id(S44);
  pp1 := hom< K->S44 | S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8,
                                           e2,e2,e2,e2,e2,e2,e2,e2 >;
  pp2 := hom< K->S44 | e2,e2,e2,e2,e2,e2,e2,e2,
            S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8 >;
  ii1 := hom< S44->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6), 
                       K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >; 
  ii2 := hom< S44->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22), 
                     K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  
  if #G1 ne #G2 then return false, _; end if;
  if G1 subset K and G2 subset K and #G1 lt 20000 and
                   #{Fix(g):g in G1} ne #{Fix(g): g in G2} then
    return false, _;
  end if;
  oG1 := G1;
  if proj(G1) ne proj(G2) then
    isc, w := IsConjugate(S8, proj(G1), proj(G2) );
    if not isc then return false, _; end if;
    w := w@@proj;
    G1 := G1^w;
    nsub1 := nsub1^w;
  else w := Id(BW);
  end if;
  NP := Normaliser(S8,proj(G2)) meet proj(sgp);

  G1K := G1 meet K; G2K := G2 meet K;

  NNG21 := Normaliser(S44, pp1(G2K));
  NNG22 := Normaliser(S44, pp2(G2K));
  NNG2K := sub< K | ii1(NNG21), ii2(NNG22) >;
  KIsConj := function(S1,S2) //S1,S2 <= K
    oS1 := S1;
    isc, x1 := IsConjugate(S42, p1(S1), p1(S2) );
    if not isc then return false, _; end if;
    isc, x2 := IsConjugate(S42, p2(S1), p2(S2) );
    if not isc then return false, _; end if;
    isc, x3 := IsConjugate(S42, p3(S1), p3(S2) );
    if not isc then return false, _; end if;
    isc, x4 := IsConjugate(S42, p4(S1), p4(S2) );
    if not isc then return false, _; end if;

    x := i1(x1) * i2(x2) * i3(x3) * i4(x4);
    S1:=S1^x;

    isc, xx1 := IsConjugate(S44, pp1(S1), pp1(S2) );
    if not isc then return false, _; end if;
    isc, xx2 := IsConjugate(S44, pp2(S1), pp2(S2) );
    if not isc then return false, _; end if;

    xx := ii1(xx1) * ii2(xx2);
    S1:=S1^xx;
    isc, y := IsConjugate(NNG2K, S1, S2);
    if not isc then return false, _; end if;
    assert oS1^(x*xx*y) eq S2;
    return true, x*xx*y;
  end function;
 
  isck,x := KIsConj(G1K,G2K);

  if isck then
    G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
    if G1 eq G2 then assert oG1^(w*x) eq G2; return true, w*x; end if;
  end if;

  if not isck then //look for element in Q mapping G1K to G2K
   //T := [ t^-1: t in RightTransversal(Q,S) ]; //left transversal
   T := DoubleCosetRepresentatives(NP, proj(nsub1), proj(nsub2));
   //if #T ge 8 then #T, "double coset reps"; end if;
   found := false;
   for q in T do if not IsIdentity(q) then
    //iq := reg select q @@ nproj @@ proj else q @@ proj;
    iq := q @@ proj;
    cG1K := G1K^iq;
    isc,c := KIsConj(cG1K,G2K);
    if isc then
      x := iq*c;
      G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
      found := true; break;
    end if;
   end if; end for;
   if not found then return false,_; end if;
   if oG1^(w*x) eq G2 then return true, w*x; end if;
  end if;

  //NKG2K := Normaliser(NNG2K, G2K);
  //NG2K := sub< BW | G2, NKG2K, nelts >; 
  NG2K := BlocksNormaliser4(G2K : sgp:=sgp, nsub:=nsub2 );
  isc,y := IsConjugate(NG2K,G1,G2);
  if not isc then return false, _; end if;
  assert oG1^(w*x*y) eq G2;
  return true, w*x*y;
end function;

BlocksIsConjugate4B := function(G1,G2)
//different (original) version - not for use when proj(G1) eq 1
//subgroups of BW - decide if conjugate in subgroup sgp of BW
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  proj := hom<BW -> S8 | S8.1, S8.2, Id(S8), Id(S8) >;
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  S42 := DirectProduct(S4,S4);
  i1 := hom< S42->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6) >;
  i2 := hom< S42->K | K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >;
  i3 := hom< S42->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22) >;
  i4 := hom< S42->K | K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  e:=Id(S42);
  p1 := hom< K->S42 | S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e,e,e,e,e >;
  p2 := hom< K->S42 | e,e,e,e, S42.1, S42.2, S42.3, S42.4, e,e,e,e,e,e,e,e >;
  p3 := hom< K->S42 | e,e,e,e,e,e,e,e,S42.1, S42.2, S42.3, S42.4, e,e,e,e >;
  p4 := hom< K->S42 | e,e,e,e,e,e,e,e,e,e,e,e, S42.1, S42.2, S42.3, S42.4 >;
  //in hard cases projections onto S8xS8 are useful
  S42 := DirectProduct(S4,S4);
  S44 := DirectProduct(S42,S42);
  e2:=Id(S44);
  pp1 := hom< K->S44 | S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8,
                                           e2,e2,e2,e2,e2,e2,e2,e2 >;
  pp2 := hom< K->S44 | e2,e2,e2,e2,e2,e2,e2,e2,
            S44.1, S44.2, S44.3, S44.4, S44.5, S44.6, S44.7, S44.8 >;
  ii1 := hom< S44->K | K!(1,2,3,4), K!(1,2), K!(5,6,7,8), K!(5,6), 
                       K!(9,10,11,12), K!(9,10), K!(13,14,15,16), K!(13,14) >; 
  ii2 := hom< S44->K | K!(17,18,19,20), K!(17,18), K!(21,22,23,24), K!(21,22), 
                     K!(25,26,27,28), K!(25,26), K!(29,30,31,32), K!(29,30) >;
  
  if #G1 ne #G2 then return false, _; end if;
  oG1 := G1;
  if proj(G1) ne proj(G2) then
    isc, w := IsConjugate(S8, proj(G1), proj(G2) );
    if not isc then return false, _; end if;
    w := w@@proj;
    G1 := G1^w;
  else w := Id(BW);
  end if;
  NP := Normaliser(S8,proj(G2));

  G1K := G1 meet K; G2K := G2 meet K;

  NNG21 := Normaliser(S44, pp1(G2K));
  NNG22 := Normaliser(S44, pp2(G2K));
  NNG2K := sub< K | ii1(NNG21), ii2(NNG22) >;
  KIsConj := function(S1,S2) //S1,S2 <= K
    oS1 := S1;
    isc, x1 := IsConjugate(S42, p1(S1), p1(S2) );
    if not isc then return false, _; end if;
    isc, x2 := IsConjugate(S42, p2(S1), p2(S2) );
    if not isc then return false, _; end if;
    isc, x3 := IsConjugate(S42, p3(S1), p3(S2) );
    if not isc then return false, _; end if;
    isc, x4 := IsConjugate(S42, p4(S1), p4(S2) );
    if not isc then return false, _; end if;

    x := i1(x1) * i2(x2) * i3(x3) * i4(x4);
    S1:=S1^x;

    isc, xx1 := IsConjugate(S44, pp1(S1), pp1(S2) );
    if not isc then return false, _; end if;
    isc, xx2 := IsConjugate(S44, pp2(S1), pp2(S2) );
    if not isc then return false, _; end if;

    xx := ii1(xx1) * ii2(xx2);
    S1:=S1^xx;
    isc, y := IsConjugate(NNG2K, S1, S2);
    if not isc then return false, _; end if;
    assert oS1^(x*xx*y) eq S2;
    return true, x*xx*y;
  end function;
 
  isck,x := KIsConj(G1K,G2K);

  if isck then
    G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
    if G1 eq G2 then assert oG1^(w*x) eq G2; return true, w*x; end if;
  end if;

  // Q, nproj := quo< NP | proj(G2) >;
  nproj, Q := RegularRepresentation(NP, proj(G2));

  //now must generate subgroup containing normaliser of G2K.
  nelts := [ Sym(32) | g : g in Generators(G2) | not g in K ];
  //do clever search through Q
  oQ := #Q;
  S := sub< Q | [nproj(proj(g)):g in nelts] >;
  if #S eq 1 then
    reps := {2..Degree(Q)};
  else
    reps := { 1^t : t in DoubleCosetRepresentatives(Q,S,S) } diff {1};
  end if;
  larger := true;
  while larger do
   larger := false;
   for i in reps do
    isc, q := IsConjugate(Q,1,i);
    iq := q @@ nproj @@ proj;
    cG2K := G2K^iq;
    isc,c := KIsConj(cG2K,G2K);
    if isc then
      Append(~nelts,iq*c);
      S := sub<Q | S,q>;
      reps := { 1^t : t in DoubleCosetRepresentatives(Q,S,S) } diff {1};
      larger := true;
      break;
    end if;
   end for;
  end while;

  if not isck then //look for element in Q mapping G1K to G2K
   T := [ t^-1: t in RightTransversal(Q,S) ]; //left transversal
   found := false;
   for q in T do if not IsIdentity(q) then
    iq := q @@ nproj @@ proj;
    cG1K := G1K^iq;
    isc,c := KIsConj(cG1K,G2K);
    if isc then
      x := iq*c;
      G1 := G1^x; G1K:=G1K^x; assert G1K eq G2K;
      found := true; break;
    end if;
   end if; end for;
   if not found then return false,_; end if;
   if oG1^(w*x) eq G2 then return true, w*x; end if;
  end if;

  NKG2K := Normaliser(NNG2K, G2K);
  NG2K := sub< BW | G2, NKG2K, nelts >; 
  //NG2K := BlocksNormaliser4(G2K);
  isc,y := IsConjugate(NG2K,G1,G2);
  if not isc then return false, _; end if;
  assert oG1^(w*x*y) eq G2;
  return true, w*x*y;
end function;

DesignUseful4 := function(M)
//M <= K. Decide whether we can usefully use design to find normaliser of M
//and test conjugacy with M. If so, returns blocksizes. If not return 0.
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  N := M meet KV4;
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  for i in [8,12,16,20,24] do
    blocks := { Fix(g) : g in N | #Fix(g) eq i };
    if #blocks eq 0 or #blocks eq Binomial(8,i div 4) then
      continue;
    end if;
    des := IncidenceStructure<32 | blocks>;
    if AutomorphismGroup(des) subset BW then
      return i;
    end if;
  end for;
  return 0;
end function;

DesignNormaliser4 := function(M,bs : nsub:=M )
//compute normaliser in BW of M using design with blocksize bs
//nsub is known subgroup of normaliser
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  N := M meet KV4;
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  ades := BW;
  blocks := { Fix(g) : g in N | #Fix(g) eq bs };
  des := IncidenceStructure<32 | blocks>;
  ades := AutomorphismGroup(des);
  assert ades subset BW;
  return BlocksNormaliser4(M: sgp:=ades, nsub:=nsub );
end function;

DesignIsConjugate4 := function(M1,M2,bs : nsub1:=M1, nsub2:=M2 )
//test conjugacy of M1,M2 in BW using design with blocksize bs
//nsub1, nsub2 are known subgroups of normalisers of M1, M2
  K :=sub< Sym(32) | (1,2,3,4), (1,2), (5,6,7,8), (5,6),
                     (9,10,11,12), (9,10), (13,14,15,16), (13,14),
                     (17,18,19,20), (17,18), (21,22,23,24), (21,22),
                     (25,26,27,28), (25,26), (29,30,31,32), (29,30) >; 
  KV4 := pCore(K,2); 
  N1 := M1 meet KV4; N2 := M2 meet KV4;
  blocks1 := { Fix(g) : g in N1 | #Fix(g) eq bs };
  blocks2 := { Fix(g) : g in N2 | #Fix(g) eq bs };
  des1 := IncidenceStructure<32 | blocks1>;
  des2 := IncidenceStructure<32 | blocks2>;
  isit, u := IsIsomorphic(des1,des2 : AutomorphismGroups:="Right");
  if not isit then return false, _; end if;
  u := Sym(32)![ Position(Points(des2),u(i)) : i in [1..32] ];
  ades2 := AutomorphismGroup(des2);
  isc, c := BlocksIsConjugate4(M1^u,M2:
                                  sgp:=ades2, nsub1:=nsub1^u, nsub2:=nsub2 );
  if isc then
      return true, u*c;
  end if;
  return false, _;
end function;
 
DesignNormaliser2 := function(G,H)
//normaliser of H in G using designs - use fixed points of elements of order 2
  N := pCore(H,2);
  ot := { x: x in N | Order(x) eq 2 };
  fot := { #Fix(t) : t in ot } diff {0};
  if #fot eq 0 then return Normaliser(G,H); end if;
  blocks := { Fix(t) : t in ot | #Fix(t) eq Min(fot) };
  des := IncidenceStructure<32 | blocks>;
  ades := AutomorphismGroup(des) meet G;
  return Normaliser(ades, H);
end function;

DesignIsConjugate2 := function(G,H1,H2)
  N1 := pCore(H1,2); N2 := pCore(H2,2);
  ot1 := { x: x in N1 | Order(x) eq 2 };
  ot2 := { x: x in N2 | Order(x) eq 2 };
  if #ot1 ne #ot2 then return false,_; end if;
  fot1 := { #Fix(t) : t in ot1 } diff {0};
  fot2 := { #Fix(t) : t in ot2 } diff {0};
  if fot1 ne fot2 then return false,_; end if;
  if fot1 eq {} then return IsConjugate(G,H1,H2); end if;
  blocks1 := { Fix(t) : t in ot1 | #Fix(t) eq Min(fot1) };
  blocks2 := { Fix(t) : t in ot2 | #Fix(t) eq Min(fot2) };
  des1 := IncidenceStructure<32 | blocks1>;
  des2 := IncidenceStructure<32 | blocks2>;
  isit, u := IsIsomorphic(des1,des2 : AutomorphismGroups:="Right");

  if not isit then return false,_; end if;
  u := Sym(32)![ Position(Points(des2),u(i)) : i in [1..32] ];
  H1c := H1^u;
  ades := AutomorphismGroup(des2);
  isit, v := IsConjugate(ades,H1c,H2);
  if not isit then return false,_; end if;
  assert H1^(u*v) eq H2;
  // but is u*v in G ?
  return true,u*v;
end function;

DesignIsConjugateProj2 := function(G,H1,H2,proj)
//version where we project designs onto {1..16}
//phi is projection C2 wr S16 -> S16
  N1 := pCore(H1,2); N2 := pCore(H2,2);
  ot1 := { x: x in N1 | Order(x) eq 2 };
  ot2 := { x: x in N2 | Order(x) eq 2 };
  if #ot1 ne #ot2 then return false,_; end if;
  fot1 := { #Fix(t) : t in ot1 } diff {0};
  fot2 := { #Fix(t) : t in ot2 } diff {0};
  if fot1 ne fot2 then return false,_; end if;
  if #fot1 eq 0 then return IsConjugate(G,H1,H2); end if;
  blocks1 := { Fix(t) : t in ot1 | #Fix(t) eq Min(fot1) };
  blocks2 := { Fix(t) : t in ot2 | #Fix(t) eq Min(fot2) };
  blocks1p := { { (t+1) div 2 : t in b }  : b in blocks1 };
  blocks2p := { { (t+1) div 2 : t in b }  : b in blocks2 };
  des1p := IncidenceStructure<16 | blocks1p >;
  des2p := IncidenceStructure<16 | blocks2p >;
  isit, u := IsIsomorphic(des1p,des2p : AutomorphismGroups:="Right");
  if not isit then return false,_; end if;
  u := Sym(16)![ Position(Points(des2p),u(i)) : i in [1..16] ];
  u := u@@proj;
  H1c := H1^u;
  adesp := AutomorphismGroup(des2p) @@ proj;
  isit, v := IsConjugate(adesp,H1c,H2);
  if not isit then return false,_; end if;
  assert H1^(u*v) eq H2;
  return true,u*v;
end function;

Prim32Identify := function(G)
/* Identify primitive group of degree 32.
 * See Trans32Identify below for description of returned values.
 */
  assert Degree(G) eq 32 and IsPrimitive(G);
  X := Sym(32);
  if IsSymmetric(G) then return  <32,7,0,0>, Id(X); end if;
  if IsAlternating(G) then return  <32,6,0,0>, Id(X); end if;
  gps := read_file_eval("b32gps");
  og := #G;
  if og eq 29760 then //PGL(2,31)
    isit,g:=IsConjugate(X,G,gps[5]); assert isit;
    return <32,5,0,0>, g;
  end if;
  if og eq 14880 then //PSL(2,31)
    isit,g:=IsConjugate(X,G,gps[4]); assert isit;
    return <32,4,0,0>, g;
  end if;
  //other 3 are affine.
  k := og eq 319979520 select 3 else og eq 4960 select 2 else 1;
  S := gps[k];
  NG := pCore(G,2); NS := pCore(S,2); 
  if k eq 3 then
    isit,g:=IsConjugate(X,NG,NS); assert isit;
    return <32,k,0,0>, g;
  end if;
  MG := pCore(Stabiliser(G,1),31); KG := sub<G | NG,MG>;
  MS := pCore(Stabiliser(S,1),31); KS := sub<S | NS,MS>;
  isit,g:=IsConjugate(X,KG,KS); assert isit;
  return <32,k,0,0>, g;
end function;

Trans32K4Identify := function(G)
  S8 := sub<Sym(8) | (1,2,3,4,5,6,7,8), (1,2) >;
  S4 := sub<Sym(4) | (1,2,3,4), (1,2) >;
  BW := WreathProduct(S4, S8);
  proj := hom<BW -> S8 | S8.1, S8.2, Id(S8), Id(S8) >;
  K := Kernel(proj);
  gps := read_file_eval("b4gps");
  M4 := read_file_eval("M4");
  Kno4 := read_file_eval("Kno4");
  if #G le 2^22 then
      invs := read_file_split("invs4");
      use_invs := true;
  else
    use_invs := false;
  end if;
  P := [ p: p in MinimalPartitions(G) | #Representative(p) eq 4 ];
  //choose the ones with smallest kernel.
  min := Min( [#BlocksKernel(G,p) : p in P ] );
  P := [ p: p in P | #BlocksKernel(G,p) eq min ];
  Knos := [**];
  for p in P do
    //identify particular kernel
    u := Sym(32)!&cat[ [x: x in b] : b in p ];
    GG := G^(u^-1);
    KGG := K meet GG;
    for mct in [1..#M4] do
      M := M4[mct];
      if #M eq #KGG then
        k := Max([i: i in [1..#gps] | Kno4[i] eq mct]); 
        //so gps[k] is in normalizer of M
        bs := DesignUseful4(M);
        if bs ne 0 then
         isc, v := DesignIsConjugate4(KGG, M, bs :nsub1:=GG, nsub2:=gps[k]);
        else isc, v := BlocksIsConjugate4(KGG, M :nsub1:=GG, nsub2:=gps[k]);
        end if;
        if isc then Append(~Knos,<mct,u^-1*v>); break; end if;
      end if;
    end for;
  end for;
  minmct := Min( [t[1]: t in Knos] );
  M := M4[minmct];
  inds := [i: i in [1..#gps] | Kno4[i] eq minmct and #G eq #gps[i]];
  k := Max(inds); 
  //N := BlocksNormaliser4(M : nsub:=gps[k]);
  for ct in [1..#P] do if Knos[ct][1] eq minmct then
    v := Knos[ct][2];
    GG := G^v;
    if use_invs then
      invsG := classes_invar(G);
    end if;
    for i in inds do
      if use_invs and (eval invs[i]) cmpne invsG then
        isc:=false;
      else isc,w := BlocksIsConjugate4B(GG, gps[i]);
      end if;
      if isc then
        assert G^(v*w) eq gps[i];
        return <4, i, 0, 0>, v * w;
      end if;
    end for;
  end if; end for;
end function;

Trans32K2Identify := function(G)
  S16 := Sym(16);
  BW, _, _, proj := WreathProduct(Sym(2), S16);
  // proj := hom< BW->S16 | S16.1, S16.2, Id(S16) >; 
  K := Kernel(proj);
  M2 := read_file_eval("M2");
  P := [ p: p in MinimalPartitions(G) | #Representative(p) eq 2 ];
  //choose the ones with smallest kernel.
  min := Min( [#BlocksKernel(G,p) : p in P ] );
  exp := Valuation(min,2);
  sym := exp in {0,1,15,16};
  P := [ p: p in P | #BlocksKernel(G,p) eq min ];
  Knos := [**];
  for p in P do
    //identify particular kernel
    u := Sym(32)!&cat[ [x: x in b] : b in p ];
    GG := G^(u^-1);
    if sym then
      Append(~Knos,<1,u^-1>);
    else
      KGG := K meet GG;
      for mct in [1..#M2[exp]] do
        M := M2[exp][mct];
        isc, v := DesignIsConjugateProj2(BW, KGG, M, proj);
        if isc then Append(~Knos,<mct,u^-1*v>); break; end if;
      end for;
    end if;
  end for;
  minmct := Min( [t[1]: t in Knos] );
  M := exp eq 0 select sub<Sym(32)|> else M2[exp][minmct];
  NM := DesignNormaliser2(BW,M) @ proj;
  filename :=
        "tno2K" cat IntegerToString(exp) cat "g" cat IntegerToString(minmct);
  tnos := read_file_eval(filename);
  invar_limit := 2^22;
  if #G le invar_limit then
    filename :=
      "invs2K" cat IntegerToString(exp) cat "g" cat IntegerToString(minmct);
    invs := read_file_split(filename);
  end if;
  filename :=
        "b2gpsK" cat IntegerToString(exp) cat "g" cat IntegerToString(minmct);
  gps := read_file_split(filename);
  if not sym then
    tno := exp le 8 select exp else 16-exp;
    filename :=
        "trans2K" cat IntegerToString(tno) cat "g" cat IntegerToString(minmct);
    transgps := read_file_eval(filename);
  end if;
  tgps := {@@}; norms := []; //for storing subgps of S16 and normalizers
  conj16 := 0;
  conj32 := 0;
  for ct in [1..#P] do if Knos[ct][1] eq minmct then
    u := Knos[ct][2];
    GG := G^u;
    assert GG subset BW and GG meet K eq M;
    PG := proj(GG);
    z16 := Parent(Cputime())!0;
    z32 := Parent(Cputime())!0;
    if sym then
      tno := TransitiveGroupIdentification(PG);
      tgp := TransitiveGroup(16,tno);
      conj16 +:= 1;
      z := Cputime();
      isc, v := IsConjugate(S16, PG, tgp); assert isc; 
      z16 +:= Cputime(z);
    else
      for t in [1.. #transgps] do
        tgp := transgps[t];
	conj16 +:= 1;
        z := Cputime();
        isc, v := IsConjugate(NM, PG, tgp);
        z16 +:= Cputime(z);
        if isc then tno:=t; break; end if;
      end for;
    end if;
    if not isc then continue; end if;
    v := v@@proj;
    GG := GG^v;
    inds := [ i: i in [1..#tnos] | tnos[i] eq tno ];
    // "#inds", #inds;
    if #inds gt 0 then
       if not tgp in tgps then
          Include(~tgps, tgp);
          Append(~norms, Normaliser(Sym(16),tgp)@@proj );
       end if;
       N := norms[ Position(tgps,tgp) ];
       use_invar := #GG le invar_limit and #inds gt 1;
       if use_invar then
	/* compute the invariant for G */
	invsG := classes_invar(GG);
       end if;
       compute_S_data := true;
       for i in inds do
         if use_invar and eval_wrap(invs[i]) ne invsG then
           isc := false;
         else 
	   if compute_S_data then
	    S1 := Sylow(GG, 2);
	    k1 := Transitivity(S1);
	    so1 := {* t[1]:t in OrbitRepresentatives(BasicStabilizer(S1, k1+1)) *};
	    P1:=PCGroup(S1);
	    e1 := Exponent(P1);
	    compute_S_data := false;
	   end if;
	   gi := eval_wrap(gps[i]);
	   S2 := Sylow(gi,2);
           P2:=PCGroup(S2);
	   k2 := Transitivity(S2);
	   so2 := {*t[1]:t in OrbitRepresentatives(BasicStabilizer(S2,k2+1))*};
	   if k1 ne k2 or so1 ne so2 then
	     isc := false;
           elif not [#l: l in LowerCentralSeries(P1)] eq
                  [#l: l in LowerCentralSeries(P2)] then
//"lcs diff";
             isc := false;
	   elif  pClass(P1) ne pClass(P2) or
	     [#l:l in pCentralSeries(P1,2)] ne [#l:l in pCentralSeries(P2,2)]
	   then
//"l2cs diff";
	     isc := false;
	   elif e1 ne Exponent(P2) then
	     isc := false;
           elif [#Agemo(P1,j):j in[1..Ilog(2,e1)-1]] ne
		[#Agemo(P2,j):j in [1..Ilog(2,e1)-1]] then
//"agemo diff";
             isc := false;
           elif not ClassesData(P1) eq ClassesData(P2) then
//"classes diff";
             isc := false;
           else
//GG:Magma; gi:Magma;
	     conj32 +:= 1;
	     z := Cputime();
	     isc, w := IsConjugate(N, GG, gi );
//isc;
	     z32 +:= Cputime(z);
           end if;
         end if;
         if isc then
           assert G^(u*v*w) eq gi;
	   //"conj tests at deg 16", conj16, z16, "and 32", conj32, z32;
           return <2, exp, minmct, i>, u*v*w;
         end if;
       end for;
    end if;
  end if; end for;
end function;

intrinsic Trans32Identify(G::GrpPerm) -> Tup, GrpPermElt
{Return identifying information for a transitive permutation group of
degree 32, and a conjugating element}

/* Identify transitive group of degree 32.
 * Return a 4-tuple of integers and g in Sym(32) conjugating G to standard
 * copy.
 * First component mbs of 4-tuple is size of blocks of minimal partition,
 * with mbs=16 for a primitive group.
 * For primitive groups, second component is j <= 7 such that G is conjugate
 * to Primitivegroup(16,j);
 */

    require Degree(G) eq 32 and IsTransitive(G):
	"Group must be transitive of degree 32";

    if IsPrimitive(G) then
	return Prim32Identify(G);
    end if;

    P := MinimalPartitions(G);
    mbs := Min( [#Representative(p): p in P] );
    P := [ p: p in P | #Representative(p) eq mbs ];

    og := #G;

    if mbs ge 8 then
	assert #P eq 1;

	u := Sym(32)!&cat[ [x: x in b] : b in P[1] ];
	GG := G^(u^-1);
	filename := "b" cat IntegerToString(mbs) cat "gps";
	gps := read_file_eval(filename);
	proc := mbs eq 16 select BlocksIsConjugate16 else BlocksIsConjugate8;
	for ct in [1..#gps] do
	    if og eq #gps[ct] then
	       isit, h := proc(GG,gps[ct]);
	       if isit then return <mbs,ct,0,0>, u^-1 * h; end if;
	    end if;
	end for; 
    end if; 

    if mbs eq 4 then return Trans32K4Identify(G); end if;

    if mbs eq 2 then return Trans32K2Identify(G); end if;

end intrinsic;
