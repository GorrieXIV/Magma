freeze;


step_fmt := recformat<Ai : GrpPerm,
                      Aim1:GrpPerm, // not bound for 1st elt
		      T,
		      mT,        // the transversal and the map returned
                      last: Rec, // the record from the previous step.
                                 // not bound for the 1st elt in chain
                      Di : SeqEnum, // double coset reps for Ai G U
                      St : SeqEnum, // The stabilzers (as chains)
		      I  : SetIndx, // last`Di * last`T
                      S3 : List, // tuples <d,u> such that
                                 // for all i in [1..#last`Di*last`T]
				 // (or without last`T - depending on step up
				 //  or down...)
                                 //   S3[i][1] is the canonical rep
                                 //   S3[i][2] is the fusing elt.
                      g, s 
>;

function GetTransversalChain(U)
//intrinsic GetTransversalChain(U::GrpPerm) -> List
//{}
  c := [U];
  while #U ne 1 do
    i := Support(U);
    U := Stabilizer(U, Representative(i));
    Append(~c, U);
  end while;
  C := [**];
  for i in [1..#c-1] do
    Append(~C, <c[i], Transversal(c[i], c[i+1])>);
  end for;
  Append(~C, <c[#c], {@c[#c].0@}>);
  return C;
end function;

intrinsic InternalGetStart(G::GrpPerm, U::GrpPerm) -> Rec
{}
  r := rec<step_fmt |
               Ai := G,
	       T := {@G.0@},
	       mT := map<G -> G | x:-> G.0>,
	       I := {@G.0@},
	       S3 := [*<G.0, G.0>*],
	       Di := [G.0],
               St := [GetTransversalChain(U)]
     >;
  g,s := NewEnv(["F"]);
  r`g := g;
  r`s := s;
  s("F", false);
  return r;
end intrinsic;

intrinsic Reverse(L::List) -> List
{}
  l := [**];
  for i := #L to 1 by -1 do
    Append(~l, L[i]);
  end for;
  return l;
end intrinsic;

intrinsic InternalInduceChain(V::GrpPerm, T::Map, C::List:Conj := false) -> List
{}
  //T is a transversal map for C[1][1]/V
  c := [*<sub<V|>, {@V.0@}>*];
  if Conj cmpeq false then
    Conj := C[1][1].0;
  end if;
  assert V subset C[1][1];
  last_tUU := [C[#C][1].0];
  tUU := ChangeUniverse(last_tUU, C[1][1]);
  tU := {T((Universe(Codomain(T)).0)^Conj^-1)};
  for i := #C-1 to 1 by -1 do
    U := C[i][1] meet V;
    tUU := ChangeUniverse(last_tUU, C[i][1]);
    tV := [];
    ChangeUniverse(~last_tUU, C[i][1]);
    for t in last_tUU, s in C[i][2] do
      x := t*s;
      if x in V then
        Append(~tV, x);
        if #tU*#tV eq #last_tUU*#C[i][2] then
          break;
        end if;
      else
        xx := T(x^Conj^-1);
        if xx notin tU then
          Include(~tU, xx);
          Append(~tUU, x);
          if #tU*#tV eq #last_tUU*#C[i][2] then
            break;
          end if;
        end if;
      end if;
    end for;
    assert #tV eq Index(U, c[#c][1]);
    assert #tU eq Index(C[i][1], U);
    assert #tU*#tV eq #last_tUU*#C[i][2];
    
    last_tUU := tUU;
    if #tV ne 1 then
      Append(~c, <U, tV>);
    end if;
  end for;
  return Reverse(c), tUU;
end intrinsic;

function StepDown(A, U, R)
//intrinsic StepDown(A::GrpPerm, U::GrpPerm, R::Rec) -> Rec
//{}
  r := rec<step_fmt | 
              Ai := A,
	      Aim1 := R`Ai,
	      last := R>;
  g,s := NewEnv(["F"]);
  r`g := g;
  r`s := s;
  s("F", false);
  
  T, mT := Transversal(R`Ai, A);
  r`T := T;
  r`mT := mT;
  Di := [];
  S3 := [**];
  St := [];
  I := {@@};
  for a in R`Di do
    tmp := {};
    for t in T do
      if t notin tmp then
	st := R`St[Position(R`Di, a)];
	S1 := U meet A^(t*a);
	if GetAssertions() gt 0 then
	  S2 := U meet R`Ai^a;
	  assert S1 subset S2;
	  assert st[1][1] eq S2;
	  assert S2 eq U meet R`Ai^(t*a);
	end if;
	st, Sta := InternalInduceChain(S1, mT, st:Conj := t*a);
	if GetAssertions() gt 0 then
	  assert #Sta  eq Index(S2, S1);
	  _, ss := Transversal(S2, S1);
	  assert #{ss(x) : x in Sta} eq #Sta;
	end if;
        d := t*a;
	Append(~Di, d);
        Append(~St, st);
        for u in Sta do
          tt := mT(d*u*a^-1);
          Include(~tmp, tt);
          Include(~I, tt*a);
          Append(~S3, <d, u>);
          assert tt*a*u^-1*d^-1 in A;
        end for;
      end if;
    end for;
    assert T eq tmp;
  end for;
  r`Di := Di;
  r`I := I;
  r`S3 := S3;
  r`St := St;
  return r;
end function;

intrinsic GetRep(g::GrpPermElt, R::Rec) -> GrpPermElt, GrpPermElt
  {}

  F := R`g("F");
  if F cmpne false then
    R := F[#F];
  else
    F := [];
    RR := R;
    while assigned R`last do
      Append(~F, R);
      R := R`last;
    end while;
    RR`s("F", F);
  end if;
 
  dim1 := R`Ai.0;
  uim1 := dim1;
  for i := #F to 1 by -1 do
    R := F[i];
    if #R`Ai lt #R`Aim1 then
      t := R`mT(g*(dim1*uim1)^-1);
      p := Position(R`I, t*dim1);
      d := R`S3[p][1];
      u := R`S3[p][2];
    else
      p := Position(R`I, dim1);
      d := R`S3[p][1];
      u := R`S3[p][2];
    end if;
    dim1 := d;
    uim1 := u*uim1;
  end for;
  return dim1, uim1;
end intrinsic;


function StepUp(A, U, R) 
//intrinsic StepUp(A::GrpPerm, U::GrpPerm, R::Rec) -> Rec
//{}
  r := rec<step_fmt | 
              Ai := A,
	      Aim1 := R`Ai,
	      last := R>;
  g,s := NewEnv(["F"]);
  r`g := g;
  r`s := s;
  s("F", false);
  
  T, mT := Transversal(A, R`Ai);
  r`T := T;
  r`mT := mT;
  Di := [];
  St := [];
  I := {@@};
  S3 := [**];
 
  seen := {@@};
  data := [];
  cls := {@@};
  cls_data := [];
  for b in R`Di do
    if b in cls then
      p := Position(cls, b);
      rep := cls_data[p][1];
      rep_u := cls_data[p][2];
      new := false;
    else
      rep := false;
      new := true;
    end if;

    tt := [];
    for t in T do
      if not new and not IsIdentity(t) then
        continue;
      end if;
      tb := t*b;
      bt, ut := GetRep(tb, R);
      assert tb*ut^-1*bt^-1 in r`Aim1;
      assert bt in R`Di;
      if rep cmpeq false then
        rep := bt;
        rep_u := ut;
      end if;
      if bt notin cls then
        Include(~cls, bt);
        Append(~cls_data, <rep, rep_u*ut^-1>);
      end if;
      if bt eq rep then
        Append(~tt, ut*rep_u^-1);
      end if;
      if IsIdentity(t) then
        Include(~I, b);
        Append(~S3, <rep, rep_u*ut^-1>);
      end if;
    end for;
    if new then
      Append(~Di, rep);
      Append(~St, [*<A^rep meet U, tt>*] cat R`St[Position(R`Di, rep)]);
      assert Index(St[#St][1][1], St[#St][2][1]) eq #tt;
    end if;
  end for;

  r`Di := Di;
  r`I := I;
  r`St := St;
  r`S3 := S3;
  return r;
end function;

intrinsic YoungSubgroupLadder(p::SeqEnum:Full := false) -> SeqEnum
  {}
  s := &+ p[2..#p];
  if Full cmpeq false then
    Full := &+ p;
  end if;
  if s eq 0 then
    return [YoungSubgroup([p[1]]: Full := Full)];
  end if;
  if p[2] eq 1 then
    pp := [p[1]+1] cat p[3..#p];
    L := YoungSubgroupLadder(pp:Full := Full);
    Append(~L, YoungSubgroup(p : Full := Full));
  else
    pp := [p[1]+1, p[2]-1] cat p[3..#p];
    L := YoungSubgroupLadder(pp:Full := Full);
    pp := [p[1], 1, p[2]-1] cat p[3..#p];
    Append(~L, YoungSubgroup(pp:Full := Full));
    Append(~L, YoungSubgroup(p:Full := Full));
  end if;
  return L;
end intrinsic;  

intrinsic ProcessLadder(L::SeqEnum, G::GrpPerm, U::GrpPerm) -> Rec
  {}
  vprintf DoubleCosets, 1: 
    "Computing double coset data for groups of order %o \\ %o / %o\n",
      #L[#L], #G, #U;
  vprintf DoubleCosets, 1: 
    "Using ladder of length %o with steps %o\n", #L,
      [#L[i]/ #L[i+1] : i in [1..#L-1]];
  r := InternalGetStart(G, U);
  H := L[1];
  for i in [2..#L] do
    if H subset L[i] then
      vprintf DoubleCosets, 2: "Step %o is UP by %o\n", i, Index(L[i], H);
      r := StepUp(L[i], U, r);
    else
      vprintf DoubleCosets, 2: "Step %o is DOWN by %o\n", i, Index(H, L[i]);
      r := StepDown(L[i], U, r);
    end if;
    vprintf DoubleCosets, 2: "Now at %o double cosets\n", #r`Di;
    H := L[i];
  end for;
  return r;
end intrinsic;

intrinsic DeleteData(r::Rec)
  {}
  repeat
    r`s("F", false);
    if assigned r`last then
      s := r`last;
      delete r`last;
      delete r;
      r := s;
    else
      break;
    end if;
  until false;
end intrinsic;



/*
<example>
  Attach("/home/claus/Magma/GrpPerm/DblCoset.m");
  G := Sym(8);
  U := MaximalSubgroups(G:IsTransitive)[2]`subgroup;
  H := MaximalSubgroups(G:IsTransitive)[3]`subgroup;
  Index(G, U);
  Index(G, H);
  V := MaximalSubgroups(U)[1]`subgroup;
  z := MaximalSubgroups(G)[6]`subgroup;
  r1 := InternalGetStart(G, H);
time r2 := StepDown(z, H, r1);
time r3 := StepDown(z meet U, H, r2);
time r4 := StepUp(U, H, r3);
time c := DoubleCosetRepresentatives(G, U, H);
GetRep(c[1], r4);
GetRep(c[2], r4);
GetRep(c[3], r4);


L := YoungSubgroupLadder([14,14]);
gs := GSet(Sym(8), Subsets({1..8}, 2));
H := ActionImage(Sym(8), gs);
_, h := StandardGroup(H);
H := h(H);
r := ProcessLadder(L, Sym(28), H);

L := YoungSubgroupLadder([7,8]);
gs := GSet(Sym(6), Subsets({1..6}, 2));
H := ActionImage(Sym(6), gs);
_, h := StandardGroup(H);
H := h(H);
G := Sym(15);
r := ProcessLadder(L, G, H);


</example>

*/
