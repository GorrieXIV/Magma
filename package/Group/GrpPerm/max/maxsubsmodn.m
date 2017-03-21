freeze;

import "../../GrpMat/LMG/radquot.m" : GetRadquotPermGp;
import "extend1submodn.m" :  ExtendOneSubgroupModN;

MaxSubsModN := function(G,N : Print:=0, Presentation:=false)
/* Find maximal subgroups of permutation or matrix group G that contain normal
 * subgp N
 */
  local RF, Q, pQ, R, QN, NtoQ, QmodN, GtoQmodN, M, mm, f, phi, s, pres,
        prestosub, mods, relim, MM, Res, ss, L, subs, ans, t, u, NR, LG; 
  RF := recformat<order, length, subgroup, presentation, index, modifiers>;
  //The modifiers are elements of N outside of radical with which we multiply
  //relators to get values in radical.
  Q, pQ, R := RadicalQuotient(G);
  QN := pQ(N);
  NtoQ := hom< N->Q | [ pQ(N.i) : i in [1..Ngens(N)]] >;
  //we need a perm rep of Q/QN.
  if Print gt 1 then
     "  Getting perm rep of radical quotient mod N";
  end if;
  QmodN, GtoQmodN := GetRadquotPermGp(G,N);
  if Print gt 1 then
    "  Found perm rep of degree", Degree(QmodN);
  end if;
  M := MaximalSubgroupsH(QmodN : Print:=Print, Presentation:=true);
  //need QmodN itself
  mm := rec <RF | subgroup:=QmodN, length:=1, order := #QmodN >;
  f,phi := FPGroup(QmodN:StrongGenerators:=true);
  mm`presentation := f;
  mm`subgroup := sub< QmodN | [phi(f.i) : i in [1..Ngens(f)] ] >;
  Append(~M,mm);
  // now calculate modifiers
  if Print gt 2 then
    "    Calculating modifiers";
  end if;
  if Presentation then
    MM := [];
    for m in M do
      s := m`subgroup;
      //if Ngens(s) eq 0 then s := sub<s|s.0>; end if;
      pres := m`presentation;
      mm := rec< RF | length:=m`length, order:=m`order, index:=Index(QmodN,s),
                      presentation:=pres>;
      s := sub<G | [s.i @@ GtoQmodN : i in [1..Ngens(s)]] >;
      mm`subgroup := s;
      pres := m`presentation;
      prestosub := Ngens(s) eq 0 select hom< pres->s | [Id(s)] >
      else hom< pres->s | [s.i : i in [1..Ngens(s)]] >;
      mods := [];
      for rel in Relations(pres) do
        relim := (LHS(rel) * RHS(rel)^-1) @ prestosub @ pQ;
        assert relim in QN;
        Append(~mods, (relim^-1) @@ NtoQ);
      end for;
      mm`modifiers := mods;
      Append(~MM,mm);
    end for;
  else
    MM := [];
    Res := [];
    for m in M do
      s := m`subgroup;
      //if Ngens(s) eq 0 then s := sub<s|s.0>; end if;
      if s eq QmodN then
        s := sub<G | [s.i @@ GtoQmodN : i in [1..Ngens(s)]] >;
        mm := rec< RF | length:=m`length, order:=m`order, index:=1,
                         presentation:=m`presentation>;
        mm`subgroup := s;
        pres := m`presentation;
        prestosub := Ngens(s) eq 0 select hom< pres->s | [Id(s)] >
        else hom< pres->s | [s.i : i in [1..Ngens(s)]] >;
        mods := [];
        for rel in Relations(pres) do
          relim := (LHS(rel) * RHS(rel)^-1) @ prestosub @ pQ;
          assert relim in QN;
          Append(~mods, (relim^-1) @@ NtoQ);
        end for;
        mm`modifiers := mods;
        Append(~MM,mm);
      else
        mm := rec< RF | length:=m`length, index:=m`length >;
        s := m`subgroup;
        ss := sub< G | [s.i @@ GtoQmodN : i in [1..Ngens(s)]], N, R >;
        if Type(ss) eq GrpPerm then ReduceGenerators(~ss); end if;
        mm`subgroup := ss;
        mm`order := m`order * #R;
        if assigned mm`presentation then delete mm`presentation; end if;
        if assigned mm`modifiers then delete mm`modifiers; end if;
        Append(~Res,mm);
      end if;
    end for;
  end if;
  if Print gt 2 then
    "    Got modifiers";
  end if;

  //find maximal elementary abelian series above N
  if Type(G) eq GrpPerm then
    L := ElementaryAbelianSeries(G, N meet R);
  else //function does not exist for type GrpMat
    NR := N meet R;
    LG := ElementaryAbelianSeries(G);
    L := [ NR ];
    for i in [#LG-1 .. 1 by -1] do
      s := sub< G | LG[i], NR >;
      if s ne L[#L] then Append(~L,s); end if;
    end for; 
    L := Reverse(L);
  end if;
  for i in [1..#L-1] do
    if Print ge 1 then
      print "Lifting through layer",i,"of size",a,"^",b where
       a:=c[1][1] where b:=c[1][2] where c:= Factorisation(Index(L[i],L[i+1]));
    end if;
    if Presentation then
      M := [];
      for m in MM do
        M cat:=
         ExtendOneSubgroupModN(G,N,pQ,NtoQ,L[i],L[i+1],m,#G,true: Print:=Print,
                                                             Maximal:=true);
      end for;
      MM := M;
    else
      assert #MM eq 1;
      M :=  ExtendOneSubgroupModN(G,N,pQ,NtoQ,L[i],L[i+1],MM[1],#G,true:
                                               Print:=Print, Maximal:=true);
      if Print gt 1 then
        print #M,"subgroups after lifting through layer", i;
      end if;
      MM := [];
      for m in M do
        mm := m;
        if m`order * #L[i+1] * #QN  eq #G then
            Append(~MM, mm);
        else
            s := sub<G|m`subgroup,L[i+1]>;
            if Type(s) eq GrpPerm then ReduceGenerators(~s); end if;
            mm`subgroup := s;
            mm`order *:= #L[i+1];
            if assigned mm`presentation then delete mm`presentation; end if;
            if assigned mm`modifiers then delete mm`modifiers; end if;
            Append(~Res, mm);
        end if;
      end for;
    end if;
  end for;

  subs := Presentation select MM else Res;
  //adjoin N
  ans := [];
  for s in subs do
    t := s;
    u := s`subgroup;
    for g in Generators(N) do if not g in u then
      u := sub< G | u, g >;
    end if; end for;
    t`subgroup := u; t`order := #u;
    if t`subgroup ne G then Append(~ans,t); end if;
  end for;
  return ans;
end function;
