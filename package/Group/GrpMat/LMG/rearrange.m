freeze;

import "autinfo.m": InitialiseAutInfoC, InitialiseAutInfoG, ProcessAutC,
 ProcessAutG, AutTuple;
import "initialize.m": NameChange;

CanCalculateAutGpAndMaxSubs := function(name)
//to test whether we can apply general automorphism function to socle factor
  local s,r,q;
  s:=name[1]; r:=name[2]; q:=name[3];
  if s eq 1 then //L(r+1,q)
    if r lt 7 then return true; end if;
    if q eq 2 and r lt 14 then return true; end if;
  elif s eq 3 and r eq 2 then //S(4,q)
    return true;
  elif s eq 10 and r lt 4 then //U(3,q), U(4,q)
    return true;
  elif s eq 17 and r lt 1000 then //A_n
    return true;
  elif name in
   { <2,3,3>, //O(7,3)
     <2,3,5>, //O(7,5)
     <2,4,3>, //O(9,3)
     <3,3,2>, //S(6,2)
     <3,3,3>, //S(6,3)
     <3,3,4>, //S(6,4)
     <3,3,5>, //S(6,5)
     <3,4,2>, //S(8,2)
     <3,4,3>, //S(8,3)
     <3,5,2>, //S(10,2)
     <3,6,2>, //S(12,2)
     <4,4,2>, //O+(8,2)
     <4,4,3>, //O+(8,3)
     <4,4,4>, //O+(8,4)
     <4,5,2>, //O+(10,2)
     <4,5,3>, //O+(10,3)
     <4,6,2>, //O+(12,2)
     <5,2,3>, <5,2,4>, <5,2,5>, //G2(3), G2(4), G2(5)
     <10,4,2>, //U(5,2)
     <10,4,3>, //U(5,3)
     <10,5,2>, //U(6,2)
     <10,6,2>, //U(7,2)
     <10,7,2>, //U(8,2)
     <11,2,8>, //Sz(8)
     <11,2,32>,//Sz(32)
     <12,4,2>, //O-(8,2)
     <12,4,3>, //O-(8,3)
     <12,4,4>, //O-(8,4)
     <12,5,2>, //O-(10,2)
     <12,5,3>, //O-(10,3)
     <12,6,2>, //O-(12,2)
     <13,4,2>, //3D4(2)
     <15,4,2>, //Tits group F(4,2)'
     <18,1,0>, <18,2,0>, <18,3,0>, <18,4,0>, <18,5,0>, //Mathieu groups
     <18,6,0>, <18,8,0>, <18,11,0>, //J1, J2, J3
     <18,7,0>, //HS
     <18,9,0>, //MCl
     <18,10,0>, //Suz
     <18,13,0>, //Co2
     <18,14,0>, //Co3
     <18,15,0>, //He
     <18,16,0>, //Fi22
     <18,20,0>, //Ru
     <18,21,0> //ONan
   } then return true;
  end if;
  return false;
end function;

Rearrange := procedure(G)
  local r, T, series, tofacs, fromfacs, factoword, ims, cslen, Y, W, w, g, ww,
  ig, iw, flag, ct, factorsol, factorname, factorord, factortype, ord, issimp,
  ninsol, nsocfacs, socfac, sfclass, socperm, socpermtriv, inpker, perm, x,
  conx, imnode, invim, socpermw, socpermg, Fg, Ftosp, Ftospw, Ftospg, S, node,
  genims, inner, ag, aw, mat, insr, deg, p, m, l;

  vprint LMG,1 : "Classifying composition factors";
  r := G`LMGNode;
  series:=r`series;
  tofacs:=r`tofacs;
  fromfacs:=r`fromfacs;
  factoword:=r`factoword;
  W:=r`W;
  Y:=r`Y;
  ims:=r`ims;
  factorsol:=r`factorsol;
  factorname:=r`factorname;
  factorord:=r`factorord;

  factortype := [];
  /* factortype[i] will eventually be
   * 1 if CF[i] is cyclic and in SR(G) (soluble radical)
   * 2 if CF[i] is nonabelian and in Socstar(G)
   * 3 if CF[i] is cyclic and in Pker(G)
   * 4 if CF[i] is not in Pker(G)
   */
  ninsol := #[x: x in factorsol | not x];
  nsocfacs := 0;
  socfac := {@ @}; //the indices in CS of the socle factors
  sfclass := []; //sfclass[i] is true iff socfac[i] is C8-group
  socperm := ninsol eq 0 select  sub< Sym(1) | > else sub< Sym(ninsol) | >;
  socpermtriv := true;
  cslen := #tofacs;

  //OK, let's start rearranging!

  for cfno in [1..cslen] do
    vprint LMG,2: "Classifying factor number:",cfno;
    //first decide whether factor is in pker
    inpker := true;
    if nsocfacs gt 1 then
      //work out permutation action on socle factors
      for ct in [1..#W[cfno]] do
        w := W[cfno][ct];
        g := Y[cfno][ct];
        perm := [1..ninsol];
                //will be the permutation of the socle factors induced by g.
        for sfno in [1..nsocfacs] do
          x := Y[socfac[sfno]][1]; //first generator of socfac sfno.
          conx := x^g;
          imnode := CompositionTreeFactorNumber( G, conx ) - 1;
          assert factortype[imnode] le 2;
          while factortype[imnode] eq 1 do
            ww := (conx^-1) @
                Function(tofacs[imnode]) @ Function(factoword[imnode]);
            conx *:= Evaluate( ww, Y[imnode] );
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert factortype[imnode] le 2;
          end while;
          perm[sfno] := Position(socfac, imnode);
          if socpermtriv then
            if perm[sfno] ne sfno then
              inpker := false;
            end if;
            if inpker and ct eq 1 and sfno eq nsocfacs-1 then
              //must be trivial permutation and hence in pker.
              break ct;
            end if;
          end if;
        end for; //for sfno in [1..nsocfacs] do
        if socpermtriv then
          //now time to set up socle permutation group
          socperm := sub< Sym(ninsol) | perm >;
          socpermw := [w]; //slp of element of G inducing this generator
          socpermg := [g]; //element of G inducing this generator
          Fg := FreeGroup(1); //for solving word problem in socperm
          Ftosp :=  hom< Fg->socperm | perm >;
          Ftospw := hom< Fg->Parent(w) | socpermw >;
          Ftospg := hom< Fg->Generic(G) | socpermg >;
          socpermtriv := false;
        else //socperm not trivial
          //check whether perm already in group and hence whether in pker.
          perm := Sym(ninsol)!perm;
          if inpker and perm in socperm then
            //adjust 
            invim := perm @@ Ftosp;
            vprint LMG,2: "adjusting to force into pker";
            W[cfno][ct] := w * Ftospw(invim)^-1;
            Y[cfno][ct] := g * Ftospg(invim)^-1;
          else 
            if inpker then
              assert ct eq 1;
              inpker := false;
            end if;
            //adjoin perm to socperm
            socperm := sub< Sym(ninsol) |
                   [socperm.i : i in [1..Ngens(socperm)]] cat [perm] >;
            Append(~socpermw, w);
            Append(~socpermg, g);
            Fg := FreeGroup(Ngens(socperm));
            Ftosp :=  hom< Fg->socperm | 
                                     [socperm.i : i in [1..Ngens(socperm)]] >;
            Ftospw := hom< Fg->Parent(w)| socpermw >;
            Ftospg := hom< Fg->Generic(G) | socpermg >;
          end if; //if inpker and perm in socperm then
        end if; //if socpermtriv then / else
      end for; //for ct in [1..#W[cfno]] do
    end if;
    if not inpker then
      factortype[cfno] := 4;
      continue;
    end if;

    //now we are in pker
    if not factorsol[cfno] then
      //this is a new socle factor
      factortype[cfno] := 2;
      for sfno in [nsocfacs .. 1 by -1] do
        //first adjust generators to induce inner automorphisms
        //on other socle factors. 
        //We handle socle factors in reverse order to make sure that later
        //adjustments do not ruin earlier adjustments.
        S := ims[socfac[sfno]];
        node := socfac[sfno];
        for ct in [1..#W[cfno]] do
          w := W[cfno][ct];
          g := Y[cfno][ct];
          genims := [];
          for x in Y[socfac[sfno]] do
            conx := x^g;
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert factortype[imnode] le 2;
            while factortype[imnode] eq 1 do
              ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
              conx *:= Evaluate( ww, Y[imnode] );
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert imnode eq node;
            end while;
            Append(~genims, conx @ Function(tofacs[node]) );
          end for;
          o8plus := sfclass[sfno] and
                     S`AutInfo`type eq "O+" and Dimension(S) eq 8;
          if o8plus then
//Must be careful because gaut acts on transformed group.
            gaut := S`AutInfo`gaut;
            mat := S`AutInfo`fmat;
            imat := mat^-1;
            gaY := [ (gaut( (x @ Function(tofacs[node]))^mat )^imat) @
                          Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
            genims1 := [];
            for x in gaY do
              conx := x^g;
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert factortype[imnode] le 2;
              while factortype[imnode] eq 1 do
                ww := (conx^-1) @
                    Function(tofacs[imnode]) @ Function(factoword[imnode]);
                conx *:= Evaluate( ww, Y[imnode] );
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert imnode eq node;
              end while;
              Append(~genims1, conx @ Function(tofacs[node]) );
            end for;
            genims2 := [];
            gaY := [ (gaut(gaut( (x @ Function(tofacs[node]))^mat ))^imat) @
                           Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
            for x in gaY do
              conx := x^g;
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert factortype[imnode] le 2;
              while factortype[imnode] eq 1 do
                ww := (conx^-1) @
                    Function(tofacs[imnode]) @ Function(factoword[imnode]);
                conx *:= Evaluate( ww, Y[imnode] );
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert imnode eq node;
              end while;
              Append(~genims2, conx @ Function(tofacs[node]) );
            end for;
          else genims1:=[]; genims2:=[];
          end if;
          if sfclass[sfno] then
            inner, ag, aw, mat := ProcessAutC(S, genims, g, w :
                             genims1:=genims1, genims2 := genims2 );
          else
            inner, ag, aw, mat := ProcessAutG(S, genims, g, w);
          end if;
          assert inner;
          ig := mat @ Function(fromfacs[node]);
          flag, iw := CompositionTreeElementToWord( G, ig ); assert flag;
          W[cfno][ct] := aw * iw^-1;
          Y[cfno][ct] := ag * ig^-1;
          //now a check
          if sfclass[sfno] then
            g := Y[cfno][ct]; genims:=[];
            for x in Y[socfac[sfno]] do
              conx := x^g;
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert factortype[imnode] le 2;
              while factortype[imnode] eq 1 do
                ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
                conx *:= Evaluate( ww, Y[imnode] );
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              end while;
              assert imnode eq node;
              Append(~genims, conx @ Function(tofacs[node]) );
            end for;
            if o8plus then
              gaut := S`AutInfo`gaut;
              mat := S`AutInfo`fmat;
              imat := mat^-1;
              gaY := [ (gaut( (x @ Function(tofacs[node]))^mat )^imat) @
                         Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
              genims1 := [];
              for x in gaY do
                conx := x^g;
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert factortype[imnode] le 2;
                while factortype[imnode] eq 1 do
                  ww := (conx^-1) @
                      Function(tofacs[imnode]) @ Function(factoword[imnode]);
                  conx *:= Evaluate( ww, Y[imnode] );
                  imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                  assert imnode eq node;
                end while;
                Append(~genims1, conx @ Function(tofacs[node]) );
              end for;
              genims2 := [];
              gaY := [ (gaut(gaut( (x @ Function(tofacs[node]))^mat ))^imat) @
                            Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
              for x in gaY do
                conx := x^g;
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert factortype[imnode] le 2;
                while factortype[imnode] eq 1 do
                  ww := (conx^-1) @
                      Function(tofacs[imnode]) @ Function(factoword[imnode]);
                  conx *:= Evaluate( ww, Y[imnode] );
                  imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                  assert imnode eq node;
                end while;
                Append(~genims2, conx @ Function(tofacs[node]) );
              end for;
            else genims1:=[]; genims2:=[];
            end if;
            tup := AutTuple(S,genims:genims1:=genims1, genims2:=genims2);
            assert tup[1] eq 0 and tup[2] eq 0 and IsScalar(tup[3]);
          end if;
        end for;
      end for; //for sfno in [1..nsocfacs] do
      nsocfacs +:= 1;
      Include(~socfac, cfno);
      S := ims[cfno];
      if Type(S) eq GrpMat and RecogniseClassical(S) cmpeq true then
        sfclass[nsocfacs] := true;
        vprint LMG,2: "classical type socle factor";
        if cfno lt cslen then //don't need to do this for factor at top
          InitialiseAutInfoC(S);
        end if;
      else
        sfclass[nsocfacs] := false;
        vprint LMG,2: "general type socle factor";
        if cfno lt cslen then //don't need to do this for factor at top
          //A:=AutomorphismGroup(S);
          if not CanCalculateAutGpAndMaxSubs(NameChange(factorname[cfno])) then
             error "Cannot calculate automorphism group of socle factor",
                     factorname[cfno];
          end if;
          InitialiseAutInfoG(S);
        end if;
      end if;
    else 
      vprint LMG,2: "soluble composition factor";
      if nsocfacs eq 0 then
        factortype[cfno] := 1;
        continue;
      end if;
      //test whether it passes through into SR(G)
      insr := true;
      for sfno in [nsocfacs .. 1 by -1] do
        S := ims[socfac[sfno]];
        node := socfac[sfno];
        w := W[cfno][1];
        g := Y[cfno][1];
        genims := [];
        for x in Y[socfac[sfno]] do
          conx := x^g;
          imnode := CompositionTreeFactorNumber( G, conx ) - 1;
          assert factortype[imnode] le 2;
          while factortype[imnode] eq 1 do
              ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
              conx *:= Evaluate( ww, Y[imnode] );
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
          end while;
          assert imnode eq node;
          Append(~genims, conx @ Function(tofacs[node]) );
/*
if CompositionTreeFactorNumber( G, conx ) - 1 ne node then
"ERROR B";
CompositionTreeFactorNumber( G, conx ) - 1, sfno, //Y[socfac[sfno]], conx,
node; end if;
*/
        end for;
        o8plus := sfclass[sfno] and S`AutInfo`type eq "O+" and
                  Dimension(S) eq 8;
        if o8plus then
//Must be careful because gaut acts on transformed group.
          gaut := S`AutInfo`gaut;
          mat := S`AutInfo`fmat;
          imat := mat^-1;
          gaY := [ (gaut( (x @ Function(tofacs[node]))^mat )^imat) @
                      Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
          genims1 := [];
          for x in gaY do
            conx := x^g;
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert factortype[imnode] le 2;
            while factortype[imnode] eq 1 do
              ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
              conx *:= Evaluate( ww, Y[imnode] );
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert imnode eq node;
            end while;
            Append(~genims1, conx @ Function(tofacs[node]) );
          end for;
          genims2 := [];
  
          gaY := [ (gaut(gaut( (x @ Function(tofacs[node]))^mat ))^imat) @
                     Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
          for x in gaY do
            conx := x^g;
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert factortype[imnode] le 2;
            while factortype[imnode] eq 1 do
              ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
              conx *:= Evaluate( ww, Y[imnode] );
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert imnode eq node;
            end while;
            Append(~genims2, conx @ Function(tofacs[node]) );
          end for;
        else genims1:=[]; genims2:=[];
        end if;
        if sfclass[sfno] then
          inner, ag, aw, mat := ProcessAutC(S, genims, g, w :
                             genims1:=genims1, genims2 := genims2 );
          if not inner and o8plus and
                                 S`AutInfo`level[#(S`AutInfo)`level] eq 5 then
             //graph automorphism of O8+
             assert factorord[cfno] in {2,3};
             vprint LMG, 3:
                 "stored O8+ graph automorphism of order",factorord[cfno];
          end if;
        else
          inner, ag, aw, mat := ProcessAutG(S, genims, g, w);
        end if;
        if inner then
          ig := mat @ Function(fromfacs[node]);
          flag, iw := CompositionTreeElementToWord( G, ig ); assert flag;
          W[cfno][1] := aw * iw^-1;
          Y[cfno][1] := ag * ig^-1;
          //now a check
          if sfclass[sfno] then
            g := Y[cfno][1]; genims:=[];
            for x in Y[socfac[sfno]] do
              conx := x^g;
              imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              assert factortype[imnode] le 2;
              while factortype[imnode] eq 1 do
                ww := (conx^-1) @
                  Function(tofacs[imnode]) @ Function(factoword[imnode]);
                conx *:= Evaluate( ww, Y[imnode] );
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
              end while;
              assert imnode eq node;
              Append(~genims, conx @ Function(tofacs[node]) );
            end for;
            if o8plus then
              gaut := S`AutInfo`gaut;
              mat := S`AutInfo`fmat;
              imat := mat^-1;
              gaY := [ (gaut( (x @ Function(tofacs[node]))^mat )^imat) @
                           Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
              genims1 := [];
              for x in gaY do
                conx := x^g;
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert factortype[imnode] le 2;
                while factortype[imnode] eq 1 do
                  ww := (conx^-1) @
                      Function(tofacs[imnode]) @ Function(factoword[imnode]);
                  conx *:= Evaluate( ww, Y[imnode] );
                  imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                  assert imnode eq node;
                end while;
                Append(~genims1, conx @ Function(tofacs[node]) );
              end for;
              genims2 := [];
              gaY := [ (gaut(gaut( (x @ Function(tofacs[node]))^mat ))^imat) @
                         Function(fromfacs[node]) : x in Y[socfac[sfno]] ]; 
              for x in gaY do
                conx := x^g;
                imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                assert factortype[imnode] le 2;
                while factortype[imnode] eq 1 do
                  ww := (conx^-1) @
                      Function(tofacs[imnode]) @ Function(factoword[imnode]);
                  conx *:= Evaluate( ww, Y[imnode] );
                  imnode := CompositionTreeFactorNumber( G, conx ) - 1;
                  assert imnode eq node;
                end while;
                Append(~genims2, conx @ Function(tofacs[node]) );
              end for;
            else genims1:=[]; genims2:=[];
            end if;
            tup := AutTuple(S,genims:genims1:=genims1, genims2:=genims2);
            assert tup[1] eq 0 and tup[2] eq 0 and IsScalar(tup[3]);
          end if;
        else insr := false; break;
        end if;
      end for; //for sfno in [1..nsocfacs] do
      if insr then factortype[cfno] := 1;
      else factortype[cfno] := 3;
      end if;
    end if; //if not factorsol[cfno] then
    //Now we redefine fromfacs[cfno] to use the new images
    fromfacs[cfno] := map< ims[cfno]->Generic(G) |
          x :-> Evaluate( x @ Function(factoword[cfno]), Y[cfno] ) >;
  end for; //for cfno in [1..cslen] do

  deg :=#socfac;
  socperm := deg eq 0 select sub<Sym(1)|> else
    sub< Sym(deg) |
      [ [Eltseq(g)[i]: i in [1..deg]] : g in Generators(socperm) ] >;

  vprint LMG, 2: ""; vprint LMG, 2: "";
  vprint LMG, 2: "Composition factors in soluble radical:";
  for cfno in [1..cslen] do if factortype[cfno] eq 1 then
     vprint LMG, 2: cfno,":",factorname[cfno];
  end if; end for;
  vprint LMG, 2: "";
  vprint LMG, 2: "Composition factors in socle:";
  for cfno in [1..cslen] do if factortype[cfno] eq 2 then
     vprint LMG, 2: cfno,":",factorname[cfno];
  end if; end for;
  vprint LMG, 2: "";
  vprint LMG, 2: "Composition factors in PKer:";
  for cfno in [1..cslen] do if factortype[cfno] eq 3 then
     vprint LMG, 2: cfno,":",factorname[cfno];
  end if; end for;
  vprint LMG, 2: "";
  vprint LMG, 2: "Composition factors not in PKer:";
  for cfno in [1..cslen] do if factortype[cfno] eq 4 then
     vprint LMG, 2: cfno,":",factorname[cfno];
  end if; end for;

  G`LMGNode`factortype:=factortype;
  G`LMGNode`fromfacs:=fromfacs;
  G`LMGNode`socperm:=socperm;
  G`LMGNode`sfclass:=sfclass;
  G`LMGNode`W:=W;
  G`LMGNode`Y:=Y;
  p := Characteristic(BaseRing(G));
  m := [i : i in [1..cslen] | r`factorord[i] ne p ];
  G`LMGNode`ngensu := m eq [] select cslen else m[1]-1;
  l := [1..G`LMGNode`ngensu];

  G`LMGNode`unirad :=
       sub<Generic(G) | &cat[ [Y[i][j]:j in [1..#Y[i]] ] : i in l ] >;
  G`LMGNode`unirad`Order := p^#l;

  G`LMGNode`rad :=
       sub<Generic(G) | &cat[ [Y[i][j]:j in [1..#Y[i]] ] : i in [1..cslen] |
                                                        factortype[i] eq 1] >;
  G`LMGNode`rad`Order :=
            #l eq 0 select 1 else &*l where l :=
                 [ r`factorord[i] : i in [1..cslen] | factortype[i] eq 1]; 

  G`LMGNode`socstar :=
       sub<Generic(G) | &cat[ [Y[i][j]:j in [1..#Y[i]] ] : i in [1..cslen] |
                                                        factortype[i] le 2] >;
  G`LMGNode`socstar`Order :=
                 &*[ r`factorord[i] : i in [1..cslen] | factortype[i] le 2]; 

  G`LMGNode`pker :=
       sub<Generic(G) | &cat[ [Y[i][j]:j in [1..#Y[i]] ] : i in [1..cslen] |
                                                        factortype[i] le 3] >;
  G`LMGNode`pker`Order :=
                 &*[ r`factorord[i] : i in [1..cslen] | factortype[i] le 3]; 
end procedure;
