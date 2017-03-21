freeze;

import "lmgrec.m": LMGRF;
import "rearrange.m": Rearrange;
import "initialize.m": NameChange, Initialize;
NFUR := function(G,g)
//write g in unipotent radical as EltSeq of normal form word in generators
  local elt, t;
  r := G`LMGNode;
  elt := [];
  t := r`ngensu;
  while g ne Id(G) do
       exp := Eltseq(g @ Function(r`tofacs[t]) )[1];
       Append(~elt, exp);
       g := r`Y[t][1]^-exp * g;
       t-:=1;
  end while;
  return elt;
end function;

NFSR:= function(G,g)
//write g in solrad as EltSeq of normal form word in generators of F
  local n, r, radfac, elt, pos, exp;
  r := G`LMGNode;
  radfac := Reverse([i : i in [1..#r`factortype] | r`factortype[i] eq 1]);
  elt := [0 : i in [1..#radfac]];
  while g ne Id(G) do
       n := CompositionTreeFactorNumber( G, g ) - 1;
       if n le r`ngensu then
          s := NFUR(G,g);
          d := Position(radfac, r`ngensu);
          for i in [1..#s] do elt[d+i-1]:=s[i]; end for;
          return elt;
       end if;
       pos := Position(radfac,n); assert pos gt 0;
       exp := Eltseq(g @ Function(r`tofacs[n]) )[1];
       elt[pos] := exp;
       g := r`Y[n][1]^-exp * g;
  end while;
  return elt;
end function;

InSR:= function(G,g)
//Test if g in in Rad(G)
  local n, r, radfac, pos, exp, ingp, w;
  ingp, w := CompositionTreeElementToWord(G, g);
  if not ingp then
    return false, _;
  end if;
  r := G`LMGNode;
  radfac := Reverse([i : i in [1..#r`factortype] | r`factortype[i] eq 1]);
  while g ne Id(G) do
       n := CompositionTreeFactorNumber( G, g ) - 1;
       if n le r`ngensu then
          return true, w;
       end if;
       pos := Position(radfac,n);
       if pos eq 0 then
          return false, _;
       end if;
       exp := Eltseq(g @ Function(r`tofacs[n]) )[1];
       g := r`Y[n][1]^-exp * g;
  end while;
  return true, w;
end function;

GetUniRad := procedure(G)
/* Compute PC-presentation P of unipotent radical U of G, together with
 * invertible map U->P.
 */
  local radfac, p, l, NF, pclen, F, rels, pos, ord, Q, phi, m, m1, r, e;

  if not assigned G`LMGNode`socperm then
    Rearrange(G);
  end if;
  r := G`LMGNode;
  p := Characteristic(BaseRing(G));
  l := #r`factorord;
  m := [i : i in [1..l] | r`factorord[i] ne p ];
  radfac := m eq [] select Reverse([1..l]) else Reverse([1..m[1]-1]);
   //reversed because PC generators are numbered from top down
  pclen := #radfac;
  if pclen eq 0 then
    P := PCGroup(sub<G|>);
    G`LMGNode`uniradPC := P;
    G`LMGNode`uniradtoPC :=
       map< Generic(G)->P | x :-> Id(P), x :-> Id(G) >;
    return;
  end if;

  F := FreeGroup(pclen);

  rels := [];
  //calculate pcrels
  for i in [1..pclen] do
    pos := radfac[i];
    ord := #r`ims[pos];
    if r`Y[pos][1]^ord eq Id(G) then
      Append(~rels, F.i^ord = Id(F));
    else 
      e := NFUR(G, r`Y[pos][1]^ord );
      Append(~rels, F.i^ord = &*[ F.k^e[k] : k in [1..#e] ] );
    end if;
    for j in [i+1..pclen] do
      if ( r`Y[radfac[j]][1], r`Y[pos][1] ) eq Id(G) then
        Append(~rels, F.j^F.i = F.j);
      else
        //Append(~rels, F.j^F.i = NF( r`Y[radfac[j]][1]^r`Y[pos][1] ) );
        e := NFUR(G, r`Y[radfac[j]][1]^r`Y[pos][1] );
        Append(~rels, F.j^F.i = &*[ F.k^e[k] : k in [1..#e] ] );
      end if;
    end for;
  end for;
  vprint LMG,2: "Got PC-relations of unipotent radical";

  Q, phi := quo< GrpPC : F | rels >;
  m := hom< F->Generic(G) | [ r`Y[i][1] : i in radfac ] >;

  NF := function(g)
    local e;
    e := NFUR(G,g);
    return &*[ F.k^e[k] : k in [1..#e] ];
  end function;
  m1 := map< Generic(G)->Q | x :-> NF(x) @ phi, x :-> x @@ phi @ m  >;
    //note m1 will fail on g if g not in soluble radical of G
  G`LMGNode`uniradPC := Q;
  G`LMGNode`uniradtoPC := m1;
  if #Q gt 1 then
    (G`LMGNode`unirad)`LMGNode :=
       rec< LMGRF | RS:=false, isunirad:=true, israd:=false, uniradgp:=G >;
  end if;
  vprint LMG,1: "Defined PCGroup of unipotent radical";

end procedure;

GetSolRad := procedure(G)
/* Compute PC-presentation P of soluble radical L of G, together with
 * invertible map L->P.
 */
  local radfac, NF, pclen, F, rels, pos, ord, Q, phi, m, m1, r;

  if not assigned G`LMGNode or not assigned G`LMGNode`socperm then
    Rearrange(G);
  end if;
  r := G`LMGNode;
  //first try BSGS on rad
  rad := r`rad;
  Initialize(rad : Verify := G`LMGNode`verified );
  if rad`LMGNode`RS then
    vprint LMG,2 : "Defining PC-group of rad using BSGS methods";
    G`LMGNode`radPC, G`LMGNode`radtoPC := PCGroup(rad);
    return;
  end if;
  radfac := Reverse([ i : i in [1..#r`factortype] | r`factortype[i] eq 1 ]);
   //reversed because PC generators are numbered from top down
  pclen := #radfac;
  if pclen eq 0 then
    P := PCGroup(sub<G|>);
    G`LMGNode`radPC := P;
    G`LMGNode`radtoPC := map< Generic(G)->P | x :-> Id(P), x :-> Id(G) >;
    return;
  end if;

  F := FreeGroup(pclen);

  NF := function(g)
    local e;
    e := NFSR(G,g);
    return &*[ F.k^e[k] : k in [1..#e] ];
  end function;

  rels := [];
  //calculate pcrels
  for i in [1..pclen] do
    pos := radfac[i];
    ord := #r`ims[pos];
    Append(~rels, F.i^ord = NF( r`Y[pos][1]^ord ) );
    for j in [i+1..pclen] do
      if ( r`Y[radfac[j]][1], r`Y[pos][1] ) eq Id(G) then
        Append(~rels, F.j^F.i = F.j);
      else
        Append(~rels, F.j^F.i = NF( r`Y[radfac[j]][1]^r`Y[pos][1] ) );
      end if;
    end for;
  end for;
  vprint LMG,2: "Got PC-relations of solvable radical";

  Q, phi := quo< GrpPC : F | rels >;
  m := hom< F->Generic(G) | [ r`Y[i][1] : i in radfac ] >;
  m1 := map< Generic(G)->Q | x :-> NF(x) @ phi, x :-> x @@ phi @ m >;
    //note m1 will fail on g if g not in soluble radical of G
  G`LMGNode`radPC := Q;
  G`LMGNode`radtoPC := m1;
/* turn this feature off for now, because don't have rewriting algorithm 
  if #Q gt 1 then
    (G`LMGNode`rad)`LMGNode :=
       rec< LMGRF | RS:=false, israd:=true, isunirad:=false, radgp:=G >;
  end if;
*/
  vprint LMG,1: "Defined PCGroup of solvable radical";

end procedure;

GetRadModUniRad := procedure(G)
/* Compute PC-presentation P of Rad G/Uni Rad G, together with
 * invertible map Rad->P.
 */
  local p, l, radfac, NF, pclen, F, rels, pos, ord, Q, phi, m, m1, r;

  if not assigned G`LMGNode or not assigned G`LMGNode`socperm then
    Rearrange(G);
  end if;
  r := G`LMGNode;
  p := Characteristic(BaseRing(G));
  m := [i : i in [1..#r`factorord] | r`factorord[i] ne p ];
  l := m eq [] select #r`factorord else m[1]-1;

  radfac := Reverse([ i : i in [1..#r`factortype] |
                                   r`factortype[i] eq 1 and i gt l ]);
   //reversed because PC generators are numbered from top down
  pclen := #radfac;
  if pclen eq 0 then
    P := PCGroup(sub<G|>);
    G`LMGNode`radmoduniPC := P;
    G`LMGNode`radmodunitoPC :=
         map< Generic(G)->P | x :-> Id(P), x :-> Id(G) >;
    return;
  end if;
  F := FreeGroup(pclen);

  NF := function(g)
    //write g in L as normal form word in generators of F mod soc*
    local n, elt, pos, exp, w;
     elt := Id(F);
     while g ne Id(G) do
       n := CompositionTreeFactorNumber( G, g ) - 1;
       if n lt radfac[#radfac] then
         break;
       end if;
       pos := Position(radfac,n); assert pos gt 0;
       exp := Eltseq(g @ Function(r`tofacs[n]) )[1];
       elt *:= F.pos^exp;
       g := r`Y[n][1]^-exp * g;
     end while;
     return elt;
  end function;

  rels := [];
  //calculate pcrels
  for i in [1..pclen] do
    pos := radfac[i];
    ord := #r`ims[pos];
    Append(~rels, F.i^ord = NF( r`Y[pos][1]^ord ) );
    for j in [i+1..pclen] do
      Append(~rels, F.j^F.i = NF( r`Y[radfac[j]][1]^r`Y[pos][1] ) );
    end for;
  end for;

  Q, phi := quo< GrpPC : F | rels >;
  m := hom< F->Generic(G) | [ r`Y[i][1] : i in radfac ] >;
  m1 := map< Generic(G)->Q | x :-> NF(x) @ phi, x :-> x @@ phi @ m >;
    //note m1 will fail on g if g not in Rad(G)
  G`LMGNode`radmoduniPC := Q;
  G`LMGNode`radmodunitoPC := m1;
  vprint LMG,1 : "Computed PCGroup of Rad/UniRad";
end procedure;

RadModUniRad := function(G)
//not used yet
  if not assigned G`LMGNode`radmoduniPC then
    GetRadModUniRad(G);
  end if;
  return G`LMGNode`rad, G`LMGNode`radmoduniPC, G`LMGNode`radmodunitoPC;
end function;

GetPKer := procedure(G)
/* Compute PC-presentation P of PKer/SocStar G, together with
 * invertible map PKer->P.
 */
  local pkerfac, NF, pclen, F, rels, pos, ord, Q, phi, m, m1, r;

  if not assigned G`LMGNode`socperm then
    Rearrange(G);
  end if;
  r := G`LMGNode;
  pkerfac := Reverse([ i : i in [1..#r`factortype] | r`factortype[i] eq 3 ]);
   //reversed because PC generators are numbered from top down
  pclen := #pkerfac;
  if pclen eq 0 then
    P := PCGroup(sub<G|>);
    G`LMGNode`pkerPC := P;
    G`LMGNode`pkertoPC :=
        map< Generic(G)->P | x :-> Id(P), x :-> Id(G) >;
    return;
  end if;
  F := FreeGroup(pclen);

  NF := function(g)
    //write g in L as normal form word in generators of F mod soc*
    local n, elt, pos, exp, w;
     elt := Id(F);
     while g ne Id(G) do
       n := CompositionTreeFactorNumber( G, g ) - 1;
       assert r`factortype[n] le 3;
       if n lt pkerfac[#pkerfac] then
         break;
       end if;
       if r`factortype[n] eq 3 then
         pos := Position(pkerfac,n);
         exp := Eltseq(g @ Function(r`tofacs[n]) )[1];
         elt *:= F.pos^exp;
         g := r`Y[n][1]^-exp * g;
       else
         w := (g^-1) @ Function(r`tofacs[n]) @ Function(r`factoword[n]);
         g := Evaluate( w, r`Y[n] ) * g;
       end if;
     end while;
     return elt;
  end function;

  rels := [];
  //calculate pcrels
  for i in [1..pclen] do
    pos := pkerfac[i];
    ord := #r`ims[pos];
    Append(~rels, F.i^ord = NF( r`Y[pos][1]^ord ) );
    for j in [i+1..pclen] do
      Append(~rels, F.j^F.i = NF( r`Y[pkerfac[j]][1]^r`Y[pos][1] ) );
    end for;
  end for;

  Q, phi := quo< GrpPC : F | rels >;
  m := hom< F->Generic(G) | [ r`Y[i][1] : i in pkerfac ] >;
  m1 := map< Generic(G)->Q | x :-> NF(x) @ phi, x :-> x @@ phi @ m >;
    //note m1 will fail on g if g not in PKer(G)
  G`LMGNode`pkerPC := Q;
  G`LMGNode`pkertoPC := m1;
  vprint LMG,1: "Computed PCGroup of SocleKernel/SocleStar";
end procedure;

GetSocleAct := procedure(G)
/* Compute action P (=socperm) on socle factors with maps G->P, P->G.
 */
  local actfac, NF, deg, F, permlist, perms, P,
        x, w, g, ww, conx, imnode, r, socfac;

  if  not assigned G`LMGNode`socperm then
    Rearrange(G);
  end if;
  r := G`LMGNode;
  actfac := [ i : i in [1..#r`factortype] | r`factortype[i] eq 4 ];
  P := r`socperm;
  if #P eq 1 then
    G`LMGNode`Gtosocperm :=
         map< Generic(G)->P | x :-> Id(P), x :-> Id(Generic(G)) >;
    return;
  end if;
  deg := Degree(P);
  permlist := [];
  socfac := [ i : i in [1..#r`ims] | r`factortype[i] eq 2 ];
  for cfno in actfac do
    perms := [];
    for ct in [1..#r`W[cfno]] do
        w := r`W[cfno][ct];
        g := r`Y[cfno][ct];
        perm := [1..deg];
                //will be the permutation of the socle factors induced by g.
        for sfno in [1..deg] do
          x := r`Y[socfac[sfno]][1]; //first generator of socfac sfno.
          conx := x^g;
          imnode := CompositionTreeFactorNumber( G, conx ) - 1;
          assert r`factortype[imnode] le 2;
          while r`factortype[imnode] eq 1 do
            ww := (conx^-1) @
                Function(r`tofacs[imnode]) @ Function(r`factoword[imnode]);
            conx *:= Evaluate( ww, r`Y[imnode] );
            imnode := CompositionTreeFactorNumber( G, conx ) - 1;
            assert r`factortype[imnode] le 2;
          end while;
          perm[sfno] := Position(socfac, imnode);
        end for; //for sfno in [1..nsocfacs] do
        Append(~perms,Sym(deg)!perm);
    end for; //for ct in [1..#W[cfno]] do
    Append(~permlist, perms);
  end for; //for cfno in actfac do

  ngens := #&cat permlist;
  F := FreeGroup(ngens);

  NF := function(g)
    //write g in L as normal form word in generators of F mod PKer
    local n, elt, pos, exp, w;
     elt := Id(P);
     while g ne Id(G) do
       n := CompositionTreeFactorNumber( G, g ) - 1;
       if n lt actfac[1] then
         break;
       end if;
       w := g @ Function(r`tofacs[n]) @ Function(r`factoword[n]);
       if r`factortype[n] eq 4 then
         pos := Position(actfac,n);
         elt *:= Evaluate( w, permlist[pos] );
       end if;
       g := Evaluate( w^-1, r`Y[n] ) * g;
     end while;
     return elt;
  end function;

  ma := hom< F->P | &cat permlist >;
  mb := hom< F->Generic(G) | &cat [ [ y : y in r`Y[i] ] : i in actfac ] >;
  //this time we use a map with inverse supplied
  m1 := map< Generic(G)->P | x :-> NF(x), x :-> x @@ ma  @ mb >;
  G`LMGNode`Gtosocperm := m1;
  vprint LMG,1: "Computed the socle action";

end procedure;

CommGp := function(H,K) //H,K<=G, return [H,K]
//INTRINSIC
  local G, S, D, flag;
  assert Generic(H) eq Generic(K);
  if HasCompositionTree(H) and LMGIsSubgroup(H,K) then G:= H;
  elif HasCompositionTree(K) and LMGIsSubgroup(K,H) then G:= K;
  else G := sub< Generic(H) | H,K >; _ := CompositionTree(G);
  end if;

  S := sub< Generic(G) |
      [ (H.i,K.j) : i in [1..Ngens(H)],  j in [1..Ngens(K)] ] >;
  D := sub< Generic(G) | [Random(S)^Random(G) : i in [1..Max(Ngens(G),5)]] >;
  repeat
    done := true;
    _ := CompositionTree(D);
    //verify normality
    for g in Generators(G) do for d in Generators(D) do
      flag := CompositionTreeElementToWord(D, d^g);
      if not flag then
         vprint LMG, 3: "need more generators";
         done:=false;
         D := sub< Generic(G) | D, d^g,
                         [Random(D)^Random(G) : i in [1..5]] >;
         break g;
      end if;
    end for; end for;
  until done;
  return(D);
end function;

GetChiefSer := procedure(G)
  local r, cseries, cfacname, len, P, m1,  E, l, rho, d, p, A, mats, M, CM,
  m, phi, newgens, socfacs, orbs, nm, cf, cseriesrad, radmods, radmodactions,
  f, newgensrad;
  if not assigned G`LMGNode`radPC then
    GetSolRad(G);
  end if;
  if not assigned G`LMGNode`pkerPC then
    GetPKer(G);
  end if;
  if not assigned G`LMGNode`Gtosocperm then
    GetSocleAct(G);
  end if;
  r := G`LMGNode;
  cseries := [ sub<G|> ];
  cfacname := [];
  len := 1;
  //work up through the 4 layers
  //Layer 1
  if #[t : t in [1..#r`factortype] | r`factortype[t] eq 1] ne 0 then
    P := r`radPC;
    m1 := r`radtoPC;
    //solvable case is easier
    if LMGIsSoluble(G) then
      E := ChiefSeries(P);
      radmods := [* *];
      radmodactions := [* *];
      genmodactions := [* *];
      for l in [#E-1 .. 1 by -1] do
        //chief factors for layer E[l]/E[l+1]
        L, rho := quo< E[l] | E[l+1] >;
        d := Ngens(L);
        p := Factorisation(#L)[1][1];
        cfacname[len] := <19, 0, p, d>;
        len +:= 1;
        cseries[len] := sub< Generic(G) | cseries[len-1],
                                         [ L.i @@ rho @@ m1 : i in [1..d] ]  >;
        m,f := GModule(P, E[l], E[l+1]);
        r := Representation(m);
        d := Dimension(m);
        mtriv :=
         forall{x : x in ActionGenerators(m) | x eq IdentityMatrix(GF(p),d)};  
        Append(~radmods,<m,f,r,mtriv>);
        Append(~radmodactions, map< G->GL(d,p) | g :-> GL(d,p)!(g@m1@r) > );
        Append(~genmodactions, [GL(d,p)!(G.i@m1@r) : i in [1..Ngens(G)]] );
      end for;
      G`LMGNode`cseries := cseries;
      G`LMGNode`cfactorname := cfacname;
      G`LMGNode`cseriesrad := Reverse(E);
      G`LMGNode`radmods := radmods;
      G`LMGNode`radmodactions := radmodactions;
      G`LMGNode`genmodactions := genmodactions;
      return;
    end if;
    E := ElementaryAbelianSeriesCanonical(P);
    radmods := [* *];
    radmodactions := [* *];
    genmodactions := [* *];
    cseriesrad := [ sub<P|> ];
    for l in [#E-1 .. 1 by -1] do
      //chief factors for layer E[l]/E[l+1]
      L, rho := quo< E[l] | E[l+1] >;
      //need to make this into a G-module
      d := Ngens(L);
      p := Factorisation(#L)[1][1];
      A := MatrixAlgebra(GF(p),d);
      mats := [ 
   A!Matrix( [ Eltseq( ((L.j @@ rho @@ m1)^g) @ m1 @ rho ) : j in [1..d] ] ) :
              g in [G.i : i in [1..Ngens(G)]] ];
      M := GModule(G,mats);
      CM := CompositionSeries(M);
      for i in [1..#CM] do
        if i eq 1 then m, phi := quo< CM[i] | sub<M|> >;
        else m, phi := quo< CM[i] | CM[i-1] >;
        end if;
        cfacname[len] := < 19, 0, p, Dimension(m) >;
        len +:= 1;
        newgensrad := [
   (L!ChangeUniverse( Eltseq(m.j @@ phi @ Morphism(CM[i],M)), Integers() ))
            @@ rho  : j in [1..Ngens(m)] ];
        newgens := [ l @@ m1 : l in newgensrad ];
        cseriesrad[len] := sub< P | cseriesrad[len-1], newgensrad >;
        cseries[len] := sub< Generic(G) | cseries[len-1], newgens >;
        m,f := GModule(P, cseriesrad[len], cseriesrad[len-1]);
        d := Dimension(m);
        mtriv :=
         forall{x : x in ActionGenerators(m) | x eq IdentityMatrix(GF(p),d)};  
        Append(~radmods, <m,f,Representation(m),mtriv>);
        Append( ~radmodactions, map< G -> GL(d,p) |  g :->
   GL(d,p)!Matrix( [ Eltseq( ((m.j @@ f @@ m1)^g) @ m1 @ f ) : j in [1..d] ] )
                                  > );
        Append( ~genmodactions, [ GL(d,p)!Matrix(
             [ Eltseq( ((m.j @@ f @@ m1)^G.i) @ m1 @ f ) : j in [1..d] ]) :
                 i in [1..Ngens(G)]] );
      end for;
    end for;
    G`LMGNode`cseriesrad := cseriesrad;
    G`LMGNode`radmods := radmods;
    G`LMGNode`radmodactions := radmodactions;
    G`LMGNode`genmodactions := genmodactions;
    vprint LMG, 3: "Got chief factors of solvable radical";
  else
    G`LMGNode`cseriesrad := [ sub<r`radPC|> ];
    G`LMGNode`radmods := [**];
    G`LMGNode`radmodactions := [**];
    G`LMGNode`genmodactions := [**];
  end if;

  //layer 2
  socfacs := [t : t in [1..#r`factortype] | r`factortype[t] eq 2];
  if #socfacs gt 0 then
    orbs := Orbits(r`socperm);
    for o in orbs do
      nm := NameChange( r`factorname[ socfacs[o[1]] ] );
      cfacname[len] := < nm[1], nm[2], nm[3], #o >;
      len +:= 1;
      newgens := &cat[ r`Y[i] : i in [socfacs[x] : x in o] ];
      cseries[len] := sub< Generic(G) | cseries[len-1], newgens >;
    end for;
    vprint LMG, 3: "Got chief factors of SocleStar";
  end if;

  //layer 3
  if #[t : t in [1..#r`factortype] | r`factortype[t] eq 3] ne 0 then
    P := r`pkerPC;
    m1 := r`pkertoPC;
    E := ElementaryAbelianSeriesCanonical(P);
    for l in [#E-1 .. 1 by -1] do
      //chief factors for layer E[l]/E[l+1]
      L, rho := quo< E[l] | E[l+1] >;
      //need to make this into a G-module
      d := Ngens(L);
      p := Factorisation(#L)[1][1];
      A := MatrixAlgebra(GF(p),d);
      mats := [ 
   A!Matrix( [ Eltseq( ((L.j @@ rho @@ m1)^g) @ m1 @ rho ) : j in [1..d] ] ) :
              g in [G.i : i in [1..Ngens(G)]] ];
      M := GModule(G,mats);
      CM := CompositionSeries(M);
      for i in [1..#CM] do
        if i eq 1 then m, phi := quo< CM[i] | sub<M|> >;
        else m,phi := quo< CM[i] | CM[i-1] >;
        end if;
        cfacname[len] := < 19, 0, p, Dimension(m) >;
        len +:= 1;
        newgens := [
   (L!ChangeUniverse( Eltseq(m.j @@ phi @ Morphism(CM[i],M)), Integers() ))
            @@ rho @@ m1 : j in [1..Ngens(m)] ];
        cseries[len] := sub< Generic(G) | cseries[len-1], newgens >;
      end for;
    end for;
    vprint LMG, 3: "Got chief factors of SocleActionKernel/SocleStar";
  end if;

  //layer 4
  m1 := r`Gtosocperm;
  if #[t : t in [1..#r`factortype] | r`factortype[t] eq 4] ne 0 then
    P := r`socperm;
    E := ChiefSeries(P);
    cf := ChiefFactors(P);
    for l in [#E-1 .. 1 by -1] do
      //chief factors for layer E[l]/E[l+1]
      cfacname[len] := cf[l]; 
      len +:= 1;
      newgens := [ g @@ m1 : g in Generators(E[l]) ];
      cseries[len] := sub< Generic(G) | cseries[len-1], newgens >;
    end for;
  end if; 
  vprint LMG, 3: "Got chief factors of G/SocleActionKernel";
  cseries[#cseries] := G; //to avoid recomputations later

  G`LMGNode`cseries := cseries;
  G`LMGNode`cfactorname := cfacname;
end procedure;
