freeze;

forward DistinctExtensionsNew;
declare verbose GrpExt, 2;

import "modext.m":	RepresentativeModules;
import "../GrpCoh/strongpres.m":  SplitExtensionPermRepSG, MatrixOfExtensionSG,
                                  EvaluateCocycleSG;
intrinsic ExtensionsOfElementaryAbelianGroup
         (p :: RngIntElt, d :: RngIntElt, G :: GrpPerm) -> SeqEnum
{All extensions (up to isomorphism) of an elementary abelian group
 of order p^d by a group G}
  local mods, F, FtoG;
  if not IsPrime(p) then
     error "First argument must be prime";
  end if;
  mods := RepresentativeModules(G,sub<G|>,GF(p),d);
  if #G eq 1 then
    ng := Ngens(G);
    F := FreeGroup(d+ng);
    rels := [F.i : i in [1..ng]] cat [F.i^p : i in [ng+1..ng+d]] cat
            &cat[[ (F.i,F.j) : j in [i+1..ng+d] ] : i in [ng+1..ng+d-1] ];
    return [ quo< F | rels > ];
  end if;
  F, FtoG := FPGroup(G:StrongGenerators:=false);
  return &cat[ DistinctExtensionsNew(G,sub<G|>,F,M : FtoG:=FtoG ) : M in mods ];
end intrinsic;

intrinsic ExtensionsOfElementaryAbelianGroup
   (p :: RngIntElt, d :: RngIntElt, G :: GrpPerm, cqt :: Tup) -> SeqEnum
{All extensions (up to isomorphism with N fixed) of an elementary abelian group
 of order p^d by a group G}
  /* In this version, <tup> contains lots of additional parameters:
   * F, N, Nmoddegs, centquot, GQ, proj.
   * N is a normal subgroup of G, and the 'up to isomorphism'
   * means 'up to an isomorphism fixing N', so we get may get more extensions.
   * F is a presentation of G with corresponding generators.
   * Nmoddegs are the degrees of the irreducible constituents of the
   * representative modules as N-modules.
   * If centquot is true, then we only consider modules on which N acts
   * trivially. In that case, GQ should be a faithful perm. rep. of G/N.
   * and proj the map G -> G/N
   */
  local mods, rho, triv, id, abmods, F, N, Nmoddegs, centquot, GQ, proj;
  if not IsPrime(p) then
     error "First argument must be prime";
  end if;
  F := cqt[1];
  N := cqt[2];
  Nmoddegs := cqt[3];
  //centquot := cqt[4];
  centquot := false;
  GQ := cqt[5];
  proj := cqt[6];
  if not IsNormal(G,N) then
     error "N should be a normal subgroup of G";
  end if;
  if centquot then
    abmods := RepresentativeModules(GQ,sub<GQ|>,GF(p),d);
    mods := [];
    for m in abmods do
      rho := Representation(m);
      Append(~mods,GModule(G,[rho(proj(G.i)) : i in [1..Ngens(G)]]));
    end for;
  else
    mods := RepresentativeModules(G,N,GF(p),d);
    mods := [ m : m in mods |  Nmoddegs eq
             Sort([Dimension(c) : c in CompositionFactors(Restriction(m,N))])];
  end if;
  vprint GrpExt,1: #mods, "modules to consider";
  return &cat[ DistinctExtensionsNew(G,N,F,M) : M in mods ];
end intrinsic;

ModuleForFPGroup := function(F,M)
/* M should be a module for a group G, and F an e an FP-group isomorphic to
 * G with corresponding generators.
 * The corresponding module for F is returned.
 */
  return GModule(F,[ActionGenerator(M,i):i in [1..Nagens(M)]]);
end function;

RelatorValue := function(E,M,r)
/* M should equal ModuleForFPGroup(F,MM), where MM is a module  for a
 * permutation group G isomorphic to a
 * finitely presented group F, and r is a
 * defining relator of F (i.e. a word of form LHS(rr)*RHS(rr)^-1
 * where rr is in Relations(F)).
 * E should be an extension of M by F resulting from a call of
 * Extension(EP,Q), where EP = ExtensionProcess(G,M,F).
 * The value of r (which should be a prefix of one
 * of the relators of E) as an element of M is computed from this
 * relation of E.
 */
  local w, lr, match, pos, found, F, ng, map, mw, modelt;
  
  F := Group(M);
  map := hom< F -> E | [E.i : i in [1..Ngens(F)] ] >;
  w := map(r);
  ng := Ngens(F);
  found := false;
  for r in Relations(E) do
    if RHS(r) ne Id(E) then
       error "Relations of E are not in expected form";
    end if;
    lr := LHS(r);
    match, pos := Match(lr,w,1);
    if match and pos eq 1 then
      found := true;
        mw := ElementToSequence(w^-1*lr);
        modelt := M!0;
        for i in [1..#mw] do
          if Abs(mw[i])-ng le 0 or Abs(mw[i])-ng gt Dimension(M) then
            found := false; break;
          end if;
          if mw[i] gt 0 then
             modelt -:= M.(mw[i]-ng);
          else
             modelt +:= M.(-mw[i]-ng);
          end if; 
        end for;
      if found then break; end if;
    end if;
  end for;


  if not found then
    error "Did not find relation of E with w as prefix";
  end if;

  return modelt;
end function;

SplitExtensionPermGroup := function(G,M)
/* G should be a finite group and M a module for G over a finite field.
 * the semidirect product of M by G is returned as a permutation group
 * with two orbits of lengths |M|, deg(G), where the action on the first
 * orbit has M as a regular normal subgroup, and the action on the
 * second is the same as G.  The images of G, M in this
 * permutation group are also returned.
 */
  local ME, phi, deg, gens, gen,  S;
  ME := [m : m in M];
  phi := Representation(M);
  /* first generators of G in action on M */
  gens := [];
  for i in [1..Ngens(G)] do 
    mat := phi(G.i);
    gen := [ Position(ME,ME[j]*mat) : j in [1..#ME] ] cat
           [ #ME + j^(G.i) : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;
  /* next generators of M */
  for i in [1..Ngens(M)] do
    gen := [ Position(ME,ME[j]+M.i) : j in [1..#ME] ] cat
           [ #ME + j : j in [1..Degree(G)] ];
    Append(~gens, gen );
  end for;

  deg := #ME + Degree(G);
  S := sub< Sym(deg) | gens >;
  return S, sub<S | [S.i:i in [1..Ngens(G)] ] >,
            sub<S | [S.i:i in [1+Ngens(G)..Ngens(S)] ] >;
end function;

intrinsic DistinctExtensions
   (G :: GrpPerm, N :: GrpPerm, F :: GrpFP, M :: ModGrp:
                  FtoG:=hom<F->G|[G.i: i in [1..Ngens(G)]]> ) -> SeqEnum
{All extensions (up to isomorphism) of M by G}
/* M is a module for permutation group G over a prime field.
 * N is a normal subgroup of G.
 * F is a presentation of G with corresponding generators.
 * This function returns a list of presentations for nonisomorphic extensions
 * of M by G, where two such extension E1,E2 are isomorphic if there exists
 * a group isomorphism  E1->E2 that maps N to N and M to M.
 * (Note that if M is not characteristic in E1, then it is possible for E1, E2
 *  to be isomorphic as groups, but not as extensions in this sense.)
 */
  local FM, S, H, MM, A, cno, auto, autno, innerno, derno, modautno,
        StoG, GtoS, der, modaut, FF, FtoFF, rels, genims, phi, orels,
        allrelims, relims, F2, FFtoF2, F2M,
        cd, ch2, EP, E, d, K, p, V, W,  cem, B2, H2, H2vecs, H2vec,
        convmat, actionmats, actionmat, MMab, MMtiMMab, Mmat, imvec, relim,
        MG, reps, rep, extensions, map, proj, keeprels, FE, w, lr, match, pos,
        NN, Norb, Nstab, Nreps, orbno, Ni, Nia,  sa, P, R, Q, x;
  vprint GrpExt,1: "  Next module";
  ch2 := CohomologicalDimension(G,M,2);
  vprint GrpExt,1: "  Dimension of cohomology group =",ch2;
  // first deal with some easy cases
  if ch2 eq 0 then
    EP := ExtensionProcess(G,M,F);
    return [Extension(EP,[])];
  end if;
  //Calculate cd, the degree of the splitting field of M
  if not IsIrreducible(M) then
    cd := 0;
  elif IsAbsolutelyIrreducible(M) then
    cd := 1;
  else
    _,_,cd := IsAbsolutelyIrreducible(M);
  end if;
  if ch2 eq 1 or ch2 eq cd then //only one nonsplit extension in this case
    EP := ExtensionProcess(G,M,F);
    return  [ Extension(EP,[0:i in [1..ch2]]),
              Extension(EP,[1] cat [0:i in [1..ch2-1]]) ];
  end if;
  nrels := #Relations(F);
  S, H, MM := SplitExtensionPermGroup(G,M);
  StoG := hom < S->G |
             [G.i : i in [1..Ngens(G)]] cat [Id(G): i in [1..Ngens(MM) ]] >;
  GtoS := hom < G->S | [S.i : i in [1..Ngens(G)]]  >;
  NN := sub< S | GtoS(N), MM >;
  A := AutGpSG(S,H,MM);
  autno := Ngens(A);
  innerno := #A`InnerGenerators;
  // the first innerno generators of A are inner
  // the next few (up to derno) are derivations.
  der := true;
  cno := innerno+1;
  while der and cno le autno do
    auto := A.cno;
    for s in Generators(S) do
      if not s^-1*auto(s) in MM then
         der := false;
         break;
      end if;
    end for;
    if der then
      for n in Generators(MM) do
        if n ne auto(n) then
           der := false;
           break;
        end if;
      end for;
    end if;
    if der then cno +:= 1; end if;
  end while;
  derno := cno-1;
  // the next few (up to modautno) are module automorphisms 
  modaut := true;
  while modaut and cno le autno do
    auto := A.cno;
    for s in Generators(S) do
      if not s^-1*auto(s) in MM then
         modaut := false;
         break;
      end if;
    end for;
    if modaut then cno +:= 1; end if;
  end while;
  modautno := cno-1;

  /* Perform an orbit-stabiliser calculation for the action of the outer
   * automorphisms in A on NN.
   */
  Norb := [NN];
  Nreps := [Id(A)];
  Nstab := [A.i : i in [derno+1..modautno]];
  // we will need these together with stabilising outer automorphisms.
  orbno:=1;
  while orbno le #Norb do
    Ni := Norb[orbno];
    for i in [modautno+1..autno] do
      a := A.i;
      Nia := Ni@a;
      pos := Position(Norb,Nia);
      if pos eq 0 then
        Append(~Norb,Nia);
        Append(~Nreps,Nreps[orbno]*a);
      else
        sa := Nreps[orbno]*a*Nreps[pos]^-1;
        if not IsInner(sa) and Position(Nstab,sa) eq 0 then
          Append(~Nstab,sa);
        end if;
      end if;
    end for;
    orbno +:=1;
  end while;
  vprint GrpExt,1: "  ",#Nstab, "stabilizing automorphisms";

  modautno := modautno - derno;
  autno := #Nstab;
  if autno-modautno gt 3 then
    // try to reduce the aut. gp. generated by Nstab
     phi,P:=ClassAction(A);
     vprint GrpExt,1: "  Degree of class action =",Degree(P);
     Q := sub< P | [phi(Nstab[i]) : i in [modautno+1..autno]] >;
     R := sub<Q|>;
     while R ne Q do
       x := Random(Q);
       while x in R do  x := Random(Q); end while;
       R := sub<Q|R,x>;
     end while;
     if Ngens(R) lt autno-modautno then
       Nstab := [Nstab[i]:i in [1..modautno]] cat
                [(R.i) @@ phi : i in [1..Ngens(R)]];
     end if;
     vprint GrpExt,1: "  ",#Nstab, "stabilizing automorphisms now";
  end if;
  autno := #Nstab;
  /* Now we find the images of the group relators under the automorphisms
   * of S that act nontrivially on G.
   * At the same time we build up a new FPGroup for G that contains the
   * original relators together with each of these images.
   */
  vprint GrpExt,1: "  Setting up extension";
  FF := FreeGroup(Ngens(F));
  FtoFF := hom< F -> FF | [FF.i : i in [1..Ngens(F)] ] >;
  rels := [ FtoFF(LHS(r)*RHS(r)^-1) : r in Relations(F) ];
  orels := rels;
  allrelims := [];
  //FtoG := hom< F->G | [G.i : i in [1..Ngens(G)]] >;
  for cno in [modautno+1..autno] do
    auto := Nstab[cno]^-1;
    genims := [ H.i @ auto @ StoG @@ FtoG @ FtoFF : i in [1..Ngens(G)] ];
    phi := hom < FF->FF | genims >;
    relims := [ phi(o) : o in orels ];
    rels := rels cat relims;
    Append(~allrelims,relims);
  end for;
  F2, FFtoF2 := quo < FF | rels >;
  orels := [ FFtoF2(r) : r in orels ];
  allrelims := [ [FFtoF2(r) : r in ar ] : ar in allrelims ];
  EP := ExtensionProcess(G,M,F2);
  d := Dimension(M);
  FM := ModuleForFPGroup(F,M);
  F2M := ModuleForFPGroup(F2,M);
  cem := ComplementEquationsMatrix(FM);
  K := Field(M);
  V := VectorSpace(K,nrels*d);
  B2 := sub< V | [V!(cem[i]) : i in [1..Ngens(G)*d] ] >;
    // B2 represents the space of 2-coboundaries.
  H2vecs := [];
  for i in [1..ch2] do
    E := Extension(EP,[0:j in [1..i-1]] cat [1] cat [0 : j in [i+1..ch2]]);
    H2vec := [];
    for r in orels do
      H2vec := H2vec cat ElementToSequence(RelatorValue(E,F2M,r));
    end for;
    _,H2vec := DecomposeVector(B2,V!H2vec);
    Append(~H2vecs,H2vec);
  end for;
  H2 := sub< V | H2vecs >;
    // H2 represents the space of 2-cocyles mod H2 = B2 + H2.
  /* We are going to want to write elements of H2 in terms of the
   * given generating set H2vecs rather than the echelonised basis, so we
   * need to use a conversion matrix. (The 'Coordinates' function use
   * the echlonised basis.)
   */
  convmat:=Matrix(K,ch2,&cat[Coordinates(H2,H2.i):i in [1..ch2] ]) ^ -1;
  // multiply 'coordinates on right by convmat to get what we want

  /* Now we start to build up the ch2Xch2 matrices describing the action of
   * the automorphisms in Nstab on H2.
   * We need a mechanism to convert elements of MM to vectors 
   */
  p := Characteristic(K);
  MMab := FreeAbelianGroup(d);
  MMab := quo< MMab | [p*MMab.i : i in [1..d]]>; 
  MMtoMMab := hom< MM->MMab | [MMab.i : i in [1..d]] >;
  actionmats := [];
  // First the module autos.
  for cno in [1..modautno] do
    auto := Nstab[cno];
    //build dxd matrix of action on M
    Mmat := [];
    for i in [1..d] do
      Append(~Mmat,ElementToSequence(MMtoMMab(auto(MM.i))));
    end for;
    Mmat := Matrix(K,d,&cat(Mmat));
    actionmat := [];
    for i in [1..ch2] do
     //multiply each length d block of H2.i by Mmat
      imvec := V!(ElementToSequence(Matrix(K,d,ElementToSequence(H2.i))*Mmat));
      _,imvec := DecomposeVector(B2,imvec); 
      Append(~actionmat,Vector(K,Coordinates(H2,imvec))*convmat);
    end for;
    actionmat := Matrix(actionmat);
    Append(~actionmats,actionmat);
  end for;
  // Now the automorphisms that act nontrivially on G
  W := VectorSpace(K,d);
  vprint GrpExt,1:
      "  Computing general automorphism actions for",autno-modautno,"auts";
  for cno in [modautno+1..autno] do
    relims := allrelims[cno-modautno];
    auto := Nstab[cno];
    //build dxd matrix of action on M
    Mmat := [];
    for i in [1..d] do
      Append(~Mmat,ElementToSequence(MMtoMMab(auto(MM.i))));
    end for;
    Mmat := Matrix(K,d,&cat(Mmat));
    actionmat := [];
    for i in [1..ch2] do
      imvec := [];
      for j in [1..nrels] do
        relim := relims[j];
        //find the value in MM of relim in H2.i and multiply by Mmat.
        E := Extension(EP,[0:k in [1..i-1]] cat [1] cat [0 : k in [i+1..ch2]]);
        imvec := imvec cat
                 ElementToSequence((W!RelatorValue(E,F2M,relim))*Mmat);
      end for;
      imvec := V!imvec;
      _,imvec := DecomposeVector(B2,imvec); 
      Append(~actionmat,Vector(K,Coordinates(H2,imvec))*convmat);
    end for;
    actionmat := Matrix(actionmat);
    Append(~actionmats,actionmat);
  end for;

  /* The orbit representatives of the action of the matrix group generated
   * by actionmats on the underlying vector space represent the
   * distinct (nonisomorphic) extensions of M by G */
  MG := sub< GL(ch2,K) | actionmats >;
  reps := [ Representative(o) : o in Orbits(MG) ];
  vprint GrpExt,1: "  ",#reps,"orbit representatives";
  extensions :=  [];
  for rr in reps do
    rep := ElementToSequence(rr);
    rep := [ Integers()!x : x in rep ];
    E := Extension(EP,rep);
    // clean up by discarding superfluous relations.
    map := hom< F2 -> E | [E.i : i in [1..Ngens(F2)] ] >;
    proj := hom< E -> F2 |
                 [F2.i : i in [1..Ngens(F2)] ] cat [Id(F2) : i in [1..d]] >;
    keeprels := [ LHS(r) : r in Relations(E) | proj(LHS(r)) eq Id(F2) ];
     //these are the module and action relations of G on M
    for orel in orels do
      w := map(orel);
      for r in Relations(E) do
        lr := LHS(r);
        match, pos := Match(lr,w,1);
        if match and pos eq 1 then
          Append(~keeprels,lr);
          break;
        end if;
      end for;
    end for;
    FE := FreeGroup(Ngens(E));
    map := hom< E-> FE | [FE.i : i in [1..Ngens(E)]] >;
    E := quo< FE | [map(r) : r in keeprels] >; 
    Append(~extensions,E);
  end for;
  vprint GrpExt,1: "  ",#extensions,"extensions";

  return extensions;
end intrinsic;

/*
intrinsic DistinctExtensionsNew
   (G :: GrpPerm, N :: GrpPerm, F :: GrpFP, M :: ModGrp:
                  FtoG:=hom<F->G|[G.i: i in [1..Ngens(G)]]> ) -> SeqEnum
{All extensions (up to isomorphism) of M by G}
*/
DistinctExtensionsNew := function (G, N, F, M:
                  FtoG:=hom<F->G|[G.i: i in [1..Ngens(G)]]> )
/* M is a module for permutation group G over a prime field.
 * N is a normal subgroup of G.
 * F is a presentation of G with corresponding generators.
 * of M by G, where two such extension E1,E2 are isomorphic if there exists
 * a group isomorphism  E1->E2 that maps N to N and M to M.
 * (Note that if M is not characteristic in E1, then it is possible for E1, E2
 *  to be isomorphic as groups, but not as extensions in this sense.)
 */
  local sgno, GF, p, K, ng, RG, nr, d, E, P, Q, MM, EtoP, EtoG, A,
        H2, dH2, H2mats, H2mat, Gtriv, Mims, Mactmat, w, Gims, Gaut,
        Relims, seq, emat, lv, Relimvals, MtoE, z,
        cno, auto, autno, innerno, derno, modautno,
        PtoG,NN, Norb, Nstab, Nreps, orbno,Ni,a,Nia,pos,sa,phi,PP,QQ,RR,x,
        MG,reps,rep,extensions;

        function ExtPres(CM,seq,F,sgno)
        // variant of ExtensionOfModuleSG to produce extension
        // on generators of original group G.
         local invar, G, mats, imats, p, K, gens, w, g, RG, nr,
               d, emat, FF, rels, rel, rel1, rel2, phi, Z, E, mc;
        
          emat := seq eq [0:i in [1..Dimension(CM`H2)]] select []
                  else MatrixOfExtensionSG(CM, seq);
          Z := Integers();
          mats:=CM`mats; imats:=CM`imats;
          K := CM`ring;
          p := #K;
        
          ng := Ngens(F);
          RG := Relations(F);
          nr := #RG;
          d := CM`dim;
        
          //Now we can construct the extension.
          FF := FreeGroup(ng+d);
          rels := [];
          for i in [1..d] do
            Append(~rels,(FF.(ng+i))^p);
          end for;
          for i in [1..d] do for j in [i+1..d] do
            Append(~rels,(FF.(ng+i),FF.(ng+j)));
          end for; end for;
          for i in [1..ng] do for j in [1..d] do
            if sgno[i] eq 0 then w := FF.(ng+j);
            else
              w:=Id(FF);
              for k in [1..d] do
                w := w * (FF.(ng+k))^(Z!mats[sgno[i]][j][k]);
              end for;
            end if;
            Append(~rels,FF.i^-1*FF.(ng+j)*FF.i*w^-1);
          end for; end for;
          phi := hom<F->FF | [FF.i : i in [1..ng]] >;
          for k in [1..nr] do
            rel := LHS(RG[k])*RHS(RG[k])^-1;
            rel1 := ElementToSequence(rel);
            // convert to strong generator numebrs
            rel2 := [];
            for k in rel1 do
              if k gt 0 and sgno[k] gt 0 then Append(~rel2,sgno[k]);
              elif k lt 0 and sgno[-k] gt 0 then Append(~rel2,-sgno[-k]);
              end if;
            end for;
            rel := phi(rel);
            if emat cmpne [] then
              mc:=ElementToSequence(EvaluateCocycleSG(CM,emat,rel2));
              for i in [1..d] do
                rel := rel*FF.(ng+i)^-(Z!mc[i]);
              end for;
            end if;
            Append(~rels,rel);
          end for;
        
          E := quo<FF|rels>;
         return E;
        end function;

  vprint GrpExt,1: "  Next module";

  
  G`BSGS := RandomSchreierCoding(G);
  CM := CohomologyModule(G,M);
  // Each generator of G is either identity or of the strong generators in
  //CM`gr`sg.  We start by recording which one!
  sgno := [ Position(CM`gr`sg,G.i) : i in [1..Ngens(G)] ];

  //l1 := CM`gr`sg;
  //l2 := [G.i : i in [1..Ngens(G)] ];
  //sgno := [ Position(l1,x) : x in l2 ];
  //l1;l2;sgno;

  H2:=CohomologyGroup(CM,2);
  ch2 := Dimension(H2);

  vprint GrpExt,1: "  Dimension of cohomology group =",ch2;
  // first deal with some easy cases
  if ch2 eq 0 then
    return [ExtPres(CM,[],F,sgno)];
  end if;
  //Calculate cd, the degree of the splitting field of M
  if not IsIrreducible(M) then
    cd := 0;
  elif IsAbsolutelyIrreducible(M) then
    cd := 1;
  else
    _,_,cd := IsAbsolutelyIrreducible(M);
  end if;
  if ch2 eq 1 or ch2 eq cd then //only one nonsplit extension in this case
    return  [ ExtPres(CM,[0:i in [1..ch2]],F,sgno),
              ExtPres(CM,[1] cat [0:i in [1..ch2-1]],F,sgno) ];
  end if;

  SplitExtensionPermRepSG(CM);

  GF:=CM`gr`gf;
  K := CM`ring;
  Z := Integers();
  p := #K;

  ng := Ngens(GF);
  RG := Relations(GF);
  nr := #RG;
  d := CM`dim;
  dH2 := Dimension(H2);

  E := CM`SplitExtension;
  EtoG := hom < E->GF | [GF.i : i in [1..ng]] cat [Id(GF) : i in [1..d]] >;
  P := CM`SplitExtensionPermRep;
  EtoP := hom < E->P | [P.i : i in [1..Ngens(E)]] >;
  Q := sub<P|[P.i : i in [1..ng]]>;
  MM := sub<P|[P.i : i in [ng+1..ng+d]]>;

  PtoG := hom< P->G | [ CM`gr`sg[i] : i in [1..ng]] cat [Id(G) : i in [1..d]]>;
  //time NN := N @@ CM`gr`f2p @@ EtoG @ EtoP;
  NN := N @@ PtoG;

  MtoE := hom< MM->E | [E.(ng+i) : i in [1..d]] >;
  vprint GrpExt, 1: "Computing automorphism group of split extension";
  A := AutGpSG(P,Q,MM);
  vprint GrpExt, 1: "Done - order =",#A;

  autno := Ngens(A);
  innerno := #A`InnerGenerators;
  // the first innerno generators of A are inner
  // the next few (up to derno) are derivations.
  der := true;
  cno := innerno+1;
  while der and cno le autno do
    auto := A.cno;
    for s in Generators(P) do
      if not s^-1*auto(s) in MM then
         der := false;
         break;
      end if;
    end for;
    if der then
      for n in Generators(MM) do
        if n ne auto(n) then
           der := false;
           break;
        end if;
      end for;
    end if;
    if der then cno +:= 1; end if;
  end while;
  derno := cno-1;
  // the next few (up to modautno) are module automorphisms 
  modaut := true;
  while modaut and cno le autno do
    auto := A.cno;
    for s in Generators(P) do
      if not s^-1*auto(s) in MM then
         modaut := false;
         break;
      end if;
    end for;
    if modaut then cno +:= 1; end if;
  end while;
  modautno := cno-1;

  /* Perform an orbit-stabiliser calculation for the action of the outer
   * automorphisms in A on NN.
   */
  Norb := [NN];
  Nreps := [Id(A)];
  Nstab := [A.i : i in [derno+1..modautno]];
  // we will need these together with stabilising outer automorphisms.
  orbno:=1;
  while orbno le #Norb do
    Ni := Norb[orbno];
    for i in [modautno+1..autno] do
      a := A.i;
      Nia := Ni@a;
      pos := Position(Norb,Nia);
      if pos eq 0 then
        Append(~Norb,Nia);
        Append(~Nreps,Nreps[orbno]*a);
      else
        sa := Nreps[orbno]*a*Nreps[pos]^-1;
        if not IsInner(sa) and Position(Nstab,sa) eq 0 then
          Append(~Nstab,sa);
        end if;
      end if;
    end for;
    orbno +:=1;
  end while;
  vprint GrpExt,1: "  ",#Nstab, "stabilizing automorphisms";

  modautno := modautno - derno;
  autno := #Nstab;
  if autno-modautno gt 3 then
    // try to reduce the aut. gp. generated by Nstab
     phi,PP:=ClassAction(A);
     vprint GrpExt,1: "  Degree of class action =",Degree(PP);
     QQ := sub< PP | [phi(Nstab[i]) : i in [modautno+1..autno]] >;
     RR := sub<QQ|>;
     while RR ne QQ do
       x := Random(QQ);
       while x in RR do  x := Random(QQ); end while;
       RR := sub<QQ|RR,x>;
     end while;
     if Ngens(RR) lt autno-modautno then
       Nstab := [Nstab[i]:i in [1..modautno]] cat
                [(RR.i) @@ phi : i in [1..Ngens(RR)]];
     end if;
     vprint GrpExt,1: "  ",#Nstab, "stabilizing automorphisms now";
  end if;
  autno := #Nstab;
  /* Now we start to build up the ch2Xch2 matrices describing the action of
   * the automorphisms in Nstab on H2.
   */
  H2mats := []; // list of matrices of degree dH2 giving action

  for agno in [1 .. autno] do
    // need action of Nstab[agno] on MM
    Mims := [P.i @ Nstab[agno] @ MtoE : i in [ng+1..ng+d]];
    Mactmat := Matrix(K,d,d,[0:i in [1..d^2]]);
    for r in [1..d] do
      w := Mims[r];
      for j in [1..#w] do
        g := GeneratorNumber(Subword(w,j,1));
        if g gt 0 then Mactmat[r][g-ng] +:=1;
        else Mactmat[r][-g-ng] -:=1;
        end if;
      end for;
    end for;
    //If action on P/M is nontrivial need action of Nstab[agno]^-1 on
    //group relators.
    if agno gt modautno then
      Gims := [P.i @ (Nstab[agno]^-1) @@ EtoP @ EtoG : i in [1..ng]];
      Gaut := hom<GF->GF | Gims >;
      Relims := [ (LHS(r)*RHS(r)^-1) @ Gaut : r in RG ];
    end if;

    H2mat := Matrix(K,dH2,dH2,[0: i in [1..dH2^2]]);
   // the matrix specifying the action of Nstab[agno] on H2,
   //which we now compute
    for H2gno in [1..dH2] do
      seq := [0: i in [1..dH2]]; seq[H2gno]:=1;
      emat := MatrixOfExtensionSG(CM,seq);
     if agno le modautno then
        lv := &cat [ElementToSequence(emat[i]*Mactmat) : i in [1..nr]];
     else
        Relimvals := [EvaluateCocycleSG(CM,emat,w) : w in Relims];
        lv := &cat [ElementToSequence(Relimvals[i]*Mactmat) : i in [1..nr]];
     end if;
     H2mat[H2gno] := lv @ CM`Z2toH2;
    end for;

    if H2mat ne IdentityMatrix(K,dH2) then
      Append(~H2mats,H2mat);
    end if;
  end for;

  /* The orbit representatives of the action of the matrix group generated
   * by actionmats on the underlying vector space represent the
   * distinct (nonisomorphic) extensions of M by G */
  MG := sub< GL(dH2,K) | H2mats >;
  reps := [ Representative(o) : o in Orbits(MG) ];
  vprint GrpExt,1: "  ",#reps,"orbit representatives";
  extensions :=  [];
  for rr in reps do
    rep := ElementToSequence(rr);
    rep := [ Integers()!x : x in rep ];
    Append(~extensions,ExtPres(CM,rep,F,sgno));
  end for;
  vprint GrpExt,1: "  ",#extensions,"extensions";

  return extensions;
end function; /* DistinctExtensionsNew */
