freeze;

import "compab.m":  ReduceAbAutMat, ReduceAbAutVec, CheckRelationsA,
       IsAutAndInverse, MatrixOfGroupElement,  ComplementEquationsMatrixA;

//Version for general soluble groups
MakeModuleRecordPCPGA := function(P,invar,mats)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed.
 * P is a GrpPC for a finite soluble group
 * The cohomological functions take this record as argument.
 */
  local R, PG, ng, relpos, imats, r, F, rels, PtoF, FQ, ct, MF, primes;

  PG := PCGenerators(P);
  ng := #PG;
  if ng ne #mats then
    error "Wrong number of matrices in MakeModuleRecordPCPGA";
  end if;

  primes := PCPrimes(P);
  mats := [ ReduceAbAutMat(invar,m) : m in mats];
  imats:=[];
  for i in [1..ng] do
    isit, imats[i] := IsAutAndInverse(invar,mats[i]);
    if not isit then
    error "A matrix in MakeModuleRecordPCPGA does not define an automorphism";
    end if;
  end for;

  r := EmptyCohomologyModule();
  r`modtype := GrpAb;
  r`gptype := GrpPC;
  r`gpc := P;
  r`mats := mats; r`imats := imats;
  r`invar:=invar;
  r`dim := #invar;
  r`ring := invar[#invar] eq 0 select Integers() else Integers(invar[#invar]);

  /* We need a well-defined ordering for the PC relations of P, and
   * a corresponding GrpFP to use for the ComplementEquationsMatrix.
   * We use the ordering P.1^primes[1], ... P.n^primes[ng],
   * P.2^P.1, P.3^P.1, P.3^P.2,...
   * The array relpos gives the number of the corresponding relation.
   * relpos[i][i] for P.i^p  and relpos[j][i] for P.j^P.i.
   *
   * The format for relations of an extension of M by P will be
   * P.i^primes[i] = word * m  or  P.j^P.i = word * m, for m in M, where j>i.
   */
  relpos := [ [] : i in [1..ng] ];
  F := FreeGroup(ng);
  /* function method too slow - better assume PCpres is conditioned. */
  PtoF := function(w) //map word in P to corresponding word in F
   local s; s:=ElementToSequence(w); return &*[F.i^s[i]:i in [1..ng]];
  end function;
  PtoF := hom < P->F | [F.i : i in [1..ng]] >; //unsafe
  rels := [];
  
  ct := 0;
  for i in [1..ng] do 
    ct +:= 1;
    relpos[i][i] := ct;
    Append(~rels,PtoF(P.i^primes[i])^-1 * PtoF(P.i)^primes[i] ); 
  end for;
  
  for j in [2..ng] do for i in [1..j-1] do
    ct +:= 1;
    relpos[j][i] := ct;
    Append(~rels,PtoF(P.j*P.i)^-1 * PtoF(P.j) * PtoF(P.i)); 
  end for; end for;

  r`relpos := relpos;
  r`gf := quo<F|rels>;
  r`gftoG := hom< r`gf->P | [P.i : i in [1..ng]] >;

  if not CheckRelationsA(r`gf,invar,mats:imats:=imats) then
    error "Matrices do not satisfy relations on strong generators";
  end if;
  return r;
end function;

PCElToSeq := function(w)
  /* w is a word in a PC-group. Convert to an integer sequence.
   * (ElementToSequence does not do the right thing here!)
   */
  local s, es, l;
  es := ElementToSequence(w);
  l := #es; 
  s := [];
  for i in [1..l] do
    s := s cat [ i : j in [1..es[i]] ];
  end for;
  return s;
end function;
    
OneCocyclePCPGA := function(CM,s)
//returns a function G-> module
  local nselt, OC, d, ng, K, GR, invar, mats, imats, V, genims, Z;
  nselt := ElementToSequence(((CM`H1)!s) @@ CM`Z1toH1);
  ng := Ngens(CM`gf); //same as NPCgens !
  d := CM`dim;
  K := CM`ring;
  invar := CM`invar;
  mats := CM`mats; imats:=CM`imats;
  Z := Integers();
  V := RSpace(Z,d);
  //find images of one-cocyle on generators
  genims := [ V!(nselt[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    w := PCElToSeq(g);
    cmat := IdentityMatrix(Z,d);
    ans := V!0;
    //scan from right hand end
    for g in Reverse(w) do
      if g lt 0 then
        cmat := imats[-g]*cmat;
        ans -:= genims[-g]*cmat;
      else
        ans +:= genims[g]*cmat;
        cmat := mats[g]*cmat;
      end if;
    end for;
    return ReduceAbAutVec(invar,ans);
  end function;

  return OC;
end function;

IdentifyOneCocyclePCPGA := function(CM,OC)
  //identify from action on strong generators
  local sg, s;
  sg := PCGenerators(CM`gpc);
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(Integers(),#s)!s;
  if not s in CM`Z1 then
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  return s @ CM`Z1toH1;
end function;

IsOneCoboundaryPCPGA := function(CM,OC)
//if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local ng, d, K, Z, isc, sg, v, w;

  d := CM`dim;
  K := CM`ring;
  Z := Integers();

  sg := PCGenerators(CM`gpc);
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  w := Vector(K, w);
  isc, v := IsConsistent(CM`csm, w);
  if not isc then return false, _; end if;
  /* Need lop off the unwanted end of v and write over Z. */
  V := RSpace(Z,d);
  v := V![-v[j] : j in [1..d]];
  return true, func< tp | v >;
end function;

CollectGeneralWordPCPGA := procedure(P,w,add,d,~X,colno,relpos,invar,mats,imats)
/* P is a PC-group and w a sequence of integers in the range [1..NPCgens(P)],
 * representing a word in P. The word is collected, using P.
 * As we do this, we fill in entries of X in columns [colno+1..colno+d]
 * for tails arising.
 * If add is true, add entries to X, otherwise subtract.
 */
  local wmap, actmat, primes, collecting, pos, gen, nextgen,
         genct, rowno;

  // We want the matrix for the whole word.
  // The acting matrix will be that of the suffix of the word from the
  // current point in the word.
  if #w le 1 then return; end if;
  wmat :=  mats[w[1]];
  for i in [2..#w] do wmat := wmat*mats[w[i]]; end for;
  wmat:=ReduceAbAutMat(invar,wmat);

  primes := PCPrimes(P);

  collecting := true;
  changed := true;
  while collecting do
    if changed then
       if #w le 1 then return; end if;
       pos := 1;
       gen := w[pos];
       genct := 1;
       actmat := imats[gen]*wmat;
       actmat:=ReduceAbAutMat(invar,actmat);
    end if;
    pos := pos+1;
    nextgen := w[pos];
    actmat := imats[nextgen]*actmat;
    actmat:=ReduceAbAutMat(invar,actmat);
    genct :=  nextgen eq gen select genct+1 else 1;
    if nextgen lt gen then
      Insert(~w,pos-1,pos,PCElToSeq(P.gen*P.nextgen));
      rowno := d*(relpos[gen][nextgen]-1);
      //  Alter X in positions [rowno+1..rowno+d, colno+1..colno+d]
      if add then
        InsertBlock(~X,
           ReduceAbAutMat(invar,ExtractBlock(X,rowno+1,colno+1,d,d)+actmat),
                                                          rowno+1,colno+1);
      else
        InsertBlock(~X,
           ReduceAbAutMat(invar,ExtractBlock(X,rowno+1,colno+1,d,d)-actmat),
                                                          rowno+1,colno+1);
      end if;
      changed := true;
    elif genct eq primes[gen] then
      Insert(~w,pos-primes[gen]+1,pos,PCElToSeq(P.gen^primes[gen]));
      rowno := d*(relpos[gen][gen]-1);
      //  Alter X in positions [rowno+1..rowno+d, colno+1..colno+d]
      if add then
        InsertBlock(~X,
          ReduceAbAutMat(invar,ExtractBlock(X,rowno+1,colno+1,d,d)+actmat),
                                                          rowno+1,colno+1);
      else
        InsertBlock(~X,
          ReduceAbAutMat(invar,ExtractBlock(X,rowno+1,colno+1,d,d)-actmat),
                                                          rowno+1,colno+1);
      end if;
      changed := true;
    else
      gen := nextgen;
      changed := false;
    end if;
    if not changed and pos eq #w then
      collecting := false;
    end if;
  end while;
end procedure;

SecondCohomologyGroupPCPGA := procedure(CM)
/* 
 * SecondCohomologyGroupPCPG computes a matrix and stores its nullspace, which
 *  is isomorphic to Z^2(G,M), then computes B2, H2.
 */

  local  P, mats, imats, primes, K, d, ng, nr, ncols, X, colno, rowno, relpos,
         w, invar, V1, nsgens, stg, v, Y, Z, VZ, YZ;


  if assigned CM`H2 then return; end if;
  if not assigned CM`cem then
    ComplementEquationsMatrixA(CM);
  end if;

  mats:=CM`mats; imats:=CM`imats; relpos:=CM`relpos;
  K := CM`ring;
  Z := Integers();
  invar:=CM`invar;
  d := CM`dim;
  P:=CM`gpc;
  primes:=PCPrimes(P);

  ng := NPCGenerators(P);
  nr := ng * (ng+1) div 2; // number of PC-relations

  /* Set up the matrix  X  where we will store the equations */
  ncols := d * (ng*(ng-1)*(ng-2) div 6 + ng*(ng-1) + ng); 
     // d * number of associativity conditions to be checked.
  vprint ModCoho: "Setting up",ncols,"equations in",nr*d,"unknowns";
  X:=Hom(RSpace(Z,nr*d),RSpace(Z,ncols))!0;
  
  colno:=0;

  // 1. the (P.i^primes[i])*P.i = P.i*(P.i^primes[i]) conditions.
  for i in [1..ng] do
    w := [i : n in [1..primes[i]+1]];
    CollectGeneralWordPCPGA(P,w,true,d,~X,colno,relpos,invar,mats,imats);
    w := [i] cat PCElToSeq(P.i^primes[i]); 
    rowno := d*(relpos[i][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
      if invar[k] ne 0 then X[rowno+k][colno+k]  mod:= invar[k]; end if;
    end for;
    CollectGeneralWordPCPGA(P,w,false,d,~X,colno,relpos,invar,mats,imats);
    colno +:= d;
  end for;

  // 2. the P.j*P.i*P.i^primes[i]-1 = P.j*(P.i^primes[i]) (j>i) conditions.
  for j in [2..ng] do for i in [1..j-1] do
    w := [j] cat [i : n in [1..primes[i]]];
    CollectGeneralWordPCPGA(P,w,true,d,~X,colno,relpos,invar,mats,imats);
    w := [j] cat PCElToSeq(P.i^primes[i]); 
    rowno := d*(relpos[i][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
      if invar[k] ne 0 then X[rowno+k][colno+k]  mod:= invar[k]; end if;
    end for;
    CollectGeneralWordPCPGA(P,w,false,d,~X,colno,relpos,invar,mats,imats);
    colno +:= d;
  end for; end for;

  // 3. the P.j^primes[j]*P.i = P.j^primes[j]-1*P.j*P.i (j>i) conditions.
  for j in [2..ng] do for i in [1..j-1] do
    w := [j : n in [1..primes[j]]] cat [i];
    CollectGeneralWordPCPGA(P,w,true,d,~X,colno,relpos,invar,mats,imats);
    w := [j : n in [1..primes[j]-1]] cat PCElToSeq(P.j*P.i); 
    rowno := d*(relpos[j][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
      if invar[k] ne 0 then X[rowno+k][colno+k]  mod:= invar[k]; end if;
    end for;
    CollectGeneralWordPCPGA(P,w,false,d,~X,colno,relpos,invar,mats,imats);
    colno +:= d;
  end for; end for;

  // 4. the (P.k*P.j)*P,i = P.k*(P.j*P.i) (k>j>i) conditions.
  for k in [3..ng] do for j in [2..k-1] do for i in [1..j-1] do
    w := [k,j,i];
    CollectGeneralWordPCPGA(P,w,true,d,~X,colno,relpos,invar,mats,imats);
    w := [k] cat PCElToSeq(P.j*P.i); 
    rowno := d*(relpos[j][i]-1);
    for k in [1..d] do
      X[rowno+k][colno+k] -:= 1;
      if invar[k] ne 0 then X[rowno+k][colno+k]  mod:= invar[k]; end if;
    end for;
    CollectGeneralWordPCPGA(P,w,false,d,~X,colno,relpos,invar,mats,imats);
    colno +:= d;
  end for; end for; end for;
  X := Hom(RSpace(K,nr*d),RSpace(K,ncols))!X;
  vprint ModCoho: "Done.";

  //We won't store X itself, since it is very large - we only
  // need its nullspace.
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  if k eq 0 then
    vprint ModCoho: "Getting nullspace of ",Nrows(X),"by",Ncols(X),"matrix";
    ns := Nullspace(X);
  else
    Y := Matrix(K,k,d,[0: i in [1..k*d]]);
    for i in [1..k] do Y[i][i] := invar[i]; end for;
    ns := Nullspace(VerticalJoin(X,
             DirectSum([Y :i in [1..Ncols(X) div d]])));
  end if;
  vprint ModCoho: "Got Nullspace, dimension =", Dimension(ns);

  //First lop off the unwanted ends of the rows of ns
  V1 := RSpace(K,nr*d);
  nsgens := [ V1![(ns.i)[j] : j in [1..nr*d]] : i in [1..Dimension(ns)]];
  //need to adjoin generators for invariants of abelian group.
  Y:=[];
  for g in [1..nr] do
    stg := (g-1)*d;
    for j in [1..k] do
      v := V1!0;
      v[stg+j] := invar[j];
      Append(~Y,v);
    end for;
  end for;
  nsgens cat:= Y;

  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    VZ := RSpace(Integers(),nr*d);
    YZ := [ VZ!y : y in nsgens ];
    for g in [1..nr] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
    end for;
    nsgens := YZ; V1 := VZ;
  end if;
  CM`Z2 := sub< V1 | nsgens >;
  vprint ModCoho: "Calculated Z2";

  I := Image(CM`cem);

  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    YZ := [ VZ!(I.i) : i in [1..Ngens(I)] ] cat [ VZ!y : y in Y];
    for g in [1..nr] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
    end for;
    CM`B2 := sub< VZ | YZ >;
  else CM`B2 := sub< V1 | [I.i :i in [1..Ngens(I)]] cat Y >;
  end if;
  vprint ModCoho: "Calculated B2";

  CM`H2, CM`Z2toH2 := quo< CM`Z2 | CM`B2 >;
  vprint ModCoho: "Calculated H2";

end procedure;

ExtensionOfModulePCPGA := function(CM,seq)
/* CM`H2 should have been computed already with SecondCohomologyGroup.
 * seq should be an integer sequence representing an element of  CMF`H2.
 * A PC -presentation of a corresponding extension of the module by the
 * group is returned
 */
 local Z, P, primes, p, mats, K, imats, ng, z2v, w, rels, rel, phi,
       H2, e, invar, lv, d, nr, E, A;

  if not assigned CM`H2 then
    error "Call SecondCohomologyGroupSGRep(CM) first!";
  end if;
  Z := Integers();
  P:=CM`gpc; invar:=CM`invar; mats:=CM`mats; d := CM`dim;
  ng := NPCGenerators(P);
  primes := PCPrimes(P);
  d := CM`dim;
  P:=CM`gpc;
  nr := ng * (ng+1) div 2; // number of PC-relations

  H2 := CM`H2;
  e := H2!0;
  if #seq ne Ngens(H2) then
    error "Second argument has wrong length";
  end if;
  for i in [1..#seq] do
    e +:= seq[i]*H2.i;
  end for;
  z2v := RSpace(Z,d*nr)!(e @@ CM`Z2toH2);
  z2v:=ReduceAbAutVec(invar,z2v);

  //Now we can construct the extension.
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do if invar[i] ne 0 then
    Append(~rels,(F.(ng+i))^invar[i] = Id(F));
  end if; end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,F.(ng+j)^F.(ng+i) = F.(ng+j));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^Z!mats[i][j][k];
    end for;
    Append(~rels,F.(ng+j)^F.i = w);
  end for; end for;

  phi := hom<P->F | [F.i : i in [1..ng]] >;
  colno := 0;
  for i in [1..ng] do
    w := Id(F);
    for k in [1..d] do w := w * F.(ng+k)^Z!z2v[colno+k];  end for;
    Append(~rels,phi(P.i)^primes[i] = phi(P.i^primes[i])*w);
    colno +:= d;
  end for;

  for j in [2..ng] do for i in [1..j-1] do
    w := Id(F);
    for k in [1..d] do w := w * F.(ng+k)^Z!z2v[colno+k];  end for;
    Append(~rels,phi(P.j)^phi(P.i) = phi(P.j^P.i)*w);
    colno +:= d;
  end for; end for;

  E := quo<GrpGPC: F | rels >;
  A := AbelianGroup(invar);
  E`Projection :=
   hom< E -> P | [P.i: i in [1..ng]] cat [Id(P) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  return E, E`Projection, E`Injection;
end function;

TwoCocyclePCPGA := function(CM,s)
  /* Returns 2-cocylec function of extension defined by s */
  local E, P, ng, d, K, phi;
  E := ExtensionOfModulePCPGA(CM,ElementToSequence(s));
  invar := CM`invar;
  P := CM`gpc;
  ng := NPCGenerators(P);
  d := CM`dim;
  K := Integers();
  phi := hom< P->E | [E.i : i in [1..ng] ] : Check:=false >;

  TC := function(gtp)
  /* g1,g2 should be elements of G = CM`gpc.
   * Lift g1,g2,g1*g2 to w1,w2,w3 in E.
   * m in module such that w1*w2 = w3*m in E is returned.
   */
   local w1, w2, w3, s, m, g1, g2;
   g1 := gtp[1];
   g2 := gtp[2];
   w1 := phi(g1);
   w2 := phi(g2);
   w3 := phi(g1*g2);
   s := ElementToSequence(w3^-1*w1*w2);
   m := RSpace(K,d)![ s[i] : i in [ ng+1 .. ng+d] ];
   return ReduceAbAutVec(invar,m);
  end function;
  return TC;
end function;

IdentifyTwoCocyclePCPGA := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * The corresponding element of CM`H2 is returned.
 * For each relator w of G, we use the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the required element of H2.
 */
  local P, V, primes, K, catrv, w, rv, suff, g, F, PtoF, rels,
        invwds, mats, imats, cmat, r, ans;
  P := CM`gpc;
  primes := PCPrimes(P);
  ng := NPCGenerators(P);
  mats := CM`mats; imats := CM`imats;
  K := BaseRing(mats[1]);
  V := RSpace(K,CM`dim);
  F := FreeGroup(ng);
  PtoF := function(w) //map word in P to corresponding word in F
   local s; s:=ElementToSequence(w); return &*[F.i^s[i]:i in [1..ng]];
  end function;
  //PtoF := hom < P->F | [F.i : i in [1..ng]] >;

  //We first have to sort out terms for inverses of generators
  invwds := [];
  for i in [1..ng] do
    invwds[i] := -(V!TC(<P.i,P.i^-1>));
  end for;
  TC1 := V!TC(<Id(P),Id(P)>);

  rels := [];
  for i in [1..ng] do
    Append(~rels,PtoF(P.i^primes[i])^-1 * PtoF(P.i)^primes[i] );
  end for;
  for j in [2..ng] do for i in [1..j-1] do
    Append(~rels,PtoF(P.j*P.i)^-1 * PtoF(P.j) * PtoF(P.i));
  end for; end for;

  catrv := [];
  suff := Id(P);
  cmat := mats[1]^0;
  for r in rels do
    w := ElementToSequence(r);
    rv := V!0;
    for j in Reverse(w) do
      if j gt 0 then
        rv +:= V!TC(<P.j, suff>);
        suff := P.j*suff;
        cmat := mats[j]*cmat;
      else
        rv +:= (invwds[-j] - TC1)*cmat;
        rv +:= V!TC(<P.j, suff>);
        suff := P.j*suff;
        cmat := imats[-j]*cmat;
      end if;
    end for;
    catrv := catrv cat ElementToSequence(rv);
  end for;
  catrv := RSpace(Integers(),#catrv)!catrv;
  if not catrv in CM`Z2 then
    error "Input to IdentifyTwoCocycle is not a cocycle";
  end if;

  return catrv @ CM`Z2toH2;
end function;

IsTwoCoboundaryPCPGA := function(CM,TC)
/* Here TC must be a function of 2-variables defining a two-cycle
 * If it is a two coboundary, then a 1-cocycle OC is returned
 * such that TC(<g1,g2>) = OC(<g1>)^g2 + OC(<g2>) - OC(g1g2>). 
 * For each relator w of G, we usr the two-cocycle to evaluate  w in M,
 * then cat all the values together to give a vector which identifies.
 * the element of H2.
 */
  local K, Z, V, catrv, w, rv, suff, g, F, FtoG, invwds, mats, cmat, invar, dim,
        P, primes, d, G, ng, genims, OC, sg;

  P := CM`gpc;
  primes := PCPrimes(P);
  ng := NPCGenerators(P);
  mats := CM`mats; imats := CM`imats;
  K := BaseRing(mats[1]);
  F := FreeGroup(ng);
  PtoF := function(w) //map word in P to corresponding word in F
   local s; s:=ElementToSequence(w); return &*[F.i^s[i]:i in [1..ng]];
  end function;
  //PtoF := hom < P->F | [F.i : i in [1..ng]] >;

  invar:=CM`invar; dim := #invar;
  Z := Integers();
  K := CM`ring;
  V := RSpace(Z,dim);

  //We first have to sort out terms for inverses of generators
  invwds := [];
  for i in [1..ng] do
    invwds[i] := -(V!TC(<P.i,P.i^-1>));
  end for;
  TC1 := V!TC(<Id(P),Id(P)>);

  rels := [];
  for i in [1..ng] do
    Append(~rels,PtoF(P.i^primes[i])^-1 * PtoF(P.i)^primes[i] );
  end for;
  for j in [2..ng] do for i in [1..j-1] do
    Append(~rels,PtoF(P.j*P.i)^-1 * PtoF(P.j) * PtoF(P.i));
  end for; end for;

  catrv := [];
  suff := Id(P);
  cmat := mats[1]^0;
  for r in rels do
    w := ElementToSequence(r);
    rv := V!0;
    for j in Reverse(w) do
      if j gt 0 then
        rv +:= V!TC(<P.j, suff>);
        suff := P.j*suff;
        cmat := mats[j]*cmat;
      else
        rv +:= (invwds[-j] - TC1)*cmat;
        rv +:= V!TC(<P.j, suff>);
        suff := P.j*suff;
        cmat := imats[-j]*cmat;
      end if;
    end for;
    rv := ReduceAbAutVec(invar,rv);
    catrv := catrv cat ElementToSequence(rv);
  end for;

  catrv := Vector(K, catrv);
  isc, v := IsConsistent(CM`cem, catrv);
  if not isc then return false, _; end if;

  /* Need to lop off the unwanted end of v and spliut up into vectors over Z. */

  //now define associated 1-cochain
  v := Eltseq(v);
  d := dim;
  genims := [ V!(v[(i-1)*d+1 .. i*d]) : i in [1..ng] ];

  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    if g eq Id(P) then return TC1; end if;
    w := PCElToSeq(g);
    cmat := IdentityMatrix(Z,d);
    ans := V!0;
    g := Id(P);
    //scan from right hand end
    first := true;
    for k in Reverse(w) do
      if k lt 0 then
        ans := ans + (TC1 + V!TC( <P.(-k),P.(-k)^-1>) )*cmat;
        cmat := imats[-k]*cmat;
        ans :=  first select ans - genims[-k]*cmat
                       else ans - genims[-k]*cmat - V!TC(<P.(-k)^-1,g>);
        g := P.(-k)^-1*g;
      else
        ans :=  first select ans + genims[k]*cmat
                       else ans + genims[k]*cmat - V!TC(<P.k,g>);
        g := P.k*g;
        cmat := mats[k]*cmat;
      end if;
      first := false;
    end for;
    return ReduceAbAutVec(invar,ans);
  end function;

  return true, OC;
end function;

SplitExtensionPCPGA := procedure(CM)
/* Sets CM`SplitExtension to be  finite presentation of a split extension
 * of module by G. Strong generators of G come first.
 */

 local Z, P, primes, mats, K, finite, imats, ng, z2v, w, rels, rel, phi,
       H2, e;

  if assigned CM`SplitExtension then return; end if;
  Z := Integers();
  P:=CM`gpc;
  mats:=CM`mats;
  invar:=CM`invar;
  d := CM`dim;
  K := CM`ring;
  ng := NPCGenerators(P);
  primes := PCPrimes(P);

  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do if invar[i] gt 0 then
    Append(~rels,(F.(ng+i))^invar[i] = Id(F));
  end if; end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,F.(ng+j)^F.(ng+i) = F.(ng+j));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^Z!mats[i][j][k];
    end for;
    Append(~rels,F.(ng+j)^F.i = w);
  end for; end for;

  phi := hom<P->F | [F.i : i in [1..ng]] >;
  colno := 0;
  for i in [1..ng] do
    Append(~rels,phi(P.i)^primes[i] = phi(P.i^primes[i]));
  end for;

  for j in [2..ng] do for i in [1..j-1] do
    Append(~rels,phi(P.j)^phi(P.i) = phi(P.j^P.i));
  end for; end for;

  E := quo<GrpGPC: F | rels >;
  A := AbelianGroup(invar);
  E`Projection :=
   hom< E -> P | [P.i: i in [1..ng]] cat [Id(P) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  CM`SplitExtension:= E;
end procedure;

AutGroupOnH2PCPGA := function(CM)
/* Compute action of the automorphism group of the pair (G,Module) (obtained
 * from automorphism group of split extension of module by group) on
 * H^2. Return result as sequence of matrices.
 */
  local G, P, mats, imats, invar, K, ng, RG, nr, d, E, M, EtoG, GtoEE, A, AG, 
        H2, dH2, H2invar, H2mats, H2mat, Gtriv, Mims, Mactmat, w, Gims, Gaut,
        Relims, seq, EE, lv, Relimvals, Z, Asg, ims, im, ct, cr, pos, EP, phi;

  if not assigned CM`H2 then 
     SecondCohomologyGroupPCPGA(CM);
  end if;
  if not assigned CM`SplitExtension then
    SplitExtensionPCPGA(CM);
  end if;

  P:=CM`gpc;
  mats:=CM`mats; imats:=CM`imats;
  invar := CM`invar;
  Z := Integers();
  K := CM`ring;

  H2 := CM`H2;
  H2invar := Moduli(H2);
  ChangeUniverse(~H2invar,Integers());
  d := CM`dim;
  dH2 := #H2invar;
  res := invar[d];
  if res ne 0 then
    for i in [1..#H2invar] do
      if H2invar[i] eq 0 then H2invar[i] := res; end if;
    end for;
  end if;
  ng := NPCGenerators(P);
  G := CM`gf;
  RG := Relations(G);
  nr := #RG;
  d := CM`dim;
  dH2 := #H2invar;

  E := CM`SplitExtension;
  EtoG := hom < E->G | [G.i : i in [1..ng]] cat [Id(G) : i in [1..d]] >;
  M := sub<E|[E.i : i in [ng+1..ng+d]]>;
  vprint ModCoho: "Computing automorphism group of split extension";
  EP, phi := PCGroup(E); 
  A := AutomorphismGroup(EP);
  //transfer to E
  AG := AutomorphismGroup( E, [ E.i: i in [1..ng+d]],
         [ [ E.i @ phi @ A.j @@ phi : i in [1..ng+d] ]  : j in [1..Ngens(A)] ]);
  vprint ModCoho: "Got automorphism group, order",#A,";",Ngens(A),"generators";
  // We don't want all of A - just the subgroup fixing M - to find
  // generators of that, we have to do an orbit-stabilizer argument.
  Asg := [];
  ims := [M];
  cr := [ Id(AG) ];
  ct := 1;
  while ct le #ims do
    im := ims[ct];
    for n in [1..Ngens(A)] do
      if IsInner(A.n) then continue; end if;
      a := AG.n;
      pos := Position(ims,im @ a);
      if pos eq 0 then
        Append(~ims,im @ a);
        Append(~cr,cr[ct] * a);
      else
        Append(~Asg,cr[ct] * a * cr[pos]^-1);
      end if;
    end for;
    ct +:= 1;
  end while;
  vprint ModCoho: "Got stabilizer of module in automorphism group,
         order",#A div #ims,"; ",#Asg,"generators";

  H2mats := []; // list of matrices of degree dH2 giving action
  Z2deg := Degree(CM`Z2);
  V1 := RSpace(K,Z2deg);
  V2 := RSpace(Z,dH2);
  V3 := RSpace(K,dH2);
  V4 := RSpace(Z,Z2deg);

  for a in Asg do
    //If actions on E/M and M are trivial then we can skip it 
    Gtriv := true;
    for gno in [1..ng] do
      if not E.gno^-1 * (E.gno @ a) in M then
         Gtriv := false;
         break;
      end if;
    end for;
    // need action of a on M
    Mims := [E.(ng+i) @ a : i in [1..d]];
    if Gtriv then
      if [E.(ng+i) : i in [1..d]] eq Mims then
        //action on M is also trivial
          continue a;
       end if;
    end if;
    Mactmat := Matrix(Z,d,d,[0:i in [1..d^2]]);
    for r in [1..d] do
      w := ElementToSequence(Mims[r]);
      for g in [ng+1..ng+d] do
        Mactmat[r][g-ng] +:= w[g];
      end for;
    end for;
    Mactmat := ReduceAbAutMat(invar,Mactmat);
    //If action on E/M is nontrivial need action of a^-1 on group relators.
    if not Gtriv then
      Gims := [ EtoG( E.i @ (a^-1) ) : i in [1..ng]];
      Gaut := hom<G->G | Gims >;
      Relims := [ (RHS(r)^-1*LHS(r)) @ Gaut : r in RG ];
    end if;

    H2mat := Matrix(Z,dH2,dH2,[0: i in [1..dH2^2]]);
   // the matrix specifying the action of a on H2, which we now compute
    for H2gno in [1..dH2] do
      seq := [0: i in [1..dH2]]; seq[H2gno]:=1;
     if Gtriv then
        //lv := V4!((V3!seq) @@ CM`Z2toH2);
        lv := seq @@ CM`Z2toH2;
        for i in [1..nr] do
          InsertBlock(~lv,
              ExtractBlock(lv,1,d*(i-1)+1,1,d)*Mactmat, 1,d*(i-1)+1);
        end for;
     else
        EE := ExtensionOfModulePCPGA(CM,seq);
        GtoEE := hom < G->EE | [EE.i : i in [1..ng]] >;
        Relimvals := [w @ GtoEE : w in Relims];
        lv := [];
        for i in [1..nr] do
          lv[i] := Vector(Z,[0: j in [1..d]]); 
          w := ElementToSequence(Relimvals[i]);
          for g in [ng+1..ng+d] do
            lv[i][g-ng] +:= w[g];
          end for;
          lv[i] := lv[i] * Mactmat;
        end for;
        lv := &cat [ ElementToSequence(v) : v in lv ];
     end if; 
     //H2mat[H2gno] := V2!((V1!lv) @ CM`Z2toH2);
     H2mat[H2gno] := lv @ CM`Z2toH2;
    end for;

    if H2mat ne IdentityMatrix(Z,dH2) then
      Append(~H2mats,H2mat);
    end if;
  end for;

  return H2mats;
end function;

DistinctExtensionsPCPGA := function(CM)
/* Compute orbit representatives of this action, and return
 * a list of presentations of the corresponding extensions.
 */
  local  H2mats, Z, H2invar, cd, V, H2elts, celt, lev, had,
         orbreps, orb, ct, rep, imrep;

  if not assigned CM`H2 then
     SecondCohomologyGroupPCPGA(CM);
  end if;
  if #(CM`H2) eq 0 then
    SplitExtensionPCPGA(CM); return [CM`SplitExtension];
  end if;
  H2mats := AutGroupOnH2PCPGA(CM);
  H2invar := Moduli(CM`H2);
  ChangeUniverse(~H2invar,Integers());
  d := CM`dim;
  invar := CM`invar;
  cd := #H2invar;
  res := invar[d];
  if res ne 0 then
    for i in [1..cd] do
      if H2invar[i] eq 0 then H2invar[i] := res; end if;
    end for;
  end if;

  Z := Integers();
  V := RSpace(Z,cd);
  /* First we have to make a list of all elements of the abelian group
   * define by H2invar.
   */
  celt := [0: i in [1..cd]];
  H2elts := {@ V!celt @};
  lev := cd;
  while lev gt 0 do
    celt[lev] +:= 1;
    if celt[lev] eq H2invar[lev] then
      celt[lev] := 0;
      lev -:=1;
      continue;
    end if;
    Include(~H2elts,V!celt);
    lev := cd;
  end while;

  //now work out orbits of action.
  had := [ false : i in [1..#H2elts] ];
  had[1] := true;
  orbreps := [1];
  for H2eltno in [2..#H2elts] do
    if had[H2eltno] then
      continue;
    end if;
    Append(~orbreps,H2eltno);
    orb := [H2eltno];
    ct := 1;
    while ct le #orb do
      rep := orb[ct];
      had[rep] := true;
      for mat in H2mats do
        imrep := Position(H2elts,ReduceAbAutVec(H2invar,H2elts[rep]*mat));
        if not had[imrep] then
          had[imrep] := true;
          Append(~orb,imrep);
        end if;
      end for;
      ct +:= 1;
    end while;
  end for;

  return
    [ ExtensionOfModulePCPGA(CM,ElementToSequence(H2elts[x])) : x in orbreps ];

end function;

