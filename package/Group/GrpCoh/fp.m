freeze;

import "compab.m":  ReduceAbAutMat, ReduceAbAutVec, CheckRelationsA,
       IsAutAndInverse, MatrixOfGroupElement,  ComplementEquationsMatrixA;
forward CheckRelations;

//Version for fp-groups
MakeModuleRecordFPG := function(G,M)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed. 
 * G is a GrpFP
 * M should be a module for G over K.
 * The cohomological functions take this record as argument.
 */ 
  local R, gens, ng, relpos, mats, imats, r, rels, PtoF, FQ, ct, MF;

  R := Representation(M);
  gens := [ G.i : i in [1..Ngens(G)] ];
  ng := #gens;
  mats := [ R(gens[i]) : i in [1..ng] ];
  imats := [ m^-1 : m in mats ];
  r := EmptyCohomologyModule();
  r`modtype := ModGrp;
  r`gptype := GrpFP;
  r`module := M;
  r`gf := G;
  r`gftoG := IdentityHomomorphism(G);
  r`mats := mats; r`imats := imats;
  r`dim := Dimension(M);
  r`ring := BaseRing(M);

  if not CheckRelations(r`gf,mats : imats:=imats) then
    error "Matrices do not satisfy group relations";
  end if;

  return r;
end function;

MakeModuleRecordFPGA := function(G, invar, mats)
/* This is called prior to calling any of the cohomological functions,
 * and returns a cohomology module with fields for the various objects
 * that may get computed. 
 * G is a GrpFP
 * M should be a module for G over K.
 * The cohomological functions take this record as argument.
 */ 
  local gens, ng, relpos, imats, r, rels, PtoF, FQ, ct, MF;
  gens := [ G.i : i in [1..Ngens(G)] ];
  ng := #gens;
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
  r`gptype := GrpFP;
  r`gf := G;
  r`gftoG := IdentityHomomorphism(G);
  r`mats := mats; r`imats := imats;
  r`invar:=invar;
  r`dim := #invar;
  r`ring := invar[#invar] eq 0 select Integers() else Integers(invar[#invar]);

  if not CheckRelationsA(r`gf,invar,mats:imats:=imats) then
    error "Matrices do not satisfy relations on strong generators";
  end if;

  return r;
end function;

OneCocycleFPG := function(CM,s)
//returns a function G-> module
  local nselt, OC, d, ng, K, GR, mats, imats, V, genims;
  nselt := ElementToSequence(((CM`H1)!s) @@ CM`Z1toH1);
  ng := Ngens(CM`gf); //same as NPCgens !
  d := CM`dim;
  K := CM`ring;
  mats := CM`mats; imats:=CM`imats;
  V := RSpace(K,d);
  //find images of one-cocyle on generators
  genims := [ V!(nselt[(i-1)*d+1 .. i*d]) : i in [1..ng] ];
  OC := function(gtp)
    local w, cmat, ans, g;
    g := gtp[1];
    w := Eltseq(g);
    cmat := IdentityMatrix(K,d);
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
    return ans;
  end function;

  return OC;
end function;

IdentifyOneCocycleFPG := function(CM,OC)
  //identify from action on strong generators
  local G, sg, s;
  G := CM`gf;
  sg := [ G.i : i in [1..Ngens(G)] ];
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(CM`ring,#s)!s;
  if not s in CM`Z1 then
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  return s @ CM`Z1toH1;
end function;

IsOneCoboundaryFPG := function(CM,OC)
//if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local G, d, K, isc, sg, v, w;

  d := CM`dim;
  K := CM`ring;

  G := CM`gf;
  sg := [ G.i : i in [1..Ngens(G)] ];
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  w := Vector(K, w);
  isc, v := IsConsistent(CM`csm, w);
  if not isc then return false, _; end if;
  return true, func< tp | -v >;
end function;

OneCocycleFPGA := function(CM,s)
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
    w := Eltseq(g);
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

IdentifyOneCocycleFPGA := function(CM,OC)
  //identify from action on strong generators
  local G, sg, s;
  G := CM`gf;
  sg := [ G.i : i in [1..Ngens(G)] ];
  s := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  s := RSpace(Integers(),#s)!s;
  if not s in CM`Z1 then
    error "Input to IdentifyOneCocycle is not a cocycle";
  end if;
  return s @ CM`Z1toH1;
end function;

IsOneCoboundaryFPGA := function(CM,OC)
//if so then return 0-cochain z such that OC(<g>) = z(<>)^(1-g) for g in G
  local G, ng, d, K, Z, isc, sg, v, w;

  d := CM`dim;
  K := CM`ring;
  Z := Integers();

  G := CM`gf;
  sg := [ G.i : i in [1..Ngens(G)] ];
  w := &cat [ ElementToSequence(OC(<sg[i]>)) : i in [1..#sg] ];
  w := Vector(K, w);
  isc, v := IsConsistent(CM`csm, w);
  if not isc then return false, _; end if;
  /* Need lop off the unwanted end of v and write over Z. */
  V := RSpace(Z,d);
  v := V![-v[j] : j in [1..d]];
  return true, func< tp | v >;
end function;
    
SplitExtensionFPG := procedure(CM)
/* Sets CM`SplitExtension to be  finite presentation of a split extension
 * of module by G. Generators of G come first.
 */

 local Z, G, p, mats, K, finite, imats, ng,  w, rels, rel, phi,
       e, E, A;

  if assigned CM`SplitExtension then return; end if;
  Z := Integers();
  G:=CM`gf;
  mats:=CM`mats;
  d := CM`dim;
  K := CM`ring;
  finite := IsFinite(K);
  if finite then p := #K; end if;
  ng := Ngens(G);

  F := FreeGroup(ng+d);
  rels := [];
  if finite then for i in [1..d] do
    Append(~rels,(F.(ng+i))^p = Id(F));
  end for; end if;
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

  phi := hom<G->F | [F.i : i in [1..ng]] >;
  for r in Relations(G) do
    Append( ~rels, phi(LHS(r))=phi(RHS(r)) );
  end for;

  E := quo<F|rels>;
  A := finite select AbelianGroup([p:i in [1..d]])
                else AbelianGroup([0:i in [1..d]]);
  E`Projection :=
   hom< E -> G | [G.i: i in [1..ng]] cat [Id(G) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;

  CM`SplitExtension:= E;
end procedure;

SplitExtensionFPGA := procedure(CM)
/* Sets CM`SplitExtension to be  finite presentation of a split extension
 * of module by G. Strong generators of G come first.
 */

 local Z, G, mats, K, finite, imats, ng,  w, rels, rel, phi, e;

  if assigned CM`SplitExtension then return; end if;
  Z := Integers();
  G:=CM`gf;
  mats:=CM`mats;
  invar:=CM`invar;
  d := CM`dim;
  K := CM`ring;
  ng := Ngens(G);

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

  phi := hom<G->F | [F.i : i in [1..ng]] >;
  for r in Relations(G) do
    Append( ~rels, phi(LHS(r))=phi(RHS(r)) );
  end for;

  E := quo<F|rels>;
  A := AbelianGroup(invar);
  E`Projection :=
   hom< E -> G | [G.i: i in [1..ng]] cat [Id(G) : i in [1..d]] >;
  E`Injection := hom< A-> E |  [E.(ng+i): i in [1..d]] >;
  CM`SplitExtension:= E;
end procedure;

CheckRelations := function(G, mats:imats := [])
/* CheckRelations merely checks that the defining relators of G are
 * satisfied by the action matrices -
 * i.e. it checks that it really is a G-module
 */
  local Z, d, ng, phi, r, i;
  Z := Integers();
  if Category(G) ne GrpFP then
    error "Argument for CheckRelations must be an fp-group";
  end if;
  ng := #Generators(G);
  if ng ne #mats then
    error "Wrong number of matrices in CheckRelations";
  end if;

  if imats eq [] then imats := [ m^-1 : m in mats ]; end if;

  WdToMat := function(w)
    local m;
    m := mats[1]^0;
    for i in w do
      if i gt 0 then m *:= mats[i]; else m *:= imats[-i]; end if;
    end for;
    return m;
  end function;

  /* Now we can check if the relations of G are satisfied. */
  for r in Relations(G) do
    if WdToMat(Eltseq(LHS(r))) ne WdToMat(Eltseq(RHS(r))) then
       print "Relation ",r,
           " of the group is not satisfied by the action matrices.";
       return false;
    end if;
  end for;
  return true;
end function;

