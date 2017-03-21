freeze;

ReduceAbAutVec := function(invar,vec)
/* invar is a list of invariants of a finite abelian group A (with
 * invar[i]>1, invar[i] divides invar[i+1] and vec a sequence of
 * integers of length divisible by d. Reduce vec[ld+j] mod invar[j]
 * and return resulting vector.
 */
 local d, ct, Z;
 Z := Integers();
 d := #invar;
 if d ne 0 and #ElementToSequence(vec) mod d ne 0 then
   error "vec must gave length divisible by #invar";
 end if;
 ct := 1;
 for i in [1..#ElementToSequence(vec)] do
   if invar[ct] ne 0 then
     vec[i]:= Z!vec[i] mod invar[ct];
   end if;
   if ct eq d then ct:=1; else ct +:=1; end if;
 end for;
 return vec;
end function;

ReduceAbAutMat := function(invar,mat)
/* invar is a list of invariants of a finite abelian group A (with
 * invar[i]>1, invar[i] divides invar[i+1] and mat a dxd integer
 * matrix, where d = #invar;
 * Reduce (i,j) entry of mat mod invar[j]
 */
  local d, newmat, Z;
  Z := Integers();
  d := #invar;
  newmat := MatrixAlgebra(Z,d)!mat;
  for i in [1..d] do for j in [1..d] do
     if invar[j] ne 0 then
       newmat[i][j] mod:= invar[j];
     end if;
  end for; end for;
  return newmat;
end function;

IsAutAndInverse := function(invar,mat)
/* invar is a list of invariants of a finite abelian group A (with
 * invar[i]>1, invar[i] divides invar[i+1] and mat an dxd integer
 * matrix, where d = #invar;
 * inv is regarded as a matrix in which (i,j) entry is taken
 * modulo invar[j].
 * Test whether inv defines an automorphism of A - return true/false
 * If so, return also matrix representing its inverse automorphism.
 */
  local Z, d, invarmat;
  //Form d x d diagonal matrix of invariants
  Z := Integers();
  d := #invar;
  invarmat := DiagonalMatrix(Z,invar);
  // First test whether mat even defines an endomorphism.
  if HermiteForm(VerticalJoin(invarmat*mat,invarmat)) ne
                 VerticalJoin(invarmat,ScalarMatrix(Z,d,0)) then
    print "Matrix does not define a homomorphism!";
    return false, _;
  end if;
  // Now test if it is surjective, and hence an automorphism
  hf, tmat := HermiteForm(VerticalJoin(mat,invarmat));
  if hf ne VerticalJoin(ScalarMatrix(Z,d,1),ScalarMatrix(Z,d,0)) then
    print "Matrix does not define an automorphism!";
    return false, _;
  end if;
  return true, ReduceAbAutMat(invar,Submatrix(tmat,1,1,d,d));
end function;

MatrixOfGroupElement := function(g,invar,mats,imats)
/* In this function imats must be calculated in advance!
 * g is a word defining an element of the FP group G.
 * The matrix of g is computed from mats and imats.
 */
 local s, m, Z;
 Z := Integers();
 s := ElementToSequence(g);
 if #s eq 0 then
   return IdentityMatrix(Z,#invar);
 end if;
 m := s[1] gt 0 select ReduceAbAutMat(invar,mats[s[1]])
                  else ReduceAbAutMat(invar,imats[-s[1]]);
 for i in [2..#s] do
   if s[i] gt 0 then m := ReduceAbAutMat(invar,m*mats[s[i]]);
    else m := ReduceAbAutMat(invar,m*imats[-s[i]]);
   end if;
 end for; 
 return m;
end function;

CheckRelationsA := function(G,invar,mats:imats := [])
/* CheckRelations merely checks that the defining relators of G are
 * satisfied by the action matrices -
 * i.e. it checks that it really is a G-module
 */
  local Z, d, ng, phi, r, R, i;
  Z := Integers();
  if Category(G) ne GrpFP then
    error "Argument for CheckRelationsA must be an fp-group";
  end if;
  d := #invar;
  ng := #Generators(G);
  if ng ne #mats then
    error "Wrong number of matrices in CheckRelationsA";
  end if;

  if imats eq [] then
    for i in [1..ng] do
      isit, imats[i] := IsAutAndInverse(invar,mats[i]); 
      if not isit then
        error "A matrix in CheckRelationsA does not define an automorphism";
      end if;
    end for;
  end if;
 
  /* Now we can check if the relations of G are satisfied. */
  R := Relations(G);
  for r in R do
    if MatrixOfGroupElement(LHS(r),invar,mats,imats) ne
       MatrixOfGroupElement(RHS(r),invar,mats,imats) then
       print "Relation ",r,
           " of the group is not satisfied by the action matrices.";
       return false;
    end if;
  end for;
  return true;
end function;

ComplementEquationsMatrixA := procedure(CM)
/* 
 * CM as returned by MakeModuleRecordSGA.
 * Let d = #invar, ng=#Generators(G) and nr=#Relators(G).
 * ComplementEquationsMatrixA sets CM`cem to be a (ng+nr)*d x nr*d matrix X
 * which is used to decide whether the extensions that can be defined by
 * ModuleExtensionA are split.
 * (In fact, they are split if  the system of linear equations
 *  x*X = -v has a solution for x (a vector of length ng*d), where
 *  the length nr*d vector v is obtained by concatenating the vectors
 *  in RelVals.
 *  The complement is obtained by replacing the generators E.1,..,E.ng
 *  of E in the extension by E.i*m(i), where m(i) is in the abelian group A
 *  and the solution x is the concatenation of the vectors m(i).)
 * However, the matrix X here is independent of RelVals, which represents
 * the right hand side of the equations to be solved.
 * In particular, the nullspace of X (solutions of x.X = 0) gives a basis
 * for the space of complements of A in the semidirect product of A by G.
 * (In other words it is a basis for Z^1(G,A).)
 */
  local K, invar, G, mats, imats, d, ng, nr, RG, r, w, lhs, rhs, X, Y, m,
        i, j, k, g, k1, k2, l, neg, si, sg;

  if assigned CM`cem then return; end if;
  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  K := CM`ring;
  d := CM`dim;
  ng := Ngens(G);
  RG := Relations(G);
  nr := #RG;
  /* Set up the matrix  X  where we will store the equations */
  X:=Hom(RSpace(K,ng*d),RSpace(K,nr*d))!0;

  /* Now fill in the entries of X */
  for i in [1..nr] do
    /* The i-th relation gives rise to the d columns of X from (i-1)*d+1 to i*d
     * First turn it into a relator.
     */
    r := RG[i]; w := LHS(r)*RHS(r)^-1; l := #w;
    si := (i-1)*d;
    m := IdentityMatrix(Integers(),d);
    /* We will scan the relator w from right to left.
     * m is the matrix giving the action of the current suffix of w.
     */
    for j in Reverse([1..l]) do
      g := GeneratorNumber(Subword(w,j,1));
      if g lt 0 then
        neg := true;
        g := -g;
        m := ReduceAbAutMat(invar,imats[g]*m);
           /* In this case we want the inverse of the matrix for g to
            * act on -m(g) (where m(g) is the unknown tail of g).
            */
      else
        neg := false;
      end if;
      /* The rows of X from (g-1)*d+1 to g*d correspond to the generator
       * g, and will be changed by this generator.
       */
      sg := (g-1)*d;
      for k1 in [1..d] do for k2 in [1..d] do
        if neg then
           X[sg+k1][si+k2] -:= m[k1][k2];
        else
           X[sg+k1][si+k2] +:= m[k1][k2];
        end if;
        if invar[k2] ne invar[d] then
          X[sg+k1][si+k2] := (Integers()!X[sg+k1][si+k2]) mod invar[k2];
        end if;
      end for; end for;
      if  not neg then
         m := ReduceAbAutMat(invar,mats[g]*m);
      end if;
    end for;
  end for;

  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  if k eq 0 then
     CM`cem := X;
  else
    Y := Matrix(K,k,d,[0: i in [1..k*d]]);
    for i in [1..k] do Y[i][i] := invar[i]; end for;
    CM`cem := VerticalJoin(X,DirectSum([Y:i in [1..nr]]));
  end if;

end procedure;

ComplementSubspaceA := procedure(CM)
/* This sets CM`Z1, the 2-cocyle space.
 * Over Z or a finite field, this is just the nullspace of the
 * ComplementEquationsMatrix, but it is more complicated here!
 */
  local invar,G, mats, imats, K, d, ng, cem, N,  V, Y, sg, k, VZ, YZ;

  if assigned CM`Z1 then return; end if;
  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  d := CM`dim;
  ng := Ngens(G);
  K := CM`ring;

  if not assigned CM`cem then
    ComplementEquationsMatrixA(CM);
  end if;
  N := Nullspace(CM`cem);
  /* We first lop off the unwanted ends of the rows of N. */
  V := RSpace(K,ng*d);
  Y := [ V![(N.i)[j] : j in [1..ng*d]] : i in [1..Dimension(N)]];
  /* We need to adjoin generators for the invariants of the abelian group */
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  for g in [1..ng] do
    sg := (g-1)*d;
    for j in [1..k] do
      v := V!0;
      v[sg+j] := invar[j];
      Append(~Y,v);
    end for;
  end for;

  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    VZ := RSpace(Integers(),ng*d);
    YZ := [ VZ!y : y in Y ];
    for g in [1..ng] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
      V := VZ; Y := YZ;
    end for;
  end if;

  CM`Z1 :=  sub<V|Y>;
end procedure;

ConjugateComplementSubspaceA := procedure(CM)
/* Let X be the matrix returned by ComplementEquationsMatrixA(M).
 * Let d = #invar, ng=#Generators(G) and nr=#Relators(G).
 * ConjugateComplementSubspaceA sets CM`B1 to be  a d-dimensional subspace of
 * an ng*d vector space over K, which is the subspace of NullSpace(X) which
 * correspond to those complements of M in the semidirect product of M by G that
 * are conjugate to the principal complement under M.
 * In fact, the i-th spanning vector of the subspace returned
 *  comes from conjugation by the i-the generator of M.
 * (In other words it corresponds to the subspace B^1(G,M) of Z^1(G,M).)
 */
  local invar, G, mats, imats, K, d, ng, X, V, v, m, i, j, k, g, sg, sk;

  if assigned CM`B1 then return; end if;
  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  K:=CM`ring;
  d := CM`dim;
  ng := Ngens(G);

  V := RSpace(K,ng*d);
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  X:=Hom(RSpace(K,d+k*ng),RSpace(K,ng*d))!0;

  for i in [1..d] do
  /* compute the i-th spanning vector v of Y, which comes from conjugating the
   * generators of G by the i-th generator of the vector space of M.
   */
    for g in [1..ng] do
    /* The entries for the action of the i-th generator of M on the g-th
     * of G will go in the columns (g-1)*d+1 .. g*d of v.
     */
      m := mats[g];
      sg := (g-1)*d;
      for j in [1..d] do
        X[i][sg+j] :=  (i eq j) select m[i][j]-1 else m[i][j];
      end for;
    end for;
  end for;
  /* We need to adjoin generators for the invariants of the abelian group */
  for g in [1..ng] do
    sk := (g-1)*k;
    sg := (g-1)*d;
    for j in [1..k] do
      X[d+sk+j][sg+j] := invar[j];
    end for;
  end for;
  CM`csm := X;

  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  VZ := RSpace(Integers(),ng*d);
  YZ := [ VZ!X[i] : i in [1..Nrows(X)] ];
  if (invar[d] ne 0) then
    for g in [1..ng] do
      sg := (g-1)*d;
      for j in [k+1..d] do
        v := VZ!0;
        v[sg+j] := invar[j];
        Append(~YZ,v);
      end for;
    end for;
  end if;

  CM`B1 := sub< VZ | YZ >;
end procedure;

ZeroCohomologyGroupA := procedure(CM)
  local invar,G, mats, imats, K, d, ng, cem, N, dN, V, Y, sg, k, VZ, YZ;

  if assigned CM`H0 then return; end if;
  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  K := CM`ring;
  d := CM`dim;
  ng := Ngens(G);

  if not assigned CM`csm then
    ConjugateComplementSubspaceA(CM);
  end if;
  N := Nullspace(CM`csm);
  dN := Dimension(N);
  /* We first lop off the unwanted ends of the rows of N. */
  V := RSpace(K,d);
  Y := [ V![(N.i)[j] : j in [1..d]] : i in [1..dN]];
  Y := [ y : y in Y | y ne V!0 ];
  dN := #Y;
  /* We need to adjoin generators for the invariants of the abelian group */
  k := #[i : i in [1..d] | invar[i] ne invar[d] ];
  for j in [1..k] do
    v := V!0;
    v[j] := invar[j];
    Append(~Y,v);
  end for;
  //for now, we lift the result back up the integers, since quotients of
  //spaces over finite integer rings are not well behave.
  if (invar[d] ne 0) then
    VZ := RSpace(Integers(),d);
    YZ := [ VZ!y : y in Y ];
    for j in [k+1..d] do
      v := VZ!0;
      v[j] := invar[j];
      Append(~YZ,v);
    end for;
    V := VZ; Y := YZ;
  end if;

  CM`Z0  :=  sub<V|Y>;
  CM`H0, CM`Z0toH0 :=
        quo< CM`Z0 | sub< CM`Z0 | [(CM`Z0).i : i in [dN+1..Ngens(CM`Z0)]]> >;

end procedure;

FirstCohomologyGroupA := procedure(CM)
/* sets CM`H1 and CM`Z1toH1, the quotient H^1(G,Module) = Z1/B1,
 * and natural map from Z1 to H1.
 */
  if assigned CM`H1 then return; end if;
  if not assigned CM`Z1 then
    ComplementSubspaceA(CM);
  end if;
  if not assigned CM`B1 then
    ConjugateComplementSubspaceA(CM);
  end if;

  CM`H1, CM`Z1toH1 := quo< CM`Z1 | CM`B1 >;
end procedure;

SplitExtensionA := procedure(CM)
/* Sets CM`SplitExtension to be  finite presentation of a split extension
 * of abelian group A defined by invar by G. Generators of G come first.
 */
  local G, invar, mats, imats, Z, d, ng, F, rels, phi;

  if assigned CM`SplitExtension then return; end if;
  invar:=CM`invar; G:=CM`gf; mats:=CM`mats; imats:=CM`imats;
  Z:=Integers();
  d := #invar;
  ng := #Generators(G);
  F := FreeGroup(ng+d);
  rels := [];
  for i in [1..d] do if invar[i] ne 0 then
    Append(~rels,(F.(ng+i))^invar[i]);
  end if; end for;
  for i in [1..d] do for j in [i+1..d] do
    Append(~rels,(F.(ng+i),F.(ng+j)));
  end for; end for;
  for i in [1..ng] do for j in [1..d] do
    w:=Id(F);
    for k in [1..d] do
      w := w * (F.(ng+k))^mats[i][j][k];
    end for;
    Append(~rels,F.i^-1*F.(ng+j)*F.i*w^-1);
  end for; end for;
  phi := hom<G->F | [F.i : i in [1..ng]] >;
  for r in Relations(G) do
    Append(~rels,phi(LHS(r)*RHS(r)^-1));
  end for;
  CM`SplitExtension := quo< F |rels >;
end procedure;

PermutationRepresentationSumH := function(G,reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
  * with the image group.
 */
  local nreps, degrees, phi, cdphi, g, ims, img, sumdeg, deg, cd, cdgens;
  nreps := #reps;
  degrees := [];
  sumdeg := 0;
  for j in [1..nreps] do
    phi:=reps[j];
    if Domain(phi) cmpne G then
      error
    "Domain of maps in reps must be G in PermutationRepresentationSum(G,reps)";
    end if;
    cdphi :=  Codomain(phi);
    if Category(cdphi) ne GrpPerm then
      error
  "Codomain of maps must be perm-gps in PermutationRepresentationSum(G,reps)";
    end if;
    degrees[j]:=Degree(cdphi);
    sumdeg +:= degrees[j];
  end for;
  deg:=sumdeg;

  // The codomain of the summed representation will be the direct product of the
  // codomains of the given maps.
  cdgens := [Sym(deg)|];
  sumdeg := 0;
  for j in [1..nreps] do
    for g in Generators(Codomain(reps[j])) do
      Append(~cdgens,[i:i in [1..sumdeg]] cat
            [i^g + sumdeg : i in [1..degrees[j]]] cat
            [i : i in [sumdeg+degrees[j]+1..deg]]);
    end for;
    sumdeg +:= degrees[j];
  end for;

  cd := sub<Sym(deg)|cdgens>;
  ims := [cd|];
  for i in [1..Ngens(G)] do
    g := G.i;
    img:=[];
    sumdeg:=0;
    for j in [1..nreps]  do
      for k in [1..degrees[j]] do
        img[sumdeg+k] := sumdeg + k^reps[j](g);
      end for;
      sumdeg +:= degrees[j];
    end for;
    Append(~ims,img);
  end for;

  return hom<G -> cd | ims >, sub<cd|ims>;

end function;

SplitExtensionPermRepA := procedure(CM)
/* Find faithful perm. rep. of CM`SplitExtension.
 * This method is aimed at example with a relatively large module and
 * a relatively small group. Subgroups of the module are used as
 * stabilizers.
 */
  local E, G, invar, d, ng, oE, reps, found, fac, rep, P, oldord, f;

  if assigned CM`SplitExtensionPermRep then return; end if;
  vprint ModCoho: "Finding permutation representation of split extension *";

  if not assigned CM`SplitExtension then
    SplitExtensionA(CM);
  end if;
  E := CM`SplitExtension;
  invar := CM`invar;
  G := CM`gf;
  d := CM`dim;
  oE := #G * &*invar;
  ng := Ngens(G);
  reps := [PowerStructure(HomGrp)|];

  fac := d;
  found := false;
  oldord := 1;
  while not found do
    f := Factorisation(invar[fac]);
    //Reduce degree of rep. by using factorisation of cyclic factor.
    for t in f do
       H:=sub< E | [E|E.(ng+k) : k in [1..d] | k ne fac] cat
                   [E|E.(ng+fac)^(t[1]^t[2])] >;
       rep := CosetAction(E,H);
       Append(~reps,rep);
       _,P := PermutationRepresentationSumH(E,reps);
       found := #P eq oE;
       if found then break; end if;
       if #P eq oldord then Prune(~reps); end if;
       oldord := #P;
    end for;
    fac -:=1;
  end while;

  CM`SplitExtensionPermRep := P;
  vprint ModCoho: "Found representation of degree",Degree(P);

end procedure;

ComplementInSplitExtensionA := function(CM,seq)
/* CM`H1 should have been computed already with FirstCohomologyGroup.
 * seq should be an integer sequence representing an element of  CM`H1.
 * A corresponding complement in CM`SplitExtension is returned.
 */
 local cv, ng, d, se, gens, g;

  if not assigned CM`H1 then
    error "Call FirstCohomologyGroupA(CM) first!";
  end if;
  if not assigned CM`SplitExtension then
    error "Call SplitExtensionA(CM) first!";
  end if;
  cv := ReduceAbAutVec(CM`invar,seq @@ CM`Z1toH1);
  ng := Ngens(CM`gf);
  d := #(CM`invar);
  se := CM`SplitExtension;
  gens := [];
  for i in [1..ng] do
    g := se.i;
    for j in [1..d] do
      g := g * se.(ng+j)^cv[(i-1)*d + j];
    end for;
    Append(~gens,g);
  end for;
  return sub < se | gens >;
end function;
