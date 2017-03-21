freeze;

ExtensionsEquationsMatrix := function(M)
/* M should be a KG-module for an fp-group G, and a finite field K of prime
 * order.
 * Let d = Dimension(M), og=#, ng=#Generators(G) and nr=#Relators(G).
 * ComplementEquations returns a
 * ((nr + (og*(ng-1)+1))*d X nr*og*d matrix X, the nullspace
 * of which is isomorphic to Z^2(G,M).
 */

   local K, p, G, d, ng, nr, og, RG, ct, sgno, sg, sv, X,
         im, ims, mat, celt, gno, r, w, l, g;
  if Category(M) ne ModGrp then
    error "First argument for ComplementEqnsMat must be a KG-module";
  end if;
  K:=BaseRing(M);
  p:=#K;
  if not IsPrime(p) then
    error
   "The base-ring of first argument for ComplementEqnsMat is not a prime field";
  end if;
  G:=Group(M);
  if Category(G) ne GrpFP then
    error
 "First argument for ComplementEqnsMat must be a KG-module, with G an fp-group";
  end if;
  d := Dimension(M);
  ng := #Generators(G);
  RG := Relations(G);
  nr := #RG;
  og := #G;

  // Set up the coset table for G (= regular perm. rep.), with Schreier Vector
  // and define Schreier generators of relation module.
  // The Schreier generators will be numbered from nr+1, because the
  // nr relators are to be used also as generators of the relation module.
  ct := CosetImage(G,sub<G|>);
  sgno := nr;
  sg:=[];
  for i in [1..og] do sg[i]:=[]; end for;
  for i in [1..og] do for j in [1..ng] do sg[i][j]:=0; end for; end for;
  sv:=[-1];
  for i in [2..og] do sv[i]:=[0]; end for;
  ims := [1];
  for i in [1..og] do for j in [1..ng] do
    im := ims[i];
    if sv[im^(ct.j)] eq 0 then //definition
       sv[im^(ct.j)] := j;
       Append(~ims,im^(ct.j));
    else //new Schreier generator
      sgno +:= 1;
      sg[im][j] := sgno;
    end if;
  end for; end for;

  /* Set up the matrix  X  where we will store the equations */
  print "Setting up",nr*og*d,"equations in",sgno*d,"unknowns";
  X:=Hom(VectorSpace(K,sgno*d),VectorSpace(K,nr*og*d))!0;

  for elt in [1..og] do
    //Calculate inverse of action matrix
    mat := IdentityMatrix(K,d);
    celt := elt;
    gno := sv[celt];
    while gno ne -1 do
      mat := mat * ActionGenerator(M,gno)^-1;
      celt := celt ^ (ct.gno)^-1;
      gno := sv[celt];
    end while;

    for rno in [1..nr] do
      str := d*(nr*(elt-1) + (rno-1));
      //Scan relation no. rno under group element no. elt.
      //The equations generated are numbers str+1 .. str+d.
      r := RG[rno]; w := LHS(r)*RHS(r)^-1; l := #w;
      celt := elt;
      for j in [1..l] do
        g := GeneratorNumber(Subword(w,j,1));
        if g ge 0 then
          sgno := sg[celt][g];
          if sgno gt 0 then
            for k in [1..d] do
              X[d*(sgno-1)+k][str+k] +:= 1;
            end for;
          end if;
          celt := celt ^ ct.g;
        else
          g := -g;
          celt := celt ^ (ct.g)^-1;
          sgno := sg[celt][g]; 
          if sgno gt 0 then
            for k in [1..d] do
              X[d*(sgno-1)+k][str+k] -:= 1;
            end for;
          end if;
        end if;
      end for;
      if celt ne elt then
        error "Scanning error!";
      end if;
      /* The equations specify that the word in the Schreier generators
       * coming from the scanned relator is equal to the conjugate of
       * of the Schreier generator for that relator under the inverse of
       * group element number elt - mat is the matirx for this inverse.
       */
      for j in [1..d] do for k in [1..d] do
        X[d*(rno-1)+j][str+k] -:= mat[j][k];
      end for; end for;
    end for;
  end for;
  print "Done";

  return X;
end function;

TrimmedNullspace := function(M)
  /* Computes  Nullspace of X:=ExtensionsEquationsMatrix(M),
   * and takes only the first nr*d columns.
   */
  local K, X, nc, N;
  K:=BaseRing(M);
  nc := #Relations(Group(M)) * Dimension(M);
  X := ExtensionsEquationsMatrix(M);
  N := Nullspace(X);
  deg := Degree(N);
  V1 := VectorSpace(K,deg);
  V2 := VectorSpace(K,nc);
  h:= hom<V1->V2 | [V2.i : i in [1..nc]] cat [V2!0 : i in [nc+1..deg]] >;
  return sub < V2 | [h(N.i) : i in [1..Ngens(N)]] >;
end function;
