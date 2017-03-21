freeze;

/*
    Various utility functions for computing maximal subgroups.
    Written by Derek Holt.
*/

IsHomomorphismH := function(phi,genims)
/* Checks whether a map phi (defined by generator images genims) on a
 * permutation group is a homomorphism.
 */
  local P;

  P:=Domain(phi);
  return TestHomomorphism(P, genims);

end function;

PermRepAlmostSimpleGroupH := function(G,K)
/* Attempt to find a reasonable degree perm. rep. of the almost simple
 * group G/K.
 */
  local p, P, N, S, R, ind, minind, fact, m, pg, mp, mb, mpb;

  ind := #G div #K;
  minind := ind;
  S := K;
  R := SolubleResidual(G);
  for fact in Factorisation(ind) do
    p:=fact[1];
    P := sub<G | K, Sylow(R,p)>;
    N:=Normaliser(G,P);
    if #G div #N lt minind then
      S:=N; minind := #G div #N;
    end if;
  end for;

  m,pg := CosetAction(G,S);
  if IsPrimitive(pg) then
    return m,pg;
  end if;

  mp := MaximalPartition(pg);
  mb, mpb := BlocksAction(pg,mp);

  return m*mb, mpb;
end function; 

DirectProductWithEmbeddingsAndProjectionsH:=function(G,H)
/* G and H should be permutation groups.
 * The direct product P of G and H as computed by DirectProduct is
 * returned.
 * The embeddings of G into P and H into P are also returned,
 * followed by the projections of P onto G and H.
 */
  local P, e, p;

  P, e, p := DirectProduct(G, H);
  return P, e[1], e[2], p[1], p[2];
end function;

IsConjugateSequencesH := function(G,s1,s2)
/* s1 and s2 should be sequences of elements of the group G of the same
 * length. This function tests whether there is an element g in G with
 * s1[i]^g eq s2[i] for all i.
 * It returns true of false, and also a conjugating element g if it exists.
 */
  local el, C, conj, g;
  if Universe(s1) cmpne G or Universe(s2) cmpne G then
    error
     "Universes of s1 and s2 must be group G in IsConjugateSequenceH(G,s1,s2)";
  end if;
  if #s1 ne #s2 then
    return false,_;
  end if;
  el := Id(G); C := G;
  for i in [1..#s1] do
    conj, g := IsConjugate(C,s1[i]^el,s2[i]);
    if not conj then
      return false,_;
    end if;
    el := el*g;
    C := Centraliser(C,s2[i]);
  end for;

  return true, el;
end function;

PermutationRepresentationSumH := function(G,reps)
/* reps should be a list of homomorphisms from group G to permutation
 * groups (subgroups of Sym(n_i)). The summed permutation representation
 * reps[1]+..resp[r] of degree n_1+n_2+..n_r is returned, together
  * with the image group.
 */
  local phi;

  phi := RepresentationSum(G, reps);
  return phi, Image(phi);

end function;

PresentationSubgroupTF := function(genlist,preslist,projlist,fplist)
/* This function computes a presentation of a maximal subgroup  H of a
 * TF permutation group.
 * H has a normal subgroup N of fairly small index which is a direct
 * product of groups N_1,...,N_r, which are permuted under conjugation
 * by H.
 * genlist, preslist, projlist and fplist should each be lists, where
 * genlist has length r+1 and the others have length r.
 * genlist[i] should be a list of generators of N_i (1 <= i <= r).
 * (but some of these lists may be empty, which happens when H is a partly
 *  diagonal)
 * genlist[r+1] should contain an irredundant list of elements of H that
 * generate  H modulo N.
 * preslist[i] should be a presentation of N_i on these generators.
 * projlist[i] should be the natural projection N -> N_i.
 * fplist[i] should be the word map of N_i.
 * (These conditions are not checked!)
 * 
 * The group H with generating set the union of the generators in genlist,
 * together with a presentation of H on these generators is returned.
 */
  local r, ct, n, gensH, H, N, factors, subgpptr, F, Frels, actperms, g,
        actgroup, x, dx, w, rel, dy, ngx, y, h, dn, Q, pQ, presQ, relval,
        liftQ;

  r := #genlist-1;
  ct:=1;
  while #genlist[ct] eq 0 do ct+:=1; end while;
  n := Degree(Universe(genlist[ct]));
  gensH := &cat(genlist);
  //H := PermutationGroup<n|gensH>;
  H := sub< Universe(gensH) | gensH >;
  N:=sub<H| &cat([genlist[i] : i in [1..r] ]) >;
  factors := [ sub<H|genlist[i]> : i in [1..r] ];
 // subgpptr will be used to locate the generators of each factor within H
  subgpptr:=[];
  subgpptr[1]:=0;
  for i in [2..r+1] do
    subgpptr[i] := subgpptr[i-1] + #genlist[i-1];
  end for;

  /* The permutations in genlist[r+1] permute the N_i by conjugation,
   * and we will define the corresponding permutations on [1..r]
   */
  actperms:=[];
  for i in [1..#genlist[r+1]] do
    g:=genlist[r+1][i];
    actperms[i]:=[];
    for j in [1..r] do
      if #genlist[j] eq 0 or r eq 1 then
        actperms[i][j]:=j;
      else
        actperms[i][j] := Position(factors,factors[j]^g);
      end if;
    end for;
  end for;

  F:=FreeGroup(#gensH);
  Frels := [F|];
  // Now we start to set up the defining relations.
  // First, for each orbit of H on the factors we want a presentation
  // of one factor in the orbit, + commutativity relations with other factors.
  actgroup:=PermutationGroup<r|actperms>;
  for o in Orbits(actgroup) do
    x:=Representative(o);
    if #genlist[x] eq 0 then
      continue;
    end if;
    dx:=subgpptr[x];
    for rS in Relations(preslist[x]) do
      w:=ElementToSequence(LHS(rS)*RHS(rS)^-1);
      w := [i gt 0 select dx+i else -(dx-i):i in w];
      Append(~Frels,w);
    end for;

    ngx := Ngens(factors[x]);
    for y in [1..r] do if y ne x and #genlist[y] ne 0 then
      dy:=subgpptr[y];
      for i in [1..ngx] do for j in [1..Ngens(factors[y])] do 
        if Position(Frels,(F.(dy+j),F.(dx+i))) eq 0 then
          // avoid using the same commutator twice!
          Append(~Frels,(F.(dx+i),F.(dy+j)));
        end if;
      end for; end for;
    end if; end for;
  end for;

  if Index(H,N) eq 1 then
    return H, quo<F|Frels>;
  end if;

  // Next the relations of the action of H on the factors
  dn:=subgpptr[r+1];
  for i in [1..#genlist[r+1]] do
    g := genlist[r+1][i];
    for x in [1..r] do if #genlist[x] ne 0 then
      dx := subgpptr[x];
      y := actperms[i][x];
      dy:=subgpptr[y];
      for k in [1..#genlist[x]] do
        h := genlist[x][k];
        w := ElementToSequence((h^g) @ projlist[y] @@ fplist[y]);
                         // h^g should be in N_y.
        // relator will be (F.(dn+i))^-1*F.(dx+k)*F.(dn+i)*w^-1;
	w := [j gt 0 select -dy-j else dy-j : j in w];
	w cat:= [dn+i, dx+k, -dn-i];
	Reverse(~w);
	Append(~Frels,w);
      end for;
    end if; end for;
  end for;

  //Finally the relators derived from those of H/N.
  Q, pQ := quo<H|N>;
  //Q, pQ := SocleQuotient(H);
   // generators of this should correspond to genlist[r+1] but to be safe:
  Q := sub< Q | [pQ(g) : g in genlist[r+1]] >;
  presQ := FPGroup(Q);
  // define an inverse 'hom' for evaluating relators in N.
  liftQ := hom< presQ -> H | genlist[r+1] >;
  for rQ in Relations(presQ) do
    w:=LHS(rQ)*RHS(rQ)^-1;
    relval := liftQ(w);
    w:=ElementToSequence(w);
    rel := [i gt 0 select dn+i else -(dn-i): i in w];
    // Now we append the inverses of the components of relval to rel
    for x in [1..r] do if #genlist[x] ne 0 then
      dx := subgpptr[x];
      w := ElementToSequence(relval @ projlist[x] @@ fplist[x]);
      for j in Reverse(w) do
        if j gt 0 then
          // rel := rel * (F.(dx+j))^-1;
	  Append(~rel, -(dx+j));
        else
          // rel := rel * F.(dx-j);
	  Append(~rel, dx-j);
        end if;
      end for;
    end if; end for;
    Append(~Frels,rel);
  end for;

  return H, quo<F|Frels>;
end function;

SubgroupTF := function(genlist)
/* This function is a cut down version of PresentationSubgroupTF, with
 * the same (now a bit redundant) parameters, that just creates the
 * maximal subgroup, without a presentation.
 */
  local r, ct, n, gensH, H; 

  r := #genlist-1;
  ct:=1;
  while #genlist[ct] eq 0 do ct+:=1; end while;
  n := Degree(Universe(genlist[ct]));
  gensH := &cat(genlist);
  //H := PermutationGroup<n|gensH>;
  H := sub< Universe(gensH) | gensH >;
  return H;
end function;

MinimalOvergroupsH := function(G,H)
/* H is a proper subgroup of G.
 * return all minimal subgroups K with H < K <= G.
 */
  local theta, P, stab;
  theta, P := CosetAction(G,H);
  if IsPrimitive(P) then
    overgps := {G};
  else
    overgps:={};
    for p in MinimalPartitions(P) do
      stab:=Stabiliser(P,[x : x in p | 1 in x][1]);
         // i.e. stabiliser of the block containing 1 -
         // pullback to G will be a minimal overgroup of N.
      Include(~overgps,stab @@ theta);
    end for;
  end if;
  return overgps;
end function;

WreathComplementTail := function(W,A,B,C,g)
/* A technical function.
 * W is a wreath product of A by a group P.
 * A is a factor of the base group and B is the direct product of all
 * other factors (so base group = A x B).
 * C/B is a complement of (A x B)/B in X/B
 * (perhaps from call of Complement(X,sub<W|A,B>,B).) where X = N_W(A).
 * An element a of A is returned such that g = c a for some c in C.
 */
  local gensA, gensB, BG, pA, XN, pC;
 
  gensA := [A.i : i in [1..Ngens(A)]];
  gensB := [B.i : i in [1..Ngens(B)]];
  BG := sub<W | gensA cat gensB >; // base group of W
  AssertAttribute(BG,"Order",#A*#B);
  RandomSchreier(BG);
 
  pA := hom < BG->A | gensA cat [Id(A): i in [1..Ngens(B)]] >;
                                              //projection of BG onto A.
/*
  H := sub<W | g,BG >; 
  I := H meet C;
  for c in Transversal(I,B) do
    y := c^-1 * g;
    if y in BG then
      return pA(y);
    end if;
  end for;
*/
  XN := sub < W | [C.i : i in [1..Ngens(C)]] cat [A.i : i in [1..Ngens(A)]]>;
  AssertAttribute(XN,"Order",#C * #A);
  RandomSchreier(XN);
  // XN = Normaliser(W,A)
  pC := hom < XN -> C | [C.i : i in [1..Ngens(C)]] cat
                                   [Id(C) : i in [1..Ngens(A) ]]>;
  return pA(pC(g)^-1 * g);
 
 
end function;


ConjugatingElement := function(G,x)
/* find an element of G with same conjugation action on G as x
 * give error if no such element.
 */
  local C, yes, el, g, y;
  C:=G;
  y:=Id(G);
  for g in Generators(G) do
    yes, el := IsConjugate(C,g^y,g^x);
    if not yes then
      error "No conjugating element in ConjugatingElement";
    end if;
    y := y*el;
    C := Centraliser(C,g^x);
  end for;

  return y;
end function;
