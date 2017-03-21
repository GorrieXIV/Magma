freeze;

/*
 Function names in this file:
StandardiseReduct(group, n, q, dim)
SLPointStab(n, q)
SLStabOfNSpace(d, p, n)
IsGLConjugateReducible(H, K, Print)
GLConjElts(A, B)
*/





//This function tries to conjugate some power of $A$ to B. will
//result in a conjugating element mapping <A> to <B>.

GLConjElts:= function(A, B)
  centralisers_conj:= false;
  o1:= Order(A);
  o2:= Order(B);
  if not o1 eq o2 then
    return false, _;
  end if;
  for i in [1..o1] do
    pow:= A^i;
    if Order(pow) eq o2 then
      centralisers_conj, x:= IsSimilar(pow, B);
      if centralisers_conj then
        return true, x;
      end if;
    end if;
  end for;
  return false, _;
end function;







/*
 * This function takes as input a reducible group and returns a list
 * of matrices that will conjugate the group into a nice standard
 * form.
 */

function StandardiseReduct(group, n, q, dim)
  module:= GModule(group);
  constit:= ConstituentsWithMultiplicities(module);
  ghoms:= [GHom(constit[i][1], module) : i in [1..#constit]];
  dims:= [Dimension(ghoms[i]) : i in [1..#constit]];
  if dim eq 0 then
     //if there are constituents of multiplicity 1 then we
    //only work with them.
    bestmods:= [i : i in [1..#constit] | (dims[i] gt 0) 
                and (constit[i][2] eq 1)];
    if #bestmods gt 0 then 
       dif:= n;
       for x in bestmods do
         if AbsoluteValue(dims[x] - n/2) lt dif then
           ghom:= ghoms[x];
           dif:= AbsoluteValue(dims[x] - n/2);
         end if;
       end for;
       spaces:= [Image(ghom.1)];
    else
      //all constituents which correspond to submodules 
      //have multiplicity greater than 1
       exts:= [];
       for c in constit do
         bool, mat, ext_field:= IsAbsolutelyIrreducible(c[1]);
         if not bool then
           Append(~exts, ext_field);
         else 
           Append(~exts, 1);
         end if;
       end for;
       if exists(t){i : i in [1..#constit] | (dims[i] gt 0) and
         (dims[i]*Dimension(constit[i][1]) div exts[i]) lt n} then
         //this is the case where there's one constituent whose
         //copies don't span the whole space.
         ghom:= ghoms[t];
         images:= [Image(ghom.j) : j in [1..dims[t]]];
         spaces:= [sub<module|images>];
         assert Dimension(spaces[1]) eq (dims[t]*Dimension(constit[t][1]) 
            div exts[t]);
       else //should be a unique consts of multiplicity k,
           //image of GHom dim k  and dimensiton n/k.
         assert #constit eq 1;
         spaces:= [Image(ghoms[1].1)];
       end if;  
    end if;
  else
    //this looks to see if there's a constituent of the right dimension
    //that actually corresponds to a submodule of module.
    //first look for case 1 above: there's one of multiplicity 1 and of the 
    //right dimension. in this case we will need all such.
    spaces:= [];
    good_constits:= [i : i in [1..#constit] | Dimension(constit[i][1]) 
                    eq dim and dims[i] gt 0 and constit[i][2] eq 1];
    for j in good_constits do
      images:= [Image(ghoms[j].i) : i in [1..dims[j]]];
      Append(~spaces, sub<module|images>);
    end for;
    if #good_constits eq 0 then
      //now we look for case 2 above:
      exts:= [];
      for c in constit do
        bool, mat, ext_field:= IsAbsolutelyIrreducible(c[1]);
        if not bool then 
          Append(~exts, ext_field);
        else
          Append(~exts, 1);
        end if;
      end for; 
      good_constits:= [i : i in [1..#constit] | 
          (dims[i]*Dimension(constit[i][1]) div exts[i]) eq dim];
      for j in good_constits do
        images:= [Image(ghoms[j].i) : i in [1..dims[j]]];
        Append(~spaces, sub<module|images>);
      end for;
    end if;
    if (#good_constits eq 0) and (#constit eq 1) then 
      bool, mat, ext_field:= IsAbsolutelyIrreducible(constit[1][1]);
      if bool then ext_field:= 1; end if;
      if  ((Dimension(constit[1][1])*constit[1][2] div ext_field) eq n) then
      //now we look for case 3 above: there's a constituent of the
      //right dimension such that its multiplicity is equal to 
      //the dimension of GHom and the product of this number with 
      //the dimension is the whole space
        spaces:= [Image(ghoms[1].1)];
      end if;
    end if;
  end if;

  if #spaces eq 0 then
    //we couldn't find a match.
    return [], 0;
  end if;
  d:= Dimension(spaces[1]);
  if dim gt 0 and not d eq dim then
    return [], 0;
  end if;
  mats:= [GL(n, q)|];
  for space in spaces do
    vecs:= Morphism(space, module);
    mat1:= Matrix(GF(q), d, n, Eltseq(vecs));
    space2, phi:= quo<module| space>;
    vecs2:= Basis(space2)@@phi;
    mat2:= Matrix(GF(q), n-d, n, &cat[[vecs2[i][j] : j in [1..n]] : 
                                                         i in [1..n-d]]); 
    mat3:= VerticalJoin(mat2, mat1);
    Append(~mats, mat3^-1);
  end for;
  return mats, d;
end function;

/***************************************************************/

/* 
 * Point meet hyperplane can be taken to be <(0, 0, \ldots, 1)> and
 * hyperplane is (0, a_1, \ldots, a_d-1).
 * that is matrices with (a)i1 = 0 for i > 1, (a)di = 0 for i < d.
 *
 */  
 
function SLPointMeetHyperplane(d, p)
  diag:= [<i,i,1>: i in [1..d]];
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z, z^-1] cat [1 : i in [3..d]]);
  diag2:= DiagonalMatrix([1 : i in [1..d-2]] cat [z, z^-1]);
  if d gt 3 then 
    sl1:= DiagonalJoin(<GL(1, p).0, SL(d-2, p).1, GL(1, p).0>);
    sl2:= DiagonalJoin(<GL(1, p).0, SL(d-2, p).2, GL(1, p).0>);
  else
    sl1:= GL(d, p).0;
    sl2:= GL(d, p).0;
  end if;
  transvec1:= GL(d, p)!Matrix(GF(p), d, d, [<1,2,1>] cat diag);
  transvec2:= GL(d, p)!Matrix(GF(p), d, d, [<d-1,d,1>] cat diag);
  return sub<SL(d, p)|diag1, diag2, sl1, sl2, transvec1, transvec2>;
end function;

/***************************************************************/

/*
 * We take the n-space to be (0, \ldots, 0, a_1, \ldots, a_n) and
 * the (d-n)-space to be (a_1, \ldots, a_d-n, 0, \ldots, 0)
 */

function SLStabOfNSpaceMissDual(d, p, n)
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  dir_prod:= DirectProduct(SL(d-n, p), SL(n, p));
  return sub<SL(d, p)|diag1, dir_prod>;
end function;



/****************************************************************/
 
function SLPointStab(d, p)
  z:= PrimitiveElement(GF(p));
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLPointMeetHyperplane(d, p);
  transvec:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<2,1,1>]);
  return sub<SL(d, p)|grp, transvec>;
end function;    

/****************************************************************/

function SLStabOfNSpace(d, p, n)
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLStabOfNSpaceMissDual(d, p, n);
  transvec:= GL(d, p)!Matrix(GF(p), d,d, [<1, d-n+1, 1>] cat diag);
  return sub<SL(d, p)|grp, transvec>;
end function;


/**************************************************************/

/*
 * The main function: input two matrix groups G, H 
 * that are subgroups of GL(n, q) for some fixed n and q.
 * Print > 0 means it prints stuff, otherwise doesn't. 
 * Output: true, conj_elt if they are conjugate reducible subgroups of
 * GL(n, q).              
 *         "unknown" if they are both irreducible.
 *         false, _; otherwise.
 */

intrinsic IsGLConjugateReducible(G::GrpMat, H::GrpMat: Print:=0) 
-> BoolElt, GrpMatElt
{If G and H are conjugate reducible subgroups of the general linear 
group then returns true and an element conjugating G to H. 
Returns "unknown" if they are both irreducible. 
Returns false otherwise.} 
  n:= Degree(G); 
  q:= #BaseRing(G); assert q eq #BaseRing(H);
  require n eq Degree(H): "Groups must have same dimension";
  require q eq #BaseRing(H): "Groups must be over same field";


  z:= PrimitiveElement(GF(q));

  G_irred:= IsIrreducible(G); H_irred:= IsIrreducible(H);

  if not (G_irred eq H_irred) then
    if Print gt 0 then "not both reducible"; end if;
    return false, _, _;
  elif G_irred then
    return "unknown", _;
  end if;
   

  //if the groups are small and cyclic it's better to deal with them
  //like that
  if IsCyclic(G) then
    if not IsCyclic(H) then 
      return false, _, _;
    else
      assert exists(g){x : x in G | Order(x) eq #G};
      assert exists(h){x : x in H | Order(x) eq #H};
      conj, elt:= GLConjElts(g, h);
      if not conj then
        return false, _, _;
      else
        return true, (GL(n, q)!elt)^(-1);
      end if;
    end if;
  end if;      
             
   


  //first call to StandardiseReduct looks for "convenient" fixed
  //subspace of G, and returns a matrix so that G is visibly
  //reducible. 
  mats1, dim:= StandardiseReduct(G, n, q, 0);
  G:= G^mats1[1];
 
  //now we look to see if H stabilises any subspaces of the same
  //dimension, and get a list of standardising matrices, one for each
  //possible choice of dim-dimensional subspace. 
  mats:= StandardiseReduct(H, n, q, dim);
  if mats cmpeq false then
    if Print gt 0 then 
      "H does not preserve space of appropriate dimension";
    end if;
    return false, _;
  end if;

  diag:= DiagonalMatrix([z] cat [1 : i in [2..n]]);
  if dim eq 1 then
    overgroup:= sub<GL(n, q)|SLPointStab(n, q), diag>;
  else
    overgroup:= sub<GL(n, q)|SLStabOfNSpace(n, q, dim), diag>;
  end if;
  p, ov_p:= OrbitAction(overgroup, RSpace(overgroup).1);
  G_p:= G@p;

  //loop through each possible choice of subspace for H, looking to 
  //see if the resulting standardised groups are conjugate in overgroup.
  for i in [1..#mats] do    
    mat2:= mats[i];   
    bool, mat3:= IsConjugate(ov_p, G_p, (H^mat2)@p);
    if bool then
      return true, mats1[1]*(mat3@@p)*mat2^-1;
    end if;
  end for;
  
  if Print gt 0 then "groups not conjugate in any overgroup"; end if;
  return false, _;

end intrinsic;
