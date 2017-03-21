freeze;

/*
functions for NormaliserReducible 

SLPointMeetHyperplane
SLStabOfNSpaceMissDual
SLPointStab
SLStabOfNSpace
aplus
bplus
pslsize
SLstab_order
make_cob_matrix
SubspaceStabiliser
StabiliseSubmodules
WreathCase
TensorCase
DirectProductCase
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

/*********************************************/

function SLStabOfNSpaceMissDual(d, p, n)
  z:= PrimitiveElement(GF(p));
  diag1:= DiagonalMatrix([z] cat [1 : i in [2..d-1]] cat [z^-1]);
  dir_prod:= DirectProduct(SL(d-n, p), SL(n, p));
  return sub<SL(d, p)|diag1, dir_prod>;
end function;

/*********************************************/

function SLPointStab(d, p)
  z:= PrimitiveElement(GF(p));
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLPointMeetHyperplane(d, p);
  transvec:= GL(d, p)!Matrix(GF(p), d, d, diag cat [<2,1,1>]);
  return sub<SL(d, p)|grp, transvec>;
end function;

/****************************************/

function SLStabOfNSpace(d, p, n)
  diag:= [<i,i,1>: i in [1..d]];
  grp:= SLStabOfNSpaceMissDual(d, p, n);
  transvec:= GL(d, p)!Matrix(GF(p), d,d, [<1, d-n+1, 1>] cat diag);
  return sub<SL(d, p)|grp, transvec>;
end function;

/***************************************************/


/*from K&L shape of subspace stabilizer is q^{d(n-d)} * a^+_{d,n-d}/(q-1,n) * L\
_d(q) \times L_{n-d}(q) * b^+_{m,n-m}

a^+_{d,n-d}:=|{(\lambda_1,\lambda_2) \in \mathbb{F}^*_q \times \mathbb{F}^*_q |\
 \lambda_1^d * \lambda_2^{n-d} = 1 }|

b^+_{d,n-d} := (q-1)/(a^+_{d,n-d}) * (q-1,d) * (q-1,n-d)

This is inside GL not SL
*/

aplus:=function(q,seq);
  k:=#seq;
  F:=FiniteField(q^2);

  S:=[];
  for f in F do
    if f^(q-1) cmpeq Identity(F)
      then Append(~S,f);
    end if;
  end for;
  F2:=CartesianPower(S,k);

  L:=[];
  for l in F2 do
    y:=1;
    for i in [1..k] do
      y:=y*(l[i]^seq[i]);
    end for;
    if y cmpeq Identity(F)
      then Append(~L,l);
    end if;
  end for;
  return(#L);
end function;

/************************************/

bplus:=function(n,q,d,a);
  x:=(q-1)/ a;
  y:=Gcd(q-1,d)*Gcd(q-1,n-d);
  return IntegerRing()!(x*y);
end function;

/*********************************************/
pslsize:=function(n, q)
  prod:=q^(1/2 *n*(n-1));
  i:=n;
  while i gt 1 do
    prod:=prod*(q^i-1);
    i:=i-1;
  end while;
  d:=Gcd(q-1,n);
  return IntegerRing()!(prod/d);
end function;


/***********************************/


function SLstab_order(n,q,d)
  a:=aplus(q,[n,n-d]);
  b:=bplus(n,q,d,a);

  if d lt 2 then
    P1:=1;
  else
    P1:=pslsize(d,q);
  end if;
  if n-d lt 2 then
    P2:=1;
  else
    P2:=pslsize(n-d,q);
  end if;
  order:=q^(d*(n-d)) * (a div Gcd(q-1,n)) * P1 * P2 * b * Gcd(n,q-1);
  return order;
end function;

//GLstab_order:=SLstab_order*(q-1);

/*************************************************/

/*
needed for: SubspaceStabiliser, TensorCase, WreathCase, DirectProductCase

Takes a list of G-homomorphisms in matrix form mapping a subspace into the whole module. Finds a set of vectors including the G-homs which span V and makes the associated change of basis matrix.
*/



make_cob_matrix:=function(rows,q)
  n:=#rows[1];
  V:=VectorSpace(GF(q),n);
  check:=sub<V | rows>;
  check_dim:=Dimension(check);
  if not check_dim eq #rows then
    //there are some redundant vectors 
    //take a subset which spans the space
    subspace:=sub<V | rows[1]>;
    keep:=[rows[1]];
    for i in [2..#rows] do
      ss_dim:=Dimension(subspace);
      subspace:=sub<V | subspace, rows[i]>;
      if Dimension(subspace) eq ss_dim+1 then
        Append(~keep,rows[i]);
      end if;
    end for;
    rows:=keep;
  end if;

  if check_dim eq n then
    return GL(n,q)!Matrix(rows);

  else
    vectors:=[Vector(v):v in rows];
    W:=sub<V|vectors>;
    new_rows:=[];
    while Dimension(W) lt n do
      ext:=[e : e in ExtendBasis(W, V)|not e in W];
      new_rows:=new_rows cat ext;
      W:=sub<V|W,ext>;
    end while;
    
    cob_rows:=new_rows cat vectors;    
  end if;

  cob:=GL(n,q)!Matrix(GF(q),n,n,cob_rows);
  return cob;

end function;

/****************************************/

/*
needed for: StabiliseSubmodules

Takes a list of G-hom spaces (mapping a subspace into the whole module) and dimension of the subspace.
Returns the stabiliser in GL(n,q) of the subspace over the new basis.
*/


function SubspaceStabiliser(ghoms,d);
  n:=Ncols(ghoms[1].1);
  q:=#BaseRing(ghoms[1]);
  rows:=&cat[ &cat[RowSequence(ghom.i):i in [1..Ngens(ghom)]]:ghom in ghoms];
  cob:=make_cob_matrix(rows,q);
  if d eq 1 then
    SLStab:=SLPointStab(n,q);
  else
    SLStab:=SLStabOfNSpace(n,q,d);
  end if;
  daddy_group:=sub<GL(n,q)|SLStab,GL(n,q).1>;

  return daddy_group, cob^-1;
end function;




/*************************************************/

/*
takes a list of lists of records (V_i's) relating to irred submods of same dim and same mult
Find the combination of the v_is with collective dimension closest to n/2 and take stabiliser of associated submodule as overgroup

block:=rec < const_data | index:=i, const:=c[1], const_dim:=Dimension(c[1]), mult:=c[2], ghom:=Ghom, ghom_dim:=Ghom_dim, valid:=Ghom_dim gt 0 >;

const_data:=recformat<index, const, const_dim, mult,  ghom, ghom_dim, valid>;

if CompletelyReducible:=false then some consts have ghom dims smaller than mult

returns true if got overgroup, false if not
*/


function StabiliseSubmodules(Vs:CompletelyReducible:=true)
  n:=Ncols((Vs[1]`blocks)[1]`ghom.1);
  q:=#BaseRing((Vs[1]`blocks)[1]`ghom.1);

  L:=[s:s in Subsets(Set([1..#Vs]))|not IsEmpty(s)];
  collective_dims:=[];
  for sub in L do
    sum:=0;
    
    if CompletelyReducible then
      dims_to_add:=[Vs[i]`V_dim:i in sub];
    else  
      dims_to_add:=[]; 
      for i in sub do
        sub_sum:=0; 
        for block in Vs[i]`blocks do
          sub_sum:=sub_sum+block`const_dim*Minimum(block`mult, block`ghom_dim);
        end for;
        Append(~dims_to_add,sub_sum);
      end for;  
    end if;

    for d in dims_to_add do
      sum:=sum+d;
    end for;
    Append(~collective_dims, sum);
  end for;

  list:=[l:l in L];

  dif:= n;
  for i in [1..#L] do
    Try:=AbsoluteValue(collective_dims[i] - n/2);
    if Try lt dif then
      chosen_Vs:=[Vs[j]:j in list[i]];
      chosen_dim:=collective_dims[i];
      dif:=Try;
    end if;
  end for;

  if chosen_dim eq n then
    return GL(n,q), GL(n,q).0, false;
    /* can happen if problem case - not comp red but ghom dims = mults for each const */
  end if;

  chosen_ghoms:=&cat[[block`ghom:block in V`blocks]:V in chosen_Vs];
  overgroup,cob:=SubspaceStabiliser(chosen_ghoms,chosen_dim);

  return overgroup, cob, true;
end function;



/********************************************/



/*
Case when all submodules are isomorphic.
Takes a ghom space mapping one subspace into the whole module and mult = the number of isomorphic submodules.
Returns the tensor product of GL_mult(q) and the subspace over the new basis
also returns change of basis matrix
*/

function TensorCase(ghom,mult)
  n:=Ncols(ghom.1);
  q:=#BaseRing(ghom);
  block_dim:=n div mult;
  A:=GL(mult,q);
  B:=GL(block_dim,q);

  T:=&cat [[TensorProduct(a,b):a in Generators(A)]:b in Generators(B)];
  tensor:=sub<GL(n,q)|T>;
  rows:=&cat [RowSequence(ghom.i):i in [1..Ngens(ghom)]];
  cob:=make_cob_matrix(rows,q);
  return tensor,cob;

end function;


/********************************************/


/*
Case when all submods have same dim and mult and are all non-isomorphic.
Takes a list of ghom spaces mapping one subspace into the whole module and num = number of non-isomorphic submodules.
Returns the wreath product of the subspace and GL_num(q) over the new basis. Also returns change of basis matrix.
*/

function WreathCase(ghoms,num)
  n:=Ncols(ghoms[1].1);
  q:=#BaseRing(ghoms[1]);
  dim:=n div num;
  wreath:=WreathProduct(GL(dim,q),Sym(num));
  rows:=&cat[&cat [RowSequence(ghom.i):i in [1..Ngens(ghom)]]:ghom in ghoms];
  cob:=make_cob_matrix(rows,q);
  return wreath,cob;
end function;


/*******************************************/

/* group is completely reducible and all collections of groups with same dim and same mult have just one isomorphism type.
overgroup is a direct product of the irred submods
*/

function DirectProductCase(group,Vs)
  block_ghoms:=&cat[[block`ghom:block in V`blocks]:V in Vs];
  rows:=&cat[&cat [RowSequence(ghom.i):i in [1..Ngens(ghom)]]:ghom in block_ghoms];
  q:=#BaseRing(Vs[1]`blocks[1]`const);
  cob:=make_cob_matrix(rows,q);
  group_diag:=group^cob^-1;

  for_dirproduct:=[];
  start:=1;
  for V in Vs do
    dim:=V`V_dim;
    block_gens:=[ExtractBlock(gen,start,start,dim, dim):gen in Generators(group_diag)];
    small_group:=sub<GL(dim,q)|block_gens>;
    norm:=GLNormaliser(small_group: Overgroup:=true);
    small_overgroup:=(norm`overgroup)^(norm`cob^-1);
    Append(~for_dirproduct,small_overgroup);
    start:=start+V`V_dim;
  end for;

  overgroup:=DirectProduct([H:H in for_dirproduct]);
  return overgroup,cob;
end function;

