freeze;


/*
 * Function names in this file:
 MakeTensor(group, a, process)
 GLCentralGL(dim1, dim2, q)
 StandardiseTens(group, d, p, process)
 IsGLConjugateTensor(H, K: Print)  
 */


/**********************************************************************
This function seeks to find an element of GL(d, q) which will
conjugate group1 to group2. They are assumed to be conjugate
groups which preserve a tensor product. The idea is to conjugate each
of them via a change of basis matrix into a standard copy of the
tensor product. 

It may be that each group
preserves more than 1 tensor decompotion - we demand that group2 has
the same size decomposition as group1, and run again on a random
conjugate if IsTensor returns unknown.
***********************************************************************/


/*******************************************************************
This function just conjugates a group until IsTensor returns
false, and returns the true, conjugating element. If it runs for more 
than 100 times it returns false, _ 
*********************************************************************/

MakeTensor:= function(group, a, process)
  for i in [1..100] do
    if IsTensor(group^a) cmpeq true then
      return true, a;
    end if;
  a:= Random(process);
  end for;
  return false, _;
end function;

/****************************************************************
*         The following function produces the central           *
*         product of GL(dim1, p) and GL(dim2, p)                *
*****************************************************************/

function GLCentralGL(dim1, dim2, p)
  assert #Factorisation(p) eq 1;
  gens1:= SetToSequence(Generators(GL(dim1, p)));
  gens2:= SetToSequence(Generators(GL(dim2, p)));
  Append(~gens1, Identity(GL(dim1, p)));
  Append(~gens2, Identity(GL(dim2, p)));
  newgens:= [];
  for x in gens1 do
    for y in gens2 do 
	Append(~newgens, KroneckerProduct(x, y));
    end for;
  end for;
  return sub<GL(dim1*dim2, p)| newgens>;
end function;


/****************************************************************
*   The following function takes a tensor decomposable          *
*   group and standardises it - its tensor basis is             *
*   the identity matrix, and it embeds into GL(dim1) circ       *
*   GL(dim2) where dim1 \leq dim2. It returns the group         *
*   as well as the required conjugating element                 *
*****************************************************************/

function StandardiseTens(group, d, p, process)

  /* First we ensure that we know that group is tensor - 
   * conj is the element that we will have conjugated by to 
   * make IsTensor return true
   */
  a:= Random(process);
  x, conj:= MakeTensor(group, a, process);
  if not x then          /*Unable to get IsTensor to return true*/     
    "can't make group preserve tensor product";
    return "unknown", _;
  end if;

  /* now we find a tensor decomposition and the change of basis matrix, 
   * and conjugate group^a so that it lies in a standard copy of the
   * full group preserving this tensor decomposition.
   */
  new_group:= group^conj;
  for i in [1..5] do
    if (IsTensor(new_group) cmpeq true) then
      break;
    end if;
    if i eq 5 then 
      "IsTensor misbehaving";
      return "unknown", _;
    end if;
  end for;

  basis:= TensorBasis(new_group);
  standard_group:= new_group^basis;
  return standard_group, conj*basis;
end function;


/****************************************************************
************ The main function **********************************
*****************************************************************/

intrinsic IsGLConjugateTensor(H::GrpMat, K::GrpMat: Print:=0) 
-> BoolElt, GrpMatElt
{If conjugates of H and K are shown to be conjugate in a maximal tensor
product subgroup of the general linear group then returns 
true and a matrix conjugating H to K. If they are shown not to be 
conjugate in the general linear group then returns false. 
Otherwise returns "unknown".} 

  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  p:= #BaseRing(H); 
  require p eq #BaseRing(K): "Groups must be over same field";

  require IsAbsolutelyIrreducible(H): "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K): "Groups must be absolutely irreducible";
  process:= RandomProcess(GL(d, p));

  standardised:= false;
  if Print gt 0 then "standardising H"; end if;
  for i in [1..100] do
    standard_H, Hconj:= StandardiseTens(H, d, p, process);
    if standard_H cmpeq "unknown" then return "unknown", _; end if;
    bool:= IsTensor(standard_H);
    if not (bool cmpeq true) then
      bool:= IsTensor(standard_H);
      if not (bool cmpeq true) then
        return "unknown", _;
      end if;
    end if;

    factors1:= TensorFactors(standard_H);
    dim1:= Dimension(factors1[1]);
    dim2:= Dimension(factors1[2]);
    if (TensorBasis(standard_H) eq Identity(GL(d, p))) then
      standardised:= true;
      break;
    end if;
  end for;
  if not standardised then return "unknown", _; end if;

  for g in Generators(standard_H) do
    if not IsProportional(g, dim1) then 
      if Print gt 0 then "failed to decompose H's generators"; end if;
      return "unknown", _;
    end if;
  end for;

  overgroup:= GLCentralGL(dim2, dim1, p);
  hom, ov_hom:= OrbitAction(overgroup, RSpace(overgroup).1);

 //We now check that K has a decomposition of the correct degree,
 //and produce its two factors.
  if Print gt 0 then "standardising K"; end if;
  conj2:= Identity(GL(d, p));
  found:= false;
  for i in [1..1000] do
    new_K:= K^conj2;
    temp:= IsTensor(new_K : Factors:= [[dim1, dim2]]);
    if (temp cmpeq true) then 
      if Dimension(TensorFactors(new_K)[1]) eq dim1 then
        found:= true;
        break;				  
      end if; 
    end if;
    conj2:= Random(process);
  end for;

  //The next bit can probably be upgraded to return "false" instead of
  //"unknown", but I shall be cautious for now..
  if not found then
    "K probably does not preserve a tensor decomposition";
    "of the right dimension"; 
    return "unknown", _;
  end if;

  basis2:= TensorBasis(new_K);
  standard_K:= new_K^(basis2);  
  for g in Generators(standard_K) do
    if not IsProportional(g, dim1) then 
      if Print gt 0 then "failed to decompose K's generators"; end if;
      return "unknown", _;
    end if;
  end for;

  if Print gt 0 then "final conjugacy check"; end if;
  bool, elt:= IsConjugate(ov_hom, standard_H@hom, standard_K@hom);
  if bool then
    return true, Hconj*(elt@@hom)*(basis2^-1)*(conj2^-1);
  end if;
  return "unknown", _;
end intrinsic;


