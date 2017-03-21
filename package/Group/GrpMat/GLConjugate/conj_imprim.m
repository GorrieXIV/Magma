freeze;

/* Function names in this file:
MakeImprim(group, a, process)
StandardiseBlocks(listofblocks, d, p)
IsGLConjugateImprimitive(H, K: Print)
*/

/**********************************************************************
This function seeks to find an element of GL(d, q) which will
conjugate H to K. They are assumed to be imprimitive irreducible
groups. The idea is to find a basis of blocks for H
and the same for K. We then conjugate both of them to a standard
basis for the full imprimitive group on this type of decomposition,
and look for a conjugating element in there. 

It may be that each group preserves more than 1 system of
imprimitivity - if we do not get isomorphic induced action on 
blocks then we reconjugate K. Since the 2 groups are assumed 
to be conjugate, this should eventually work.

the other problem is that IsPrimitive changes its mind occasionally
so we have to *check* this and if necessary reconjugate either or 
both groups until it returns "fail".

At present I'm relying on the fact that when you construct a wreath
product of GL(m/d) \wr Sym(d) you get blocks {e_1, \ldots, e_{m/d}},
\ldots {e_{m - m/d}, \ldots, e_d}. I'm also relying on the
H and K, in that I assume the groups are
transitive on the set of blocks. 
***********************************************************************/


/*******************************************************************
This function just conjugates a group until IsPrimitive returns
false, and returns true, conjugating element. If it runs for more 
than 1000 times it returns false, _ 
*********************************************************************/

MakeImprim:= function(group, a, process)
  i:= 0;
  for i in [1..100] do
    if IsPrimitive(group^a) cmpeq false then
       return true, a;
    end if;
    a:= Random(process);
  end for;                     
  return false, _;
end function;


/*********************************************************************
This is the function which takes a list of blocks of an
imprimitive element g, (relative to which g
is block matrices) and returns a conjugating element standardise such
that g^standardise is block matrices wrt the standard basis. 

*********************************************************************/

StandardiseBasis:= function(listofblocks, d, p)
  nmr_of_blocks:= #listofblocks;
  //The following line produces a single list of vectors
  list:= &cat[Basis(listofblocks[i]) : i in [1..nmr_of_blocks]];
  //turn the list of vectors into list of rows in a matrix 
  mat:= GL(d, p)!&cat[[list[i][j] : j in [1..d]] : i in [1..d]];
  return mat^-1;
end function;


/****************************************************************
************ The main function **********************************
*****************************************************************/


intrinsic IsGLConjugateImprimitive(H::GrpMat, K::GrpMat: Print:=0) -> BoolElt, GrpMatElt
{If conjugates of H and K can be shown to be conjugate inside a 
maximal imprimitive subgroup of the general linear group, then
returns true and a matrix conjugating H to K. If H and K are shown 
not to be conjugate in the general linear group then returns false. 
Otherwise returns "unknown".}
  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  p:= #BaseRing(H); 
  require p eq #BaseRing(K): "Groups must be over same field";

  require IsAbsolutelyIrreducible(H) : "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K) : "Groups must be absolutely irreducible";


  process:= RandomProcess(GL(d, p));
 
 /* First we ensure that we know that H is imprimitive - 
  * a is the element that we will have conjugated by to 
  * make IsPrimitive return false
  */
  H_imprim, a:= MakeImprim(H, Identity(GL(d, p)), process);
  if not H_imprim then return "unknown", _; end if;
   new_H:= H^a; 

 /* now we find a system of impritivity and the induced action 
  * on the set of blocks, and conjugate H^a so that it 
  * lies in a standard copy of the full wreath product preserving
  * this block system
  */
  if not (IsPrimitive(new_H) cmpeq false) then
    if not (IsPrimitive(new_H) cmpeq false) then
      //hopefully won't get to here: if we do then IsPrimitive
      //is misbehaving. 
      return "unknown", _;
    end if;
  end if;

  assert not IsPrimitive(new_H);
  H_blocks:= Blocks(new_H); permH:= BlocksImage(new_H);
  aprime:= StandardiseBasis(H_blocks, d, p);
  standard_H:= H^aprime;
  
  overgroup:= WreathProduct(GL(d div #H_blocks, p), Sym(#H_blocks)); 
  hom, ov_hom:= OrbitAction(overgroup, RSpace(overgroup).1);

  //We now start working on K
  b:= Identity(GL(d, p));
  for i in [1..20] do
    //We want a different copy of K each time
    conjelt:= Random(process);
    K_temp:= K^conjelt;

    //This is to ensure that we have a system of imprimitivity
    x, b:= MakeImprim(K_temp, b, process);
    if not x then return "unknown", _; end if; 
      
    new_K:= K_temp^b;
    if not (IsPrimitive(new_K) cmpeq false) then 
      if Print gt 0 then
        //hopefully won't get here. 
        "IsPrimitive behaving unpredictably, or block sizes wrong";
      end if;
      continue;
    end if;
    K_blocks:= Blocks(new_K);
    if not (#K_blocks eq #H_blocks) then
      continue;   //have found wrong block system.
    end if;
    permK:= BlocksImage(new_K);
    if not IsConjugate(Sym(#H_blocks), permH, permK) then
       continue;  //Have found wrong block system.
    end if;

    //if we reach this far then we hopefully have the right system of
    //imprimitivity for K
    bprime:= StandardiseBasis(K_blocks, d, p);
    standard_K:= new_K^bprime;
    
    if Print gt 0 then    
      "conjugating in overgroup";
    end if;    
    x, y:= IsConjugate(ov_hom, standard_H@hom, standard_K@hom);  
    if x then                  /*FOUND IT!!*/
      return true, (a*aprime*(y@@hom)*bprime^-1*b^-1*conjelt^-1);
    end if;
  end for;	
  return "unknown", _;
end intrinsic;

