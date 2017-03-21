freeze;

/*
 * Function names in his file:
 MakeTensorInduced(group, a, process)
 IsGLConjugateTensorInduced(H, K: Print)
 */

/**********************************************************************
This function seeks to find an element of GL(d, q) which will
conjugate H to K. They are assumed to be tensor induced groups. 

We find the change of basis matrix which exhibits the kronecker
product, check that it is correct, and then see if they are conjugate
in GL(d/s) \wr Sym(s)

***********************************************************************/


/*******************************************************************
This function just conjugates a group until IsTensorInduced return
true, and returns true, conjugating element. If it runs for more 
than 100 times it returns false, _ 
*********************************************************************/

MakeTensorInduced:= function(group, a, process)
  for i in [1..100] do
    if IsTensorInduced(group^a) cmpeq true then
       return true, a;
    end if;
    a:= Random(process);
  end for;
  return false, _;
end function;

/****************************************************************
************ The main function **********************************
*****************************************************************/

intrinsic IsGLConjugateTensorInduced(H::GrpMat, K::GrpMat: Print:=0) 
-> BoolElt, GrpMatElt
{If conjugates of H and K are conjugate in a maximal tensor induced
subgroup of the general linear group then returns true and a 
matrix conjugating H to K. If H and K are shown not to be conjguate 
in the general linear group then returns false. Otherwise returns "unknown".} 

  d:= Degree(H);
  require d eq Degree(K): "Groups must have same dimension";
  q:= #BaseRing(H); 
  require q eq #BaseRing(K): "Groups must be over same field";

  require IsAbsolutelyIrreducible(H): "Groups must be absolutely irreducible";
  require IsAbsolutelyIrreducible(K): "Groups must be absolutely irreducible";

  process:= RandomProcess(GL(d, q));

  if Print gt 0 then "ensuring H tensor induced"; end if;
  x, a:= MakeTensorInduced(H, Identity(GL(d, q)), process);
  if not x then          /*Unable to get IsTensor to return true*/     
     if Print gt 0 then "H not tensor induced"; end if;
     return "unknown", _;
  end if;
  new_H:= H^a;
  for i in [1..5] do
    if (IsTensorInduced(new_H) cmpeq true) then
      break;
    end if;
    if i eq 5 then 
      return "unknown", _;
    end if;
  end for;

  assert IsTensorInduced(new_H);

  if Print gt 0 then "standardising H"; end if;
  tensor_basis1:= TensorInducedBasis(new_H);
  standard_H:= new_H^tensor_basis1;
  assert IsTensorInduced(standard_H);
  H_gens:= SetToSequence(Generators(standard_H));
  
  if Print gt 0 then "checking standardisation of H"; end if;
  perms:= TensorInducedPermutations(standard_H);
  num_facs:= Degree(Parent(perms[1]));
  dim:= Integers()!Round(Root(d, num_facs));
  assert dim^num_facs eq d;

 /* Always wise to check that we do have kronecker products of the
  * correct degree for the maps in the kernel of the homomorphism to
  * Sym(num_facs). 
  */
  for j in [1..num_facs] do   
    for k in [1..#H_gens] do
      if perms[k] cmpeq Identity(Sym(num_facs)) then 
        if not IsProportional(standard_H.k, dim^j) then
          if Print gt 0 then
	    "dim =", dim, "j = ", j;
            "k = ", k, "standard_H.k = ", standard_H.k;
	    "decomposition of H failed";
          end if;
	  return "unknown", _;
	end if;
      end if;
    end for;
  end for;

  overgroup:= TensorWreathProduct(GL(dim, q), Sym(num_facs)); 
  hom, ovp:= OrbitAction(overgroup, Orbit(overgroup, RSpace(overgroup).1));

  //We now start working on K.
  b:= Identity(GL(d, q));
  for i in [1..20] do
    // Want a a different copy of K each time       
    conjelt:= Random(process);
    new_K:= K^conjelt;

    if Print gt 0 then "ensuring K suitably tensor induced"; end if;
    if not (IsTensorInduced(new_K: InducedDegree:= num_facs) cmpeq true) then
      return false, _;
    end if;

    tensor_basis2:= TensorInducedBasis(new_K);
    standard_K:= new_K^tensor_basis2;
    assert IsTensorInduced(standard_K);      
     
    if Print gt 0 then "checking standardisation of K"; end if;
    gens2:= SetToSequence(Generators(standard_K));
    perms2:= TensorInducedPermutations(standard_K);
    for j in [1..num_facs] do   
      for k in [1..#gens2] do
	if perms2[k] cmpeq Identity(Sym(num_facs)) then
          if not IsProportional(standard_K.k, dim^j) then
            if Print gt 0 then 
	      "decomposition of K failed";
            end if;
            return "unknown", _;
          end if;
	end if;
      end for;
    end for;
    
    if Print gt 0 then "final conjugacy test"; end if; 
    x, y:= IsConjugate(ovp, standard_H@hom, standard_K@hom);  
    if x then                  /*FOUND IT!!*/
      return true, a*tensor_basis1*(y@@hom)*tensor_basis2^-1*conjelt^-1;
    end if;
  end for;	
  return "unknown", _;
end intrinsic;






