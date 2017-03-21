freeze;

import "NormaliserReducible_functions.m": StabiliseSubmodules, TensorCase, 	WreathCase, DirectProductCase;


/*
Takes a reducible matrix group G < GL(n,q) and returns an overgroup R and a matrix x such that the normaliser in GL(n,q) of G is inside R^(x^-1).
If Print is an integer greater than 0 then returns information about the type of reducible group.

Returns a record in group_norm format
*/

group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;


/**********************************/

function NormaliserReducible(group:Print:=0)
  n:=Dimension(group);
  q:=#BaseRing(group);
  comp_red:=false;
  all_abs_irred:=false;
  if IsIrreducible(group) then
    return "irreducible";
  end if;

  module:=GModule(group);
  if IsDecomposable(module) then 
    decomp:=Decomposition(module);
    if not false in [IsIrreducible(com):com in decomp] then
      comp_red:=true; 
    end if;
    if not false in [IsAbsolutelyIrreducible(com):com in decomp] then
      all_abs_irred:=true;    
    end if;
  end if;

  consts:=ConstituentsWithMultiplicities(module); 

  const_data:=recformat<index, const, const_dim, mult, ghom, ghom_dim, valid_mult, valid>;

/* 
valid: if ghom has dimension 0 then quotient is not a subspace.
Only want to stabilize the real subspaces. 
If more than one subspace of the same dim then they might map to each other so stabilize all. 
*/

  //make a list called 'blocks' of records with info about the constituents

  blocks:=[];
  for i in [1..#consts] do
    c:=consts[i];
    Ghom:=GHom(c[1],module);
    Ghom_dim:=Dimension(Ghom);

    block:=rec < const_data | index:=i, const:=c[1], const_dim:=Dimension(c[1]), mult:=c[2] ,ghom:=Ghom, ghom_dim:=Ghom_dim, valid_mult:=Minimum(c[2],Ghom_dim), valid:=Ghom_dim gt 0 >;
    Append(~blocks, block);
  end for;

  Dims:=[block`const_dim:block in blocks | block`valid eq true];
  Mults:=[block`valid_mult:block in blocks | block`valid eq true];
  Vs:=[];
  V_data:=recformat<blocks, dim, mult, num_isom_types, V_dim >;
  for d in Set(Dims) do
    blocks_d:=[block:block in blocks|block`valid eq true and block`const_dim eq d];

    for m in Set(Mults) do
      mults_d:=[block:block in blocks_d|block`valid_mult eq m];
      if not IsEmpty(mults_d) then 
        //all consts of same mult and dimension
        V_record:=rec < V_data | blocks:=mults_d, dim:=d, mult:=m, num_isom_types:=#mults_d, V_dim:=d*m*#mults_d>; 
        Append(~Vs,V_record);
      end if;
    end for;
  end for;

  dimVs:=0;
  for V in Vs do
    dimVs:=dimVs+V`V_dim;
  end for;

  if (not comp_red) or (not all_abs_irred) or (dimVs lt n) then 
    //stabilise combination of V_i's with collective dim closest to n/2
    if Print gt 0 then 
      "Submodule stabiliser case";
    end if;
    ovgroup,mat, got_ov:=StabiliseSubmodules(Vs:CompletelyReducible:=comp_red);
    
  else //group completely reducible   

    isom_types:=[V`num_isom_types:V in Vs];   
    if #Vs eq 1 then 
      V:=Vs[1];
      
      if isom_types[1] eq 1 then        //tensor product 
        block:=(V`blocks)[1];
        if block`ghom_dim gt block`mult then
          //problem case
          if Print gt 0 then 
            "Problem case";
          end if;
          ovgroup:=GL(n,q);
          mat:=GL(n,q).0;
          got_ov:=false;

        elif not IsAbsolutelyIrreducible(block`const) then 
          if Print gt 0 then 
            "Problem case";
          end if;
          ovgroup:=GL(n,q);
          mat:=GL(n,q).0;
          got_ov:=false;

        else 
          if Print gt 0 then 
            "Tensor product case";
          end if;
          ovgroup,mat:=TensorCase(block`ghom, block`valid_mult);
          mat:=mat^-1;
          got_ov:=true;
        end if;

      else        //wreath product
        if Print gt 0 then 
          "Wreath product case";
        end if;
        wreath_ghoms:=[block`ghom:block in V`blocks];
        ovgroup, mat:=WreathCase(wreath_ghoms,isom_types[1]);
        mat:=mat^-1;
        got_ov:=true;
      end if;
        
    else      
      //more than one V
      if Print gt 0 then 
        "Direct product case";
      end if;
      ovgroup, mat:= DirectProductCase(group,Vs);
      mat:=mat^-1;
      got_ov:=true;
    end if;
  end if;

  return rec<group_norm|overgroup:=ovgroup, cob:=mat, got_overgroup:=got_ov, full_norm:=false>;
end function;







