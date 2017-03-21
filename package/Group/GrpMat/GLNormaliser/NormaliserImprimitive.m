freeze;

/*
includes functions: 
NormaliserImprimOneBlock
NormaliserImprimitive
*/

import "NormaliserReducible_functions.m" : WreathCase;


group_norm:=recformat<overgroup,cob,got_overgroup,full_norm, derived_group>;

/********************************************************
NormaliserImprimOneBlock takes an imprimitive matrix group G stabilizing 1 block system B with K the block kernel of B in G(?)
*/


NormaliserImprimOneBlock:=function(G,K)
  n:=Dimension(G);
  q:=#BaseRing(G);
  module:=GModule(K);
  const:=Constituents(module);
  ghoms:=[GHom(c,module):c in const];
  ovgroup,mat:=WreathCase(ghoms,#const);
  //assert not false in [x in overgroup:x in Generators(G)];
  return rec<group_norm|overgroup:=ovgroup, cob:=mat^-1, got_overgroup:=true,full_norm:=false>;
end function;


/*************************
NormaliserImprimitive takes an imprimitive group G and returns record in format group_norm
doesn't recurse so doesn't need der_group
*/


function NormaliserImprimitive(group)
  n:=Dimension(group);
  q:=#BaseRing(group);

  //try each block dims and pick one with fewest normal subs
  B1:=Blocks(group);
  dim:=Dimension(B1[1]);
  K1:=Stabiliser(group,B1);
  ok1:=#K1;
  possKs:=[k`subgroup:k in NormalSubgroups(group: OrderEqual:=ok1) | not IsIrreducible(k`subgroup) and not k`subgroup eq K1];

  /*get other normal subgps of G that might be block system stablisers conjugate to K1*/

  /* see if there's any better block system dimension*/
  divs:=[d: d in Divisors(n)| not d in [dim,n]];
  if #divs gt 0 then
    for d in divs do 
      if IsPrimitive(group:BlockSizes:=d) then
        B2:=Blocks(group);
        K2:=Stabiliser(group,B1);
        newKs:=[k`subgroup:k in NormalSubgroups(group: OrderEqual:=#K2) | not IsIrreducible(k`subgroup) and not k`subgroup eq K2];
        if #newKs lt #possKs then
          dim:=d;
          possKs:=newKs;
          B1:=B2;
          K1:=K2;
        end if;
      end if;
    end for;
  end if;

  N:=NormaliserImprimOneBlock(group,K1);
  GL_stab_B1:=N`overgroup;
  mat:=N`cob;
  //stabiliser in GL of the block system B1

  if #possKs eq 0 then
    //only one block system
    return rec<group_norm|overgroup:=GL_stab_B1,cob:=mat,got_overgroup:=true, full_norm:=false>;  
  end if;

  /* try as many invariants as possible to whittle them down */

  ks1:=[k : k in possKs | Set(ChiefFactors(k)) cmpeq Set(ChiefFactors(K1))];
  if #ks1 eq 0 then
    return rec<group_norm|overgroup:=GL_stab_B1, cob:=mat, got_overgroup:=true, full_norm:=false>; 

  else 
    ks2:=[k : k in ks1 | #Constituents(GModule(K1)) eq #Constituents (GModule(k))]; 
    if #ks2 eq 0 then
      return rec<group_norm|overgroup:=GL_stab_B1, cob:=mat,got_overgroup:=true, full_norm:=false>;
 
    else 
      ks3:=[k : k in ks2 | SequenceToMultiset([#o:o in Orbits(k)]) eq SequenceToMultiset([#o:o in Orbits(K1)])];
      if #ks3 eq 0 then
        return rec<group_norm|overgroup:=GL_stab_B1, cob:=mat,got_overgroup:=true, full_norm:=false>;   
      end if;
    end if;
  end if;
  //see if any conjugate to K1
  conj_ks:=[];
  conj_elts:=[];
  RandomSchreier(K1);
  done:=0;
  i:=1;
  while done eq 0 do
    k:=ks3[i];
    RandomSchreier(k);
    if dim eq 1 then
      bool,x:=IsConjugate(GL(n,q),k, K1);    
    else
      bool,x:=IsGLConjugate(k, K1);    //can be slow
    end if;
    if bool then 
      Append(~conj_ks,k);
      Append(~conj_elts,x);
    end if;
    if (#conj_ks gt 1) or (i eq #ks3) then
      done:=1;
    else i:=i+1;
    end if;
  end while;
 
  if #conj_ks eq 0 then
    return rec<group_norm|overgroup:=GL_stab_B1, cob:=mat,got_overgroup:=true, full_norm:=false>; 
  end if;

  // group preserves more than 2 block systems
    return rec<group_norm|got_overgroup:=false>;
end function;
    
