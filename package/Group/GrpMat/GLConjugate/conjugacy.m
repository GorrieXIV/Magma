freeze;

/*
 Function names in this file:
 IsConjTest(H, K)
 MightBeEqual(val1, val2)
 IsGLConjugate(H, K: Print)
*/

/*
 * This function contains the main functions for the
 * GLConjugacy test. IsConjTest mostly designed and implemented by
 * Bill Unger. IsGLConjugate mostly designed and implemented by
 * Colva Roney-Dougal, with some input from Bill Unger.
 * Colva Roney-Dougal is planning to publish an article on this called 
 *"Conjugacy of subgroups of the general linear group", which will
 * explain the theory behind what's going on.
 */

//quick test to see if its possible that the two groups are conjugate
//looks for quick and easy differences to rule out.
IsConjTest:= function(H, K)
  d:= Dimension(H);
  if #H ne #K then 
    return true, false; 
  end if;
  if H eq K then 
    return true, true; 
  end if;

  //"orbits of spaces";
  q := #BaseRing(H);
  if q^d le 2^25 then
      if IsPrime(#BaseRing(H)) then
	for i in [1, 2] do
	  Hs:= [x[1] : x in OrbitsOfSpaces(H, i)];
	  Ks:= [x[1] : x in OrbitsOfSpaces(K, i)];
	  Sort(~Hs); Sort(~Ks);
	  if Hs ne Ks then 
	    return true, false; 
	  end if;
	end for;
      else 
	H_orb:= [#x : x in Orbits(H)];
	K_orb:= [#x : x in Orbits(K)];
	Sort(~H_orb); Sort(~K_orb);
	if H_orb ne K_orb then
	  return true, false;
	end if;
      end if;
  end if;

  //"solubility";
  H_solv:= IsSolvable(H);
  K_solv:= IsSolvable(K);
  if not H_solv eq K_solv then 
    return true, false; 
  end if;

  if H_solv then
    H_classes:= Classes(H); K_classes:= Classes(K);
    if not #H_classes eq #K_classes then 
      return true, false; 
    end if;

    classlength:= #H_classes;
    for i in [1..classlength] do
      if not exists(t){ cl : cl in K_classes | H_classes[i][2] 
           eq cl[2] and MinimalPolynomial(H_classes[i][3]) 
           eq MinimalPolynomial(cl[3])} then 
        return true, false; 
      end if;
      Exclude(~K_classes, t);
    end for;
    if #H le 1000 and not IsIsomorphic(PCGroup(H), PCGroup(K)) then
	return true, false;
    end if;
  end if;

  return false, _;
end function;

/****************************************************************/

function MightBeEqual(val1, val2)
  if not ((val1 cmpeq val2) or (val1 cmpeq
       "unknown") or (val2 cmpeq "unknown")) then
    return false;
  end if;
  return true;
end function;


/****************************************************************/
//
//Print > 1: lots and lots of printing.
//Print = 1: some printing.
//Print < 1: no printing.

intrinsic IsGLConjugate(H::GrpMat, K::GrpMat: Print:=0)
-> BoolElt, GrpMatElt
{If H and K are conjugate in the general linear group then returns true and
a matrix conjugating H to K. Otherwise returns false. If Print > 1 then 
lots of information will be printed at run-time. If Print = 1 then 
some information will be printed. If Print < 1 then no information 
will be printed.}

  n:= Degree(H);
  require n eq Degree(K): "Groups must have same dimension";
  q:= #BaseRing(H); 
  require q eq #BaseRing(K): "Groups must be over same field";

  /*
   * first we use IsConjTest to try to show that H and K 
   * are not conjugate.
   */
  if Print gt 0 then "Trying to prove are not conjugate"; end if;
  a,b:= IsConjTest(H, K);
  if a then 
    if b then 
      return true, GL(n, q)!1; 
    else 
      return false, _; 
    end if; 
  end if;

  /* 
   * Now we work our way through the Aschbacher classes to try 
   * to show that H and K are conjugate.
   */
   
  if Print gt 0 then "Testing for irreducibility"; end if;
  boolean, conj:= IsGLConjugateReducible(H, K:Print:= Print-1);
  if boolean cmpeq true then return boolean, conj; 
  elif boolean cmpeq false then return false, _; end if;
  
  H_semilin:= IsSemiLinear(H); K_semilin:= IsSemiLinear(K);
  if not MightBeEqual(H_semilin, K_semilin) then
    return false, _;
  end if;
  if (H_semilin cmpeq true) and (K_semilin cmpeq true) then
    if Print gt 0 then
      "Testing conjugacy as semilinear groups";
    end if;
    boolean, conj:= IsGLConjugateSemilinear(H, K:Print:= Print-1);
    if boolean cmpeq true then return true, conj; 
    elif boolean cmpeq false then return false, _; end if;

    //if the groups are not absolutely irreducible then we
    //cannot run other AS recognition code, so we try ConjSemilin
    //a second time before we give up.
    if not IsAbsolutelyIrreducible(H) then
      if Print gt 0 then "Trying semilinear conjugacy again"; end if;
      boolean, conj:= IsGLConjugateSemilinear(H, K:Print:= Print-1);
      if boolean cmpeq true then return true, conj; 
      elif boolean cmpeq false then return false, _; end if;
    end if;
  end if;

  //we assume absolute irreducibility before we run the other 
  //AS-recognition functions.
  if IsAbsolutelyIrreducible(H) then 
        
    if n gt 2 then
      if Print gt 0 then 
        "Trying IsGLConjugateBigClassical";
      end if;
      boolean, conj:= IsGLConjugateBigClassical(H, K: Print:= Print-1);
      if boolean cmpeq true then return true,conj;
      elif boolean cmpeq false then return false, _;
      end if;
    end if; 

    H_imprim:= IsPrimitive(H); K_imprim:= IsPrimitive(K);
    if (n gt 2) and (not MightBeEqual(H_imprim, K_imprim)) then
      return false, _;
    end if;
    if (H_imprim cmpeq false) and (K_imprim cmpeq false) then
      if Print gt 0 then
        "Testing conjugacy as imprimitive groups";
      end if;
      boolean, conj:= IsGLConjugateImprimitive(H, K: Print:= Print-1);
      if boolean cmpeq true then return true, conj; end if;
    end if;

    H_te:= IsTensor(H); K_te:= IsTensor(K);
    if not MightBeEqual(H_te, K_te) then
      return false, _;
    end if;
    if (H_te cmpeq true) and (K_te cmpeq true) then
      if Print gt 0 then
        "Testing conjugacy as tensor product groups";
      end if;
      boolean, conj:= IsGLConjugateTensor(H, K:Print:= Print-1);
      if boolean cmpeq true then return true, conj;
      elif boolean cmpeq false then return false, _; end if;
    end if;

      
    //Extraspecial normaliser functions all rather buggy when n = 2, not safe. 
    if n gt 2 then
      H_extra:= IsExtraSpecialNormaliser(H);
      K_extra:= IsExtraSpecialNormaliser(K);
      if not MightBeEqual(H_extra, K_extra) then
        return false, _;
      end if;
      if (H_extra cmpeq true) and (K_extra cmpeq true) then
        if Print gt 0 then
          "Testing conjugacy as extraspecial normaliser groups";
        end if;
        boolean, conj:= IsGLConjugateExtraspecial(H, K: Print:= Print-1);
        if boolean cmpeq true then return true, conj; end if;
      end if;
    end if;

    if n gt 2 then
      if Print gt 0 then
        "Testing conjugacy as groups preserving forms";
      end if;
      boolean, conj:= IsGLConjugateClassical(H, K: Print:= Print-1);
      if boolean cmpeq true then return true, conj;
      elif boolean cmpeq false then return false, _; end if;
    end if;

    H_sub:= IsOverSmallerField(H : Scalars:= true);
    K_sub:= IsOverSmallerField(K : Scalars:= true);
    if not MightBeEqual(H_sub, K_sub) then
      return false, _;
    end if;
    if (H_sub cmpeq true) and (K_sub cmpeq true) then
      if Print gt 0 then
        "Testing conjugacy as subfield groups"; 
      end if;
      boolean, conj:= IsGLConjugateSubfield(H, K: Print:=Print-1);
      if boolean cmpeq true then return true, conj;
      elif boolean cmpeq false then return false, _; end if;
    end if;

    if n gt 4 then //waste of time if n = 4.
      H_ti:= IsTensorInduced(H);
      K_ti:= IsTensorInduced(K);
      if not MightBeEqual(H_ti, K_ti) then
        return false, _;
      end if;
      if (H_ti cmpeq true) and (K_ti cmpeq true) then
        if Print gt 0 then
          "Testing conjugacy as tensor induced groups";
        end if;
        boolean, conj:= IsGLConjugateTensorInduced(H, K:Print:= Print-1);
        if boolean cmpeq true then return true, conj; 
        elif boolean cmpeq false then return false, _; end if;
      end if;
    end if;
  end if;

  /* 
   * Now we use a beefed-up version of the normal algorithm for 
   * conjugacy, and possibly recurse on a characteristic subgroup.
   */
  if Print gt 0 then "Using characteristic subgroups"; end if;
  HR:= Radical(H);
  KR:= Radical(K);
  phi, glp:= OrbitAction(GL(n, q), RSpace(GL(n, q)).1);
  if #HR ne #KR then return false, _; end if;
  if #HR gt 1 and #HR lt #H then
    if Print gt 0 then "Working with soluble radical"; end if;
    a,b:= $$(HR, KR:Print:=Print);
    if not a then return false, _; end if;
    H:= H^b;
    if H eq K then return true, b; end if;
    c,d:= IsConjugate(Normalizer(glp, KR@phi), H@phi, K@phi);
    if c then return true, b*(d@@phi); else return false, _; end if;

  elif #HR eq 1 then
     if Print gt 0 then "Working with socle"; end if;
     HR:= Socle(H@phi)@@phi;
     KR:= Socle(K@phi)@@phi;
     if H ne HR then
       a,b:= $$(HR, KR: Print:=Print);
       if not a then return false, _; end if;
       H:= H^b;
       if H eq K then return true, b; end if;
       c,d:= IsConjugate(Normalizer(glp, KR@phi), H@phi, K@phi);
       if c then return true, b*(d@@phi); else return false, _; end if;

     else
       c, d:= IsConjugate(glp, H@phi, K@phi);
       if c then return true, d@@phi; else return false, _; end if;
     end if;

  else
    if Print gt 0 then "Working with derived series"; end if;
    dsH:= DerivedSeries(H);
    dsK:= DerivedSeries(K);
    len:= #dsH;
    if len ne #dsK then return false, _; end if;
    if exists{i: i in [1..len]|#dsH[i] ne #dsK[i]} then
      return false, _;
    end if;

    if len le 2 then
      c, d:= IsConjugate(glp, H@phi, K@phi);
      if c then return c, d@@phi; else return false, _; end if;
    else
      HR:= dsH[len -1];
      KR:= dsK[len -1];
      a,b:= IsConjugate(glp, HR@phi, KR@phi);
      if not a then return false, _; end if;
      H:= H^(b@@phi);
      if H eq K then return true, b@@phi; end if;
      c,d:= IsConjugate(Normalizer(glp, KR@phi), H@phi, K@phi);
      if c then return true, (b*d)@@phi; else return false, _; end if;
    end if;
  end if;
end intrinsic;
