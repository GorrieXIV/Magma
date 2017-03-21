freeze;

import "psl2p.m" :L2pIdentify;
import "psl2p2.m":L2p2Identify;
import "psl2p3.m":L2p3Identify;
import "psl2q.m" :L2qIdentify;
import "psl3p.m" :L3pIdentify;
import "psl3p2.m":L3p2Identify;
import "psl3q.m" :L3qIdentify;
import "psl4p.m" :L4pIdentify;
import "psl4q.m" :L4qIdentify;
import "psl5p.m" :L5pIdentify;
import "psl5q.m" :L5qIdentify;
import "psl6p.m" :L6pIdentify;
import "psl6q.m" :L6qIdentify;
import "psl7p.m" :L7pIdentify;
import "psl7q.m" :L7qIdentify;
import "psl63.m": L63Identify;
import "psl73.m": L73Identify;
import "psl8+2.m":L7_2Identify, L8_2Identify, L9_2Identify, L10_2Identify,
                  L11_2Identify, L12_2Identify, L13_2Identify, L14_2Identify;
import "oplus8_2.m": OPlus8_2Identify;
import "oplus8_3.m": OPlus8_3Identify;
import "oplus8_4.m": OPlus8_4Identify;
import "ominus8_2.m": OMinus8_2Identify;
import "ominus8_3.m" :OMinus8_3Identify;
import "ominus8_4.m" :OMinus8_4Identify;
import "psu3p.m" :U3pIdentify;
import "psu3q.m" :U3qIdentify;
import "psu4q.m" :U4qIdentify;
import "psp4p.m" :PSp4pIdentify;
import "psp4q.m" :PSp4qIdentify;
import "co3.m"   :CO3Identify;
import "co2.m"   :CO2Identify;
import "he.m"    :HeIdentify;
import "g24.m"    :G24Identify;
import "g25.m"    :G25Identify;
import "s64.m"    :S64Identify;
import "s82.m"    :S82Identify;
import "s102.m"   :S102Identify;
import "s122.m"   :S122Identify;
//import "u39.m"    :U39Identify; no longer needed
import "u53_72_82.m"   :U53Identify;
import "u62.m"   :U62Identify;
import "u53_72_82.m"   :U72Identify;
import "u53_72_82.m"   :U82Identify;
import "s63o73.m"    :S63O73Identify;
import "s65o75.m"    :S65O75Identify;
import "s83o93.m"    :S83O93Identify;
import "tw3d42.m"    :tw3D42Identify;
import "tits.m"    :TitsIdentify;
import "om102.m"    :Om102Identify;
import "op102.m"    :Op102Identify;
import "opm10_3.m"  :OPlus10_3Identify, OMinus10_3Identify;
import "opm12_2.m"  :OPlus12_2Identify, OMinus12_2Identify;
import "fi22.m"    :Fi22Identify;
import "suz.m"    :SuzIdentify;
import "ru.m"    :RuIdentify;
import "ON.m"    :ONIdentify;
import "oddfns2.m" :IncorporateCentralisingGenerators;

/*
 *   Written by Derek Holt - updated Dec 2002 
 */
/* This file contains the procedures for identifying an almost
 * simple group G of small order as a subgroup of Aut(T) for some simple T,
 * reading off its maximal subgroups from stored data, and
 * finding an injection from G to a permutation representation of Aut(T).
 *
 * Note, two of the functions,
 * OuterAutsRGQH, CalculateIsomRGQH, 
 * are the same as those in autgps/radquot.m
 *
 * The function SGDBAccess(resorder,order,ASG) locates a record for an
 * almost simple group ASG that has order 'order', and soluble residual of
 * order 'resorder', provided that it has one stored.
 *
 * When there is more than one subgroup * stored for that order -
 * for example, for order=720, there are three -
 * the sum of the class orders of the ASG is used to identify th
 * isomorphism type.
 *
 * Each simple group T  in the list is defined by two generators,  x  and  y
 * with orders ox and oy, say.
 * (x and y  are actually defined as generators of a free group of rank 2.)
 * x is always chosen so that there is a unique Aut(T)-class of elements
 * of order ox in T.
 *
 * The list returned for G is a record with the following fields:
 * name - a string, describing the group G.
 * resname - a string, describing the simple soluble residual T of the group.
 * geninfo - a list of length two, the elements are 3-tuples
 *           giving order of element (i.e. ox or oy), length of
 *        class of element a,y. Ignore third component.
 * conjelts - in cases where G is not normal in Aut(T), we may have to
 *        replace the original generators x,y of T by conjugates under
 *        autmorphisms of T that do not normalise G.
 *        conjelts is a list of the (nontrivial) conjugating automorphisms.
 * NOTE - first example of this is PSL(3,4) order 20160
 * rels - a list of words in  x  and  y which, taken together with
 *        x^ox and y^oy constitute a set of defining relators for T.
 * outimages - the images (as words in gens of T) of the generators of T
 *        under generators of the outer automorphism group of T.
 * subgens - words in the outer automorphisms generators of T that
 *           together with T generate G.
 * maxsubints - the intersections of the maximal subgroups of G that do not
 *           contain T with T.
 * permrep - a pemrutation representation of Aut(T), where the generators
 *           are x,y followed by generating automorphisms.
 */

OuterAutsRGQH := function(RGQ,oims,proj,printlevel)
/* Calculate outer automorphisms as automorphisms of RGQ
 * The list is twice as long as #oims and the corresponding outer
 * automorphisms are followed by the list of their inverses.
 */
  local rgqauts, iso, isoi;

  if printlevel gt 2 then
    print "    +Calculating outer automorphisms of simple group.";
  end if;
  rgqauts := [];
  if #oims ne 0 then
    for oi in oims do
      iso := hom< RGQ->RGQ | [im@proj : im in oi] >;
      if printlevel gt 2 then
         print "      +Defined an outer automorphism.";
      end if;
      Append(~rgqauts,iso);
    end for;
    /* and append their inverses */
    for oi in oims do
      iso := hom< RGQ->RGQ | [im@proj : im in oi] >;
      isoi := hom< RGQ->RGQ | [x@@iso : x in [RGQ.i:i in [1..#oi]] ]>;
      Append(~rgqauts,isoi);
    end for;
  end if;
  if printlevel gt 2 then
    print "    +Found outer automorphisms.";
  end if;
  return rgqauts;
end function;

CalculateIsomRGQH:=function(RGQ,w,rgqauts)
  /* w should be a nontrivial word in the outer automorphism generators,
   * or a corresponding list of integers.
   * Calculate and return the corresponding isomorphism of RGQ
   */
  local sw, aut, noi;
  noi := #rgqauts/2;
  sw := ElementToSequence(w);
  /* Inverses in auts come at the end, so change numbering in sw */
  for i in [1..#sw] do
    if sw[i] lt 0 then
      sw[i] := noi-sw[i];
    end if;
  end for;
  aut := rgqauts[sw[1]];
  for i in [2..#sw] do
    aut := aut*rgqauts[sw[i]];
  end for;
  return aut;
end function;


function SGDBAccess(resorder, order, ASG)
 
    local D, n, f, invar, rec;
    D := AlmostSimpleGroupDatabase();
    n, f := NumberOfGroups(D, resorder, order);
    if n eq 0 then
      return false, _;
    elif n eq 1 then
      return true, GroupData(D,f); 
    else
      invar := &+[cl[1] : cl in Classes(ASG)];
      fl, rec := ExistsGroupData(D, resorder, order, invar);
      if fl eq false then return false, _; end if; //should not happen
      return true, rec;
    end if;

end function;

PermRepAlmostSimpleGroupH := function(G,K)
/* q eq 4 or Attempt to find a reasonable degree perm. rep. of the almost simple
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

forward IdentifySymEvenDeg, IdentifySymOddDeg, IdentifyAltSymNatural,
        IdentifyAltEvenDeg, IdentifyAltOddDeg, ActionOnOrbitsU;
IdentifyAlmostSimpleGroupH := function(RGQ,GQ,printlevel:max:=true)
/* GQ should be the normaliser of the simple factor RGQ in a TF-group.
 * A monomorphism from GQ to a standard permutation representation of
 * Aut(T) (where T is a simple group in the database) is returned;
 * together with Aut(T) itself;  if max is true, the images of the
 * intersection of the maximal subgroups of GQ that do not contain T in
 * Aut(T), returned as lists of generators; and optionally a presentation
 * F of T together with the associated map F->T.
 * The image of G is uniquely determined by the isomorphism type of G.
 */
local S, invar, orgq, ogq, storedgp, geninfo,
      ox, oy, rels, oims, sg, pr, msi, H, fl, 
      proj, x, y, foundx, el, imx, imy, origimx, origimy,  conjelts, conjeltct,
      foundhom,  foundgqhom, isinner, phi, ok, C, ASG, tau, ASG2, tau2,
      RF, rgqauts, aut, GQgens, newGQ, prgens, inj, msiims, w, ws, copysg,
      p, q, sporadic, classical, isso, type, fac, F, wm, d, l; 

  S := recformat<generators: SeqEnum, normgen: GrpPermElt,
                 presentation: GrpFP, order, length: Integers() >;
  orgq := #RGQ;
  C := Centraliser(GQ,RGQ);
  ogq := Index(GQ,C);
  if #C eq 1 then
    ASG := GQ;
    tau := IdentityHomomorphism(GQ);
  else
    tau, ASG := ActionOnOrbitsU(GQ, C);
    if #ASG ne ogq then //not faithful
      tau, ASG := PermRepAlmostSimpleGroupH(GQ,C);
    end if;
  end if;

  /* At this point ogq is the order of an almost simple group ASG,
   * with simple normal subgroup RGQ of order orgq. These groups need to be
   * identified.
   * This is done either by looking up the groups in the database of
   * almost simple groups, or by identifying the group as a member of
   * a generic class.
   * When introducing new generic classes, it is necessary to observe
   * only the following rules.
   * We must return three values: phi, A, subims, + two optionals, F, wm.
   * A must be a permutation group, containing a normal subgroup S, where
   * S is isomorphic to RGQ, and A is isomorphic to the full automorphism
   * group of S; the generators of A must include generators of S.
   * phi must be a monmomorphism from ASG to A, mapping RGQ isomorphically
   * to S.
   * F is a finite presentation of S with word map wm.
   */

  /* deal with large alternating and symmetric groups separately */
  
  fl, n := IsFactorial(2*orgq);
  isso, type := IsSimpleOrder(orgq);
  if not isso then error "Bad simple group order"; end if;
  if type[1] eq 17 then  // RGQ = Alt(n) case
    n := type[2];
    if 9 le n and n le 999 then
      if printlevel gt 1 then print "In Alt case"; end if;
      orbreps := OrbitRepresentatives(ASG);
      if ogq gt orgq then //Sym(n)
        if printlevel gt 0 then
          print
  "The almost simple group is Sym(",n,"), with soluble residual Alt(",n,").";
        end if;

	if exists(x){t[2]: t in orbreps | t[1] eq n} then
	  phi, pr, msi :=
                IdentifyAltSymNatural(ASG,n,true,x,printlevel:max := max);
        elif n mod 2 eq 0 then
          phi, pr, msi := IdentifySymEvenDeg(ASG,n,printlevel:max:=max);
        else
          phi, pr, msi := IdentifySymOddDeg(ASG,n,printlevel:max:=max);
        end if;
        msiims := [];
        if max then for K in msi do
          H := K meet Alt(n); 
          x:=Random(K);
          while x in H do x:=Random(K); end while;
          Append(~msiims,rec<S| generators:=[H.i : i in [1..Ngens(H)]],
                         order:=#K div 2, normgen:=x>);
        end for; end if;
      else //Alt(n)
        if printlevel gt 0 then
          print "The almost simple group is Alt(",n,").";
        end if;
	if exists(x){t[2]: t in orbreps | t[1] eq n} then
	  phi, pr, msi :=
               IdentifyAltSymNatural(ASG,n,false,x,printlevel:max := max);
        elif IsEven(n) then
          phi, pr, msi := IdentifyAltEvenDeg(ASG,n,printlevel:max:=max);
        else
          phi, pr, msi := IdentifyAltOddDeg(ASG,n,printlevel:max:=max);
        end if;
        if max then
          msiims := [ rec<S|generators:=[G.i : i in [1..Ngens(G)]],
                                         order:=#G, normgen:=Id(G)> :
                          G in msi];
        else msiims := [];
        end if;
      end if;
      phi := tau*phi;
      // might deal with presentations later!
      return phi, pr, msiims, _, _;
    end if;
  end if;

  /* deal with some large sporadic/individual groups */
  sporadic := false;
  if orgq eq 17971200 then // Tits' group
    phi, pr, msi, F, wm :=
         TitsIdentify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 211341312 then //3D4(2)
    phi, pr, msi, F, wm :=
	 tw3D42Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 251596800 then //G24
    phi, pr, msi, F, wm :=
	 G24Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 5859000000 then //G25
    phi, pr, msi, F, wm :=
	 G25Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 4030387200 then //He
    phi, pr, msi, F, wm :=
         HeIdentify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
/*
  elif orgq eq 42573600 then // U39 - now done by general U(3,q)
    phi, pr, msi, F, wm :=
         U39Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
*/
  elif orgq eq 258190571520 then // U53
    phi, pr, msi, F, wm :=
         U53Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 9196830720 then //U62
    phi, pr, msi, F, wm :=
         U62Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 227787103272960 then //U72
    phi, pr, msi, F, wm :=
         U72Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 7434971050829414400 then //U82
    phi, pr, msi, F, wm :=
         U82Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 4585351680 then //S63 or O73
    phi, pr, msi, F, wm :=
         S63O73Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 228501000000000 then //S65 or O75
    phi, pr, msi, F, wm :=
         S65O75Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 65784756654489600 then //S83 or O93
    phi, pr, msi, F, wm :=
         S83O93Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 4106059776000 then //S64
    phi, pr, msi, F, wm :=
         S64Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 47377612800 then //S82
    phi, pr, msi, F, wm :=
         S82Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 24815256521932800 then //S102
    phi, pr, msi, F, wm :=
         S102Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 208114637736580743168000 then //S122
    phi, pr, msi, F, wm :=
         S122Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 495766656000 then //CO3
    phi, pr, msi, F, wm :=
         CO3Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 23499295948800 then //O+(10,2)
    phi, pr, msi, F, wm :=
         Op102Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 25015379558400 then //O-(10,2)
    phi, pr, msi, F, wm :=
         Om102Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 1289512799941305139200 then //O+(10,3)
    phi, pr, msi, F, wm :=
         OPlus10_3Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 650084965259666227200 then //O-(10,3)
    phi, pr, msi, F, wm :=
         OMinus10_3Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 50027557148216524800 then //O+(12,2)
    phi, pr, msi, F, wm :=
         OPlus12_2Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 51615733565620224000 then //O-(12,2)
    phi, pr, msi, F, wm :=
         OMinus12_2Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 42305421312000 then //CO2
    phi, pr, msi, F, wm :=
         CO2Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 64561751654400 then //Fi22
    phi, pr, msi, F, wm :=
         Fi22Identify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 448345497600 then //Suz
    phi, pr, msi, F, wm :=
         SuzIdentify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 145926144000 then //Ru
    phi, pr, msi, F, wm :=
         RuIdentify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  elif orgq eq 460815505920 then //ONan
    phi, pr, msi, F, wm :=
         ONIdentify(ASG: max:=max, Print:=printlevel);
    sporadic := true;
  end if;

  /* deal with some classicals */
  q := type[3];
  if q gt 0 then
    fac := Factorisation(q);
    p := fac[1][1];
  end if;
  classical := false;
  if type[1] eq 1 and type[2] eq 1 then //RGQ = PSL(2,q);
    if fac[1][2] eq 1 and p gt 11 then //PSL(2,p)
      if printlevel gt 0 then print "In PSL(2,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L2pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] eq 2 and p gt 3 then //PSL(2,p^2)
      if printlevel gt 0 then print "In PSL(2,p^2) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L2p2Identify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] eq 3 and p gt 2 then //PSL(2,p^3)
      if printlevel gt 0 then print "In PSL(2,p^3) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L2p3Identify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] gt 3  then //PSL(2,p^e), e>3
      if printlevel gt 0 then print "In general PSL(2,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L2qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 1 and type[2] eq 2 then //RGQ = PSL(3,q);
    if (fac[1][2] eq 1 and p gt 3) or q eq 9 then //PSL(3,p)
      if printlevel gt 0 then print "In PSL(3,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L3pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] eq 2 and p gt 2 then //PSL(3,p^2)
      if printlevel gt 0 then print "In PSL(3,p^2) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L3p2Identify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] gt 2  then //PSL(3,p^e), e>3
      if printlevel gt 0 then print "In general PSL(3,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L3qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 1 and type[2] eq 3 then //RGQ = PSL(4,q);
    if fac[1][2] eq 1 and p gt 3 then //PSL(4,p)
      if printlevel gt 0 then print "In PSL(4,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L4pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] gt 1 then //PSL(4,p^e), e > 1
      if printlevel gt 0 then print "In PSL(4,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L4qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 1 and type[2] eq 4 then //RGQ = PSL(5,q);
    if fac[1][2] eq 1 and p gt 2 then //PSL(5,p)
      if printlevel gt 0 then print "In PSL(5,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L5pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif fac[1][2] gt 1 then
      if printlevel gt 0 then print "In PSL(5,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L5qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 1 and type[2] eq 5 and q gt 2 then //RGQ = PSL(6,q);
    // note that PSL(6,2) is in the database
    if fac[1][2] eq 1 and p gt 3 then //PSL(6,p)
      if printlevel gt 0 then print "In PSL(6,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L6pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif q eq 3 then //RGQ = PSL(6,3);
      if printlevel gt 0 then print "In PSL(6,3) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L63Identify(ASG: max:=max, Print:=printlevel);
    elif fac[1][2] gt 1 then
      if printlevel gt 0 then print "In PSL(6,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L6qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 1 and type[2] eq 6 then //RGQ = PSL(7,q);
    if fac[1][2] eq 1 and p gt 3 then //PSL(7,p)
      if printlevel gt 0 then print "In PSL(7,p) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L7pIdentify(ASG, q: max:=max, Print:=printlevel);
    elif q eq 2 then //RGQ = PSL(7,2);
      if printlevel gt 0 then print "In PSL(7,3) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L7_2Identify(ASG: max:=max, Print:=printlevel);
    elif q eq 3 then //RGQ = PSL(7,3);
      if printlevel gt 0 then print "In PSL(7,3) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L73Identify(ASG: max:=max, Print:=printlevel);
    elif fac[1][2] gt 1 then
      if printlevel gt 0 then print "In PSL(7,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := L7qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif q eq 2 and type[1] eq 1 and type[2] ge 7  and type[2] le 13 then
               //RGQ = PSL(d,2) 8 <= d <= 14;
    if printlevel gt 0 then print "In PSL(",type[2]+1,",2) case"; end if;
    classical := true;
    if type[2]+1 eq 8 then phi, pr, msi, F, wm :=
                  L8_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 9 then phi, pr, msi, F, wm :=
                  L9_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 10 then phi, pr, msi, F, wm :=
                  L10_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 11 then phi, pr, msi, F, wm :=
                  L11_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 12 then phi, pr, msi, F, wm :=
                  L12_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 13 then phi, pr, msi, F, wm :=
                  L13_2Identify(ASG: max:=max, Print:=printlevel);   
    elif type[2]+1 eq 14 then phi, pr, msi, F, wm :=
                  L14_2Identify(ASG: max:=max, Print:=printlevel);   
    end if;
  elif type[1] in {2,3} and type[2] eq 2 then //RGQ = PSp(4,q);
    if fac[1][2] eq 1 then //PSp(4,p)
      if p gt 3 then
        if printlevel gt 0 then print "In PSp(4,p) case"; end if;
        classical := true;
        phi, pr, msi, F, wm
             := PSp4pIdentify(ASG, q: max:=max, Print:=printlevel);
      end if;
    else //PSp(4,q)
      if printlevel gt 0 then print "In PSp(4,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm:= PSp4qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 10 and type[2] eq 2 then //RGQ = PSU(3,q);
    if fac[1][2] eq 1 then //PSU(3,p)
      if p gt 5 then
        if printlevel gt 0 then print "In PSU(3,p) case"; end if;
        classical := true;
        phi, pr, msi, F, wm :=U3pIdentify(ASG, q: max:=max, Print:=printlevel);
      end if;
    else
      if printlevel gt 0 then print "In PSU(3,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := U3qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif type[1] eq 10 and type[2] eq 3 then //RGQ = PSU(4,q);
    if q gt 2 then
      if printlevel gt 0 then print "In PSU(4,q) case"; end if;
      classical := true;
      phi, pr, msi, F, wm := U4qIdentify(ASG, q: max:=max, Print:=printlevel);
    end if;
  elif q eq 2 and type[1] eq 4 and type[2] eq 4 then //RGQ = Omega^+(8,2)
    if printlevel gt 0 then print "In Omega^+(8,2) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OPlus8_2Identify(ASG: max:=max, Print:=printlevel);
  elif q eq 3 and type[1] eq 4 and type[2] eq 4 then //RGQ = Omega^+(8,3)
    if printlevel gt 0 then print "In Omega^+(8,3) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OPlus8_3Identify(ASG: max:=max, Print:=printlevel);
  elif q eq 4 and type[1] eq 4 and type[2] eq 4 then //RGQ = Omega^+(8,4)
    if printlevel gt 0 then print "In Omega^+(8,4) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OPlus8_4Identify(ASG: max:=max, Print:=printlevel);
  elif q eq 2 and type[1] eq 12 and type[2] eq 4 then //RGQ = Omega^-(8,2)
    if printlevel gt 0 then print "In Omega^-(8,2) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OMinus8_2Identify(ASG: max:=max, Print:=printlevel);
  elif q eq 3 and type[1] eq 12 and type[2] eq 4 then //RGQ = Omega^-(8,3)
    if printlevel gt 0 then print "In Omega^-(8,3) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OMinus8_3Identify(ASG: max:=max, Print:=printlevel);
  elif q eq 4 and type[1] eq 12 and type[2] eq 4 then //RGQ = Omega^-(8,4)
    if printlevel gt 0 then print "In Omega^-(8,4) case"; end if;
    classical := true;
    phi, pr, msi, F, wm :=
         OMinus8_4Identify(ASG: max:=max, Print:=printlevel);
  end if;

  if sporadic or classical then
    if max then
       msiims := [ rec<S|generators:=[G.i : i in [1..Ngens(G)]], order:=#G> :
                        G in msi];
    else msiims := [];
    end if;
    phi := tau*phi;
    return phi, pr, msiims, F, wm;
  end if;

  if orgq gt 20158709760 then
    foundx := false;
  else
    foundx, storedgp := SGDBAccess(orgq,ogq,ASG);
  end if;

  if printlevel gt 0 then print "In general case"; end if;

  if not foundx then
    error "Sorry, the top factor of order",ogq,"is not currently stored";
  end if;

  if printlevel gt 0 then
    if ogq gt orgq then
      print "The almost simple group is",storedgp`name,"with soluble residual",
            storedgp`resname;
    else
      print "The almost simple group is",storedgp`name;
    end if;
  end if;
  if printlevel gt 1 then
    print "  +Mapping group from database onto almost simple group.";
  end if;

  // print storedgp;
  geninfo:=storedgp`geninfo; // print geninfo;
  ox:=geninfo[1][1]; 
  oy:=geninfo[2][1];
  rels:=storedgp`rels; // print rels;
  conjelts:=storedgp`conjelts; // print conjelts;
  oims := storedgp`outimages;//  print oims;
  sg := storedgp`subgens; // print sg;
  pr := storedgp`permrep; // print pr;
  msi := storedgp`maxsubints; // print msi;

  RF<x, y>, proj :=  quo< Parent(rels[1]) | $.1^ox, $.2^oy, rels >;
 
  foundx := false;
  while not foundx do
    el := Random(RGQ);
    el_ord := Order(el);
    if el_ord mod ox eq 0 then
	imx := el ^ (el_ord div ox);
// 	if #Class(RGQ, imx) eq geninfo[1][2] then
	if Index(RGQ, Centralizer(RGQ, imx)) eq geninfo[1][2] then
	    foundx := true;
	end if;
    end if;
  end while;
 
  foundhom:=false;
  while not foundhom do
    el := Random(RGQ);
    el_ord := Order(el);
    if el_ord mod oy ne 0 then
        continue;
    end if;
    imy := el ^ (el_ord div oy);
    phi := hom<RF->RGQ | [imx,imy] >;
    ok := true;
    for w in rels do
      if not phi(w) eq Id(RGQ) then
        ok := false;
        break;
      end if;
    end for;
    if ok then
      foundhom := true;
    end if;
  end while;
  if printlevel gt 1 then
    print "  +Found map onto soluble residual of almost simple group";
  end if;
  if #conjelts gt 0 then
    origimx:=imx; origimy:=imy;
  end if;
  
  foundgqhom:=false;
  isinner:=true;
  conjeltct:=0;
  while not foundgqhom do
    if conjeltct gt 0 then
      if printlevel gt 2 then
        print "    +Trying conjugates of generators";
      end if;
      /* We have to replace our elements imx and imy by conjugates
       * under the automorphism of RGQ defined by conjelts[conjeltct]
       */
      w := conjelts[conjeltct];
      aut := CalculateIsomRGQH(RGQ,w,rgqauts);
      imx:=origimx@aut; imy:=origimy@aut;
      phi := hom<RF->RGQ | [imx,imy] >;
    end if;
    RGQ := sub<RGQ|[imx,imy]>;
    GQgens := [ GQ | imx,imy];
    prgens := [pr.1,pr.2];
  /* Next locate specified automorphisms of RGQ in GQ */
    if #oims ne 0 then
      rgqauts :=
          OuterAutsRGQH(RGQ,oims,proj * hom<RF->RGQ|[imx,imy]>,printlevel);
    end if;
    for k in [1..#sg] do
      w := sg[k];
      aut := CalculateIsomRGQH(RGQ,w,rgqauts);
      /* find element of GQ inducing this aut */
      isinner, el:=IsInnerAutomorphism(GQ, RGQ, aut);
      if not isinner then
        if conjeltct eq #conjelts then
          error "Failed to find required inner aut of radical quotient";
        end if;
        conjeltct +:= 1;
        break;
      end if;
      Append(~GQgens,el);
      ws := ElementToSequence(w);
      el := Id(pr);
      for i in ws do
        if i gt 0 then
          el := el*pr.(i+2);
        else
          el := el*(pr.(-i+2))^-1;
        end if;
      end for;
      Append(~prgens,el);
    end for;
    if not isinner then
      continue;
    end if;
    foundgqhom:=true;
  end while; // while not foundgqhom...
  if printlevel gt 1 then
    print "  +Completed identification of almost simple group.";
  end if;
  GQnew := sub<GQ|GQgens>;
  // We may need to add some extra generators from C to get GQ
  // BEWARE - Bill Unger's change to avoid verification of GQnew
  if Type(GQ) eq GrpPerm then
      IncorporateCentralisingGenerators(GQ, ~GQnew, C, ~prgens);
  else
      while GQnew ne GQ do
	el:=Random(C);
	if not el in GQnew then
	  Append(~GQgens,el);
	  Append(~prgens,Id(pr));
	  GQnew := sub<GQ|GQgens>;
	  RandomSchreier(GQnew);
	end if;
      end while;
  end if;
  inj := hom<GQnew->pr | prgens>;
  msiims:=[];
  if max then for subgp in msi do
    copysg:=subgp;
    copysg`generators := [ gg@phi@inj : gg in subgp`generators];
    Append(~msiims,copysg);
  end for; end if;

  if orgq le 5000 then
    return inj, pr, msiims, RF, hom< RF->pr | [pr.1,pr.2] >;
  else
    H := sub<pr|[pr.1,pr.2]>;
    H`Order := orgq;
    F, wm := FPGroupStrong(H);
    return inj, pr, msiims, F, wm;
  end if;
end function;

/* In the following functions, G should be a permutation group known to be
 * isomorphic to  Sym(n) or Alt(n) for a given value of n > 8.
 * An explicit isomorphism G->S_n/A_n is returned plus the image S_n/A_n.
 * The free group of rank 2 + the the maximal subgroups of G 
 *  are also returned.
 * (The free group is ignored by calling functions and is there for backward
 *  compatibility.)
 * The main point is to find elements of G that map onto the standard
 * generators (1,2) and (1,2,3,4,...,n) of S_n, or to
 * (1,2,3), (1,2,3,...,n) or (2,3,..,n) of A_n.
 * The cases Sym(n), Alt(n), n even or odd are treated in four separate
 * functions.
 * The Bratus-Pak algorithm is used, with variations for n < 20.
 * (Note: Their description for Alt(n) is very incomplete!!)
 */
forward IntransitiveSubgroupsAltSym, ImprimitiveSubgroupsAltSym,
        PrimitiveSubgroupsAltSym; 
IdentifySymEvenDeg := function(G,n,printlevel:max:=true)
// case n even, G=Sym(n)
local seeking, g, g1, g2, f, t, x, l, P, st, sl, S, subs;

  //first seek Goldbach element.
  if printlevel gt 2 then
    print "    +Identifying Sym(n) even degree case";
  end if;
  if n le 8 then
    error "Use IdentifySymEvenDeg only for degree at least 10";
  end if;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=Factorisation(Order(g));
    if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    end if;
  end while;

  //next a transposition
  seeking:=true;
  while seeking do
    t:=Random(G);
    f:=Factorisation(Order(t));
    if #f eq 3 and f[1][1] eq 2 and f[1][2] eq 1 and
        f[2][2] eq 1 and f[3][2] eq 1 and f[2][1]+f[3][1]+2 eq n then
      t:=t^(f[2][1]*f[3][1]);
      seeking:=false;
    end if;
  end while;
  
  //get a conjugate commuting with neither g1 nor g2.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if (t,g1) ne Id(G) and (t,g2) ne Id(G) then
      seeking:=false;
    end if;
  end while;

  //finally an n-cycle
  l := g1*t*g2;

  P := sub<G|l,t>;
  if P ne G then
    error "Generation problem in IdentifySymEvenDeg";
  end if;

  S:=sub< Sym(n) | Alt(n), (1,2) >; // we want alternating generators first.
  sl:=S!([2..n] cat [1]);
  st:=S!(1,2);

  if printlevel gt 2 then
    print "    +Completed identification - getting maximal subgroups";
  end if;

  subs := max select IntransitiveSubgroupsAltSym(n,true) cat
          ImprimitiveSubgroupsAltSym(n,true) cat
          PrimitiveSubgroupsAltSym(n,true) else [];
  return  hom< P->S | sl, st >, S, subs;
end function;

IdentifySymOddDeg := function(G,n,printlevel:max:=true)
// case n odd, G=Sym(n)
local seeking, g, g1, g2, f, t, u, o, x, l, P, st, sl, S, subs;

  if printlevel gt 2 then
    print "    +Identifying Sym(n) odd degree case";
  end if;
  //first seek Goldbach element.
  if n le 8 then
    error "Use IdentifySymOddDeg only for degree at least 9";
  end if;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=Factorisation(Order(g));
    if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n-1 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    end if;
  end while;

  //next a transposition
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=Factorisation(o);
    
    if (n eq 9 and o eq 14) or (n eq 11 and o eq 18) or (n eq 13 and o eq 22)
     or (n eq 15 and o eq 26) or (n eq 17 and o eq 210) or
       (n eq 19 and o eq 34) or
       (o ge 21 and #f eq 4 and f[1][1] eq 2 and f[1][2] eq 1 and
        f[2][1] eq 3 and f[2][2] eq 1 and
        f[3][2] eq 1 and f[4][2] eq 1 and f[3][1]+f[4][1]+5 eq n) then
      seeking:=false;
      t := t^(o div 2);
    end if;
  end while;
  
  //get a conjugate commuting with neither g1 nor g2.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if (t,g1) ne Id(G) and (t,g2) ne Id(G) then
      seeking:=false;
    end if;
  end while;

  // get a conjugate of t commuting with g1 but not g2 and touching fixed point.
  seeking:=true;
  while seeking do
    x:=Random(G);
    u:=t^x;
    if (u,g1) eq Id(G) and (u,g2) ne Id(G) and (u,u^g2) ne Id(G)
      and (u,u^(g2^2)) ne Id(G) then
      seeking:=false;
    end if;
  end while;

  //finally an n-cycle
  l := g1*t*g2*u;

  P := sub<G|l,t>;
  if P ne G then
    error "Generation problem in IdentifySymOdd";
  end if;

  S:=sub< Sym(n) | Alt(n), (1,2) >; // we want alternating generators first.
  st:=S!(1,2);
  sl:=S!([2..n] cat [1]);

  if printlevel gt 2 then
    print "    +Completed identification - getting maximal subgroups";
  end if;

  subs := max select IntransitiveSubgroupsAltSym(n,true) cat
          ImprimitiveSubgroupsAltSym(n,true) cat
          PrimitiveSubgroupsAltSym(n,true) else [];
  return  hom< P->S | sl, st >, S, subs;
end function;

IdentifyAltOddDeg := function(G,n,printlevel:max:=true)
// case n odd, G=Alt(n)
local seeking, g, g1, g2, f, t, o, x, l, P, st, sl, S, subs;

  if printlevel gt 2 then
    print "    +Identifying Alt(n) odd degree case";
  end if;
  //first seek Goldbach element.
  if n le 8 then
    error "Use IdentifyAltOddDeg only for degree at least 9";
  end if;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=Factorisation(Order(g));
    if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n-1 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    end if;
  end while;

  //next a 3-cycle
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=Factorisation(o);
    
    if (n eq 9 and o eq 15) or (n eq 11 and o eq 21) or (n eq 13 and o eq 24)
     or (n eq 15 and o eq 105) or (n eq 17 and o eq 39) or
       (o ge 19 and #f eq 3 and f[1][1] eq 3 and f[1][2] eq 1 and
        f[2][2] eq 1 and f[3][2] eq 1 and f[2][1]+f[3][1]+3 eq n) then
      seeking:=false;
      t := t^(o div 3);
    end if;
  end while;
 
  //get a conjugate commuting with neither g1 nor g2
  //and touching the fixed point.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if (t,g1) ne Id(G) and (t,g2) ne Id(G) and
       (t^g1,t^g2) ne Id(G) and (t^g1,t^(g2^2)) ne Id(G) and
       (t^(g1^2),t^g2) ne Id(G) and Order(t*t^g1) eq 2 then
 // The final condition rules out Order(g1)=3 and t touches g1 twice.
      seeking:=false;
    end if;
  end while;

  //finally an n-cycle - we have to find out whether we want g1*t*g2 or g2*t*g1
  l := g1*t*g2;
  if Order(t*t^l) ne 2 then
    l := g2*t*g1;
  end if;

  P := sub<G|l,t>;
  if P ne G then
    error "Generation problem in IdentifyAltOdd";
  end if;

  S:=sub< Sym(n) | Alt(n), (1,2) >; // we want alternating generators first.
  sl:=S!([2..n] cat [1]);
  st:=S!(1,2,3);

  if printlevel gt 2 then
    print "    +Completed identification - getting maximal subgroups";
  end if;

  subs := max select IntransitiveSubgroupsAltSym(n,false) cat
          ImprimitiveSubgroupsAltSym(n,false) cat
          PrimitiveSubgroupsAltSym(n,false) else [];
  return  hom< P->S | sl, st >, S, subs;
end function;

IdentifyAltEvenDeg := function(G,n,printlevel:max:=true)
// case n odd, G=Alt(n)
local seeking, g, g1, g2, f, t, o, x, l, P, st, sl, S, subs;

  if printlevel gt 2 then
    print "    +Identifying Alt(n) even degree case";
  end if;
  //first seek Goldbach element fixing two points.
  if n le 8 then
    error "Use IdentifyAltEvenDeg only for degree at least 10";
  end if;
  seeking:=true;
  while seeking do
    g:=Random(G);
    f:=Factorisation(Order(g));
    if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n-2 then
      seeking:=false;
      g1:=g^f[2][1];
      g2:=g^f[1][1];
    end if;
  end while;

  //next a 3-cycle
  seeking:=true;
  while seeking do
    t:=Random(G);
    o:=Order(t);
    f:=Factorisation(o);
    if (n eq 10 and o eq 21) or (n eq 12 and o eq 21) or (n eq 14 and o eq 33)
     or (n eq 16 and o eq 39) or (n eq 18 and o eq 39) or
       (o ge 20 and #f eq 3 and f[1][1] eq 3 and f[1][2] eq 1 and
        f[2][2] eq 1 and f[3][2] eq 1 and f[2][1]+f[3][1]+4 eq n) then
      seeking:=false;
      t := t^(o div 3);
    end if;
  end while;
 
  //get a conjugate commuting with neither g1 nor g2
  //and touching one of the fixed points.
  seeking:=true;
  while seeking do
    x:=Random(G);
    t:=t^x;
    if (t,g1) ne Id(G) and (t,g2) ne Id(G) and
       (t^g1,t^g2) ne Id(G) and (t^g1,t^(g2^2)) ne Id(G) and
       (t^(g1^2),t^g2) ne Id(G) and Order(t*t^g1) eq 2 then
 // The final condition rules out Order(g1)=3 and t touches g1 twice.
      seeking:=false;
    end if;
  end while;

  //now an (n-1)-cycle - we have to find out whether we want g1*t*g2 or g2*t*g1
  l := g1*t*g2;
  if Order(t*t^l) ne 2 then
    l := g2*t*g1;
  end if;

  //now a conjugate of t commuting with t and fixing the other fixed point of g
  seeking:=true;
  while seeking do
    x:=Random(G);
    u:=t^x;
    if (u,g1) ne Id(G) and (u,g2) ne Id(G) and
       (u^g1,u^g2) ne Id(G) and (u^g1,u^(g2^2)) ne Id(G) and
       (u^(g1^2),u^g2) ne Id(G) and Order(u*u^g1) eq 2 and
       t ne u and t ne u^2 and (t,u) eq Id(G) then
      seeking:=false;
    end if;
  end while;

  //conjugate t until it does not commute with u
  while (t,u) eq Id(G) do t:=t^l; end while;

  //Now either t^u or t^(u^-1) is a suitable 3-cycle.
  t := Order(t^u*t^(u*l)) eq 3 select t^u else t^(u^-1);

  P := sub<G|l,t>;
  if P ne G then
    error "Generation problem in IdentifyAltOdd";
  end if;

  S:=sub< Sym(n) | Alt(n), (1,2) >; // we want alternating generators first.
  sl:=S!([1] cat [3..n] cat [2]);
  st:=S!(1,2,3);

  if printlevel gt 2 then
    print "    +Completed identification - getting maximal subgroups";
  end if;

  subs := max select IntransitiveSubgroupsAltSym(n,false) cat
          ImprimitiveSubgroupsAltSym(n,false) cat
          PrimitiveSubgroupsAltSym(n,false) else [];
  return  hom< P->S | sl, st >, S, subs;
end function;


IntransitiveSubgroupsAltSym := function(n,sym)
// return the intransitive maximal subgroups of Alt(n) or Sym(n)
local subs, A, P;
  subs:=[];
  A := Alt(n);
  for d in [1..(n-1) div 2] do
    X := Sym(d);
    dummy := #X;
    Y := Sym(n-d);
    dummy := #Y;
    P := DirectProduct(X,Y);
    if (sym) then
      Append(~subs,P);
    else
      Append(~subs,P meet A);
    end if;
  end for;

  return subs;
end function;

ImprimitiveSubgroupsAltSym := function(n,sym)
// return the imprimitive maximal subgroups of Alt(n) or Sym(n) intersected
// with Alt(n).  sym is true according to whether we have Sym(n) or Alt(n). 
local subs, A, P;
  subs:=[];
  A := Alt(n);
  for d in Divisors(n) do if d ne 1 and d ne n then
    if n eq 8 and d eq 2 and not sym then
      continue; // the only case of nonmaximality - lies in AGL(3,2)
    end if;
    X := Sym(d);
    dummy := #X;
    Y := Sym(n div d);
    dummy := #Y;
    P := WreathProduct(X,Y);
    if (sym) then
      Append(~subs,P);
    else
      Append(~subs,P meet A);
    end if;
  end if; end for;

  return subs;
end function;

PrimitiveSubgroupsAltSym := function(n,sym)
// return the primitive maximal subgroups of Alt(n) or Sym(n) intersected
// with Alt(n). sym is true according to whether we have Sym(n) or Alt(n). 

  local maxprim, subs, x, A, P;

  /* The n-th component of the following list consists of a list of 3 lists.
   * (i) those d such that PrimitiveGroup(n,d) is maximal in Sym(n)
   * (ii) those d such that PrimitiveGroup(n,d) is maximal in Alt(n)
   * (iii) those d as in (ii) for which there are two conjugacy classes
   *       of corresponding subgroups in Alt(n). We conjugate
   *      PrimitiveGroup(n,d) by (1,2) to get one in the other class.
   */
maxprim:=[
[[ ], [ ], [ ]], 					  // 1
[[ ], [ ], [ ]], 					  // 2
[[ ], [ ], [ ]], 					  // 3
[[ ], [ ], [ ]], 					  // 4
[[3], [2], [ ]], 					  // 5
[[2], [1], [ ]], 					  // 6
[[4], [5], [5]], 					  // 7
[[5], [3], [3]], 					  // 8
[[7], [6,9], [9]], 					  // 9
[[7], [6], [ ]],	 				  // 10
[[4], [6], [6]],	  				  // 11
[[2], [4], [4]],	 				  // 12
[[6], [5,7], [7]], 					  // 13
[[2], [1], [ ]],	 				  // 14
[[ ], [4], [4]],	 				  // 15
[[ ], [20], [20]],	 				  // 16
[[5], [8], [8]], 			 		  // 17
[[2], [1], [ ]],	 				  // 18
[[6], [5], [ ]],	 				  // 19
[[2], [1], [ ]],	 				  // 20
[[1,3,7], [2,6], [ ]], 					  // 21
[[2], [1], [ ]],	 				  // 22
[[4], [5], [5]],	 				  // 23
[[2], [3], [3]],	 				  // 24
[[22,26], [21,24], [ ]],				  // 25
[[5], [2], [ ]],					  // 26
[[11], [13,10], [13]],					  // 27
[[11], [9,12], [12]],					  // 28
[[ ], [ ], [ ]],					  // 29
[[ ], [ ], [ ]],	 				  // 30
[[ ], [9,10], [9,10]],					  // 31
[[ ], [3], [3]],					  // 32
[[ ], [2], [2]],					  // 33
[[ ], [ ], [ ]],					  // 34
[[ ], [4], [4]],					  // 35
[[19, 8], [18,20], [20]],				  // 36
[[ ], [ ], [ ]],					  // 37
[[ ], [ ], [ ]],					  // 38
[[ ], [ ], [ ]],					  // 39
[[4,6], [2,5], [ ]],					  // 40
[[ ], [ ], [ ]],					  // 41
[[ ], [ ], [ ]],					  // 42
[[ ], [ ], [ ]],					  // 43
[[ ], [ ], [ ]],					  // 44
[[5], [4,7], [7]],					  // 45
[[ ], [ ], [ ]],					  // 46
[[ ], [ ], [ ]],					  // 47
[[ ], [ ], [ ]],					  // 48
[[33,38], [32,37], [ ]],				  // 49
[[ 6 ],[ 2, 7 ],[ 7 ]], //50
[[],[],[]], //51
[[],[ 1 ],[ 1 ]], //52
[[],[],[]], //53
[[],[],[]], //54
[[ 2, 3, 6 ],[ 5 ],[]], //55
[[ 6, 7 ],[ 2, 4 ],[]], //56
[[],[ 1, 3 ],[ 1, 3 ]], //57
[[],[],[]], //58
[[],[],[]], //59
[[ 5 ],[ 4 ],[]], //60
[[],[],[]], //61
[[],[],[]], //62
[[ 4 ],[ 1, 6 ],[ 6 ]], //63
[[],[ 64, 72 ],[ 64, 72 ]], //64
[[ 2 ],[ 1, 5, 7, 11 ],[ 5, 7, 11 ]], //65
[[],[ 5 ],[ 5 ]], //66
[[],[],[]], //67
[[ 3 ],[ 2 ],[]], //68
[[],[],[]], //69
[[],[],[]], //70
[[],[],[]], //71
[[],[],[]], //72
[[],[ 14 ],[ 14 ]], //73
[[],[],[]], //74
[[],[],[]], //75
[[],[],[]], //76
[[],[ 2 ],[ 2 ]], //77
[[ 2, 4 ],[ 1, 3 ],[]], //78
[[],[],[]], //79
[[],[],[]], //80
[[145, 153],[144, 152],[]], //81
[[ 8 ],[ 6 ],[]], //82
[[],[],[]], //83
[[ 3 ],[ 1 ],[]], //84
[[ 4 ],[ 3 ],[]], //85
[[],[],[]], //86
[[],[],[]], //87
[[],[],[]], //88
[[],[],[]], //89
[[],[],[]], //90
[[ 6 ],[ 4, 5, 8 ],[ 4, 8 ]], //91
[[],[],[]], //92
[[],[],[]], //93
[[],[],[]], //94
[[],[],[]], //95
[[],[],[]], //96
[[],[],[]], //97
[[],[],[]], //98
[[],[],[]], //99
[[ 32, 34, 36 ],[ 33, 35 ],[]], //100
[[],[],[]], //101
[[],[ 1 ],[ 1 ]], //102
[[],[],[]], //103
[[],[],[]], //104
[[ 3, 9 ],[ 7, 8 ],[ 7 ]], //105
[[],[],[]], //106
[[],[],[]], //107
[[],[],[]], //108
[[],[],[]], //109
[[],[],[]], //110
[[],[],[]], //111
[[],[ 8 ],[ 8 ]], //112
[[],[],[]], //113
[[],[],[]], //114
[[],[],[]], //115
[[],[],[]], //116
[[],[ 3 ],[ 3 ]], //117
[[],[],[]], //118
[[],[ 2 ],[ 2 ]], //119
[[ 10 ],[ 8, 19, 21 ],[ 19, 21 ]], //120
[[ 48, 54 ],[ 47, 53, 55 ],[ 55 ]], //121
[[ 5 ],[ 3 ],[]], //122
[[],[],[]], //123
[[],[],[]], //124
[[ 33, 43 ],[ 32, 40 ],[]], //125
[[ 12, 13, 17 ],[ 6, 8, 10, 15 ],[ 6 ]], //126
[[],[ 13 ],[ 13 ]], //127
[[],[ 3 ],[ 3 ]], //128
[[],[ 2 ],[ 2 ]], //129
[[ 5 ],[ 2 ],[]], //130
[[],[],[]], //131
[[],[],[]], //132
[[],[ 1 ],[ 1 ]], //133
[[],[],[]], //134
[[],[ 3 ],[ 3 ]], //135
[[ 3, 12 ],[ 10, 11 ],[ 10 ]], //136
[[],[],[]], //137
[[],[],[]], //138
[[],[],[]], //139
[[],[],[]], //140
[[],[],[]], //141
[[],[],[]], //142
[[],[],[]], //143
[[],[ 10, 12, 14],[ 10, 12, 14]], //144
[[],[],[]], //145
[[],[],[]], //146
[[],[],[]], //147
[[],[],[]], //148
[[],[],[]], //149
[[],[],[]], //150
[[],[],[]], //151
[[],[],[]], //152
[[],[ 4 ],[ 4 ]], //153
[[],[],[]], //154
[[],[ 1 ],[ 1 ]], //155
[[ 3, 7 ],[ 1, 6 ],[]], //156
[[],[],[]], //157
[[],[],[]], //158
[[],[],[]], //159
[[],[],[]], //160
[[],[],[]], //161
[[ 5 ],[ 3 ],[]], //162
[[],[],[]], //163
[[],[],[]], //164
[[ 4 ],[ 2, 5 ],[ 5 ]], //165
[[],[],[]], //166
[[],[],[]], //167
[[ 5 ],[ 4 ],[]], //168
[[ 68, 73 ],[ 67, 72 ],[]], //169
[[ 5 ],[ 3 ],[]], //170
[[ 2, 4 ],[ 1, 3 ],[]], //171
[[],[],[]], //172
[[],[],[]], //173
[[],[],[]], //174
[[ 2 ],[ 1, 4 ],[ 4 ]], //175
[[],[ 3, 4 ],[ 3, 4 ]], //176
[[],[],[]], //177
[[],[],[]], //178
[[],[],[]], //179
[[],[],[]], //180
[[],[],[]], //181
[[],[],[]], //182
[[],[ 2 ],[ 2 ]], //183
[[],[],[]], //184
[[],[],[]], //185
[[],[ 1 ],[ 1 ]], //186
[[],[],[]], //187
[[],[],[]], //188
[[],[],[]], //189
[[],[ 4 ],[ 4 ]], //190
[[],[],[]], //191
[[],[],[]], //192
[[],[],[]], //193
[[],[],[]], //194
[[],[],[]], //195
[[ 8 ],[],[]], //196
[[],[],[]], //197
[[],[],[]], //198
[[],[],[]], //199
[[],[],[]], //200
[[],[],[]], //201
[[],[],[]], //202
[[],[ 1 ],[ 1 ]], //203
[[],[],[]], //204
[[],[],[]], //205
[[],[],[]], //206
[[],[],[]], //207
[[],[ 3 ],[ 3 ]], //208
[[],[],[]], //209
[[ 4 ],[ 2, 3 ],[ 2 ]], //210
[[],[],[]], //211
[[],[],[]], //212
[[],[],[]], //213
[[],[],[]], //214
[[],[],[]], //215
[[],[ 20 ],[ 20 ]], //216
[[],[],[]], //217
[[],[],[]], //218
[[],[],[]], //219
[[ 3 ],[ 2 ],[]], //220
[[],[],[]], //221
[[],[],[]], //222
[[],[],[]], //223
[[],[],[]], //224
[[ 10 ],[ 8 ],[]], //225
[[],[],[]], //226
[[],[],[]], //227
[[],[],[]], //228
[[],[],[]], //229
[[],[],[]], //230
[[],[ 4 ],[ 4 ]], //231
[[],[],[]], //232
[[],[],[]], //233
[[],[ 2 ],[ 2 ]], //234
[[],[],[]], //235
[[],[],[]], //236
[[],[],[]], //237
[[],[],[]], //238
[[],[],[]], //239
[[],[],[]], //240
[[],[],[]], //241
[[],[],[]], //242
[[ 34 ],[ 33 ],[]], //243
[[ 4 ],[ 3 ],[]], //244
[[],[],[]], //245
[[],[],[]], //246
[[],[],[]], //247
[[],[ 1 ],[ 1 ]], //248
[[],[],[]], //249
[[],[],[]], //250
[[],[],[]], //251
[[],[],[]], //252
[[ 3, 7 ],[ 1, 2, 4, 6 ],[ 1, 4 ]], //253
[[],[],[]], //254
[[],[ 2 ],[ 2 ]], //255
[[],[ 238, 242 ],[ 238, 242 ]], //256
[[],[ 13 ],[ 13 ]], //257
[[],[],[]], //258
[[],[],[]], //259
[[],[],[]], //260
[[],[],[]], //261
[[],[],[]], //262
[[],[],[]], //263
[[],[],[]], //264
[[],[],[]], //265
[[],[ 1 ],[ 1 ]], //266
[[],[],[]], //267
[[],[],[]], //268
[[],[],[]], //269
[[],[],[]], //270
[[],[],[]], //271
[[],[],[]], //272
[[],[ 6 ],[ 6 ]], //273
[[],[],[]], //274
[[],[ 2 ],[ 2 ]], //275
[[],[ 4, 6 ],[ 4, 6 ]], //276
[[],[],[]], //277
[[],[],[]], //278
[[],[],[]], //279
[[ 11, 12, 14, 22 ],[ 9, 10, 13, 19 ],[]], //280
[[],[],[]], //281
[[],[],[]], //282
[[],[],[]], //283
[[],[],[]], //284
[[],[ 1 ],[ 1 ]], //285
[[ 2 ],[ 1 ],[]], //286
[[],[],[]], //287
[[],[],[]], //288
[[ 80, 95 ],[ 79, 93 ],[]], //289
[[ 5 ],[ 3 ],[]], //290
[[],[],[]], //291
[[],[],[]], //292
[[],[],[]], //293
[[],[],[]], //294
[[],[],[]], //295
[[],[],[]], //296
[[ 2 ],[ 1 ],[]], //297
[[],[],[]], //298
[[],[],[]], //299
[[ 5, 7, 9 ],[ 2, 6, 8 ],[]], //300
[[],[],[]], //301
[[],[],[]], //302
[[],[],[]], //303
[[],[],[]], //304
[[],[],[]], //305
[[],[],[]], //306
[[],[ 13 ],[ 13 ]], //307
[[],[],[]], //308
[[],[],[]], //309
[[],[],[]], //310
[[],[],[]], //311
[[],[],[]], //312
[[],[],[]], //313
[[],[],[]], //314
[[ 2 ],[ 1, 3 ],[ 3 ]], //315
[[],[],[]], //316
[[],[],[]], //317
[[],[],[]], //318
[[],[],[]], //319
[[],[],[]], //320
[[],[],[]], //321
[[],[],[]], //322
[[],[],[]], //323
[[ 8 ],[],[]], //324
[[ 10 ],[7, 9, 12 ],[7, 12 ]], //325
[[],[],[]], //326
[[],[],[]], //327
[[],[],[]], //328
[[],[],[]], //329
[[],[ 2, 4 ],[ 2, 4 ]], //330
[[],[],[]], //331
[[],[],[]], //332
[[],[],[]], //333
[[],[],[]], //334
[[],[],[]], //335
[[],[ 6, 7 ],[ 6, 7 ]], //336
[[],[],[]], //337
[[],[],[]], //338
[[],[],[]], //339
[[],[],[]], //340
[[ 2 ],[ 1 ],[]], //341
[[],[],[]], //342
[[ 76, 88 ],[ 75, 85 ],[]], //343
[[ 6 ],[ 2, 5 ],[ 2 ]], //344
[[],[],[]], //345
[[],[],[]], //346
[[],[],[]], //347
[[],[],[]], //348
[[],[],[]], //349
[[],[],[]], //350
[[ 4, 7, 9 ],[ 3, 6, 8 ],[]], //351
[[],[],[]], //352
[[],[],[]], //353
[[],[],[]], //354
[[],[],[]], //355
[[],[],[]], //356
[[ 5 ],[ 2 ],[]], //357
[[],[],[]], //358
[[],[],[]], //359
[[ 16 ],[ 11 ],[]], //360
[[ 86, 90 ],[ 85, 88 ],[]], //361
[[ 5 ],[ 4 ],[]], //362
[[],[],[]], //363
[[ 5, 9 ],[ 3, 7, 8 ],[ 7 ]], //364
[[],[],[]], //365
[[],[],[]], //366
[[],[],[]], //367
[[],[],[]], //368
[[ 3 ],[ 2 ],[]], //369
[[],[],[]], //370
[[],[],[]], //371
[[],[],[]], //372
[[],[],[]], //373
[[],[],[]], //374
[[],[],[]], //375
[[],[],[]], //376
[[],[],[]], //377
[[],[ 7, 9 ],[ 7, 9 ]], //378
[[],[],[]], //379
[[],[],[]], //380
[[],[ 2 ],[ 2 ]], //381
[[],[],[]], //382
[[],[],[]], //383
[[],[],[]], //384
[[],[],[]], //385
[[],[],[]], //386
[[],[],[]], //387
[[],[],[]], //388
[[],[],[]], //389
[[],[],[]], //390
[[],[],[]], //391
[[],[],[]], //392
[[],[],[]], //393
[[],[],[]], //394
[[],[],[]], //395
[[],[ 2 ],[ 2 ]], //396
[[],[],[]], //397
[[],[],[]], //398
[[],[],[]], //399
[[ 11, 14 ],[ 8, 9, 13 ],[ 8 ]], //400
[[],[],[]], //401
[[],[],[]], //402
[[],[],[]], //403
[[],[],[]], //404
[[],[],[]], //405
[[ 2, 4 ],[ 1, 3 ],[]], //406
[[],[],[]], //407
[[],[],[]], //408
[[],[],[]], //409
[[],[],[]], //410
[[],[],[]], //411
[[],[],[]], //412
[[],[],[]], //413
[[],[],[]], //414
[[],[],[]], //415
[[],[ 5 ],[ 5 ]], //416
[[],[],[]], //417
[[],[],[]], //418
[[],[],[]], //419
[[],[],[]], //420
[[],[],[]], //421
[[],[],[]], //422
[[],[],[]], //423
[[],[],[]], //424
[[ 1 ],[],[]], //425
[[],[],[]], //426
[[],[],[]], //427
[[],[],[]], //428
[[],[],[]], //429
[[],[],[]], //430
[[],[],[]], //431
[[],[],[]], //432
[[],[],[]], //433
[[],[],[]], //434
[[],[ 4 ],[ 4 ]], //435
[[],[],[]], //436
[[],[],[]], //437
[[],[],[]], //438
[[],[],[]], //439
[[],[],[]], //440
[[ 22 ],[ 20 ],[]], //441
[[],[],[]], //442
[[],[],[]], //443
[[],[],[]], //444
[[],[],[]], //445
[[],[],[]], //446
[[],[],[]], //447
[[],[],[]], //448
[[],[],[]], //449
[[],[],[]], //450
[[],[],[]], //451
[[],[],[]], //452
[[],[],[]], //453
[[],[],[]], //454
[[],[ 2 ],[ 2 ]], //455
[[],[ 2 ],[ 2 ]], //456
[[],[],[]], //457
[[],[],[]], //458
[[],[],[]], //459
[[],[],[]], //460
[[],[],[]], //461
[[],[ 6 ],[ 6 ]], //462
[[],[],[]], //463
[[],[],[]], //464
[[ 2, 3, 5 ],[ 1, 4 ],[]], //465
[[],[],[]], //466
[[],[],[]], //467
[[],[],[]], //468
[[],[],[]], //469
[[],[],[]], //470
[[],[],[]], //471
[[],[],[]], //472
[[],[],[]], //473
[[],[],[]], //474
[[],[],[]], //475
[[],[],[]], //476
[[],[],[]], //477
[[],[],[]], //478
[[],[],[]], //479
[[],[],[]], //480
[[],[],[]], //481
[[],[],[]], //482
[[],[],[]], //483
[[ 8 ],[],[]], //484
[[],[],[]], //485
[[],[],[]], //486
[[],[],[]], //487
[[],[],[]], //488
[[],[],[]], //489
[[],[],[]], //490
[[],[],[]], //491
[[],[],[]], //492
[[],[],[]], //493
[[],[],[]], //494
[[ 4 ],[ 2, 8 ],[ 8 ]], //495
[[  ],[ 8, 10 ],[ 8, 10  ]], //496
[[],[],[]], //497
[[],[],[]], //498
[[],[],[]], //499
[[],[],[]], //500
[[],[],[]], //501
[[],[],[]], //502
[[],[],[]], //503
[[],[ 4 ],[ 4 ]], //504
[[],[],[]], //505
[[],[ 1 ],[ 1 ]], //506
[[],[],[]], //507
[[],[],[]], //508
[[],[],[]], //509
[[],[],[]], //510
[[],[ 1 ],[ 1 ]], //511
[[],[ 36, 56 ],[ 36, 56 ]], //512
[[],[ 9, 12 ],[ 9, 12 ]], //513
[[],[],[]], //514
[[],[],[]], //515
[[],[],[]], //516
[[],[],[]], //517
[[],[],[]], //518
[[],[],[]], //519
[[ 7 ],[ 4, 6 ],[ 4 ]], //520
[[],[],[]], //521
[[],[],[]], //522
[[],[],[]], //523
[[],[],[]], //524
[[ 6 ],[ 4, 5 ],[ 5 ]], //525
[[],[],[]], //526
[[],[ 2 ],[ 2 ]], //527
[[ 7 ],[ 5, 6 ],[ 5 ]], //528
[[ 58, 63 ],[ 57, 61 ],[]], //529
[[ 5 ],[ 4 ],[]], //530
[[],[],[]], //531
[[],[],[]], //532
[[],[],[]], //533
[[],[],[]], //534
[[],[],[]], //535
[[],[],[]], //536
[[],[],[]], //537
[[],[],[]], //538
[[],[],[]], //539
[[ 8 ],[ 7 ],[]], //540
[[],[],[]], //541
[[],[],[]], //542
[[],[],[]], //543
[[],[],[]], //544
[[],[],[]], //545
[[],[],[]], //546
[[],[],[]], //547
[[],[],[]], //548
[[],[],[]], //549
[[],[],[]], //550
[[],[],[]], //551
[[],[],[]], //552
[[],[ 1 ],[ 1 ]], //553
[[],[],[]], //554
[[],[],[]], //555
[[],[],[]], //556
[[],[],[]], //557
[[],[],[]], //558
[[],[],[]], //559
[[ 4 ],[ 2, 3 ],[ 2 ]], //560
[[],[ 2 ],[ 2 ]], //561
[[],[],[]], //562
[[],[],[]], //563
[[],[],[]], //564
[[],[],[]], //565
[[],[],[]], //566
[[],[ 5 ],[ 5 ]], //567
[[],[],[]], //568
[[],[],[]], //569
[[],[],[]], //570
[[],[],[]], //571
[[],[],[]], //572
[[],[],[]], //573
[[],[ 1 ],[ 1 ]], //574
[[],[],[]], //575
[[],[ 9 ],[ 9 ]], //576
[[],[],[]], //577
[[],[],[]], //578
[[],[],[]], //579
[[],[],[]], //580
[[],[],[]], //581
[[],[],[]], //582
[[],[],[]], //583
[[],[],[]], //584
[[],[ 4 ],[ 4 ]], //585
[[],[],[]], //586
[[],[],[]], //587
[[],[],[]], //588
[[],[],[]], //589
[[],[],[]], //590
[[],[],[]], //591
[[],[],[]], //592
[[],[],[]], //593
[[],[],[]], //594
[[ 2 ],[ 1 ],[]], //595
[[],[],[]], //596
[[],[],[]], //597
[[],[],[]], //598
[[],[],[]], //599
[[],[],[]], //600
[[],[],[]], //601
[[],[],[]], //602
[[],[],[]], //603
[[],[],[]], //604
[[],[],[]], //605
[[],[],[]], //606
[[],[],[]], //607
[[],[],[]], //608
[[],[],[]], //609
[[],[],[]], //610
[[],[],[]], //611
[[],[],[]], //612
[[],[],[]], //613
[[],[],[]], //614
[[],[],[]], //615
[[],[ 2 ],[ 2 ]], //616
[[],[],[]], //617
[[],[],[]], //618
[[],[],[]], //619
[[],[ 1 ],[ 1 ]], //620
[[],[],[]], //621
[[],[],[]], //622
[[],[],[]], //623
[[],[],[]], //624
[[ 647, 692, 696 ],[ 646, 689, 695 ],[]], //625
[[ 8 ],[ 7 ],[]], //626
[[],[],[]], //627
[[],[],[]], //628
[[],[],[]], //629
[[],[ 2 ],[ 2 ]], //630
[[],[],[]], //631
[[],[],[]], //632
[[],[],[]], //633
[[],[],[]], //634
[[],[],[]], //635
[[],[],[]], //636
[[],[],[]], //637
[[],[],[]], //638
[[],[],[]], //639
[[],[],[]], //640
[[],[],[]], //641
[[],[],[]], //642
[[],[],[]], //643
[[],[],[]], //644
[[],[],[]], //645
[[],[],[]], //646
[[],[],[]], //647
[[],[],[]], //648
[[],[],[]], //649
[[],[],[]], //650
[[],[ 1, 5 ],[ 1, 5 ]], //651
[[],[],[]], //652
[[],[],[]], //653
[[],[],[]], //654
[[],[],[]], //655
[[],[],[]], //656
[[],[ 2 ],[ 2 ]], //657
[[],[],[]], //658
[[],[],[]], //659
[[ 5 ],[ 2 ],[]], //660
[[],[],[]], //661
[[],[],[]], //662
[[],[],[]], //663
[[],[],[]], //664
[[],[],[]], //665
[[ 2, 4 ],[ 1, 3 ],[]], //666
[[],[],[]], //667
[[],[],[]], //668
[[],[],[]], //669
[[],[],[]], //670
[[],[ 2 ],[ 2 ]], //671
[[],[ 6 ],[ 6 ]], //672
[[],[],[]], //673
[[],[],[]], //674
[[],[],[]], //675
[[ 28 ],[],[]], //676
[[],[],[]], //677
[[],[],[]], //678
[[],[],[]], //679
[[ 2 ],[ 1 ],[]], //680
[[],[],[]], //681
[[],[],[]], //682
[[],[],[]], //683
[[],[],[]], //684
[[],[],[]], //685
[[],[],[]], //686
[[],[],[]], //687
[[],[],[]], //688
[[],[],[]], //689
[[],[],[]], //690
[[],[],[]], //691
[[],[],[]], //692
[[ 4 ],[ 3 ],[]], //693
[[],[],[]], //694
[[],[],[]], //695
[[],[],[]], //696
[[],[],[]], //697
[[],[],[]], //698
[[],[],[]], //699
[[],[],[]], //700
[[],[],[]], //701
[[],[],[]], //702
[[],[ 4 ],[ 4 ]], //703
[[],[],[]], //704
[[],[],[]], //705
[[],[],[]], //706
[[],[],[]], //707
[[],[],[]], //708
[[],[],[]], //709
[[],[],[]], //710
[[],[],[]], //711
[[],[],[]], //712
[[],[],[]], //713
[[],[],[]], //714
[[ 2 ],[ 1 ],[]], //715
[[],[],[]], //716
[[],[],[]], //717
[[],[],[]], //718
[[],[],[]], //719
[[],[],[]], //720
[[],[],[]], //721
[[],[],[]], //722
[[],[],[]], //723
[[],[],[]], //724
[[],[],[]], //725
[[],[],[]], //726
[[],[],[]], //727
[[],[],[]], //728
[[ 471, 495, 499 ],[ 470, 492, 498 ],[]], //729
[[ 3, 13 ],[ 2, 12 ],[]], //730
[[],[],[]], //731
[[],[],[]], //732
[[],[],[]], //733
[[],[],[]], //734
[[],[],[]], //735
[[],[],[]], //736
[[],[],[]], //737
[[],[],[]], //738
[[],[],[]], //739
[[],[],[]], //740
[[ 2 ],[ 1 ],[]], //741
[[],[],[]], //742
[[],[],[]], //743
[[],[],[]], //744
[[],[],[]], //745
[[],[],[]], //746
[[],[],[]], //747
[[],[],[]], //748
[[],[],[]], //749
[[ 1 ],[],[]], //750
[[],[],[]], //751
[[],[],[]], //752
[[],[],[]], //753
[[],[],[]], //754
[[],[],[]], //755
[[],[ 5 ],[ 5 ]], //756
[[],[ 26 ],[ 26 ]], //757
[[],[],[]], //758
[[],[ 1 ],[ 1 ]], //759
[[],[],[]], //760
[[],[],[]], //761
[[],[],[]], //762
[[],[],[]], //763
[[],[],[]], //764
[[ 2 ],[ 1 ],[]], //765
[[],[],[]], //766
[[],[],[]], //767
[[],[],[]], //768
[[],[],[]], //769
[[],[],[]], //770
[[],[],[]], //771
[[],[],[]], //772
[[],[],[]], //773
[[],[],[]], //774
[[ 1 ],[],[]], //775
[[],[],[]], //776
[[],[],[]], //777
[[],[],[]], //778
[[],[],[]], //779
[[],[ 2 ],[ 2 ]], //780
[[],[ 1 ],[ 1 ]], //781
[[],[],[]], //782
[[],[],[]], //783
[[],[ 36 ],[ 36 ]], //784
[[],[],[]], //785
[[],[],[]], //786
[[],[],[]], //787
[[],[],[]], //788
[[],[],[]], //789
[[],[],[]], //790
[[],[],[]], //791
[[],[ 2 ],[ 2 ]], //792
[[],[],[]], //793
[[],[],[]], //794
[[],[],[]], //795
[[],[],[]], //796
[[],[],[]], //797
[[],[],[]], //798
[[],[],[]], //799
[[],[],[]], //800
[[],[],[]], //801
[[],[],[]], //802
[[],[],[]], //803
[[],[],[]], //804
[[],[],[]], //805
[[ 8 ],[ 6 ],[]], //806
[[],[],[]], //807
[[],[],[]], //808
[[],[],[]], //809
[[],[],[]], //810
[[],[],[]], //811
[[],[],[]], //812
[[],[],[]], //813
[[],[],[]], //814
[[],[],[]], //815
[[],[ 2 ],[ 2 ]], //816
[[],[],[]], //817
[[],[],[]], //818
[[ 4 ],[ 3, 6 ],[ 6 ]], //819
[[ 2, 11, 20, 22 ],[ 1, 8, 17, 21 ],[]], //820
[[],[],[]], //821
[[],[],[]], //822
[[],[],[]], //823
[[],[],[]], //824
[[],[],[]], //825
[[],[],[]], //826
[[],[],[]], //827
[[],[],[]], //828
[[],[],[]], //829
[[],[],[]], //830
[[],[],[]], //831
[[],[],[]], //832
[[],[],[]], //833
[[],[],[]], //834
[[],[],[]], //835
[[],[],[]], //836
[[],[],[]], //837
[[],[],[]], //838
[[],[],[]], //839
[[],[ 2, 4 ],[ 2, 4 ]], //840
[[ 110, 114 ],[ 109, 113 ],[]], //841
[[ 5 ],[ 3 ],[]], //842
[[],[],[]], //843
[[],[],[]], //844
[[],[],[]], //845
[[],[],[]], //846
[[],[],[]], //847
[[],[],[]], //848
[[],[],[]], //849
[[],[],[]], //850
[[],[],[]], //851
[[],[],[]], //852
[[],[],[]], //853
[[],[],[]], //854
[[],[],[]], //855
[[],[],[]], //856
[[],[],[]], //857
[[],[],[]], //858
[[],[],[]], //859
[[],[],[]], //860
[[],[ 4 ],[ 4 ]], //861
[[],[],[]], //862
[[],[],[]], //863
[[],[],[]], //864
[[],[],[]], //865
[[],[],[]], //866
[[],[],[]], //867
[[],[],[]], //868
[[],[],[]], //869
[[],[],[]], //870
[[],[ 1 ],[ 1 ]], //871
[[],[],[]], //872
[[],[],[]], //873
[[],[],[]], //874
[[],[],[]], //875
[[],[],[]], //876
[[],[],[]], //877
[[],[],[]], //878
[[],[],[]], //879
[[],[ 1 ],[ 1 ]], //880
[[],[],[]], //881
[[],[],[]], //882
[[],[],[]], //883
[[],[],[]], //884
[[],[],[]], //885
[[],[],[]], //886
[[],[],[]], //887
[[],[],[]], //888
[[],[],[]], //889
[[],[],[]], //890
[[],[ 4 ],[ 4 ]], //891
[[],[],[]], //892
[[],[],[]], //893
[[],[],[]], //894
[[],[],[]], //895
[[],[],[]], //896
[[],[],[]], //897
[[],[],[]], //898
[[],[],[]], //899
[[ 8 ],[],[]], //900
[[],[],[]], //901
[[],[],[]], //902
[[ 2, 4 ],[ 1, 3 ],[]], //903
[[],[],[]], //904
[[],[],[]], //905
[[],[],[]], //906
[[],[],[]], //907
[[],[],[]], //908
[[],[],[]], //909
[[ 3 ],[ 1 ],[]], //910
[[],[],[]], //911
[[],[],[]], //912
[[],[],[]], //913
[[],[],[]], //914
[[],[],[]], //915
[[],[],[]], //916
[[],[],[]], //917
[[],[],[]], //918
[[],[],[]], //919
[[],[],[]], //920
[[],[],[]], //921
[[],[],[]], //922
[[],[],[]], //923
[[],[],[]], //924
[[],[],[]], //925
[[],[],[]], //926
[[],[],[]], //927
[[],[],[]], //928
[[],[],[]], //929
[[],[],[]], //930
[[],[],[]], //931
[[],[],[]], //932
[[],[],[]], //933
[[],[],[]], //934
[[],[],[]], //935
[[],[],[]], //936
[[],[],[]], //937
[[],[],[]], //938
[[],[],[]], //939
[[],[],[]], //940
[[],[],[]], //941
[[],[],[]], //942
[[],[],[]], //943
[[],[],[]], //944
[[],[ 2 ],[ 2 ]], //945
[[],[ 4 ],[ 4 ]], //946
[[],[],[]], //947
[[],[],[]], //948
[[],[],[]], //949
[[],[],[]], //950
[[],[],[]], //951
[[],[],[]], //952
[[],[],[]], //953
[[],[],[]], //954
[[],[],[]], //955
[[],[],[]], //956
[[],[],[]], //957
[[],[],[]], //958
[[],[],[]], //959
[[],[ 5, 8 ],[ 5, 8 ]], //960
[[ 126, 132 ],[ 125, 131 ],[]], //961
[[ 5 ],[ 4 ],[]], //962
[[],[],[]], //963
[[],[],[]], //964
[[],[],[]], //965
[[],[],[]], //966
[[],[],[]], //967
[[],[],[]], //968
[[],[ 2 ],[ 2 ]], //969
[[],[],[]], //970
[[],[],[]], //971
[[],[],[]], //972
[[],[],[]], //973
[[],[],[]], //974
[[],[],[]], //975
[[],[],[]], //976
[[],[],[]], //977
[[],[],[]], //978
[[],[],[]], //979
[[],[ 2 ],[ 2 ]], //980
[[],[],[]], //981
[[],[],[]], //982
[[],[],[]], //983
[[],[],[]], //984
[[],[],[]], //985
[[],[],[]], //986
[[],[],[]], //987
[[],[],[]], //988
[[],[],[]], //989
[[ 2 ],[ 1 ],[]], //990
[[],[],[]], //991
[[],[],[]], //992
[[],[ 2 ],[ 2 ]], //993
[[],[],[]], //994
[[],[],[]], //995
[[],[],[]], //996
[[],[],[]], //997
[[],[],[]], //998
[[],[],[]], //999
[[],[ 105 ],[ 105 ]], //1000
[[],[ 2 ],[ 2 ]], //1001
[[],[],[]], //1002
[[],[],[]], //1003
[[],[],[]], //1004
[[],[],[]], //1005
[[],[],[]], //1006
[[],[],[]], //1007
[[],[ 2, 7 ],[ 2, 7 ]], //1008
[[],[],[]], //1009
[[],[],[]], //1010
[[],[],[]], //1011
[[],[],[]], //1012
[[],[],[]], //1013
[[],[],[]], //1014
[[],[ 1 ],[ 1 ]], //1015
[[],[],[]], //1016
[[],[],[]], //1017
[[],[],[]], //1018
[[],[],[]], //1019
[[],[],[]], //1020
[[],[],[]], //1021
[[],[],[]], //1022
[[],[2],[2]], //1023
[[],[ 105, 113 ],[ 105, 113 ]], //1024
[[],[ 2, 6 ],[ 2, 6 ]], //1025
[[],[],[]], //1026
[[],[],[]], //1027
[[],[],[]], //1028
[[],[],[]], //1029
[[],[],[]], //1030
[[],[],[]], //1031
[[],[],[]], //1032
[[],[],[]], //1033
[[],[],[]], //1034
[[],[ 2 ],[ 2 ]], //1035
[[],[],[]], //1036
[[],[],[]], //1037
[[],[],[]], //1038
[[],[],[]], //1039
[[3 ],[1,5 ],[ 5 ]], //1040
[[],[],[]], //1041
[[],[],[]], //1042
[[],[],[]], //1043
[[],[],[]], //1044
[[],[ 1 ],[ 1 ]], //1045
[[],[],[]], //1046
[[],[],[]], //1047
[[],[],[]], //1048
[[],[],[]], //1049
[[],[],[]], //1050
[[],[],[]], //1051
[[],[],[]], //1052
[[],[],[]], //1053
[[],[],[]], //1054
[[],[],[]], //1055
[[],[],[]], //1056
[[],[ 2 ],[ 2 ]], //1057
[[],[],[]], //1058
[[],[],[]], //1059
[[],[],[]], //1060
[[],[],[]], //1061
[[],[],[]], //1062
[[],[],[]], //1063
[[],[],[]], //1064
[[],[],[]], //1065
[[ 5 ],[ 4 ],[]], //1066
[[],[],[]], //1067
[[],[],[]], //1068
[[],[],[]], //1069
[[],[],[]], //1070
[[],[ 2 ],[ 2 ]], //1071
[[],[],[]], //1072
[[],[],[]], //1073
[[],[],[]], //1074
[[],[],[]], //1075
[[],[],[]], //1076
[[],[],[]], //1077
[[],[],[]], //1078
[[],[],[]], //1079
[[3, 9 ],[2, 8],[ ]], //1080
[[ 2, 4 ],[ 1, 3 ],[]], //1081
[[],[],[]], //1082
[[],[],[]], //1083
[[],[],[]], //1084
[[ 1 ],[],[]], //1085
[[],[],[]], //1086
[[],[],[]], //1087
[[],[],[]], //1088
[[ 8 ],[ 7 ],[]], //1089
[[],[],[]], //1090
[[],[],[]], //1091
[[ 5 ],[ 4 ],[]], //1092
[[],[25 ],[25 ]], //1093
[[],[],[]], //1094
[[],[],[]], //1095
[[],[],[]], //1096
[[],[],[]], //1097
[[],[],[]], //1098
[[],[],[]], //1099
[[ 4 ],[ 2, 3 ],[ 3 ]], //1100
[[],[],[]], //1101
[[],[],[]], //1102
[[],[],[]], //1103
[[],[],[]], //1104
[[ 2 ],[ 1, 5 ],[ 5 ]], //1105
[[],[],[]], //1106
[[],[ 2 ],[ 2 ]], //1107
[[],[],[]], //1108
[[],[],[]], //1109
[[],[],[]], //1110
[[],[],[]], //1111
[[],[],[]], //1112
[[],[],[]], //1113
[[],[],[]], //1114
[[],[],[]], //1115
[[],[],[]], //1116
[[],[],[]], //1117
[[],[],[]], //1118
[[],[],[]], //1119
[[  ],[ 5, 14 ],[ 14 ]], //1120
[[],[],[]], //1121
[[],[],[]], //1122
[[],[],[]], //1123
[[],[],[]], //1124
[[],[],[]], //1125
[[],[],[]], //1126
[[],[],[]], //1127
[[],[ 4 ],[ 4 ]], //1128
[[],[],[]], //1129
[[],[],[]], //1130
[[],[],[]], //1131
[[],[],[]], //1132
[[],[],[]], //1133
[[],[],[]], //1134
[[],[],[]], //1135
[[],[],[]], //1136
[[],[],[]], //1137
[[],[],[]], //1138
[[],[],[]], //1139
[[ 2 ],[ 1 ],[]], //1140
[[],[],[]], //1141
[[],[],[]], //1142
[[],[],[]], //1143
[[],[],[]], //1144
[[],[],[]], //1145
[[],[],[]], //1146
[[],[],[]], //1147
[[],[],[]], //1148
[[],[],[]], //1149
[[],[],[]], //1150
[[],[],[]], //1151
[[],[],[]], //1152
[[],[],[]], //1153
[[],[],[]], //1154
[[],[],[]], //1155
[[ 4 ],[],[]], //1156
[[],[],[]], //1157
[[],[],[]], //1158
[[],[],[]], //1159
[[],[],[]], //1160
[[],[],[]], //1161
[[],[],[]], //1162
[[],[],[]], //1163
[[],[],[]], //1164
[[],[],[]], //1165
[[],[],[]], //1166
[[],[],[]], //1167
[[],[],[]], //1168
[[],[],[]], //1169
[[],[],[]], //1170
[[],[],[]], //1171
[[],[],[]], //1172
[[],[],[]], //1173
[[],[],[]], //1174
[[],[],[]], //1175
[[ 5, 9 ],[ 3, 7, 8 ],[ 7 ]], //1176
[[],[],[]], //1177
[[],[],[]], //1178
[[],[],[]], //1179
[[],[],[]], //1180
[[],[],[]], //1181
[[],[],[]], //1182
[[],[],[]], //1183
[[],[],[]], //1184
[[],[],[]], //1185
[[],[],[]], //1186
[[],[],[]], //1187
[[],[],[]], //1188
[[],[],[]], //1189
[[],[],[]], //1190
[[],[],[]], //1191
[[],[],[]], //1192
[[],[],[]], //1193
[[],[],[]], //1194
[[],[],[]], //1195
[[],[],[]], //1196
[[],[],[]], //1197
[[],[],[]], //1198
[[],[],[]], //1199
[[],[],[]], //1200
[[],[],[]], //1201
[[],[],[]], //1202
[[],[],[]], //1203
[[],[],[]], //1204
[[],[],[]], //1205
[[],[],[]], //1206
[[],[],[]], //1207
[[],[],[]], //1208
[[],[],[]], //1209
[[],[ 1 ],[ 1 ]], //1210
[[],[],[]], //1211
[[],[],[]], //1212
[[],[],[]], //1213
[[],[],[]], //1214
[[],[],[]], //1215
[[],[],[]], //1216
[[],[],[]], //1217
[[],[],[]], //1218
[[],[],[]], //1219
[[],[],[]], //1220
[[],[],[]], //1221
[[],[],[]], //1222
[[],[],[]], //1223
[[],[],[]], //1224
[[ 12, 19 ],[ 10, 18, 21 ],[ 21 ]], //1225
[[],[],[]], //1226
[[],[],[]], //1227
[[],[],[]], //1228
[[],[],[]], //1229
[[],[],[]], //1230
[[],[],[]], //1231
[[],[],[]], //1232
[[],[],[]], //1233
[[],[],[]], //1234
[[],[],[]], //1235
[[],[],[]], //1236
[[],[],[]], //1237
[[],[],[]], //1238
[[],[],[]], //1239
[[],[],[]], //1240
[[],[],[]], //1241
[[],[],[]], //1242
[[],[],[]], //1243
[[],[],[]], //1244
[[],[],[]], //1245
[[],[],[]], //1246
[[],[],[]], //1247
[[],[],[]], //1248
[[],[],[]], //1249
[[],[],[]], //1250
[[],[],[]], //1251
[[],[],[]], //1252
[[],[],[]], //1253
[[],[],[]], //1254
[[],[],[]], //1255
[[],[],[]], //1256
[[],[],[]], //1257
[[],[],[]], //1258
[[],[],[]], //1259
[[],[],[]], //1260
[[],[],[]], //1261
[[],[],[]], //1262
[[],[],[]], //1263
[[],[],[]], //1264
[[],[],[]], //1265
[[],[],[]], //1266
[[],[],[]], //1267
[[],[],[]], //1268
[[],[],[]], //1269
[[],[],[]], //1270
[[],[],[]], //1271
[[],[],[]], //1272
[[],[],[]], //1273
[[],[],[]], //1274
[[ 2 ],[ 1 ],[]], //1275
[[],[],[]], //1276
[[],[],[]], //1277
[[],[],[]], //1278
[[],[],[]], //1279
[[],[],[]], //1280
[[],[],[]], //1281
[[],[],[]], //1282
[[],[],[]], //1283
[[],[],[]], //1284
[[],[],[]], //1285
[[],[],[]], //1286
[[],[ 2 ],[ 2 ]], //1287
[[],[ 2 ],[ 2 ]], //1288
[[],[],[]], //1289
[[],[],[]], //1290
[[],[],[]], //1291
[[],[],[]], //1292
[[],[],[]], //1293
[[],[],[]], //1294
[[],[],[]], //1295
[[],[ 127, 131, 133 ],[ 127, 131, 133 ]], //1296
[[],[],[]], //1297
[[],[],[]], //1298
[[],[],[]], //1299
[[],[],[]], //1300
[[],[],[]], //1301
[[],[],[]], //1302
[[],[],[]], //1303
[[],[],[]], //1304
[[],[],[]], //1305
[[],[],[]], //1306
[[],[],[]], //1307
[[],[],[]], //1308
[[],[],[]], //1309
[[],[],[]], //1310
[[],[],[]], //1311
[[],[],[]], //1312
[[],[],[]], //1313
[[],[],[]], //1314
[[],[],[]], //1315
[[],[],[]], //1316
[[],[],[]], //1317
[[],[],[]], //1318
[[],[],[]], //1319
[[],[ 2 ],[ 2 ]], //1320
[[],[],[]], //1321
[[],[],[]], //1322
[[],[],[]], //1323
[[],[],[]], //1324
[[],[],[]], //1325
[[],[ 2 ],[ 2 ]], //1326
[[],[],[]], //1327
[[],[],[]], //1328
[[],[],[]], //1329
[[ 2 ],[ 1 ],[]], //1330
[[ 76, 90 ],[ 75, 89 ],[]], //1331
[[ 8 ],[ 4, 7 ],[ 4 ]], //1332
[[],[],[]], //1333
[[],[],[]], //1334
[[],[],[]], //1335
[[],[],[]], //1336
[[],[],[]], //1337
[[],[],[]], //1338
[[],[],[]], //1339
[[],[],[]], //1340
[[],[],[]], //1341
[[],[],[]], //1342
[[],[],[]], //1343
[[],[],[]], //1344
[[],[],[]], //1345
[[],[],[]], //1346
[[],[],[]], //1347
[[],[],[]], //1348
[[],[],[]], //1349
[[],[],[]], //1350
[[],[],[]], //1351
[[],[],[]], //1352
[[],[],[]], //1353
[[],[],[]], //1354
[[],[],[]], //1355
[[],[],[]], //1356
[[],[],[]], //1357
[[],[],[]], //1358
[[],[],[]], //1359
[[],[ 3 ],[ 3 ]], //1360
[[],[],[]], //1361
[[],[],[]], //1362
[[],[],[]], //1363
[[],[],[]], //1364
[[ 4, 12 ],[ 2, 6, 11 ],[ 6 ]], //1365
[[],[],[]], //1366
[[],[],[]], //1367
[[],[],[]], //1368
[[ 136, 140 ],[ 135, 138 ],[]], //1369
[[ 5 ],[ 4 ],[]], //1370
[[],[],[]], //1371
[[],[],[]], //1372
[[],[],[]], //1373
[[],[],[]], //1374
[[],[],[]], //1375
[[],[],[]], //1376
[[],[],[]], //1377
[[ 2, 4 ],[ 1, 3 ],[]], //1378
[[],[],[]], //1379
[[],[],[]], //1380
[[],[],[]], //1381
[[],[],[]], //1382
[[],[],[]], //1383
[[],[],[]], //1384
[[],[],[]], //1385
[[],[],[]], //1386
[[],[],[]], //1387
[[],[],[]], //1388
[[],[],[]], //1389
[[],[],[]], //1390
[[],[],[]], //1391
[[],[],[]], //1392
[[],[],[]], //1393
[[],[],[]], //1394
[[],[ 2 ],[ 2 ]], //1395
[[],[],[]], //1396
[[],[],[]], //1397
[[],[],[]], //1398
[[],[],[]], //1399
[[],[],[]], //1400
[[],[],[]], //1401
[[],[],[]], //1402
[[],[],[]], //1403
[[],[],[]], //1404
[[],[],[]], //1405
[[],[],[]], //1406
[[],[ 2 ],[ 2 ]], //1407
[[],[ 4 ],[ 4 ]], //1408
[[],[],[]], //1409
[[],[],[]], //1410
[[],[],[]], //1411
[[],[],[]], //1412
[[],[],[]], //1413
[[],[],[]], //1414
[[],[],[]], //1415
[[],[],[]], //1416
[[],[],[]], //1417
[[],[],[]], //1418
[[],[],[]], //1419
[[],[],[]], //1420
[[],[],[]], //1421
[[],[],[]], //1422
[[],[],[]], //1423
[[],[],[]], //1424
[[],[],[]], //1425
[[],[],[]], //1426
[[],[],[]], //1427
[[],[],[]], //1428
[[],[],[]], //1429
[[],[],[]], //1430
[[],[ 4 ],[ 4 ]], //1431
[[],[],[]], //1432
[[],[],[]], //1433
[[],[],[]], //1434
[[],[ 1 ],[ 1 ]], //1435
[[],[],[]], //1436
[[],[],[]], //1437
[[],[],[]], //1438
[[],[],[]], //1439
[[],[],[]], //1440
[[],[],[]], //1441
[[],[],[]], //1442
[[],[],[]], //1443
[[ 8 ],[],[]], //1444
[[],[],[]], //1445
[[],[],[]], //1446
[[],[],[]], //1447
[[],[],[]], //1448
[[],[],[]], //1449
[[],[],[]], //1450
[[],[],[]], //1451
[[],[],[]], //1452
[[],[],[]], //1453
[[],[],[]], //1454
[[],[],[]], //1455
[[],[ 2, 3 ],[ 2, 3 ]], //1456
[[],[],[]], //1457
[[],[],[]], //1458
[[],[],[]], //1459
[[],[],[]], //1460
[[],[],[]], //1461
[[],[],[]], //1462
[[],[ 1 ],[ 1 ]], //1463
[[ 3, 6 ],[ 1, 5 ],[]], //1464
[[],[],[]], //1465
[[],[],[]], //1466
[[],[],[]], //1467
[[],[],[]], //1468
[[],[],[]], //1469
[[],[],[]], //1470
[[],[],[]], //1471
[[],[],[]], //1472
[[],[],[]], //1473
[[],[],[]], //1474
[[],[],[]], //1475
[[],[],[]], //1476
[[],[],[]], //1477
[[],[],[]], //1478
[[],[],[]], //1479
[[],[],[]], //1480
[[],[],[]], //1481
[[],[],[]], //1482
[[],[],[]], //1483
[[],[],[]], //1484
[[ 2 ],[ 1 ],[]], //1485
[[],[],[]], //1486
[[],[],[]], //1487
[[],[],[]], //1488
[[],[],[]], //1489
[[],[],[]], //1490
[[],[],[]], //1491
[[],[],[]], //1492
[[],[],[]], //1493
[[],[],[]], //1494
[[],[],[]], //1495
[[],[],[]], //1496
[[],[],[]], //1497
[[],[],[]], //1498
[[],[],[]], //1499
[[],[],[]], //1500
[[],[],[]], //1501
[[],[],[]], //1502
[[],[],[]], //1503
[[],[],[]], //1504
[[],[],[]], //1505
[[],[],[]], //1506
[[],[],[]], //1507
[[],[],[]], //1508
[[],[],[]], //1509
[[],[],[]], //1510
[[],[],[]], //1511
[[],[],[]], //1512
[[],[],[]], //1513
[[],[],[]], //1514
[[],[],[]], //1515
[[],[],[]], //1516
[[],[],[]], //1517
[[],[],[]], //1518
[[],[],[]], //1519
[[],[],[]], //1520
[[ 4 ],[ 2 ],[]], //1521
[[],[],[]], //1522
[[],[],[]], //1523
[[],[],[]], //1524
[[],[],[]], //1525
[[],[],[]], //1526
[[],[],[]], //1527
[[],[],[]], //1528
[[],[],[]], //1529
[[],[],[]], //1530
[[],[],[]], //1531
[[],[],[]], //1532
[[],[],[]], //1533
[[],[],[]], //1534
[[],[],[]], //1535
[[],[],[]], //1536
[[],[],[]], //1537
[[],[],[]], //1538
[[],[],[]], //1539
[[],[ 1, 3, 5 ],[ 1, 3, 5 ]], //1540
[[],[],[]], //1541
[[],[],[]], //1542
[[],[],[]], //1543
[[],[],[]], //1544
[[],[],[]], //1545
[[],[],[]], //1546
[[],[],[]], //1547
[[],[],[]], //1548
[[],[],[]], //1549
[[ 2, 7 ],[ 1, 5 ],[ ]], //1550
[[],[],[]], //1551
[[],[],[]], //1552
[[],[],[]], //1553
[[],[],[]], //1554
[[],[],[]], //1555
[[],[],[]], //1556
[[],[],[]], //1557
[[],[],[]], //1558
[[],[],[]], //1559
[[],[],[]], //1560
[[],[],[]], //1561
[[],[],[]], //1562
[[],[],[]], //1563
[[],[],[]], //1564
[[],[],[]], //1565
[[],[],[]], //1566
[[],[],[]], //1567
[[],[],[]], //1568
[[],[],[]], //1569
[[],[],[]], //1570
[[],[],[]], //1571
[[],[],[]], //1572
[[],[],[]], //1573
[[],[],[]], //1574
[[],[ 4 ],[ 4 ]], //1575
[[],[],[]], //1576
[[],[],[]], //1577
[[],[],[]], //1578
[[],[],[]], //1579
[[],[],[]], //1580
[[],[],[]], //1581
[[],[],[]], //1582
[[],[],[]], //1583
[[],[ 1 ],[ 1 ]], //1584
[[],[],[]], //1585
[[],[],[]], //1586
[[],[],[]], //1587
[[],[],[]], //1588
[[],[],[]], //1589
[[],[],[]], //1590
[[],[],[]], //1591
[[],[],[]], //1592
[[],[],[]], //1593
[[],[],[]], //1594
[[],[],[]], //1595
[[ 4 ],[ 1, 2, 3 ],[ 1, 2 ]], //1596
[[],[],[]], //1597
[[],[],[]], //1598
[[],[],[]], //1599
[[],[ 16, 19, 20 ],[ 16, 19, 20 ]], //1600
[[],[],[]], //1601
[[],[],[]], //1602
[[],[],[]], //1603
[[],[],[]], //1604
[[],[],[]], //1605
[[],[],[]], //1606
[[],[],[]], //1607
[[],[],[]], //1608
[[],[],[]], //1609
[[],[],[]], //1610
[[],[],[]], //1611
[[],[],[]], //1612
[[],[],[]], //1613
[[],[],[]], //1614
[[],[],[]], //1615
[[],[],[]], //1616
[[],[],[]], //1617
[[],[],[]], //1618
[[],[],[]], //1619
[[],[],[]], //1620
[[],[],[]], //1621
[[],[],[]], //1622
[[],[],[]], //1623
[[],[],[]], //1624
[[],[],[]], //1625
[[],[],[]], //1626
[[],[],[]], //1627
[[],[],[]], //1628
[[],[],[]], //1629
[[],[],[]], //1630
[[],[],[]], //1631
[[],[ 2 ],[ 2 ]], //1632
[[],[],[]], //1633
[[],[],[]], //1634
[[],[],[]], //1635
[[],[],[]], //1636
[[],[],[]], //1637
[[],[],[]], //1638
[[],[],[]], //1639
[[],[],[]], //1640
[[],[],[]], //1641
[[],[],[]], //1642
[[],[],[]], //1643
[[],[],[]], //1644
[[],[],[]], //1645
[[],[],[]], //1646
[[],[],[]], //1647
[[],[],[]], //1648
[[],[],[]], //1649
[[],[],[]], //1650
[[],[],[]], //1651
[[],[],[]], //1652
[[],[ 2 ],[ 2 ]], //1653
[[],[],[]], //1654
[[],[],[]], //1655
[[],[],[]], //1656
[[],[],[]], //1657
[[],[],[]], //1658
[[],[],[]], //1659
[[],[],[]], //1660
[[],[],[]], //1661
[[],[],[]], //1662
[[],[],[]], //1663
[[],[],[]], //1664
[[],[],[]], //1665
[[],[],[]], //1666
[[],[],[]], //1667
[[],[],[]], //1668
[[],[],[]], //1669
[[],[],[]], //1670
[[],[],[]], //1671
[[],[],[]], //1672
[[],[],[]], //1673
[[],[],[]], //1674
[[],[],[]], //1675
[[],[],[]], //1676
[[],[],[]], //1677
[[],[],[]], //1678
[[],[],[]], //1679
[[],[],[]], //1680
[[ 188, 192 ],[ 187, 191 ],[]], //1681
[[ 5 ],[ 4 ],[]], //1682
[[],[],[]], //1683
[[],[],[]], //1684
[[],[],[]], //1685
[[],[],[]], //1686
[[],[],[]], //1687
[[],[],[]], //1688
[[],[],[]], //1689
[[],[],[]], //1690
[[],[],[]], //1691
[[],[],[]], //1692
[[],[],[]], //1693
[[],[],[]], //1694
[[],[],[]], //1695
[[],[],[]], //1696
[[],[],[]], //1697
[[],[],[]], //1698
[[],[],[]], //1699
[[],[],[]], //1700
[[],[],[]], //1701
[[],[],[]], //1702
[[],[],[]], //1703
[[],[],[]], //1704
[[],[],[]], //1705
[[],[],[]], //1706
[[],[],[]], //1707
[[],[],[]], //1708
[[],[],[]], //1709
[[],[],[]], //1710
[[ 3, 5 ],[ 1, 2, 4 ],[ 1 ]], //1711
[[],[],[]], //1712
[[],[],[]], //1713
[[],[],[]], //1714
[[],[],[]], //1715
[[],[ 4 ],[ 4 ]], //1716
[[],[],[]], //1717
[[],[],[]], //1718
[[],[],[]], //1719
[[],[],[]], //1720
[[],[],[]], //1721
[[],[],[]], //1722
[[],[ 17 ],[ 17 ]], //1723
[[],[],[]], //1724
[[],[],[]], //1725
[[],[],[]], //1726
[[],[],[]], //1727
[[],[ 24 ],[ 24 ]], //1728
[[],[],[]], //1729
[[],[],[]], //1730
[[],[],[]], //1731
[[],[],[]], //1732
[[],[],[]], //1733
[[],[],[]], //1734
[[],[],[]], //1735
[[],[],[]], //1736
[[],[],[]], //1737
[[],[],[]], //1738
[[],[],[]], //1739
[[],[],[]], //1740
[[],[],[]], //1741
[[],[],[]], //1742
[[],[],[]], //1743
[[],[],[]], //1744
[[],[],[]], //1745
[[],[],[]], //1746
[[],[],[]], //1747
[[],[],[]], //1748
[[],[],[]], //1749
[[ 3 ],[ 1, 4 ],[ 4 ]], //1750
[[],[],[]], //1751
[[],[],[]], //1752
[[],[],[]], //1753
[[],[],[]], //1754
[[],[ 2 ],[ 2 ]], //1755
[[],[],[]], //1756
[[],[],[]], //1757
[[],[],[]], //1758
[[],[],[]], //1759
[[],[],[]], //1760
[[],[],[]], //1761
[[],[],[]], //1762
[[],[],[]], //1763
[[ 8 ],[],[]], //1764
[[],[],[]], //1765
[[],[],[]], //1766
[[],[],[]], //1767
[[],[],[]], //1768
[[],[],[]], //1769
[[],[ 4 ],[ 4 ]], //1770
[[],[ 2, 4 ],[ 2, 4 ]], //1771
[[],[],[]], //1772
[[],[],[]], //1773
[[],[],[]], //1774
[[],[],[]], //1775
[[],[],[]], //1776
[[],[],[]], //1777
[[],[],[]], //1778
[[],[],[]], //1779
[[],[],[]], //1780
[[],[],[]], //1781
[[ 2 ],[ 1 ],[]], //1782
[[],[],[]], //1783
[[],[],[]], //1784
[[],[ 3 ],[ 3 ]], //1785
[[],[],[]], //1786
[[],[],[]], //1787
[[],[],[]], //1788
[[],[],[]], //1789
[[],[],[]], //1790
[[],[],[]], //1791
[[],[],[]], //1792
[[],[],[]], //1793
[[],[],[]], //1794
[[],[],[]], //1795
[[],[],[]], //1796
[[],[],[]], //1797
[[],[],[]], //1798
[[],[],[]], //1799
[[ 2 ],[ 1 ],[]], //1800
[[],[],[]], //1801
[[],[],[]], //1802
[[],[],[]], //1803
[[],[],[]], //1804
[[],[],[]], //1805
[[],[],[]], //1806
[[],[],[]], //1807
[[],[],[]], //1808
[[],[],[]], //1809
[[],[],[]], //1810
[[],[],[]], //1811
[[],[],[]], //1812
[[],[],[]], //1813
[[],[],[]], //1814
[[],[],[]], //1815
[[],[],[]], //1816
[[],[],[]], //1817
[[],[],[]], //1818
[[],[],[]], //1819
[[],[ 2 ],[ 2 ]], //1820
[[],[],[]], //1821
[[],[],[]], //1822
[[],[],[]], //1823
[[],[],[]], //1824
[[],[],[]], //1825
[[],[],[]], //1826
[[],[],[]], //1827
[[],[],[]], //1828
[[],[],[]], //1829
[[ 2, 4 ],[ 1, 3 ],[]], //1830
[[],[],[]], //1831
[[],[],[]], //1832
[[],[],[]], //1833
[[],[],[]], //1834
[[],[],[]], //1835
[[],[],[]], //1836
[[],[],[]], //1837
[[],[],[]], //1838
[[],[],[]], //1839
[[],[],[]], //1840
[[],[],[]], //1841
[[],[],[]], //1842
[[],[],[]], //1843
[[],[],[]], //1844
[[],[],[]], //1845
[[],[],[]], //1846
[[],[],[]], //1847
[[],[],[]], //1848
[[ 126, 130 ],[ 125, 128 ],[]], //1849
[[ 5 ],[ 3 ],[]], //1850
[[],[],[]], //1851
[[],[],[]], //1852
[[],[],[]], //1853
[[],[],[]], //1854
[[],[],[]], //1855
[[],[],[]], //1856
[[],[],[]], //1857
[[],[],[]], //1858
[[],[],[]], //1859
[[],[],[]], //1860
[[],[],[]], //1861
[[],[],[]], //1862
[[],[],[]], //1863
[[],[],[]], //1864
[[],[],[]], //1865
[[],[],[]], //1866
[[],[],[]], //1867
[[],[],[]], //1868
[[],[],[]], //1869
[[],[],[]], //1870
[[],[],[]], //1871
[[],[],[]], //1872
[[],[],[]], //1873
[[],[],[]], //1874
[[],[],[]], //1875
[[],[],[]], //1876
[[],[],[]], //1877
[[],[],[]], //1878
[[],[],[]], //1879
[[],[],[]], //1880
[[],[],[]], //1881
[[],[],[]], //1882
[[],[],[]], //1883
[[],[],[]], //1884
[[],[],[]], //1885
[[],[],[]], //1886
[[],[],[]], //1887
[[],[],[]], //1888
[[],[],[]], //1889
[[],[],[]], //1890
[[],[ 1, 5 ],[ 1, 5 ]], //1891
[[],[],[]], //1892
[[],[ 2 ],[ 2 ]], //1893
[[],[],[]], //1894
[[],[],[]], //1895
[[],[],[]], //1896
[[],[],[]], //1897
[[],[],[]], //1898
[[],[],[]], //1899
[[],[],[]], //1900
[[],[],[]], //1901
[[],[],[]], //1902
[[],[],[]], //1903
[[],[],[]], //1904
[[],[],[]], //1905
[[],[],[]], //1906
[[],[],[]], //1907
[[],[],[]], //1908
[[],[],[]], //1909
[[],[],[]], //1910
[[],[],[]], //1911
[[],[],[]], //1912
[[],[],[]], //1913
[[],[],[]], //1914
[[],[],[]], //1915
[[],[],[]], //1916
[[],[],[]], //1917
[[],[],[]], //1918
[[],[],[]], //1919
[[],[],[]], //1920
[[],[],[]], //1921
[[],[],[]], //1922
[[],[],[]], //1923
[[],[],[]], //1924
[[],[],[]], //1925
[[],[],[]], //1926
[[],[],[]], //1927
[[],[],[]], //1928
[[],[],[]], //1929
[[],[],[]], //1930
[[],[],[]], //1931
[[],[],[]], //1932
[[],[],[]], //1933
[[],[],[]], //1934
[[],[],[]], //1935
[[],[ 8 ],[ 8 ]], //1936
[[],[],[]], //1937
[[],[],[]], //1938
[[],[],[]], //1939
[[],[],[]], //1940
[[],[],[]], //1941
[[],[],[]], //1942
[[],[],[]], //1943
[[],[],[]], //1944
[[],[],[]], //1945
[[],[],[]], //1946
[[],[],[]], //1947
[[],[],[]], //1948
[[],[],[]], //1949
[[],[],[]], //1950
[[],[],[]], //1951
[[],[],[]], //1952
[[ 1, 3 ],[ 2 ],[]], //1953
[[],[],[]], //1954
[[],[],[]], //1955
[[],[],[]], //1956
[[],[],[]], //1957
[[],[],[]], //1958
[[],[],[]], //1959
[[],[],[]], //1960
[[],[],[]], //1961
[[],[],[]], //1962
[[],[],[]], //1963
[[],[],[]], //1964
[[],[],[]], //1965
[[],[],[]], //1966
[[],[],[]], //1967
[[],[],[]], //1968
[[],[],[]], //1969
[[],[],[]], //1970
[[],[],[]], //1971
[[],[],[]], //1972
[[],[],[]], //1973
[[],[],[]], //1974
[[],[],[]], //1975
[[],[],[]], //1976
[[],[],[]], //1977
[[],[],[]], //1978
[[],[],[]], //1979
[[],[],[]], //1980
[[],[],[]], //1981
[[],[],[]], //1982
[[],[],[]], //1983
[[],[],[]], //1984
[[],[],[]], //1985
[[],[],[]], //1986
[[],[],[]], //1987
[[],[],[]], //1988
[[],[],[]], //1989
[[],[],[]], //1990
[[],[],[]], //1991
[[],[],[]], //1992
[[],[],[]], //1993
[[],[],[]], //1994
[[],[],[]], //1995
[[],[],[]], //1996
[[],[],[]], //1997
[[],[],[]], //1998
[[],[],[]], //1999
[[],[],[]], //2000
[[],[],[]], //2001
[[ 2 ],[ 1 ],[]], //2002
[[],[],[]], //2003
[[],[],[]], //2004
[[],[],[]], //2005
[[],[],[]], //2006
[[],[],[]], //2007
[[],[],[]], //2008
[[],[],[]], //2009
[[],[],[]], //2010
[[],[],[]], //2011
[[],[],[]], //2012
[[],[],[]], //2013
[[],[],[]], //2014
[[],[ 2 ],[ 2 ]], //2015
[[],[ 16, 18 ],[ 16, 18 ]], //2016
[[],[],[]], //2017
[[],[],[]], //2018
[[],[],[]], //2019
[[],[],[]], //2020
[[],[],[]], //2021
[[],[],[]], //2022
[[],[],[]], //2023
[[ 3 ],[ 2 ],[]], //2024
[[ 32, 33 ],[ 30, 34 ],[ 34 ]], //2025
[[],[],[]], //2026
[[],[],[]], //2027
[[],[],[]], //2028
[[],[],[]], //2029
[[],[],[]], //2030
[[],[],[]], //2031
[[],[],[]], //2032
[[],[],[]], //2033
[[],[],[]], //2034
[[],[],[]], //2035
[[],[],[]], //2036
[[],[],[]], //2037
[[],[],[]], //2038
[[],[],[]], //2039
[[],[],[]], //2040
[[],[],[]], //2041
[[],[],[]], //2042
[[],[],[]], //2043
[[],[],[]], //2044
[[],[],[]], //2045
[[],[],[]], //2046
[[],[ 1 ],[ 1 ]], //2047
[[],[ 12 ],[ 12 ]], //2048
[[],[ 2 ],[ 2 ]], //2049
[[],[],[]], //2050
[[],[],[]], //2051
[[],[],[]], //2052
[[],[],[]], //2053
[[],[],[]], //2054
[[],[],[]], //2055
[[],[],[]], //2056
[[],[],[]], //2057
[[ 2 ],[ 1 ],[]], //2058
[[],[],[]], //2059
[[],[],[]], //2060
[[],[],[]], //2061
[[],[],[]], //2062
[[],[],[]], //2063
[[],[],[]], //2064
[[],[],[]], //2065
[[],[],[]], //2066
[[],[],[]], //2067
[[],[],[]], //2068
[[],[],[]], //2069
[[],[],[]], //2070
[[],[],[]], //2071
[[],[],[]], //2072
[[],[],[]], //2073
[[],[],[]], //2074
[[],[],[]], //2075
[[],[],[]], //2076
[[],[],[]], //2077
[[],[],[]], //2078
[[],[ 2 ],[ 2 ]], //2079
[[ 17 ],[ 15, 16 ],[ 15 ]], //2080
[[],[],[]], //2081
[[],[],[]], //2082
[[],[],[]], //2083
[[],[],[]], //2084
[[],[],[]], //2085
[[],[],[]], //2086
[[],[],[]], //2087
[[],[],[]], //2088
[[],[],[]], //2089
[[],[],[]], //2090
[[],[],[]], //2091
[[],[],[]], //2092
[[],[],[]], //2093
[[],[],[]], //2094
[[],[],[]], //2095
[[],[],[]], //2096
[[],[],[]], //2097
[[],[],[]], //2098
[[],[],[]], //2099
[[],[],[]], //2100
[[],[],[]], //2101
[[],[],[]], //2102
[[],[],[]], //2103
[[],[],[]], //2104
[[],[],[]], //2105
[[ 5 ],[ 4 ],[]], //2106
[[ 2 ],[ 1 ],[]], //2107
[[],[],[]], //2108
[[ 2 ],[ 1 ],[]], //2109
[[],[],[]], //2110
[[],[],[]], //2111
[[],[],[]], //2112
[[],[],[]], //2113
[[],[],[]], //2114
[[],[],[]], //2115
[[ 4 ],[],[]], //2116
[[],[],[]], //2117
[[],[],[]], //2118
[[],[],[]], //2119
[[],[],[]], //2120
[[],[],[]], //2121
[[],[],[]], //2122
[[],[],[]], //2123
[[],[],[]], //2124
[[],[],[]], //2125
[[],[],[]], //2126
[[],[],[]], //2127
[[],[],[]], //2128
[[],[],[]], //2129
[[],[],[]], //2130
[[],[],[]], //2131
[[],[],[]], //2132
[[],[],[]], //2133
[[],[],[]], //2134
[[],[],[]], //2135
[[],[],[]], //2136
[[],[],[]], //2137
[[],[],[]], //2138
[[],[],[]], //2139
[[],[],[]], //2140
[[],[],[]], //2141
[[],[],[]], //2142
[[],[],[]], //2143
[[],[],[]], //2144
[[],[ 2 ],[ 2 ]], //2145
[[],[],[]], //2146
[[],[],[]], //2147
[[],[],[]], //2148
[[],[],[]], //2149
[[],[],[]], //2150
[[],[],[]], //2151
[[],[],[]], //2152
[[],[],[]], //2153
[[],[],[]], //2154
[[],[],[]], //2155
[[],[],[]], //2156
[[],[],[]], //2157
[[],[],[]], //2158
[[],[],[]], //2159
[[],[],[]], //2160
[[],[],[]], //2161
[[],[ 1 ],[ 1 ]], //2162
[[],[],[]], //2163
[[],[],[]], //2164
[[],[],[]], //2165
[[],[],[]], //2166
[[],[],[]], //2167
[[],[],[]], //2168
[[],[],[]], //2169
[[],[],[]], //2170
[[],[],[]], //2171
[[],[],[]], //2172
[[],[],[]], //2173
[[],[],[]], //2174
[[],[],[]], //2175
[[],[],[]], //2176
[[],[],[]], //2177
[[],[],[]], //2178
[[],[],[]], //2179
[[],[],[]], //2180
[[],[],[]], //2181
[[],[],[]], //2182
[[],[],[]], //2183
[[],[],[]], //2184
[[],[],[]], //2185
[[],[],[]], //2186
[[ 71 ],[ 70 ],[]], //2187
[[ 4 ],[ 3 ],[]], //2188
[[],[],[]], //2189
[[],[],[]], //2190
[[],[],[]], //2191
[[],[],[]], //2192
[[],[],[]], //2193
[[],[],[]], //2194
[[],[],[]], //2195
[[],[],[]], //2196
[[ 158, 170 ],[ 157, 169 ],[]], //2197
[[ 6 ],[ 2, 5 ],[ 2 ]], //2198
[[],[],[]], //2199
[[],[],[]], //2200
[[],[],[]], //2201
[[],[],[]], //2202
[[],[],[]], //2203
[[],[],[]], //2204
[[],[],[]], //2205
[[],[],[]], //2206
[[],[],[]], //2207
[[],[],[]], //2208
[[ 70, 74 ],[ 69, 73 ],[]], //2209
[[ 5 ],[ 3 ],[]], //2210
[[ 2, 4 ],[ 1, 3 ],[]], //2211
[[],[],[]], //2212
[[],[],[]], //2213
[[],[],[]], //2214
[[],[],[]], //2215
[[],[],[]], //2216
[[],[],[]], //2217
[[],[],[]], //2218
[[],[],[]], //2219
[[],[],[]], //2220
[[],[],[]], //2221
[[],[],[]], //2222
[[],[],[]], //2223
[[],[],[]], //2224
[[],[],[]], //2225
[[],[],[]], //2226
[[],[],[]], //2227
[[],[],[]], //2228
[[],[],[]], //2229
[[],[],[]], //2230
[[],[],[]], //2231
[[],[],[]], //2232
[[],[],[]], //2233
[[],[],[]], //2234
[[],[],[]], //2235
[[],[],[]], //2236
[[],[],[]], //2237
[[],[],[]], //2238
[[],[],[]], //2239
[[],[],[]], //2240
[[],[],[]], //2241
[[],[],[]], //2242
[[],[],[]], //2243
[[],[],[]], //2244
[[],[],[]], //2245
[[],[],[]], //2246
[[],[],[]], //2247
[[],[],[]], //2248
[[],[],[]], //2249
[[],[],[]], //2250
[[],[],[]], //2251
[[],[],[]], //2252
[[],[],[]], //2253
[[],[],[]], //2254
[[],[],[]], //2255
[[],[],[]], //2256
[[],[ 1 ],[ 1 ]], //2257
[[],[],[]], //2258
[[],[],[]], //2259
[[],[],[]], //2260
[[],[],[]], //2261
[[],[],[]], //2262
[[],[],[]], //2263
[[],[],[]], //2264
[[],[],[]], //2265
[[],[],[]], //2266
[[],[],[]], //2267
[[],[],[]], //2268
[[],[],[]], //2269
[[],[],[]], //2270
[[],[],[]], //2271
[[],[],[]], //2272
[[],[],[]], //2273
[[],[],[]], //2274
[[],[],[]], //2275
[[],[],[]], //2276
[[],[],[]], //2277
[[],[ 4 ],[ 4 ]], //2278
[[],[],[]], //2279
[[],[],[]], //2280
[[],[],[]], //2281
[[],[],[]], //2282
[[],[],[]], //2283
[[],[],[]], //2284
[[],[],[]], //2285
[[],[],[]], //2286
[[],[],[]], //2287
[[],[],[]], //2288
[[],[],[]], //2289
[[],[],[]], //2290
[[],[],[]], //2291
[[],[],[]], //2292
[[],[],[]], //2293
[[],[],[]], //2294
[[],[ 2 ],[ 2 ]], //2295
[[],[],[]], //2296
[[],[],[]], //2297
[[],[],[]], //2298
[[],[],[]], //2299
[[ 3 ],[ 1, 2 ],[ 1 ]], //2300
[[],[],[]], //2301
[[],[],[]], //2302
[[],[],[]], //2303
[[],[ 8, 10 ],[ 8, 10 ]], //2304
[[],[],[]], //2305
[[],[],[]], //2306
[[],[],[]], //2307
[[],[],[]], //2308
[[],[],[]], //2309
[[],[],[]], //2310
[[],[],[]], //2311
[[],[],[]], //2312
[[],[],[]], //2313
[[],[],[]], //2314
[[],[],[]], //2315
[[],[],[]], //2316
[[],[],[]], //2317
[[],[],[]], //2318
[[],[],[]], //2319
[[],[],[]], //2320
[[],[],[]], //2321
[[],[],[]], //2322
[[],[],[]], //2323
[[],[],[]], //2324
[[],[],[]], //2325
[[],[],[]], //2326
[[],[],[]], //2327
[[],[],[]], //2328
[[],[],[]], //2329
[[],[],[]], //2330
[[],[],[]], //2331
[[],[],[]], //2332
[[],[],[]], //2333
[[],[],[]], //2334
[[],[],[]], //2335
[[],[],[]], //2336
[[],[],[]], //2337
[[],[],[]], //2338
[[],[],[]], //2339
[[],[],[]], //2340
[[],[],[]], //2341
[[],[],[]], //2342
[[],[],[]], //2343
[[],[],[]], //2344
[[],[],[]], //2345
[[ 2 ],[ 1 ],[]], //2346
[[],[],[]], //2347
[[],[],[]], //2348
[[],[],[]], //2349
[[],[],[]], //2350
[[],[],[]], //2351
[[],[],[]], //2352
[[],[],[]], //2353
[[],[],[]], //2354
[[],[],[]], //2355
[[],[],[]], //2356
[[],[],[]], //2357
[[],[],[]], //2358
[[],[],[]], //2359
[[],[],[]], //2360
[[],[],[]], //2361
[[],[],[]], //2362
[[],[],[]], //2363
[[],[],[]], //2364
[[],[],[]], //2365
[[],[],[]], //2366
[[],[],[]], //2367
[[],[],[]], //2368
[[],[],[]], //2369
[[],[],[]], //2370
[[],[],[]], //2371
[[],[],[]], //2372
[[],[],[]], //2373
[[],[],[]], //2374
[[],[],[]], //2375
[[],[],[]], //2376
[[],[],[]], //2377
[[],[],[]], //2378
[[],[],[]], //2379
[[ 4, 6, 9 ],[ 2, 5, 8 ],[]], //2380
[[],[],[]], //2381
[[],[],[]], //2382
[[],[],[]], //2383
[[],[],[]], //2384
[[],[],[]], //2385
[[],[],[]], //2386
[[],[],[]], //2387
[[],[],[]], //2388
[[],[],[]], //2389
[[],[],[]], //2390
[[],[],[]], //2391
[[],[],[]], //2392
[[],[],[]], //2393
[[],[],[]], //2394
[[],[],[]], //2395
[[],[],[]], //2396
[[],[],[]], //2397
[[],[],[]], //2398
[[],[],[]], //2399
[[],[],[]], //2400
[[1179,1229,1233],[1178,1226,1232],[]], //2401
[[ 8 ],[ 6 ],[]], //2402
[[],[],[]], //2403
[[],[],[]], //2404
[[],[],[]], //2405
[[],[],[]], //2406
[[],[],[]], //2407
[[],[],[]], //2408
[[],[],[]], //2409
[[],[],[]], //2410
[[],[],[]], //2411
[[],[],[]], //2412
[[],[],[]], //2413
[[],[],[]], //2414
[[],[ 2 ],[ 2 ]], //2415
[[],[],[]], //2416
[[],[],[]], //2417
[[],[],[]], //2418
[[],[],[]], //2419
[[],[],[]], //2420
[[],[],[]], //2421
[[],[],[]], //2422
[[],[],[]], //2423
[[],[],[]], //2424
[[],[],[]], //2425
[[],[],[]], //2426
[[],[],[]], //2427
[[],[],[]], //2428
[[],[],[]], //2429
[[],[],[]], //2430
[[],[],[]], //2431
[[],[],[]], //2432
[[],[],[]], //2433
[[],[],[]], //2434
[[],[],[]], //2435
[[],[],[]], //2436
[[],[],[]], //2437
[[],[],[]], //2438
[[],[],[]], //2439
[[],[ 2 ],[ 2 ]], //2440
[[],[],[]], //2441
[[],[],[]], //2442
[[],[],[]], //2443
[[],[],[]], //2444
[[],[],[]], //2445
[[],[],[]], //2446
[[],[],[]], //2447
[[ 5 ],[ 2 ],[]], //2448
[[],[],[]], //2449
[[],[],[]], //2450
[[ 4 ],[ 3 ],[]], //2451
[[],[],[]], //2452
[[],[],[]], //2453
[[],[],[]], //2454
[[],[],[]], //2455
[[],[],[]], //2456
[[],[ 2 ],[ 2 ]], //2457
[[],[],[]], //2458
[[],[],[]], //2459
[[],[],[]], //2460
[[],[],[]], //2461
[[],[],[]], //2462
[[],[],[]], //2463
[[],[],[]], //2464
[[],[ 2 ],[ 2 ]], //2465
[[],[],[]], //2466
[[],[],[]], //2467
[[],[],[]], //2468
[[],[],[]], //2469
[[],[],[]], //2470
[[],[],[]], //2471
[[],[],[]], //2472
[[],[],[]], //2473
[[],[],[]], //2474
[[],[],[]], //2475
[[],[],[]], //2476
[[],[],[]], //2477
[[],[],[]], //2478
[[],[],[]], //2479
[[],[],[]], //2480
[[],[],[]], //2481
[[],[],[]], //2482
[[],[],[]], //2483
[[],[],[]], //2484
[[ 2, 4 ],[ 1, 3 ],[]], //2485
[[],[],[]], //2486
[[],[],[]], //2487
[[],[],[]], //2488
[[],[],[]], //2489
[[],[],[]], //2490
[[],[],[]], //2491
[[],[],[]], //2492
[[],[],[]], //2493
[[],[],[]], //2494
[[],[],[]], //2495
[[],[],[]], //2496
[[],[],[]], //2497
[[],[],[]], //2498
[[],[],[]]  //2499
];
if sym then
    subs := [PrimitiveGroup(n,d) : d in maxprim[n][1]];
else 
    x:=Sym(n)!(1,2);
    subs := [ ];
    for d in maxprim[n][2] do
        P:=PrimitiveGroup(n,d);
        Append(~subs,P);
        if d in maxprim[n][3] then
            Append(~subs,P^x);
        end if;
    end for;
end if;

/***************************************************
 *Finally we deal with the generic cases. AGL(1, p) is
 *always Sym(p) maximal if p gt 24, with its normal subgroup
 *of index 2 being alt maximal.
 *PGL(2, p) is always Sym(p+1) maximal for p gt 23 (so 
 *degree gt 24), with PSL(2, p) being
 *alt(p+1) maximal.
 ***************************************************/
   
if n gt 23 and IsPrime(n) then
    if sym then
       Append(~subs, AGL(1, n));
    else
       Append(~subs, PrimitiveGroup(n, #Divisors(n-1) -1));
                 /*This is n:((n-1)/2)*/
    end if;
end if;
if n gt 24 and IsPrime(n-1) then
    if sym then
       Append(~subs, PGL(2, n-1));
    else
       Append(~subs, PSL(2, n-1));
    end if;
end if;

return subs;
end function;

intrinsic IdentifyAlmostSimpleGroup(G :: GrpPerm : Print := 0) -> Map, GrpPerm
{Look up G in the database of almost simple groups};

    phi, I := IdentifyAlmostSimpleGroupH(SolubleResidual(G), G, Print);
    return phi, I;
 
end intrinsic;

intrinsic IdentifyAlmostSimpleGroup(G :: GrpMat : Print := 0) -> Map, GrpPerm
{Look up G in the database of almost simple groups};

    phi, I := IdentifyAlmostSimpleGroupH(SolubleResidual(G), G, Print);
    return phi, I;
 
end intrinsic;

IdentifyAltSymNatural:= function(G,n,sym,pt,printlevel:max:=true)
  if printlevel gt 2 then
    print "    +Identifying AltSym by natural action";
  end if;
  if n le 8 then
    error "Use IdentifyAltSymNatural only for degree at least 9";
  end if;

  S := OrbitImage(G, pt);
  assert Degree(S) eq n;
  assert Ngens(S) eq Ngens(G);
  SS := StandardGroup(S);
  assert Degree(SS) eq n;
  assert Ngens(SS) eq Ngens(G);

/* Changed by DFH - the functions must have codomain Aut(S) for simple
 * groups S, and the generators of S must come first.
 */
  SSS:= sub<Sym(n) | Alt(n), (1,2)>;
  SSS`Order := Factorial(n);
/*
  SSS:=sub< SS | Alt(n) >; // we want alternating generators first.
  if sym then
    SSS:= sub<SS | SSS, (1,2)>;
    SSS`Order := Factorial(n);
  else
    SSS`Order := Factorial(n) div 2;
  end if;
*/

  if printlevel gt 2 then
    print "    +Completed identification - getting maximal subgroups";
  end if;

  subs := max select IntransitiveSubgroupsAltSym(n,sym) cat
          ImprimitiveSubgroupsAltSym(n,sym) cat
          PrimitiveSubgroupsAltSym(n,sym) else [];

//DFH changed iso to hom below
  return  hom< G->SSS | [SS.i : i in [1..Ngens(G)]] >, SSS, subs;
end function;

ActionOnOrbitsU := function(G, K)
    orbs := Orbits(K);
    d := Degree(G);
    norbs := #orbs;
    orbit_num := [];
    orbit_rep := [];
    L := Labelling(G);
    for i := 1 to norbs do
	orb := orbs[i];
	orbit_rep[i] := Rep(orb);
	for j in orb do
	    orbit_num[Index(L, j)] := i;
	end for;
    end for;
    S := Sym(norbs);
    images := [S|];
    for i := 1 to Ngens(G) do
	g := G.i;
	im := [orbit_num[Index(L, orbit_rep[j]^g)] : j in [1..norbs]];
	Append(~images, im);
    end for;
    I := sub<S|images>;
    f := hom<G->I|images>;
    return f, I;
end function;
