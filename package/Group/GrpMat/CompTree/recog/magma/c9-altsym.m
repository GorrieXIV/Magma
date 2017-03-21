/******************************************************************************
 *
 *    c9-altsym.m recognise C9 group which mod scalars is isomorphic to Alt(n) 
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Derek Holt, Eamonn O'Brien and Henrik B‰‰rnhielm
 *    Dev start : 2008-04-26
 *
 *    Version   : $Revision:: 1941                                           $:
 *    Date      : $Date:: 2010-09-04 07:15:55 +1000 (Sat, 04 Sep 2010)       $:
 *    Last edit : $Author:: dfh
 *
 *    $Id:: c9-altsym.m 1941 2010-09-03 21:15:55Z jbaa004                 $:
 *
 *****************************************************************************/

freeze;

/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

forward C9IdentifyAlternatingPermutation;

import "../../GrpMat/util/order.m": MyCentralOrder;

declare attributes Grp : AltSymData;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

C9IdentifyAlternatingGroup := function(G,n:maxtries:=100*n+5000)
local seeking, g, wg, g1, wg1, g2, wg2, f, t, wt, o, x, wx, l, wl, P, st, sl,
      WP, S;
  if n le 8 then
    error "Use IdentifyAlternatingGroup only for degree at least 9";
  end if;
  WP := RandomProcessWithWords(G);
  if n mod 2 eq 0 then
  //first seek Goldbach element.
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      g,wg:=Random(WP);
      f:=Factorisation(MyCentralOrder(G,g));
   if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n-2 then
        seeking:=false;
        g1:=g^(2*f[2][1]); wg1:=wg^(2*f[2][1]);
        g2:=g^(2*f[1][1]); wg2:=wg^(2*f[1][1]);
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
    //next a 3-cycle
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      t,wt:=Random(WP);
      o:=MyCentralOrder(G,t);
      f:=Factorisation(o);
      if (n eq 10 and o eq 21) or (n eq 12 and o eq 21) or (n eq 14 and o eq 33)
       or (n eq 16 and o eq 39) or (n eq 18 and o eq 39) or
         (o ge 20 and #f eq 3 and f[1][1] eq 3 and f[1][2] eq 1 and
          f[2][2] eq 1 and f[3][2] eq 1 and f[2][1]+f[3][1]+4 eq n) then
        seeking:=false;
        t := t^(o div 3); wt := wt^(o div 3);
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
   
    //get a conjugate commuting with neither g1 nor g2
    //and touching one of the fixed points.
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      x,wx:=Random(WP);
      t:=t^x; wt:=wt^wx;
      if not IsCentral(G, (t,g1)) and not IsCentral(G, (t,g2)) and
         not IsCentral(G, (t^g1,t^g2)) and not IsCentral(G, (t^g1,t^(g2^2))) and
         not IsCentral(G, (t^(g1^2),t^g2)) and MyCentralOrder(G,t*t^g1) eq 2 then
  // The final condition rules out CentralOrder(g1)=3 and t touches g1 twice.
        seeking:=false;
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
  //now an (n-1)-cycle - we have to find out whether we want g1*t*g2 or g2*t*g1
    l := g1*t*g2; wl:=wg1*wt*wg2;
    if MyCentralOrder(G,t*t^l) ne 2 then
      l := g2*t*g1; wl:=wg2*wt*wg1;
    end if;
  
  //now a conjugate of t commuting with t and fixing the other fixed point of g
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      x,wx:=Random(WP);
      u:=t^x; wu:=wt^wx;
      if not IsCentral(G, (u,g1)) and not IsCentral(G, (u,g2)) and
         not IsCentral(G, (u^g1,u^g2)) and not IsCentral(G, (u^g1,u^(g2^2))) and
         not IsCentral(G, (u^(g1^2),u^g2)) and MyCentralOrder(G, u*u^g1) eq 2 and
         not IsCentral(G, t*u^-1) and not IsCentral(G, t*u^-2) and IsCentral(G, (t,u)) then
        seeking:=false;
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
    //conjugate t until it does not commute with u
    ct:=0;
    while IsCentral(G, (t,u)) and ct lt maxtries do
      ct+:=1;t:=t^l; wt:=wt^wl;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
    //Now either t^u or t^(u^-1) is a suitable 3-cycle.
    if MyCentralOrder(G,t^u*t^(u*l)) eq 3 then t:=t^u; wt:=wt^wu;
    else t:=t^(u^-1); wt:=wt^(wu^-1);
    end if;
  else
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      g,wg:=Random(WP);
      f:=Factorisation(MyCentralOrder(G,g));
   if #f eq 2 and f[1][2] eq 1 and f[2][2] eq 1 and f[1][1]+f[2][1] eq n-1 then
        seeking:=false;
        g1:=g^(2*f[2][1]); wg1:=wg^(2*f[2][1]);
        g2:=g^(2*f[1][1]); wg2:=wg^(2*f[1][1]);
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
    //next a 3-cycle
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      t,wt:=Random(WP);
      o:=MyCentralOrder(G,t);
      f:=Factorisation(o);
      
      if (n eq 9 and o eq 15) or (n eq 11 and o eq 21) or (n eq 13 and o eq 24)
       or (n eq 15 and o eq 105) or (n eq 17 and o eq 39) or
         (o ge 19 and #f eq 3 and f[1][1] eq 3 and f[1][2] eq 1 and
          f[2][2] eq 1 and f[3][2] eq 1 and f[2][1]+f[3][1]+3 eq n) then
        seeking:=false;
        t := t^(o div 3); wt:=wt^(o div 3);
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
   
    //get a conjugate commuting with neither g1 nor g2
    //and touching the fixed point.
    seeking:=true;
    ct := 0;    
    while seeking and ct lt maxtries do
      ct+:=1;
      x,wx:=Random(WP);
      t:=t^x; wt:=wt^wx;
      if not IsCentral(G, (t,g1)) and not IsCentral(G, (t,g2)) and
      not IsCentral(G, (t^g1,t^g2)) and not IsCentral(G, (t^g1,t^(g2^2))) 
      and not IsCentral(G, (t^(g1^2),t^g2)) and 
      MyCentralOrder(G, t*t^g1) eq 2 then
  //The final condition rules out CentralOrder(g1)=3 and t touches g1 twice.
        seeking:=false;
      end if;
    end while;
    if ct ge maxtries then return false,_,_,_,_;end if;
  
 //finally an n- or (n-1)-cycle - we have to find out whether we want
  //g1*t*g2 or g2*t*g1
    l := g1*t*g2; wl:=wg1*wt*wg2;
    if MyCentralOrder(G,t*t^l) ne 2 then
      l := g2*t*g1; wl:=wg2*wt*wg1;
    end if;
  end if;

  return  true,t,l,wt,wl;
end function;

C9ImageOfAlternatingPermutation := function(perm,t,l,n)
/* perm is an element of Alt(n). t,l are as returned by
 * IdentifyAlternatingGroup.
 * Return g and word, where g is element of G corresponding to perm, and
 * word is SLP word for perm in generators (1,2), (1,2,...,n) of Sym(n).
 */
  local G, F, wt, wl, yes, permb, w, phi;
  G := Alt(n);
  G := n mod 2 eq 0 select sub< G | (1,2,3), [1] cat [3..n] cat [2] >
                      else sub< G | (1,2,3), [2..n] cat [1] >;
  F := SLPGroup(2);
  wt := F.1; wl := F.2;
  yes, permb, w := C9IdentifyAlternatingPermutation(Parent (perm),perm,G.1,G.2,wt,wl,n);
  if yes ne true then
    vprintf IsAltsym: "Permutation not in Alt(n)";
     return false,_,_;
  end if;
  if perm ne permb then
    vprintf IsAltsym: "Permutations do not correspond";
    return false,_,_;
  end if;
  return true, Evaluate(w, [t,l]), w;
end function;

C9FindThreeCycles := function(t,l,wt,wl,n)
/* t should be the element (1,2,3) and l the element (1,2,...,n) (n odd)
 * or (2,3,...,n) (n even) in a group isomorphic to Alt(n). Return
 * the list [(1,2,3),(2,3,4),...,(n-2,n-1,n),(n-1,n,1),(n,1,2)]
 * Return also SLPs in original generators and in wt, wl.
 */
 local a,b,c,wa,wb,wc,wan,wbn,wcn;
 //This is easier if n is odd.
 sg := SLPGroup(2);
 wtn := sg.1; wln := sg.2;
 if n mod 2 eq 1 then
   res := [t];  x := t; res_w := [wt]; wx := wt; res_wn := [wtn]; wxn := wtn;
   for i := 1 to n-1 do
      x := x^l; wx := wx^wl; wxn := wxn^wln;
      Append(~res, x); Append(~res_w, wx); Append(~res_wn, wxn);
   end for;
   return res, res_w, res_wn;
   /* return [t^(l^i) : i in [0..n-1]],
      [wt^(wl^i) : i in [0..n-1]], [wtn^(wln^i) : i in [0..n-1]]; */
 else
   a := (t^-1)^(t^l); wa := (wt^-1)^(wt^wl); wan := (wtn^-1)^(wtn^wln);
                                                                   //(2,3,4)
   b := (t^-1)^(l^-1); wb := (wt^-1)^(wl^-1); wbn := (wtn^-1)^(wln^-1);
                                                                  //(n,1,2)
   c := t^(l^-2); wc := wt^(wl^-2);  wcn := wtn^(wln^-2);//(n-1,n,1)
   res := [t, a]; x := a;
   res_w := [wt, wa]; wx := wa; res_wn := [wtn, wan]; wxn := wan;
   for i := 1 to n-4 do
      x := x^l; wx := wx^wl; wxn := wxn^wln;
      Append(~res, x); Append(~res_w, wx); Append(~res_wn, wxn);
   end for;
   return res cat [c,b], res_w cat [wc,wb], res_wn cat [wcn,wbn];

   /* return [t] cat [a^(l^i) : i in [0..n-4]] cat [c] cat [b],
          [wt] cat [wa^(wl^i) : i in [0..n-4]] cat [wc] cat [wb],
        [wtn] cat [wan^(wln^i) : i in [0..n-4]] cat [wcn] cat [wbn]; */
 end if;
end function;

//a mod n in the range [1..n]
MM := func< a,n | (a-1) mod n  + 1 >;

C9IdentifyTriple := function(G,g,tl,n)

/* g is a 3-cycle (a,b,c) in (2.)Alt(n) and tl is the list returned by
 * FindThreeCycles. Calculate and return {a,b,c}.
 * This works only for n>=10.
 */
  local il,f,a,b,c;

  //First find which elements of tl have cycles intersecting that of g
  //These are those which do not commute with g, or else equal g or g^-1.

  il := [ i : i in [1..n] | not IsCentral(G, (g,tl[i])) or 
          IsCentral(G, tl[i]*g^-1) or IsCentral(G, tl[i]*g)];

  ilc := [i : i in [1..n] | not i in il ];
  if #il eq 0 or #il gt 9 then return {}; end if;
  if #il eq 9 then 
    if n eq 9 then // 3 possibilities, {1,4,7}, {2,5,8}, {3,6,9}
      if   MyCentralOrder(G, g*tl[1]*tl[2]) eq 5 then a:=1; b:=4; c:=7;
      elif MyCentralOrder(G, g*tl[2]*tl[3]) eq 5 then a:=2; b:=5; c:=8;
      else  a:=3; b:=6; c:=9;
      end if;
    //otherwise there must be 3 sets of consecutive triples mod n - find them
    else
      f := MM( Min( ilc ) + 1, n);
      while not f in il do f := MM(f+1,n); end while;
      a := MM(f+2,n); f := MM(f+3,n);
      while not f in il do f := MM(f+1,n); end while;
      b := MM(f+2,n); f := MM(f+3,n);
      while not f in il do f := MM(f+1,n); end while;
      c := MM(f+2,n);
    end if;
  elif #il eq 8 then
    //Either 8 in a row, or separate sequences of lengths 3 and 5
    f := MM( Min( ilc ) + 1, n);
    while not f in il do f := MM(f+1,n); end while;
    if not MM(f+3,n) in il then // group of 3
      a := MM(f+2,n); f := MM(f+3,n);
      while not f in il do f := MM(f+1,n); end while;
      b := MM(f+2,n); c := MM(f+4,n);
    elif not MM(f+5,n) in il then // group of 5
      a := MM(f+2,n); b := MM(f+4,n); f := MM(f+5,n);
      while not f in il do f := MM(f+1,n); end while;
      c := MM(f+2,n);
    else //8 in a row - two possibilities!
      if MyCentralOrder(G, g*tl[MM(f+2,n)]) eq 5 then
        a:=MM(f+2,n); b:=MM(f+5,n); c:=MM(f+7,n);
      else a:=MM(f+2,n); b:=MM(f+4,n); c:=MM(f+7,n);
      end if;
    end if;
  elif #il eq 7 then
    //Either 7 in a row, or separate sequences of lengths 3 and 4
    f := MM( Min([i : i in [1..n] | not i in il ]) + 1, n);
    while not f in il do f := MM(f+1,n); end while;
    if not MM(f+3,n) in il then // group of 3
      a := MM(f+2,n); f := MM(f+3,n);
      while not f in il do f := MM(f+1,n); end while;
      b := MM(f+2,n); c := MM(f+3,n);
    elif not MM(f+4,n) in il then // group of 4
      a := MM(f+2,n); b := MM(f+3,n); f := MM(f+4,n);
      while not f in il do f := MM(f+1,n); end while;
      c := MM(f+2,n);
    else // 7 in a row - three possibilities!
      if MyCentralOrder(G,g*tl[MM(f+2,n)]) eq 5 then
        a:=MM(f+2,n); b:=MM(f+5,n); c:=MM(f+6,n);
      elif MyCentralOrder(G,g*tl[MM(f+4,n)]) eq 5 then
        a:=MM(f+2,n); b:=MM(f+3,n); c:=MM(f+6,n);
      else a:=MM(f+2,n); b:=MM(f+4,n); c:=MM(f+6,n);
      end if;
    end if;
  elif #il eq 6 then
    //must be 6 in a row - two possibilities
    f := MM( Min( ilc ) + 1, n);
    while not f in il do f := MM(f+1,n); end while;
    if MyCentralOrder(G, g*tl[MM(f+1,n)]) eq 5 then
      a:=MM(f+2,n); b:=MM(f+4,n); c:=MM(f+5,n);
    else a:=MM(f+2,n); b:=MM(f+3,n); c:=MM(f+5,n);
    end if;
  else //must be 5 in a row
    f := MM( Min( ilc ) + 1, n);
    while not f in il do f := MM(f+1,n); end while;
    a:=MM(f+2,n); b:=MM(f+3,n); c:=MM(f+4,n);
  end if;

  if not a in il or not b in il or not c in il then return {}; end if;
  return {a,b,c};
end function;

C9IdentifyAlternatingPermutation := function(P, g,t,l,wt,wl,n)
/* This takes an arbitrary element g of (k.)A_n, and the t,l,wt,wl returned by
 * IdentifyAlternatingGroup in the group isomorphic to Alt(n).
 * It returns three things -  true/false, perm, and word.
 * It decides which permutation, perm, is represented by g, and tries to
 * express g as a word in the generators of G.
 * true means it succeeded. If false is returned, then the group cannot
 * be isomorphic to Alt(n)!
 */ 
  local tl, wtl, wtln,  perm, cperm, j, k, G, pl, S, Sn, B, word, phi, yes,
        scal, scaln;
  tl, wtl, wtln := C9FindThreeCycles(t,l,wt,wl,n);
  scal := (wtl[1]*wtl[2])^2; scaln := (wtln[1]*wtln[2])^2; //central involution

  // gen := Generic (P);
  perm := {@ @};
  tr_1 := C9IdentifyTriple(P, (tl[1])^g,tl,n);
  if #tr_1 eq 0 then return false,_,_,_; end if;
  tr_i := tr_1;
  for i := 1 to n-1 do
    tr_ipl1 := C9IdentifyTriple(P, tl[i+1]^g,tl,n);
    if #tr_ipl1 eq 0 then return false,_,_,_; end if;
    d := tr_i diff tr_ipl1;
    if #d ne 1 or Rep(d) in perm then return false,_,_,_; end if;
    Include(~perm, Rep(d));
    tr_i := tr_ipl1;
  end for;
  d := tr_i diff tr_1;
  if #d ne 1 or Rep(d) in perm then return false,_,_,_; end if;
  Include(~perm, Rep(d));
  G := Sym(n);
  perm :=  G!IndexedSetToSequence(perm);
  if not IsEven(perm) then return false,_,_,_; end if;
  G := Alt(n);
  perm := G!perm;
  // construct list in Alt(n) corresponding to tl.
  pl := [ G!(i,i+1,i+2) : i in [1..n-2] ];
  S := Parent(wt); Sn := Parent(wtln[1]);
  word := Id(S); wordn := Id(Sn);
  cperm := perm;
  for i in [1..n-2] do
    k := i^cperm;
    j := k-2;
    while j ge i do
      word := wtl[j]^-1 * word;  wordn := wtln[j]^-1 * wordn;
      cperm := cperm * pl[j];
      j := j-2;
    end while;
    if j eq i-1 then
      word := wtl[i] * word; wordn := wtln[i] * wordn;
      cperm := cperm * pl[i]^-1;
    end if;
  end for;

  // Check correctness.
  B := Parent(t);
  mat := Evaluate(word, [ B.i : i in [1..Ngens(S)] ]) * g^-1;
  yes := IsCentral(P, mat);
  if yes and not IsIdentity (mat) then
    word *:= scal; wordn *:= scaln;
    if not IsScalar (Evaluate(word, [ B.i : i in [1..Ngens(S)] ]) * g^-1) then
      yes := false;
    end if;
  end if;
  return yes, perm, word, wordn;
end function;

C9VerifyIdentifyAlternatingGroup := function(G,t,l,wt,wl,centre,n)
/* Check that the IdentifyAlternatingGroup really did find an
 * isomorphism modulo scalars with Alt(n).
 * First check that group elements t,l satisfy relations for Alt(n) with
 * n odd:  a=(1,2,3), b=(1,2,...,n),
 * a^3, b^n, (a*b^2)^((n-1)/2), ((b*a)^j*b^-j)^2 (2<=j<=n-2)
 * n even:  a=(1,2,3), b=(2,...,n),
 * a^3, b^(n-1), (b^2*a^-1)^(n/2), (b*a^-1)^(n-1),
 * ((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2 (1 <= j <= n/2 - 1),
 * ((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2 (1 <= j <= n/2 - 2)
 * Then check that G=<t,l> by checking that the generators of G lie in <t,l>.
 */
 local a,b,tl,wtl,id,celts;
  a:=t; b:=l;

  if n mod 2 eq 1 then
    if not IsCentral (G, a^3) or not IsCentral (G, b^n) or 
       not IsCentral (G, (a*b^2)^((n-1) div 2)) then
      vprintf IsAltsym:  "Relator of Alt(n) not satisfied";
      return false;
    end if;
    for j in [2..n-2] do
      if not IsCentral (G, ((b*a)^j*b^-j)^2) then 
        vprintf IsAltsym:  "Relator of Alt(n) not satisfied";
        return false;
      end if;
    end for;
  else
    if not IsCentral (G, a^3) or not  IsCentral (G, b^(n-1)) or  
       not IsCentral (G, (b^2*a^-1)^(n div 2)) or  
       not IsCentral (G, (b*a^-1)^(n-1)) then
      vprintf IsAltsym:  "Relator of Alt(n) not satisfied";
      return false;
    end if;
    for j in [2..n div 2 - 1] do
      if not IsCentral (G, ((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2) then  
        vprintf IsAltsym:  "Relator of Alt(n) not satisfied";
        return false;
      end if;
    end for;
    for j in [2..n div 2 - 2] do
      if not IsCentral (G, ((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2)  then
        vprintf IsAltsym:  "Relator of Alt(n) not satisfied";
        return false;
      end if;
    end for;
  end if;

  for g in Generators(G) do
    if not C9IdentifyAlternatingPermutation(G,g,t,l,wt,wl,n) then
      vprintf IsAltsym:  "Generator of G not in <t,l>";
      return false;
    end if;
  end for;

  return true;
end function;

intrinsic C9RecogniseAlternating(G::Grp, n::RngIntElt: 
    maxtries:=100*n+5000) -> BoolElt, Map, Map, Map, Map
{Constructive recognition using the Bratus-Pak algorithm
of an absolutely irreducible matrix group G which modulo 
 scalars is isomorphic to Alt(n)}

    if n le 8 then
      "Use RecogniseAlternating only for degree at least 9";
      return false,_,_,_,_,_;
    end if;

    if Type (G) eq GrpMat then 
       require IsAbsolutelyIrreducible (G): 
       "Input group must be absolutely irreducible";
    end if;

    if assigned G`AltSymData then
      gasd := G`AltSymData;
      if gasd[1] ne "Alt" or gasd[2] ne n then
        return false,_,_,_,_,_;
      end if;
      t:=gasd[3]; l:=gasd[4]; wt:=gasd[5]; wl:=gasd[6]; 
    else
      bool, t, l, wt, wl := C9IdentifyAlternatingGroup(G, n:maxtries:=maxtries);
      if not bool then 
        vprintf IsAltsym: "Failed initial identification";
	return false,_,_,_,_,_;
      end if;
      tl, wtl, wtln := C9FindThreeCycles(t,l,wt,wl,n);
      centre := (tl[1]*tl[2])^2;  wcentre := (wtln[1]*wtln[2])^2;
      if not IsCentral (G, centre) then 
        vprintf IsAltsym: "element is not in centre";
	return false,_,_,_,_,_;
      end if;
      bool := C9VerifyIdentifyAlternatingGroup(G,t,l,wt,wl,centre,n);
      if not bool then 
	return false,_,_,_,_,_;
      end if;
      G`AltSymData := <"Alt",n,t,l,wt,wl>;
    end if;

    BBtoPerm:= map<G->Alt(n) | x :-> perm where
        bool, perm := C9IdentifyAlternatingPermutation(G,x,t,l,wt,wl,n) >;

    PermtoBB := map<Alt(n)-> G | x :-> g where
        bool, g := C9ImageOfAlternatingPermutation(x,t,l,n) >;

    W, m := WordGroup(G);

    BBtoWG := map<G-> W | x :-> w where
        bool, perm, w := C9IdentifyAlternatingPermutation(G,x,t,l,wt,wl,n) >;

    return true, BBtoPerm, PermtoBB, BBtoWG, m;
end intrinsic;

intrinsic C9AlternatingElementToWord(G::Grp, g:GrpElt) -> BoolElt, GrpSLPElt
{If g is an element of group G which has been constructively recognised
to be isomorphic modulo scalars to Alt(n), then return true and 
element of word group for g, else return false.}
   if not assigned G`AltSymData then
     error "You must run C9RecogniseAlternating first";
   end if;
   asd := G`AltSymData; assert asd[1] eq "Alt";
   bool, perm, slp, slpn := C9IdentifyAlternatingPermutation
                            (G,g,asd[3],asd[4],asd[5],asd[6],asd[2]);
   if not bool then return false, _; else return true, slp; end if;
end intrinsic;

intrinsic C9AlternatingElementToStandardWord(G::Grp, g:GrpElt) ->
                                                          BoolElt, GrpSLPElt
{If g is an element of group G which has been constructively recognised
to be isomorphic modulo scalars to Alt(n), then return true and 
element of word group for g in the standard generators 
(1,2,3),((1,)2,3,...,n), else return false.}
   if not assigned G`AltSymData then
     error "You must run C9RecogniseAlternating first";
   end if;
   asd := G`AltSymData; assert asd[1] eq "Alt";
   bool, perm, slp, slpn := C9IdentifyAlternatingPermutation
                            (G,g,asd[3],asd[4],asd[5],asd[6],asd[2]);
   if not bool then return false, _; else return true, slpn; end if;
end intrinsic;
