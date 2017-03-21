freeze;

/* Code prepared by Peter Brooksbank; revised by Eamonn O'Brien */
 
import "special-cases.m": SL2pStandardGenerators; 
import "kk-sl2.m": RecogniseSL2_KK;

/*
Code for constructive recognition of black box SL(2,q).
Intended as add-on to existing RecogniseSL2 code.
Allowable input groups: GrpMat and GrpPerm;
however, no intrinsic functions have been set up.
In principle, code should work for any black box group
possessing an element "order oracle".
Code will work in correct characteristic, but will
obviously be substantially slower than existing code.

Assumption: q is at least 4; solvable cases are dealt with by brute force.
*/

// writes a nonnegative integer <n> < <p>^<e> in base <p>
NtoPadic := function(p, e, n)
   output := IntegerToSequence (n, p, e);
   return VectorSpace(GF(p),e)!output;
end function;

// writes a vector in GF(<p>)^<e> as a nonnegative integer
PadictoN := function(p, e, vector)
   y := Eltseq (vector);
   ChangeUniverse (~y, Integers ());
   return SequenceToInteger (y, p);
end function;

/*
 <sl2ToralElement>
 INPUT:
   (1) <gp> = black box group
   (2) <q> = field size
 OUTPUT:
   (1) <flag> indicating success or failure
   (2) <h> = element of order <q>-1 or (<q>-1)/2
   (3) <w> = SLP to <h>
   (4) <isSimple>
*/

sl2ToralElementEven := function (gp, q)
   proc := RandomProcessWithWords (gp);
   limit := 48 * Floor (Log (2,q));
   count := 0;
   found := false;
   while (count le limit) and (not found) do
      count +:= 1;
      h, w := Random (proc);
      found := found or (Order (h) eq q-1);
   end while;
   if found then
return true, h, w;
   end if;
return false, _, _;
end function; 

sl2ToralElementOdd := function (gp, q)
   proc := RandomProcessWithWords (gp);
   limit := 48 * Floor (Log (2,q));
   count := 0;
   found1 := false;
   found2 := false;
   while (count le limit) and not (found1) do
      count +:= 1;
      h, w := Random (proc);
      o := Order (h);
      if o eq (q-1) then 
         found1 := true; 
      elif o eq (q-1) div 2 then 
         found2 := true; 
         hh := h;
         ww := w;
      end if;
   end while;
   if found1 then
return true, h, w, false;
   elif found2 then
return true, hh, ww, true;
   end if;
return false, _, _, _;
end function; 

sl2ToralElement := function (gp, q)
   if q mod 2 eq 0 then
      flag, h, w := sl2ToralElementEven (gp, q);
      if flag then
         return flag, h, w, true;
      else
         return false, _, _, _;
      end if;
   else
      return sl2ToralElementOdd (gp, q);
   end if;
end function;


/*
INPUT:
    (1) group <gp>
    (2) prime <p>
    (3) power <k>
    (4) element <h0> of order q-1
    (5) SLP <wh0> to <h0>
OUTPUT:
    <flag>
    <T> = full transvection group normalised by <h0>
    <WT> = corresponding words
    <l> = conjugating element
    <wl> = SLP to <j>
*/
 
sl2TransvectionGroup := function (gp, p, k, h0, wh0)

   q := p^k;
   gens := [ gp.i : i in [1..Ngens (gp)] ];
   proc := RandomProcessWithWords (gp);
   W := Parent (wh0);
   Wgens := [ W.i : i in [1..Ngens (W)] ];

   // find a suitable conjugate of <h0>
   count := 0;
   found := false;
   while (count lt 100) and (not found) do
      count +:= 1;
      g, wg := Random (proc);
      h := h0^g;
      wh := wh0^wg;
      if (h, h0)^p ne Identity (gp) then
         found := true;
      end if; 
   end while;

   if not found then
return false, _, _, _, _;
   end if;

   // find a transvection (prob 0.5 if <q> is odd)
   i := 1;
   c, wc := Random (proc);
   found := false;
   while (i lt (q-1) div Gcd (2, q-1)) and (not found) do
      t := (h0, c);
      wt := (wh0, wc);
      if (t ne Identity (gp)) and 
         (t^p eq Identity (gp)) then
            found := true;
      end if;
      i +:= 1;
      c := h * c;
      wc := wh * wc;
   end while;

   if (not found) then
return false, _, _, _, _;
   end if;

   if (t, t^h0) ne Identity (gp) then
return false, _, _, _, _;
   end if;

   // list transvection group containing <t>
   T := [ Identity (gp) ];
   WT := [ Identity (W) ];
   for e in [0..k-1] do
      h := h0^e;
      wh := wh0^e;
      x := t^h;
      wx := wt^wh;
      u := x;
      wu := wx;
      Tnew := [];
      WTnew := [];
      for i in [1..p-1] do
         for l in [1..#T] do
            Append (~Tnew, T[l] * u);
            Append (~WTnew, WT[l] * wu);
         end for;
         u := u * x;
         wu := wu * wx;
      end for;
      T := T cat Tnew;
      WT := WT cat WTnew;
   end for;

   // find generator of group not normalising <T>
   i := 1;
   found := false;
   while (i le #gens) and (not found) do
      j := gp.i;
      wj := W.i;
      if (t, t^j) ne Identity (gp) then
         found := true;
      else
         i +:= 1;
      end if;
   end while;

assert found;

   // find other tran group normalised by <h0>  
   i := 1;
   found := false;
   while (i le q) and (not found) do
      l := j * T[i];
      wl := wj * WT[i];
      s := t^l;
      if (s, s^h0) eq Identity (gp) then
         found := true;
      else
         i +:= 1;
      end if;
   end while;

assert found;

return true, T, WT, l, wl;
end function;

/*
 INPUT:
   (1) transvection group <T>
   (2) element <x> normalising <T>
   (3) prime <p>
   (4) exponent <k>
 OUTPUT:
   (1) <flag> indicating that <x> does normalise <T>
   (2) <k> x <k> matrix over GF(<p>) representing
       action of <x> on <T>
*/

ActionOnTransvectionGroup := function (T, x, p, k) 
     mat := [];
     for i in [0 .. k-1] do
       // the basis vectors of T are in positions p^i+1
       conj := T[p^i+1]^x;
       stop := false; 
       j := 0;
       repeat 
         j := j + 1;
         if conj eq T[j] then
            stop := true;
         end if;
       until stop or j eq p^k; 
       if not stop then 
return false, _; 
       end if;
       Append (~mat, NtoPadic (p, k, j-1));
     end for;
return true, Matrix (mat);
end function;


// This is Kantor-Seress Lemma 2.4.
ApplyLemma24 := function (hEndo, p, k) 
   v0 := NtoPadic (p, k, 1);
   ims := [v0];
   for i in [1..(p^k-1) div 2] do
      Append (~ims, ims[i]*hEndo);
   end for;      
   e := 0;
   repeat
      e +:= 1;
      v := v0 + ims[e];
   until not v in ims; 
return e-1;
end function;


/*
 INPUT:
   (1) transvection group <T>
   (2) toral element <h> normalising <T>
   (3) prime <p>
   (4) exponent <k>
 OUTPUT: automorphism of <T> of order <q>-1
   specified as <k> x <k> matrix over GF(<p)>
   having same minimal polynomial as the
   PrimitiveElement of GF(<q>) stored in Magma.
*/

sl2FieldGenerator := function (T, h, p, k) 

   q := p^k;
   f := GF (q);
   r := PrimitiveElement (f);
   fbas := Basis (f);   // this is the canonical basis
   V, phi := VectorSpace (f, GF (p), fbas);
   rvec := Coordinates (V, phi(r^k));

   /* 
     construct (the matrix of) auto of <T>
     induced by <h>
   */   
   flag, hEndo := ActionOnTransvectionGroup (T, h, p, k);

   if not flag then
      return false, _;
   end if;
   if p mod 2 eq 0 then
      auto := hEndo;
   else
      m := ApplyLemma24 (hEndo, p, k); 
      mat := hEndo^m + hEndo^0;
      // fac := twopart (p^k-1);
      // auto := hEndo^(2^(fac[1]-1)) * mat^(fac[2]);
      fac1, fac2 := Valuation (p^k-1, 2);
      auto := hEndo^(2^(fac1-1)) * mat^(fac2);
   end if;

   // assert Order (auto) eq (q-1);

   // search for a generator corresponding to <r>

            testvec := function (v, mat, w)
            local  vi, vs, i;
               vi := v;
               vs := w[1] * v;
               for i in [1.. Degree(w)-1] do
                   vi := vi * mat;
                   vs := vs + w[i+1] * vi;
               end for;
            return vs eq vi * mat;
            end function;

   pspace := VectorSpace (GF (p), k);
   rvec := pspace!rvec;
   gen := auto^0;
   found := false;
   i := 1;
   while (not found) and (i lt q-1) do
      gen := gen * auto;
      x := pspace.1;
      if testvec(x, gen, rvec) then
         found := true;
      end if;
      i +:= 1;
   end while;

assert found;

// assert &+ [ rvec[i]*gen^(i-1) : i in [1..k] ] eq gen^k;

return gen;
end function;


/*
 INPUT:
   (1) transvection group <T>
   (2) <WT> = list of SLPs for members of <T>
   (3) <gen> automorphism of <T> corresponding to
       PrimitiveElement
   (4) <l> not normalising <T>
   (5) prime <p>
   (6) exponent <k>
 OUTPUT:
   (1) ordered permutation <domain> of tranvections
   (2) corresponding <points> in GF(<q>)^2
   (3) re-listing of <T>
   (4) corresponding SLP list
*/

sl2PermutationDomain := function (T, WT, gen, l, p, k)   
   q := p^k;
   r := PrimitiveElement (GF (q));
   // first re-list <T>
   newT := [ T[1] , T[2] ];
   newWT := [ WT[1], WT[2] ];
   vec := NtoPadic (p, k, 1);
   for i in [1..q-2] do
      vec := vec * gen;
      n := PadictoN (p, k, vec);
      newT[i+2] := T[n+1];
      newWT[i+2] := WT[n+1];
   end for;
   // construct the domain
   t := T[2];
   tl := t^l;
   domain := [ t , tl ];
   V := VectorSpace (GF (q), 2);
   points := [ V![1,0] , V![0,1] ];
   for i in [0..q-2] do
      domain[i+3] := tl^(newT[i+2]);
      points[i+3] := V![r^i,r^0];
   end for;  
return domain, points, newT, newWT;
end function;


/*
 INPUT:
   (1) permutation domain <Y>
   (2) corresponding <points>
   (3) field 
   (4) Identity of black box group
   (5) element <x> of black box group (or overgroup)
 OUTPUT:
   (1) <flag> indicating membership in black box group
   (2) 2 x 2 matrix over GF(<q>) representing the
       projective action of <x> (on transvection groups)
*/

bbsl2ProjectiveAction := function (Y, points, f, one, x)  

   q := #f;
   r := PrimitiveElement(f);     

   searchY := function (dom, s, id)
     if exists(i){i : i in [1..#dom] | (dom[i], s) eq id} then 
        return true, i;
     else
        return false, _; 
     end if;
   end function;

   // find the images of three points
   ims := [];
   for i in [1,2,3] do
      flag, j := searchY (Y, Y[i]^x, one);
      if not flag then return false, _; end if;
      ims[i] := points[j];
   end for;

   d12 := ims[1][1]*ims[2][2] - ims[1][2]*ims[2][1];
   d13 := ims[3][1]*ims[1][2] - ims[1][1]*ims[3][2];
   d23 := ims[2][1]*ims[3][2] - ims[2][2]*ims[3][1];
   if (d12 eq Zero (f)) or (d13 eq Zero (f)) or (d23 eq Zero (f)) then
return false, _;
   end if;
   l := d23 / (d12 * d13);
   e := Log (r, l) mod (q-1);
   if q mod 2 eq 0 then
      if e mod 2 eq 1 then
         e := e + q - 1;
      end if;
      scal := r^(e div 2);
   else
      if e mod 2 eq 1 then
return false, _;
      end if;
      scal := r^(e div 2);
   end if;

   mat := Matrix([ scal*ims[1] , ims[2]/(scal*d12) ]);

return true, mat;
end function;
                
/*
 INPUT:
 1) <can_gens> are the canonical generators for SL(2,<field>) consisting of 
    <s> = lower transvection
    <t> = upper transvection
    <h> = diagonal element
 2) <field>
 3) <mat> the 2x2 matrix
 4) <nrgens>
 5) <start>
   (only in odd characteristic
      6) <sbasis> = GF(p) basis for field taken from <S>
      7) <tbasis> = GF(p) basis for field taken from <T>
   )
 OUTPUT: SLP from <can_gens> to <mat>
*/

wbsl2SLP := function (arg1, arg2, arg3, arg4, arg5, arg6, arg7, slg)

   s := arg1[1];
   t := arg1[2];
   h := arg1[3];
   a := h[1][1];
   b := t[1][2];
   c := s[2][1];
   F := arg2;
   q := #F;
   p := Characteristic (F);
   x :=  arg3;
   if q mod 2 eq 1 then
      sbasis := arg6;
      tbasis := arg7;
   end if;

   sprg := slg.arg5;
   tprg := slg.(arg5+1);
   hprg := slg.(arg5+2);
   
   slp := Id (slg);

   // reduce to upper triangular
   if x[2][2] eq 0*a then
      x := x*t^-1;
      slp := tprg;
   end if;
   // now x[2][2] ne 0
   l := x[2][1]/x[2][2];
   if l ne 0*l then
      sl := Matrix (F, [ [1,0], [-l,1] ]);
      x := x * sl;
      if q mod 2 eq 0 then
         n := Log( a, l/c ) mod (q-1);
         if n mod 2 eq 1 then
            n := n + #F - 1;
         end if;
         j := n div 2;
         sslp := sprg^(hprg^j);
      else
         V, phi := VectorSpace (F, GF (p), sbasis);
         pows :=
            [Integers()!x : x in Coordinates( V, phi(l))];
         sslp := Id (slg);
         for i in [1..#pows] do if pows[i] ne 0 then
              sslp := sslp * (sprg^(hprg^(i-1)))^pows[i];
            end if;
         end for;
      end if;
      slp := sslp * slp;
   end if;

   // reduce to diagonal
   l := x[1][2]/x[1][1];
   if l ne 0*l then
      tl := Matrix (F, [ [1,-l], [0,1] ]);
      x := x * tl;
      if #F mod 2 eq 0 then
         n := Log( a,  b/l ) mod (q-1);
         if n mod 2 eq 1 then
            n := n + q - 1;
         end if;
         j := n div 2;
         tslp := tprg^(hprg^j);
      else
         V, phi := VectorSpace(F, GF(p), tbasis);
         pows :=
            [Integers()!x : x in Coordinates( V, phi(l))];
         tslp := Id (slg);
         for i in [1..#pows] do
            if pows[i] ne 0 then
               tslp := tslp * (tprg^(hprg^(i-1)))^pows[i];
            end if;
         end for;
      end if;
      slp := tslp * slp;
   end if;

   // find the correct power of <h>
   if x[1][1]*x[2][2] ne a^0 then
return false, _;
   end if;
   n := Log( a, x[1][1]) mod (q-1);
   slp := hprg^n * slp;

return true, slp;
end function;


/*
 INPUT:
 1) <data> = black box SL2 recognition data structure
 2) <x> = black box group element
 OUTPUT: SLP from <data>.<igens> to <x>
*/

bbsl2SLP := function (G, x, slg) 

   data := G`SL2OracleData;
   f := G`DefiningField; 

   // first compute the action of <x> on transvection groups
   flag, action := bbsl2ProjectiveAction (data`domain, 
                       data`points, f, Identity (G), x);
   if not flag then return false, _; end if;
      
   // write SLP using white box method
   if Characteristic (f) mod 2 eq 1 then
      flag, slp := wbsl2SLP (data`gens, f, action, 3, 1, 
                             data`sbasis, data`tbasis, slg);
   else
      flag, slp := wbsl2SLP (data`gens, f, action, 3, 1, 0, 0, slg);
   end if;
   if not flag then return false, _; end if;

   // evaluate SLP in black box group 
   y := Evaluate (slp, data`igens); 

   // check that <y> and <x> give the same element of PSL
   if IsCentral (G, y * x^-1) then
      return true, slp;
   else
      return false, _;
   end if;

end function;

/*
 The main recognition function.
 INPUT: A group <G> for which the attribute DefiningField has been set
 OUTPUT: <true> if <G> is isomorphic to SL(2,G`DefiningField)
         <false> otherwise
 If <true> then attribute SL2OracleData for <G> is also set
*/

SL2Oracle := function (G)

   F := G`DefiningField;
   q := #F;
   assert q ge 4;

   p := Characteristic (F);
   k := Degree (F);
   slg := SLPGroup (3);

   // first find an element of order <q>-1 
   flag, h, wh, isSimple := sl2ToralElement (G, q);
   if not flag then
return false;
   end if;

   // find the two transvection groups normalised by <h>
   count := 0;
   limit := 20;
   repeat   // if <q> is odd, the basic procedure succeeds with prob 0.5
      count +:= 1;
      flag, S, WS, l, wl := sl2TransvectionGroup (G, p, k, h, wh); 
   until flag or count eq limit;
   if not flag then
return false;
   end if;

   // find (matrix of) an automorphism of <S> of order <q>-1 
   gen := sl2FieldGenerator (S, h, p, k); 

   // construct the permutation domain
   Y, points, S, WS := sl2PermutationDomain (S, WS, gen, l, p, k); 

   // assemble the data structure;
   rf := recformat<
                 igens, gens, slps, trangp, 
                 sbasis, tbasis, domain, points, isSimple 
                  >;
   data := rec< rf | >;
   s := Y[1];
   ws := WS[2];
   t := Y[2];
   wt := ws ^ wl;
   r := PrimitiveElement (F);
   W, phi := VectorSpace (F, GF (p));
   WW := VectorSpaceWithBasis ([ phi(r^i) : i in [0..k-1]]);
   one := Identity (G);
   flag, sM := bbsl2ProjectiveAction (Y, points, F, one, s);
   assert flag;
   sM := sM ^ (1-q);
assert sM eq Matrix (F, [ [1,0], [1,1] ]);
   flag, tM := bbsl2ProjectiveAction (Y, points, F, one, t);
assert flag;
   tM := tM ^ (1-q);
   a := tM[1][2];
   pows := [Integers()!x: x in Coordinates(WW, phi(-1/a)) ];
   s0M := Matrix([ [r^0,0*r], [-1/a,r^0] ]);
   s0 := &*[ S[i+1]^pows[i] : i in [1..k] ];
   ws0 := &*[ WS[i+1]^pows[i] : i in [1..k] ];
   lM := s0M * tM * s0M;
   l := s0 * t * s0;
   wl := ws0 * wt * ws0;
   b := -a/r;
   pows := [ Integers()!x: x in Coordinates (WW, phi(-b/a^2)) ];
   t1M := Matrix ([ [1,b], [0,1] ]);
   u := &*[ S[i+1]^pows[i] : i in [1..k] ];
   wu := &*[ WS[i+1]^pows[i] : i in [1..k] ];
   t1 := u ^ l;
   wt1 := wu ^ wl;
   pows := [Integers()!x: x in Coordinates (WW, phi(-b^-1)) ];
   s1M := Matrix ([ [1,0] , [-b^-1,1] ]);
   s1 := &*[ S[i+1]^pows[i] : i in [1..k] ];
   ws1 := &*[ WS[i+1]^pows[i] : i in [1..k] ];
   hM := lM * s1M * t1M * s1M;
   h := l * s1 * t1 * s1;
   wh := wl * ws1 * wt1 * ws1;
   data`gens := [ SL (2,q) | sM, tM, hM ];
   data`igens := [s, t, h];
   data`slps := [ws, wt, wh];
   data`trangp := S;
   data`domain := Y;
   data`points := points;
   if p mod 2 eq 1 then
      data`sbasis :=
               [ data`gens[1][2][1]*data`gens[3][1][1]^(2*i) : i in [0..k-1]];
      data`tbasis :=
               [ data`gens[2][1][2]*data`gens[3][2][2]^(2*i) : i in [0..k-1]];
   else 
       data`sbasis := []; data`tbasis := [];
   end if;
   // test whether <G> is SL(2,q) or PSL(2,q)
   zM := -hM^0;
   flag, slp := wbsl2SLP (data`gens, F, zM, 3, 1,
                          data`sbasis, data`tbasis, SLPGroup (3));
assert flag;
   z := Evaluate (slp, data`igens);
   if z eq Identity (G) then
      data`isSimple := true;
   else
      data`isSimple := false;
   end if;
   G`SL2OracleData := data;
      
   return true;       
end function;

/*
 INPUT:
   (1) <G> for which attribute SL2OracleData has been set
   (2) <x> an element of Generic (<G>)
 OUTPUT:
   (1) <member> = flag indicating whether <x> is in <G>
   (2) if <SL2Image> is true, the image of <x> in SL2
       else an SLP to <x> from the USER DEFINED generators of <G>
*/ 

BlackBoxElementToSLP := function (G, x : SL2Image := false)

   slg := SLPGroup (3);
   flag, slp := bbsl2SLP (G, x, slg);
   if not flag then
      // element is not in <G>
      return false, _;
   end if;
   if not G`SL2OracleData`isSimple then
      xx := Evaluate (slp, G`SL2OracleData`igens);
      if x ne xx then
         hslp := slg.3;
         q := #G`SL2OracleData`trangp;
         zslp := hslp^((q-1) div 2);
         slp := slp * zslp;
      end if;
   end if;
   if SL2Image then
      return true, Evaluate (slp, G`SL2OracleData`gens);
   end if;
   W, f := WordGroup (G);
   rho := hom < slg -> W | G`SL2OracleData`slps >;

   return true, rho (slp); 
end function;


/*
 INPUT:
   (1) <G> for which attribute SL2OracleData has been set
   (2) <x> an element of SL2
 OUTPUT: the image of <x> in <G>
*/

SL2ElementToBlackBoxElement := function (G, x)
   gens := G`SL2OracleData`gens;
   F := G`DefiningField;
   if BaseRing (x) ne F then
      // <x> is defined over the wrong field
      return false;
   end if;
   if Degree (x) ne 2 then
      // <x> has wrong degree
      return false;
   end if;
   if Determinant (x) ne 1 then
      // <x> is not in SL
      return false;
   end if;
   if Characteristic (F) mod 2 eq 1 then
      sbas := G`SL2OracleData`sbasis;
      tbas := G`SL2OracleData`tbasis;
   else
      sbas := [];
      tbas := [];
   end if;
   flag, slp := wbsl2SLP (gens, F, x, 3, 1, sbas, tbas, SLPGroup (3));
   assert flag;
   return Evaluate (slp, G`SL2OracleData`igens); 
end function;

/* used only to SL(2, p) for p = 2, 3 */

SmallSL2 := function (G, p: Verify := false)
   if Verify then 
      p, q := SL2Characteristic (G: Verify:=false);
      if p ne q or not (q in {2, 3}) then return false, _, _; end if;
   end if;

   flag, Y := SL2pStandardGenerators (SL(2, p), p);
   if not flag then return false, _, _, _, _; end if;
   if p eq 3 then 
      repeat
         flag, x := RandomElementOfOrder (G, 3);
         if flag then flag, y := RandomElementOfOrder (G, 3); end if;
      until flag and (x,y) ne Identity (G) and 
            (y^-1 * x^-1 * y^-1 * x * y * x) eq Identity (G);
   else 
      repeat
         flag, x := RandomElementOfOrder (G, 2);
         if flag then flag, y := RandomElementOfOrder (G, 2); end if;
     until flag and (x ne y) and (x * y)^3 eq Identity (G);
   end if;

   RandomSchreier (G);

   H := sub <G | x, y >;
   RandomSchreier (H);

   I := sub <GL(2, p) | Y>;
   RandomSchreier (I);

   phi := hom <H -> I | Y>;
   tau := hom <I -> H | x, y>;
   W, gamma := WordGroup (G);
   delta := InverseWordMap (G);
   phiRule := hom<H -> I | g :-> phi(g)>;
   tauRule := hom<I -> H | g :-> tau(g)>;
   deltaRule := hom<G -> W | g :-> delta(g)>;
   return true, phiRule, tauRule, deltaRule, gamma;
end function;

/*
 INPUT: 
   (1) <G> black box group (matrix gp or perm gp presumably)
   (2) <q> field size
 OUTPUT:
   (1) <isit> = flag indicating whether <G> is (P)SL(2,<q>)
   (2) <phi> = map from <G> to SL(2,<q>)
   (3) <tau> = map from SL(2,<q>) to <G>
   (4) <gamma> = map from Generic (<G>) to WordGroup (<G>)
   (5) <delta> = map from WordGroup (<G>) to Generic (<G>)
 NOTES:
   (*) Intended to serve as a subfunction of Intrinsic
       RecogniseSL2; called when it has been decided that
       <G> is not SL2 in correct characteristic.
   (*) In this case, some precomputation is needed to
       determine first the defining characteristic, and 
       second the actual field size.
   KK -- use Kantor-Kassabov; FieldBound lower bound for its use
   default: Kantor-Seress
*/

RecogniseBlackBoxSL2 := function (G, q: KK := false, FieldBound := 2^10)

   if q in {2, 3} then
       return SmallSL2 (G, q: Verify := false);
   end if;

   // for large even fields, use KK by default 
   if KK or (IsEven (q) and q ge FieldBound) then 
      return RecogniseSL2_KK (G, q);
   end if;

   vprint sl2q: "Use Kantor-Seress algorithm"; 
   G`DefiningField := GF (q);

   // apply the black box SL2 oracle
   isit := SL2Oracle (G);
   if not isit then return false, _, _, _, _; end if;

   // set up maps
   // H := sub <GL (2, q) | G`SL2OracleData`gens>;
   H := SL (2, q);
   generic := Generic (G);
   W := WordGroup (G);
   phi := hom <generic -> H | x :-> y where _, y := 
                  BlackBoxElementToSLP (G, x : SL2Image := true)>;
   tau := hom <H -> generic | x :->
                  SL2ElementToBlackBoxElement (G, x) >;
   gamma := hom <generic -> W | x :-> w where _, w := 
                  BlackBoxElementToSLP (G, x)>;
   delta := hom <W -> generic | x :->
                  Evaluate (x, [ G.i : i in [1..Ngens (G)] ])>;

   return true, phi, tau, gamma, delta;
end function;
