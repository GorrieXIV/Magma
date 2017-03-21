freeze;

import "bbutil.m": IsCentralisedBy, GroupSupport, GroupCentralisedSpace,
  twopart, MyInsertBlock, NtoPadic, PadictoN, ActionOnSubspace, Comm;

///////////////////////////////////////////////////////////
// INPUT:
//    (1) group <gp>
//    (2) integer <q>
// OUTPUT: element of <gp> of order <q>-1
LGenerators := func< G | [G.i : i in [1..Ngens(G)]] >; 

sl2ConstructToralElement := function(gp, q)
local  limit, count, h, o, gpp;
   gpp := RandomProcess(gp);
   limit := 48*Floor(Log(2,q));
   count := 0;
   repeat
      count := count + 1;
      h := Random(gp);
      o := Order(h);
   until (count eq limit) or (o eq q-1);
   if (o ne q-1) then
return "fail";
   end if;
return h;
end function; 

// same except we just look for a good piece of <q>-1
sl2ConstructToralElementAlt := function(gp, q)
local  limit, count, found, h, o, gpp;
   gpp := RandomProcess(gp);
   limit := 32*Floor(Log(2,q));
   count := 0;
   found := false;
   while (count lt limit) and (not found) do
      count := count + 1;
      h := Random(gpp);
      if (q eq 3) then
         o := Order (h);
         if (o mod 2 eq 0) then
            h := h^(o div 2);
            found := true;
         end if;
      elif (IsIdentity (h^(q-1))) then
         o := Order (h);
         if (o gt 2) then
            if (q mod 2 eq 0) or (o mod 2 eq 0) then
               found := true;
            end if;
         end if;
      end if;
   end while;
   if (not found) then
return "fail";
   end if;
return h;
end function; 

///////////////////////////////////////////////////////////
// for input <h0> of order p^k-1, this subroutine finds <T> 
// one of the two transvection groups normalised by <h0>
// it also finds <j> in <gp> conjugating <T> to <S>, the
// other transvection group normalised by <h0>
// when p eq 2, the routine always succeeds
// when p gt 2, it succeeds with probability 0.5
//////////////////////////////////////////////////////////
bbsl2ConstructTransvectionGroup := function (gp, p, k, h0)
local   q, one, count, found, g, h, i, c, t, T, e, x, 
        l, u, Tnew, new, j, gens, s, gpp, rf;

   q := p^k;
   one := One(gp);
   gpp := RandomProcess(gp);

      // find a suitable conjugate of <h0>
   count := 0;
   found := false;
   while count lt 100 and not found do
      count := count + 1;
      g := Random (gpp);
      h := h0^g;
      if Comm (h, h0)^p ne one then
         found := true;
      end if; 
   end while;
   if not found then
return "fail";
   end if;

      // find a transvection
   i := 1;
   c := Random(gpp);
   found := false;
   while i lt (q-1) div Gcd(2,q-1) and not found do
      t := Comm(h0,c);
      if t ne one and t^p eq one then
         found := true;
      end if;
      i := i + 1;
      c := h*c;
   end while;
   if not found then
return "fail";
   end if;
   if not IsIdentity( Comm(t, t^h0) ) then
// for some reason we are not always getting a transvection
// in a group normalised by <h0> -- must look into this
      ///Print("new snare \n");
return "fail";
   end if;

      // list transvection group containing <t>
   T := [one];
   for e in [0..k-1] do
      h := h0^e;
      x := t^h;
      u := x;
      Tnew := [];
      for i in [1..p-1] do
         for l in [1..#T] do
            Append(~Tnew, T[l]*u);
         end for;
         u := u*x;
      end for;
      T := T cat Tnew;
   end for;

      // find generator of group not normalising <T>
   i := 1;
   gens := LGenerators(gp);
   found := false;
   while i le #gens and not found do
      j := gens[i];
      if Comm(t, t^j) ne one then
         found := true;
      end if;
      i := i + 1;
   end while;
   if not found then
return "fail";
   end if;
 
      // finally find the other transvection group normalised by <h0>  
   i := 1;
   found := false;
   while i le q and not found do
      j := j * T[i];
      s := t^j;
      if Comm (s, s^h0) eq one then
         found := true;
      end if;
      i := i + 1;
   end while;
   if not found then
return "fail";
   end if;

   rf := recformat<TransvectionGroup, Conj>;
return rec< rf | TransvectionGroup := T, Conj := j >;
end function;


/////////////////////////////////////////////////////
// computes a matrix for the action of <x> on <T>
bbslActionOnT := function(T, x, p, k) 
local  i, j, conj, stop, mat;   

     mat := [];
     for i in [0 .. k-1] do
       // the basis vectors of T are in positions p^i +1
       conj := T[p^i +1]^x;
       stop := false; 
       j := 0;
       repeat 
         j := j + 1;
         if conj eq T[j] then
            stop := true;
         end if;
       until stop or j eq p^k; 
       if not stop then 
return "fail"; 
       end if;
       Append(~mat, NtoPadic(p, k, j-1));
     end for;

return Matrix(mat);
end function;

////////////////////////////////////////////////////////////////////
// for <p> odd, determines an automorphism of <T> of order <p>^<k>-1
bbslApplyLemma24 := function(hEndo, p, k) 
local  v0, ims, i, e, v;
   
   v0 := NtoPadic(p, k, 1);
   ims := [v0];
   for i in [1..(p^k-1) div 2] do
      Append(~ims, ims[i]*hEndo);
   end for;      
   e := 0;
   repeat
      e := e+1;
      v := v0 + ims[e];
   until not v in ims; 

return e-1;
end function;

////////////////////////////////////////////////////////
// finds the matrix representing an automorphism of <T>
// corresponding to PrimitiveElement(<field>)
bbslConstructFieldGenerator := function(T, h, p, k) 
local  f, r, fbas, rvec, hEndo, auto, m, mat, fac,
       gen, found, i, x, pspace, testvec, V, phi, W;

   f := GF(p^k);
   r := PrimitiveElement(f);
   fbas := Basis(f);   // this is the canonical basis
   V, phi := VectorSpace(f,GF(p),fbas);
   rvec := Coordinates(V, phi(r^k));

      // construct (the matrix of) some generating automorphism of <T>
   hEndo := bbslActionOnT(T, h, p, k);
   if hEndo cmpeq "fail" then
      return "fail";
   end if;
   if p mod 2 eq 0 then
      auto := hEndo;
   else
      m := bbslApplyLemma24(hEndo, p, k); 
      mat := hEndo^m + hEndo^0;
      fac := twopart(p^k-1);
      auto := hEndo^(2^(fac[1]-1)) * mat^(fac[2]);
   end if;
   if Order(auto) ne p^k - 1 then
      error "wrong order of auto";
   end if;

      // search for a generator corresponding to <r>

            testvec := function(v, mat, w)
            local  vi, vs, i;
               vi := v;
               vs := w[1] * v;
               for i in [1.. Degree(w)-1] do
                   vi := vi * mat;
                   vs := vs + w[i+1] * vi;
               end for;
            return vs eq vi * mat;
            end function;

   pspace := VectorSpace(GF(p), k);
   rvec := pspace!rvec;
   gen := auto^0;
   found := false;
   i := 1;
   while not found and i lt p^k - 1 do
      gen := gen * auto;
      //x := Random(pspace);
      x := pspace.1;
      if testvec(x, gen, rvec) then
         found := true;
      end if;
      i := i + 1;
   end while;

   if not found then
     error "not found 911";
   end if;
      // make sure we really have found it
   //if Sum( List([1..k], i->rvec[i]*gen^(i-1)) ) ne gen^k then
   if &+ [ rvec[i]*gen^(i-1) : i in [1..k] ] ne gen^k then
      print "       ({SL2:} selected wrong generator)";
       return "fail";
   end if;

      // now <gen> --> <r> is an isomorphism Aut(<T>) --> GF(p^k)
return gen;
end function;

//////////////////////////////////////////////////////////////
// obtains a permutation domain for the conjugation action on 
// transvection groups; also re-orders <T> according to <gen>
bbsl2ListPermutationDomain := function(T, gen, j, p, k) 
local  q, r, newT, vec, i, n, t, tj, domain, points, V, rf;
   
   q := p^k;
   r := PrimitiveElement( GF(q) );

      // first re-list <T>
   newT := [ T[1] , T[2] ];
   vec := NtoPadic(p, k, 1);
   for i in [1..q-2] do
      vec := vec * gen;
      n := PadictoN(p, k, vec);
      newT[i+2] := T[n+1];
   end for;

      // construct the domain
   t := T[2];
   tj := t^j;
   domain := [ t , tj ];
   V := VectorSpace(GF(q),2);
   points := [ V![1,0] , V![0,1] ];
   for i in [0..q-2] do
      domain[i+3] := tj^(newT[i+2]);
      points[i+3] := V![r^i,r^0];
   end for;

  rf := recformat<TDomain, PDomain, TransvectionGroup>;

return rec< rf | TDomain := domain,
            PDomain := points,
            TransvectionGroup := newT >;
end function;

/////////////////////////////////////////////////////////////
// computes the projective action of any given <x> in <gp> on
// the underlying 2-space
bbsl2ProjectiveAction := function(Y, points, f, one, x)
local  q, r, searchY, ims, i, d12, d13, d23, l, e, scal, mat;
  
   q := #f;
   r := PrimitiveElement(f);     

      searchY := function(dom, s, id)
      local  found, i;
         found := false;
         i := 0;
         while i lt #dom and not found do
            i := i + 1;
            if Comm(dom[i], s) eq id then
               found := true;
            end if;
         end while;
         if not found then return "fail"; end if;
      return i;
      end function;    

      // find the images of three points
   ims := [];
   for i in [1..3] do
      ims[i] := points[ searchY(Y, Y[i]^x, one) ];
   end for;

   d12 := ims[1][1]*ims[2][2] - ims[1][2]*ims[2][1];
   d13 := ims[3][1]*ims[1][2] - ims[1][1]*ims[3][2];
   d23 := ims[2][1]*ims[3][2] - ims[2][2]*ims[3][1];
   if (d12 eq Zero(f)) or (d13 eq Zero(f)) or (d23 eq Zero(f)) then
     error "<x> is not in <gp>";
   end if;
   l := d23 / (d12 * d13);
   //e := LogFFE(l, r) mod (q-1);
   e := Log(r, l) mod (q-1);
   if q mod 2 eq 0 then
      if e mod 2 eq 1 then
         e := e + q - 1;
      end if;
      scal := r^(e div 2);
   else
      if e mod 2 eq 1 then
          error "<x> is not in <gp>";
      end if;
      scal := r^(e div 2);
   end if;

   mat := Matrix([ scal*ims[1] , ims[2]/(scal*d12) ]);

return mat;
end function;


/////////////////////////////////////////////////////////////////////////////////
/////////////// straight-line program routines for SL(2,q) //////////////////////
/////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// 1) <can_gens> are the canonical generators for SL(2,<field>) consisting of 
//    <s> = lower transvection
//    <t> = upper transvection
//    <h> = diagonal element
// 2) <field>
// 3) <mat> the 2x2 matrix
// 4) <nrgens>
// 5) <start>
//   (only in odd characteristic...
//      6) <sbasis> = GF(p) basis for field taken from <S>
//      7) <tbasis> = GF(p) basis for field taken from <T>
//   )
// OUTPUT: SLP from <can_gens> to <mat>

wbsl2SLP := function( arg1, arg2, arg3, arg4, arg5, arg6, arg7, slg )
local  s, t, h, a, b, c, F, x, slp, sbasis, tbasis, l, sl, n, j,
       sslp, pows, i, tl, tslp, sprg, tprg, hprg, V, phi, p, q;

   s := arg1[1];
   t := arg1[2];
   h := arg1[3];
   a := h[1][1];
   b := t[1][2];
   c := s[2][1];
   F := arg2;
   q := #F;
   p := Characteristic(F);
   x :=  arg3;
   if #F mod 2 eq 1 then
      sbasis := arg6;
      tbasis := arg7;
   end if;

   //sprg := StraightLineProgram([[arg5,1]], arg4);
   //tprg := StraightLineProgram([[arg5+1,1]], arg4);
   //hprg := StraightLineProgram([[arg5+2,1]], arg4);
   sprg := slg.arg5;
   tprg := slg.(arg5+1);
   hprg := slg.(arg5+2);
   
   //slp := StraightLineProgram([[1,0]], arg4);
   slp := Id(slg);

      // reduce to upper triangular
   if x[2][2] eq 0*a then
      x := x*t^-1;
      slp := tprg;
   end if;
         // now x[2][2] ne 0
   l := x[2][1]/x[2][2];
   if l ne 0*l then
      //sl := a^0*[ [1,0] , [-l,1] ];
      sl := Matrix(F, [ [1,0] , [-l,1] ]);
      x := x*sl;
      if #F mod 2 eq 0 then
         //n := LogFFE( l/c , a ) mod (#F-1);
         n := Log( a, l/c ) mod (#F-1);
         if n mod 2 eq 1 then
            n := n + #F - 1;
         end if;
         j := n div 2;
         //sslp := ConjProg( sprg , PowerProg( hprg , j ) );
         sslp := sprg ^  (hprg ^ j);
      else
         V, phi := VectorSpace(F, GF(p), sbasis);
         pows :=
            [Integers()!x : x in Coordinates( V , phi(l))];
         //sslp := StraightLineProgram([[arg5,0]], arg4);
         sslp := Id(slg);
         for i in [1..#pows] do if pows[i] ne 0 then
            //sslp := ProdProg( sslp ,
            //         PowerProg(
            //       ConjProg( sprg , PowerProg( hprg , i-1 ) ) , pows[i] ) );
              sslp := sslp * (sprg^(hprg^(i-1)))^pows[i];
            end if;
         end for;
      end if;
      //slp := ProdProg( sslp , slp );
      slp := sslp * slp;
   end if;

      // reduce to diagonal
   l := x[1][2]/x[1][1];
   if l ne 0*l then
      tl := Matrix(F, [ [1,-l] , [0,1] ]);
      x := x*tl;
      if #F mod 2 eq 0 then
         //n := LogFFE( b/l , a ) mod (#F-1);
         n := Log( a,  b/l ) mod (#F-1);
         if n mod 2 eq 1 then
            n := n + #F - 1;
         end if;
         j := n div 2;
         //tslp := ConjProg( tprg , PowerProg( hprg , j ) );
         tslp := tprg  ^ ( hprg ^ j );
      else
         //pows := IntVecFFE( Coefficients( tbasis , l ) );
         V, phi := VectorSpace(F, GF(p), tbasis);
         pows :=
            [Integers()!x : x in Coordinates( V , phi(l))];
         //tslp := StraightLineProgram([[arg5,0]], arg4);
         tslp := Id(slg);
         for i in [1..#pows] do
            if pows[i] ne 0 then
           //  tslp := ProdProg( tslp , 
           //             PowerProg( 
           //      ConjProg( tprg , PowerProg( hprg , i-1 ) ) , pows[i] ) );
              tslp := tslp * (tprg^(hprg^(i-1)))^pows[i];
            end if;
         end for;
      end if;
      slp := tslp * slp;
   end if;

      // find the correct power of <h>
   if x[1][1]*x[2][2] ne a^0 then
error "<mat> is not in SL(2,<F>)";
   end if;
   //n := LogFFE( x[1][1] , a ) mod (#F-1);
   n := Log( a, x[1][1]) mod (#F-1);
   //slp := ProdProg( PowerProg( hprg , n ) , slp );
   slp := hprg^n * slp;

return slp;
end function;

//////////////////////////////////////////////////////////////////////////////////////////////
// INPUT:
// 1) <data> = black box SL2 recognition data structure
// 2) <x> = black box group element
// OUTPUT: SLP from <data>.<igens> to <x>

bbsl2SLP := function(data, x, slg)
local  f, action, slp, y;  

   f := (data`group)`DefiningField; 
   //f := DefiningField(data.group);

      // first compute the action of <x> on transvection groups
   action := bbsl2ProjectiveAction(data`domain, data`points, f, One(data`group), x);
      
      // write SLP using white box method
   if Characteristic(f) mod 2 eq 1 then
     slp := wbsl2SLP(data`gens, f, action, 3, 1, data`sbasis, data`tbasis, slg);
   else
     slp := wbsl2SLP(data`gens, f, action, 3, 1, 0, 0, slg);
   end if;

      // evaluate SLP in black box group and modify
   //y := ResultOfStraightLineProgram(slp, data.igens); 
   y := Evaluate(slp, data`igens); 
   if y eq x then
      // do nothing
   elif y*data`centre eq x then
      h := hom< Parent(data`centreProg) -> slg | slg.1, slg.2, slg.3 >;
      slp := slp * h(data`centreProg);
   else
      // something is wrong
error "999";
   end if;

return slp;
end function;

////////////////////////////////////////////////////////////////////////////////
///////////// method installation for recognition of SL(2,q) ///////////////////
////////////////////////////////////////////////////////////////////////////////

//// method for SL(2,2)
bruteforceSL22 := function (gp, slg)
local  elts, z, zM, sM, tM, nelts, s, t, hom, data, rf, V;
   //SetDefiningField (gp, GF(2));
   gp`DefiningField := GF(2);
   elts := {x: x in gp};
   if #elts ne 6 then
return "fail";
   end if;
   z := One (gp);
   zM := Matrix(GF(2),[ [1,0] , [0,1] ]);
   sM := Matrix(GF(2),[ [1,0] , [1,1] ]);
   tM := Matrix(GF(2),[ [1,1] , [0,1] ]);
   //if IsMatrixGroup (gp) then
   if Type(gp) eq GrpMat then
      if Dimension (gp) eq 2 then
         if #(BaseRing (gp)) eq 2 then
            //SetIsNaturalRep (gp, true);
            gp`IsNaturalRep := true;
               // natural rep ... just check to see if <sM> and <tM> are in <gp>
            if (not sM in elts) or (not tM in elts) then
return "fail";
            end if;
            rf := recformat<group, matrix, igens, gens>;

            data :=  rec <rf | group := gp,
                          //matrix := List (zM, x -> List (x, y -> y)),
                          matrix := zM,
                          igens := [GL(2,2) | sM, tM, zM],
                          gens := [GL(2,2) | sM, tM, zM] >;
            //SetSL2OracleData (gp, data);
            gp`SL2OracleData := data;
return data;
         end if;
      end if;
   end if;
      // treat as a black box group
   //SetIsNaturalRep (gp, false);
   gp`IsNaturalRep := false;
   nelts := [ x: x in elts | Order (x) eq 2 ];
   if (not #nelts eq 3) then
return "fail";
   end if;
   s := nelts[1];
   t := nelts[2];    // any involutions will do
      // check that we have an iso with SL(2,2)
   //hom := GroupHomomorphismByImages (SL (2, 2), gp, [sM, tM], [s, t]);
   if Order(s*t) ne 3  then
return "fail";
   end if;

   rf := recformat<group, gens, igens, domain, points, centre, centreProg>;
   V := VectorSpace(GF(2),2);
   data := rec < rf | group := gp,
                 gens := [SL(2,2) | sM, tM, zM],
                 igens := [s, t, z],
                 domain := [s, t, t^s],
                 points := [ V![1,0], V![0,1], V![1,1] ],
                 centre := One (gp),
                 centreProg := Id(slg) >;
   //SetSL2OracleData (gp, data);
   gp`SL2OracleData := data;
return data;
end function;

/////// method for SL(2,3)
bruteforceSL23 := function (gp,slg)
local  elts, centre, zM, sM, tM, nelts, s, t, found, i, hom, data, rf, V;
   //SetDefiningField (gp, GF(3));
   gp`DefiningField := GF(3);
   //elts := Elements (gp);
   elts := {x: x in gp};
   if #elts ne 24 then
return "fail";
   end if;
   centre := [x : x in elts | Order (x) eq 2];
   if not #centre eq 1 then
return "fail";
   end if;
   zM := Matrix(GF(3), [ [-1,0] , [0,-1] ] );
   sM := Matrix(GF(3), [ [1,0] , [1,1] ] );
   tM := Matrix(GF(3), [ [1,1] , [0,1] ] );
   //if IsMatrixGroup (gp) then
   if Type(gp) eq GrpMat then
      if Dimension (gp) eq 2 then
         if #(BaseRing (gp)) eq 3 then
            gp`IsNaturalRep := true;
            //SetIsNaturalRep (gp, true);
               // natural rep ... just check to see if <sM> and <tM> are in <gp>
            if (not sM in elts) or (not tM in elts) then
return "fail";
            end if;
            rf := recformat<group, matrix, igens, gens,sbasis,tbasis>;
            data := rec < rf |  group := gp,
                          matrix := zM,
                          igens := [SL(2,3) | sM, tM, zM],
                          gens := [SL(2,3) | sM, tM, zM], 
                          sbasis := Basis (GF(3)),
                          tbasis := Basis (GF(3)) >;
            //SetSL2OracleData (gp, data);
            gp`SL2OracleData := data;
return data;
         end if;
      end if;
   end if;
      // treat as a black box group
   //SetIsNaturalRep (gp, false);
   gp`IsNaturalRep := false;
   nelts := [ x: x in elts | Order (x) eq 3];
   if (not #nelts eq 8) then
return "fail";
   end if;
   s := nelts[1];
      // find a <t> that gives an iso with SL(2,3)
   found := false;
   i := 1;
   while (not found) and (i lt 8) do
      i := i + 1;
      t := nelts[i];
      if Order (s*t) eq 4 then
         found := true;
      end if;
   end while;
   if (not found) then
return "fail";
   end if;
   rf := recformat<
         group, igens, gens, domain,points,sbasis,tbasis,centre, centreProg>;
   V := VectorSpace(GF(3),2);
   data := rec< rf | group := gp,
                 gens := [SL(2,3) | sM, tM, zM],
                 igens := [s, t, centre[1]],
                 domain := [s, t, t^s, t^(s^2)],
                 points := [ V![1,0], V![0,1], V![1,1], V![1,2] ],
                 sbasis := Basis (GF(3)),
                 tbasis := Basis (GF(3)),
                 centre := centre[1],
                 centreProg := slg.3 >;
   //SetSL2OracleData (gp, data);
   gp`SL2OracleData := data;
return data;
end function;


/////////////////////////////////////////////////////////////////////////////////
//
//A SL2OracleData( <group> )  . . . method for groups in their natural repn
//                                 that are generated by transvections 
//
//
//InstallMethod( SL2OracleData, "shortcut", true, 
//               [ IsNaturalRep and HasDefiningField and 
//                 IsGeneratedByTransvectionGroups ], 0,
//function( G )
SL2OracleDataShortcut := function(G)
local   V, r, k, gens, basis, i, ngens, lbasis, ubasis, data, F, 
        intsl, intsu, tl, tu, l, h, W, phi, p, lW, uW, slg;

      ///Print( "{SL2-oracle:} Natural Representation (shortcut) \n" );
      F := G`DefiningField;
      r := PrimitiveElement(F);
      k := Degree(F); //DegreeOverPrimeField(F);
      p := Characteristic(F);
      V := VectorSpace(F,2);
      gens := [ G.i : i in [1..Ngens(G)] ] ;
      if not #gens eq 2*k then
             return "fail";
      end if;
      slg := SLPGroup(3);
      if #F eq 2 then
return bruteforceSL22 (G, slg);
      elif #F eq 3 then
return bruteforceSL23 (G, slg);
      end if;

   // check that <matgp> is not elementary abelian
      if IsIdentity( Comm( gens[1] , gens[k+1] ) ) then
              return "fail";
      end if;

   // first find the centres of the generating transvection groups
      basis := [];
      for i in [1,k+1] do
          if not (Basis(V).1)*gens[i] eq Basis(V).1 then
              Append( ~basis , (Basis(V).1)*gens[i] - Basis(V).1 );
          else
              Append( ~basis , (Basis(V).2)*gens[i] - Basis(V).2 );
          end if;
      end for;
      basis := Matrix(basis);

   // change basis
      ngens :=  [ basis*x*basis^-1 : x in gens ];

   // get "upper" and "lower" bases for F
      //lbasis := Basis( DefiningField(G) , List( ngens{[1..k]}, x->x[2][1] ) );
      //ubasis := Basis( DefiningField(G) , List( ngens{[k+1..2*k]}, x->x[1][2] ) );
      W, phi := VectorSpace(F, GF(p));

      lW := VectorSpaceWithBasis( 
                    [ phi(x[2][1]) : x in [ngens[i]: i in [1..k]] ] ); 
      uW := VectorSpaceWithBasis(
                    [ phi(x[1][2]) : x in [ngens[i]: i in [k+1..2*k]] ] );
   // construct "switcher" <l>
      intsl := [Integers()!x: x in Coordinates( lW, phi(r^0) ) ];
      intsu := [Integers() | Coordinates( uW, phi(-r^0) ) ];
      tl := &* [ gens[i]^intsl[i]: i in [1..k] ];
      tu := &* [ gens[k+i]^intsu[i]: i in [1..k] ];
      l := tl*tu*tl;

   // construct <h>, of order q-1, normalising both transvection groups
      intsl := [Integers()!x: x in Coordinates( lW, phi(-r^-1) ) ];
      intsu := [Integers()!x: x in Coordinates( uW, phi(r) ) ];
      tl := &* [ gens[i]^intsl[i]: i in [1..k] ];
      tu := &* [ gens[k+i]^intsu[i]: i in [1..k] ];
      h := l*tl*tu*tl;

   // and gather the output data
      rf := recformat<
         group, matrix, igens, gens, sbasis, tbasis >;
      data := rec< rf |
                 group := G,
                matrix := Matrix(F, basis),
                 igens := [ gens[1] , gens[k+1] , h ],
                  gens := [ ngens[1] , ngens[k+1] , basis*h*basis^-1 ] >;
      if Characteristic(F) mod 2 eq 1 then
         //data`sbasis := Basis( F , 
         //                    List([0..k-1], i->data.gens[1][2][1]*data.gens[3][1][1]^(2*i)) );
           
         //data`tbasis := Basis( F,  
         //                    List([0..k-1], i->data.gens[2][1][2]*data.gens[3][2][2]^(2*i)) );
//           data`sbasis := [ x@@phi : x in Basis( sub< W |
//     [phi(data`gens[1][2][1]*data`gens[3][1][1]^(2*i)) : i in [0..k-1]] ) ];
//           data`tbasis := [ x@@phi : x in Basis( sub< W |
//     [phi(data`gens[2][1][2]*data`gens[3][2][2]^(2*i)) i in [0..k-1]] ) ];
      data`sbasis :=
               [ data`gens[1][2][1]*data`gens[3][1][1]^(2*i) : i in [0..k-1]];
      data`tbasis :=
               [ data`gens[2][1][2]*data`gens[3][2][2]^(2*i) : i in [0..k-1]];
      end if;

return data;
end function;

/////////////////////////////////////////////////////////////////////////////////
//
//A SL2OracleData( <group> )   . . .  default method for the natural representation 
//
//InstallMethod( SL2OracleData, "natural rep default method", true, 
//               [ IsNaturalRep and HasDefiningField ], 0,
SL2OracleDataNatRep := function(G)

local   F, V,  gmod,  r, a, d, sq,  q, n, k, p, gpp, W, phi, slg,
   count, count1, count2, stop, stop1, stop2,  gens, rnd, data, 
   h, g, x, y, l, s, t, pts, gpts, evecs, evals, matrix, basis, B, ibasis, vec;                     

      ///Print( "{SL2-oracle:} Natural Representation (default) \n" );
      F := G`DefiningField;
      V := VectorSpace(F,2);
      r := PrimitiveElement( F );
      p := Characteristic(F);
      q := #F;
      k := Degree( F );
      slg := SLPGroup(3);
   if (q eq 2) then
return bruteforceSL22 (G, slg);
   elif (q eq 3) then
return bruteforceSL23 (G, slg);
   end if;

   // begin by testing for irreducibility
   // gmod := GModuleByMats( Generators(G) , F );
   // if not MTX.IsIrreducible( gmod ) then
      if not IsIrreducible(G) then
return "fail";
      end if;

   // first find an element <h> of order q-1
      h := sl2ConstructToralElement(G, q);
      if h cmpeq "fail" then
return "fail";
      end if;

   // find the two distinct eigenvectors
      //evals := Eigenvalues( F , h );
      //evecs := Eigenvectors( F , h );
      evals := [y[1]: y in Eigenvalues(h)];
      evecs := [ Eigenspace(h,y).1 : y in evals ];
      pts := [ sub< V | x > : x in evecs ];
      a := evals[1];  // a is a primitive element of GF(q)*

    // find an appropriate conjugate <g> of <h>
      count := 0;
      stop := false;
      gpp := RandomProcess(G);
      while (not stop) and (count lt 50) do
         count := count+1;
         rnd := Random( gpp );
         //gpts := List( evecs , x->Subspace( V , [x*rnd] ) );
         gpts :=  [ sub< V | x*rnd > : x in evecs ];
         if (gpts[1] ne pts[1] and gpts[1] ne pts[2] and
                              gpts[2] ne pts[1] and gpts[2] ne pts[2]) then
               stop := true;
               g := h^rnd;
               basis := [ x*rnd : x in evecs ];
            // <g> is now diagonal relative to <basis>
         end if;
      end while;
      if not stop then
return "fail";
      end if;
      basis := Matrix(basis);
      ibasis := basis^(-1);

   // set up discrete log calculation
      //B := Basis( V , basis );
      W := VectorSpaceWithBasis(basis);
      vec := Coordinates( W , evecs[1] );
      vec := [ vec[1]^(-1)*v : v in vec];   // vec has nonzero first term
      d := vec[2];
        // compute random elements until we find an appropriate one
      count := 0;
      stop := false;
      while (not stop) and (count lt 50) do
         count := count+1;
         count1 := 0;
         stop1 := false;
         while (not stop1) and (count1 lt 10) do  // note this loop unnecessary in char 2
            count1 := count1+1;
            count2 := 0;
            stop2 := false;
            while (not stop2) and (count2 lt 20) do
               count2 := count2+1;
               x := Random( gpp );
               y := basis*x*ibasis;
               if not ( IsZero(y[1][2]-d*y[1][1]) ) 
                  and not ( IsZero(d^2*y[2][1]-d*y[2][2]) ) then
                  stop2 := true;
               end if;
            end while;
            if not stop2 then
return "fail";
            end if;
            sq := (d^2*y[2][1] - d*y[2][2])/(y[1][2]-d*y[1][1]);
            //n := LogFFE( sq , a );
            n := Log( a, sq );
            if (n mod 2 eq 0) then 
               stop1 := true;
               n := (n div 2) mod (q-1);
               s := Comm( h , g^n*x );
            end if;
         end while;
         if not stop1 then
return "fail";
         end if;
         if not ( IsIdentity(s) )
            then stop := true;
         end if;
      end while;
      if not stop then
return "fail";
      end if;

   // do the same to get the upper transvection
      vec := Coordinates( W , evecs[2] );
      vec := [ vec[1]^(-1)*v : v in vec];   // vec has nonzero first term
      d := vec[2];
         // compute random elements until we find an appropriate one
      repeat
         repeat
            repeat
               x := Random( gpp );
               y := basis*x*ibasis;
            until not ( IsZero(y[1][2]-d*y[1][1]) ) 
                  and not ( IsZero(d^2*y[2][1] - d*y[2][2]) );
            sq := (d^2*y[2][1] - d*y[2][2])/(y[1][2]-d*y[1][1]);
            //n := LogFFE( sq , a );
            n := Log( a, sq );
         until (n mod 2 eq 0);  // unnecessary when q is even
         n := (n div 2) mod (q-1);
         t := Comm( h , g^n*x );
      until not ( IsIdentity(t) );  

      matrix := Matrix( evecs );
      //gens := List( [s,t,h], x->matrix*x*matrix^-1 );
      gens := [SL(2,q) |  matrix*x*matrix^-1 : x in [s,t,h] ];
      rf := recformat<
         group, matrix, igens, gens, sbasis, tbasis >;
      data := rec< rf | group := G, matrix := matrix,
                              igens := [SL(2,q) |  s , t , h ], gens := gens >;
      if q mod 2 eq 1 then
          W, phi := VectorSpace(F, GF(p));
         //data.sbasis := Basis( F , List([0..k-1], i->gens[1][2][1]*gens[3][1][1]^(2*i)) );
//           data`sbasis := [ x@@phi : x in Basis( sub< W |
//     [phi(data`gens[1][2][1]*data`gens[3][1][1]^(2*i)) : i in [0..k-1]] ) ];
         //data.tbasis := Basis( F , List([0..k-1], i->gens[2][1][2]*gens[3][2][2]^(2*i)) );
//           data`tbasis := [ x@@phi : x in Basis( sub< W |
//    [phi(data`gens[2][1][2]*data`gens[3][2][2]^(2*i)) : i in [0..k-1]] ) ];
      data`sbasis :=
               [ data`gens[1][2][1]*data`gens[3][1][1]^(2*i) : i in [0..k-1]];
      data`tbasis :=
               [ data`gens[2][1][2]*data`gens[3][2][2]^(2*i) : i in [0..k-1]];
      end if;
return data;
end function;

//////////////////////////////////////////////////////////////////////////////
//
//A SL2OracleData( <group> )  . . . black box method
//
//InstallMethod( SL2OracleData, "black box default method", true, 
//               [ HasDefiningField ], 0,
//function( G )
SL2OracleDataDefault := function(G)
local F, p, k, q, count, limit, h, data1, S, gen, j, data2, a, b, found,
      Y, points, data, s, t, r, bas, one, sM, tM, jM, pows, s0, s0M, slg,
      t1M, u, s1M, s1, t1, hM, zM, sbasis, tbasis, zslp, z, start, W, phi;

      ///Print( "{SL2-oracle:} Black Box \n" );

   F := G`DefiningField;
   p := Characteristic(F);
   k := Degree(F);
   q := #F;
   slg := SLPGroup(3);
   if (q eq 2) then
return bruteforceSL22 (G, slg);
   elif (q eq 3) then
return bruteforceSL23 (G. slg);
   end if;

      // first find an element of order <q>-1 
   h := sl2ConstructToralElement(G, q);
   if h cmpeq "fail" then
return "fail";
   end if;

      // find the two transvection groups normalised by <h>
   count := 0;
   limit := 20;
   repeat   // if <q> is odd, the basic procedure succeeds with prob 0.5
      count := count + 1;
      data1 := bbsl2ConstructTransvectionGroup(G, p, k, h); 
   until not data1 cmpeq "fail" or count eq limit;
   if count eq limit then
return "fail";
   end if;

      // find (matrix of) an automorphism of <S> of order <q>-1 
   S := data1`TransvectionGroup; 
   gen := bbslConstructFieldGenerator(S, h, p, k); 
   if gen cmpeq "fail" then
return "fail";
   end if;

      // construct the permutation domain
   j := data1`Conj;
   data2 := bbsl2ListPermutationDomain(S, gen, j, p, k); 
   Y := data2`TDomain;
   points := data2`PDomain;
   S := data2`TransvectionGroup;

   // assemble the data structure;
   rf := recformat<
         group, matrix, igens, gens, trangp, sbasis, tbasis, domain, points,
                centre, centreProg >;
   data := rec< rf | group := G >;
   s := Y[1];
   t := Y[2];
   r := PrimitiveElement(F);
   //bas := Basis(F, List([0..k-1], i->r^i));
   W, phi := VectorSpace(F, GF(p));
   WW := VectorSpaceWithBasis([ phi(r^i) : i in [0..k-1]]);
   one := One(G);
   sM := bbsl2ProjectiveAction(Y, points, F, one, s)^(1-q);
   if sM ne Matrix(F, [ [1,0] , [1,1] ]) then
      error "wrong matrix 101";
   end if;
   tM := bbsl2ProjectiveAction(Y, points, F, one, t)^(1-q);
   a := tM[1][2];
   pows := [Integers()!x: x in Coordinates(WW, phi(-1/a)) ];
   s0M := Matrix([ [r^0,0*r] , [-1/a,r^0] ]);
   //s0 := Product( List([1..k], i->S[i+1]^pows[i]) );
   s0 := &*[S[i+1]^pows[i] : i in [1..k] ];
   jM := s0M*tM*s0M;
   j := s0*t*s0;
   b := -a/r;
   pows := [ Integers()!x: x in Coordinates(WW, phi(-b/a^2)) ];
   t1M := Matrix([ [1,b] , [0,1] ]);
   u := &*[ S[i+1]^pows[i] : i in [1..k] ];
   t1 := u^j;
   pows := [Integers()!x: x in Coordinates(WW, phi(-b^-1)) ];
   s1M := Matrix([ [1,0] , [-b^-1,1] ]);
   s1 := &*[S[i+1]^pows[i] : i in [1..k] ];
   hM := jM*s1M*t1M*s1M;
   h := j*s1*t1*s1;
   data`gens := [SL(2,q) | sM, tM, hM];
   data`igens := [s, t, h];
   data`trangp := S;
   data`domain := Y;
   data`points := points;
      // construct <z> generating the centre of <G>
      // also construct SLP from {<s>,<t>,<h>} to <z>
   if p mod 2 eq 1 then
      zM := Matrix([ [-r^0,0*r] , [0*r,-r^0] ]);
      //sbasis := Basis( F , List([0..k-1], i->data.gens[1][2][1]*data.gens[3][1][1]^(2*i)) );
      //tbasis := Basis( F , List([0..k-1], i->data.gens[2][1][2]*data.gens[3][2][2]^(2*i)) );
      //data`sbasis := [ x@@phi : x in Basis( sub< W |
     //[phi(data`gens[1][2][1]*data`gens[3][1][1]^(2*i)) : i in [0..k-1]] ) ];
      //data`tbasis := [ x@@phi : x in Basis( sub< W |
      // [phi(data`gens[2][1][2]*data`gens[3][2][2]^(2*i)) : i in [0..k-1]] ) ];
      sbasis :=
               [ data`gens[1][2][1]*data`gens[3][1][1]^(2*i) : i in [0..k-1]];
      tbasis :=
               [ data`gens[2][1][2]*data`gens[3][2][2]^(2*i) : i in [0..k-1]];
      zslp := wbsl2SLP([sM,tM,hM], F, zM, 3, 1, sbasis, tbasis, slg);
      z := Evaluate(zslp, [s,t,h]);
      data`centre := z;
      if z  ne one then 
         data`centreProg := zslp;
      else
         data`centreProg := Id(slg);
      end if;
      data`sbasis := sbasis;
      data`tbasis := tbasis;
   else
      data`centre := one;
      data`centreProg := Id(slg);
   end if;
      
return data;       
end function;

SL2OracleData := function(G)
  if assigned G`IsGeneratedByTransvectionGroups and
    G`IsGeneratedByTransvectionGroups then
    return SL2OracleDataShortcut(G);
  elif assigned G`IsNaturalRep and G`IsNaturalRep then
    return SL2OracleDataNatRep(G);
  else return SL2OracleDataDefault(G);
  end if;
end function;

/////////////////////////////////////////////////////////////////////////////////////
//
//F SL2OracleCall( <group> , <p> , <k> )
//
// the generic SL2-oracle function -- can be called in any algorithmic setting
// sets attributes for <group> that will determine which method is selected

SL2OracleCall := function(G, p, k)
local  q, d, gp, support, cent, bas, data, ndata, igens, rf, slg;

   q := p^k;

      // first deal with small fields
   slg := SLPGroup(3);
   if (q eq 2) then
return bruteforceSL22 (G, slg);
   elif (q eq 3) then
return bruteforceSL23 (G, slg);
   end if;

   G`DefiningField := GF(q);
   if not assigned G`IsGeneratedByTransvectionGroups then
      G`IsGeneratedByTransvectionGroups  := false;
   end if;
   if Type(G) eq GrpMat then
      d := Dimension(G);
      if BaseRing( G ) cmpeq G`DefiningField then
         if d eq 2 then
            gp := G;
            G`IsNaturalRep := true;
         else 
            support := GroupSupport(G, VectorSpace(GF(q), d) );
            if Dimension(support) eq 2 then 
               //gp := Group( List( Generators(G), x->ActionOnSubspace(x, support) ) );
               gp := sub< GL(2,q) |
                  [ ActionOnSubspace(x, support) : x in Generators(G) ] >;
               gp`IsNaturalRep := true;
               gp`DefiningField := GF(q);
               gp`IsGeneratedByTransvectionGroups :=
                      G`IsGeneratedByTransvectionGroups;           
            else
               gp := G;
               gp`IsNaturalRep := false;
            end if;
         end if;
      else   // in black box case
         gp := G;
         gp`IsNaturalRep := false;
      end if;
   else  // most likely, <G> is a permutation group
      gp := G;
      gp`IsNaturalRep := false;
   end if;

   G`IsNaturalRep :=  gp`IsNaturalRep;
   data :=  SL2OracleData(gp);
   if data cmpeq "fail" then
return "fail";
   end if;
   
   if Type(G) eq GrpMat then
      if G`IsNaturalRep and d ne 2 then
            // find preimages of nice gens of <gp> in <G>
         cent := GroupCentralisedSpace(G, VectorSpace(GF(q), d));
         //bas :=  List(Basis(support), x->x) cat List(Basis(cent), x->x);
         bas :=  Matrix(Basis(support) cat Basis(cent));
         //igens := List(data.igens, x->bas^-1*MyInsertBlock(x,d)*bas);
         igens := [SL(d,q) | bas^-1*MyInsertBlock(x,d)*bas : x in data`igens ];
            // eventually we will use SLP groups to handle this part
            // assemble new data structure
         rf := recformat< support,
            group, matrix, igens, gens, sbasis, tbasis, natrep, data >;
         ndata := rec< rf |
           group := G,
           igens := igens,
           gens := data`gens,
           natrep := gp,
           support := support >;
         if assigned data`sbasis then
            ndata`sbasis := data`sbasis;
            ndata`tbasis := data`tbasis;
         end if;
         data := ndata;
      end if;
   end if;
   G`SL2OracleData := data;

return data; 
end function;

/////////////////////////////////////////////////////////////////////////////////////
//
//F SL2SLP( <group> , <element> , <direction> , [ [<nrgens> , <start>] ] )
//
// <group> is a constructively recognised SL2 in any representation; <element> is
// any element of <group>
// output is an SLP from a set of standard generator of <group> to <element>

SL2SLP := function(arg1, arg2, arg3, arg4, slg)
local  data, ndata, y, G, x, nrgens, start;

   G := arg1;
   x := arg2;

   if not assigned G`SL2OracleData then
print "<G> must first be constructively recognised as SL2";
return "fail";
   end if;

   data := G`SL2OracleData;
   if G`IsNaturalRep then
      if arg4 cmpne 0 then
         nrgens := arg4[1];
         start := arg4[2];
      else
         nrgens := 3;
         start := 1;
      end if;
      if "support" in Names(data) and assigned data`support then
        ndata := SL2OracleData(data`natrep);
        y := ndata`matrix * ActionOnSubspace(x, data`support) * ndata`matrix^-1;
      else
         ndata := data;
         if arg3 eq "i" then  
               // want to write an SLP to an element in the image
               // first need to change basis
            y := data`matrix * x * data`matrix^-1;
         elif arg3 eq "p" then
               // want to write an SLP to an element in the standard copy
               // no need to change basis
            y := x;
         end if;
      end if;
      if Characteristic( G`DefiningField ) mod 2 eq 0 then
return wbsl2SLP(ndata`gens, G`DefiningField, y, nrgens, start, 0, 0, slg);
      else
return wbsl2SLP(ndata`gens, G`DefiningField, y, nrgens, start,
                                         ndata`sbasis, ndata`tbasis, slg);
      end if;
   else
return bbsl2SLP(data, x, slg);
   end if;

end function;

///// some routines that will be useful in applications of the SL2 oracle /////

/////////////////////////////////////////////////////////
// INPUT: recognised SL2
// OUTPUT: element interchanging nice transvection groups
sl2ConstructSwitchingElement := function(G, slg)
local  F, one, lM, data, slp, l;
   if not assigned G`SL2OracleData then
print "<G> must first be constructively recognised as SL2";
return "fail";
   end if;
   F := G`DefiningField;
   one := One(F);
   lM := Matrix([ [0*one,one] , [-one,0*one] ]);
   data := G`SL2OracleData;
   if Characteristic(F) mod 2 eq 0 then
      slp := wbsl2SLP(data`gens, F, lM, 3, 1, 0, 0, slg);
   else
      slp := wbsl2SLP(data`gens, F, lM, 3, 1, data`sbasis, data`tbasis, slg);
   end if;
   l := Evaluate(slp, data`igens);
return l;
end function;
