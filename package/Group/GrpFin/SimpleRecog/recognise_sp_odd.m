freeze;
import "slbbrec.m": FindGoodElement, SL2DataStructure, LDataStructure,
       AppendTran, IsInTranGroup, SLConstructGammaTransv, SLdata, SLSLP,
       AdjustSeqenceUniverse, EvaluateBBGp, EvaluateMat;

///////////////////////////////////////////////////////////////////////////
//                                                                       //
// This is the implementation of the Kantor-Seress PSp(d,q) algorithm;   //
// at present code only exists for the case when <q> is odd.             //
//                                                                       //
///////////////////////////////////////////////////////////////////////////

/*
Spdata := recformat<
bbg, prime, power, gens, FB, sprog, trangp, trangpgamma, 
  centre, centreprog, c, cprog, t21, t21invtran, sinv, slpgrp, 
  rootgp, form
 >;
*/


///////////////////////////////////////////////////////////////////////////
//
//F Sp4OddConstructQ( <bbgroup>, <prime>, <power> )
//

Sp4OddConstructQ := function (bbg, bbrand, pp, e)
   local     q,        // field size
             p,        // the characteristic
             r,        // element of p.ppd^/(p;2e) order
             t,        // p-part of r
           tau,        // p'-part of r
         tauinv,       // inverse of tau
        i,j,stop,      // loop variables
          y1,z,h,      // random elements
            y2,        // y1*tau
         y1inv,y2inv,  // inverses of y1,y2
            t1,        // conjugate of t
          t1inv,       // its inverse
             T,        // transvection group containing t
            T1,T2,     // transvection groups T^y1, T^y2
     limit,jlimit,     // number of iterations
       commlimit,
             H,        // generators for C_G(t)'
            comm,      // [h,t1]
             B,        // the group T.[T1,Q].T1
            commlist,  // generators for B
             x,        // generator for Q
            xinv,      // inverse of x
            xtotau,    // x^tau
             Q,        // generators for Q
             u,        // first input generator
           adjust,     // T^adjust = transvection group of bbg.1
          adjustinv,   // inverse of adjust
         algadata,     // 2-dim data structure 
             L;        // 2-dim group acting on Q/T


   // If this is a call to start in dimension > 4 then we have -p as the 
   // input prime. In this case, we use smaller limits to report failure,
   // and more importantly, we have to adjust the construction such that
   // the constructed T is the transvection group the first input generator
   // belongs to.
 
   if pp lt 0 then 
      p := -pp;
   else 
      p := pp;
   end if;
   q := p^e;
   j := 1; 
   stop := false;
   if pp lt 0 then 
      limit := 5*q;
      jlimit := 4;
   else 
      limit := 20*q;
      jlimit := 8;
   end if;
   repeat
      r := FindGoodElement(bbg, bbrand, p, e, 4, limit);
      if r cmpeq "fails" then 
         return "fails";
      end if;

      t := r^(q^2 -1);
      tau := r^p;
      tauinv := tau^(-1);
      i := 1; 
      repeat 
        y1 := Random(bbrand);
        t1 := t^y1;
        if ((t,t1) eq One(bbg)) and (not ((t1,t1^tau) eq One(bbg)) ) 
           and (not ((tau,tau^t1) eq One(bbg)) ) then 
           stop := true;
//" found t1 with j=",j,"  i=", i, "  limit=", limit;
        else 
           i := i+1;
        end if;
        until stop or (i eq limit);
        if not stop then 
           j := j+1;
        end if;
   until stop or j eq jlimit;
   if not stop then 
      return "fails";
   end if;

   t1inv := t1^(-1);   
   y2 := y1 * tau;
   H := sub<Generic(bbg) | [Generic(bbg)|t1, tau]>;
   if pp lt 0 then 
      limit := 128*e*q;
      commlimit := 2*e*p div (p-1);
   else 
      limit := 128*e*q;
      commlimit := 2*e*p div (p-1);
   end if;
   i := 1; 
   stop := false;
   commlist:=[Generic(bbg) | t1];
   HP := RandomProcess(H);
   repeat 
     h := Random(HP);
     comm := (t1,h);
     if (not comm  eq  One(bbg)) and (comm^(p^2)  eq  One(bbg)) then
         Append(~commlist, comm);
     end if;
     if #commlist  eq  commlimit then 
//"found commlist in i=",i,"  limit=",limit;
        stop := true;
     else 
        i := i+1;
     end if;
   until stop or (i  eq  limit);
   if not stop then 
      //"not enough elements of [Q,T_1]T_1 are found";
      return "fails";
   end if;
   B := sub<Generic(bbg) | commlist>;
   limit := 4*q;
   i := 1; 
   stop := false;
   BP := RandomProcess(B);
   repeat
     x := Random(BP);
     xtotau := tauinv*x*tau;
     if (not (x eq xtotau)) and (One(bbg) eq (xtotau*x)^(p^2)) then
        stop := true;
//"found x in i=",i,"  limit=",limit;
//"dim=", #BaseFixedSpace([x![1]]);
     end if;
     i := i+1;
   until stop or (i  eq  limit);
   if not stop then 
       //"no element of Q-T found";
      return "fails";
   end if; 

   // construct Q
   Q := [Generic(bbg) | x];
   for i in [1..2*e-1] do 
      Q[i+1] := tauinv * Q[i] * tau;
   end for;

   // construct T
   T := {@ One(bbg) @};
   AppendTran(bbg,~T,t,p);
   if e gt 1 then 
      xinv := x^(-1);
      i := 1;
      stop := false;
      repeat 
         comm := xinv * Q[i]^(-1) * x * Q[i];
         if not IsInTranGroup(bbg,T,comm) then
            AppendTran(bbg,~T,comm,p);
         end if;
         i := i+1;
      until #T eq q or i eq 2*e+1;
      if #T lt q then
//"not enough elements of T found";
         return "fails";
      end if;
   end if;

   // now make the adjustment if pp<0
   // the first generator of bbg is a transvection; if perpendicular to 
   // T, T^y1, T^(y1*tau) then it is in T. Otherwise, we can conjugate
   // one of these three to the transvection group containing it
   T := [ Generic(bbg) |  t: t in T ];
   if pp lt 0 then 
      u := bbg.1;
      t := T[2];
      if not (t,u) eq One(bbg) then
         adjust:=SLConstructGammaTransv(bbg,T,[u]); 
         if adjust  cmpeq  "fails" then 
//"SLConstructGamma failed";
            return "fails"; 
         end if;
      elif not (t^y1,u) eq One(bbg) then    
         y1inv := y1^(-1);
         T1 := [Generic(bbg) | One(bbg)];
         for i in [2..q] do 
            T1[i] := y1inv * T[i] * y1;
         end for;
         adjust := SLConstructGammaTransv(bbg,T1,[u]);
         if adjust  cmpeq  "fails" then 
             "SLConstructGamma failed";
            return "fails"; 
         else 
            adjust := y1 * adjust;
         end if;
      elif not (t^y2,u) eq One(bbg) then    
         y2inv := y2^(-1);
         T2 := [Generic(bbg) | One(bbg)];
         for i in [2..q] do 
            T2[i] := y2inv * T[i] * y2;
         end for;
         adjust := SLConstructGammaTransv(bbg,T2,[u]);
         if adjust  cmpeq  "fails" then 
                "SLConstructGamma failed";
            return "fails"; 
         else 
            adjust := y2 * adjust;
         end if;
      else
         adjust := One(bbg);
      end if;
      if not adjust  eq  One(bbg) then 
         adjustinv := adjust^(-1);
         for i in [2..q] do 
             T[i] := adjustinv * T[i] * adjust;
         end for;
         for i in [1..2*e] do 
            Q[i] := adjustinv * Q[i] * adjust;
         end for;
         y1 := adjustinv * y1 * adjust;
         y2 := adjustinv * y2 * adjust;
         tau := adjustinv * tau * adjust;
         t := adjustinv * t * adjust;
      end if;
   end if;  // pp lt 0
//"so far";
   // handle the SL(2,q) acting on <alpha,gamma>
   // <gamma> is not known yet, the second transvection group in the output
   algadata := LDataStructure( bbg, p, e, T, t^(tau^y1) );
   if algadata  cmpeq  "fails" then 
//"algadata fails";
      return "fails";
   end if;

   T := algadata`trangp[1];
   // L  eq  <T^y1, T^(y1*tau)> is SL(2,q), acting on Q/T. 
   L := [Generic(bbg) | ];
   for i in [1..e] do
      L[i] := T[i+1]^y1;
      L[e+i] := T[i+1]^y2; 
   end for;
   
   return rec<SLdata |
       Q:=Q, tau:=tau, y1:=y1, y2:=y2, L:=L, algadata := algadata >;

end function;


/////////////////////////////////////////////////////////////////////////////
//
//F SpConjInQ(<bbg>, <x>, <y>, <T>, <T^y>, <something>, <p>, <e>)
//
// T^x and T^y are points not perpendicular to T and we want an element
// of Q conjugating T^x to T^y. <something> is either a list of generators
// for Q such that for odd p, 2e-long blocks generate two root groups;
// for p=2, ...
// other possibility for <something> is a record with component pQ
// pQ has e generators for each root group

SpConjInQ := function(bbg, x, y, T, Ttoy, sg, p, e) 
   local       t,         // element of T
               X,Y,       // elements of T^x, T^y
             stop,i,j,    // loop variables
               q,         // field size
              conj,       // One(bbg) or t, to make T^x, T^y not perp
               u,         // element of < T^x, T^y > 
              uinv,       // its inverse
              comm,
             limit,       // number of iterations
             genlist,     // generators for [Q,u]/T
             newgen,      // element of genlist, modified by T
               v,         // element of T conjugating T^y to perp of T^x
              vinv,       // its inverse
               B,         // list of the group <genlist>
            w1,w2,        // in t^(T^x), then in t^(T^y)
             X1,X2,       // elements of T^x
             Y1,Y2,       // in T^y
            findsi,       // function to find s_i as in sec. 5.3.2
        s1x,s2x,s1y,s2y,  // in T, the values for s_i (role of T,T^x changed)
             g,h;         // as in 5.3.2

   q := p^e;
   t := T[2];
   X := t^x;
   // handle trivial case
   if IsInTranGroup(bbg,Ttoy,X) then 
      return One(bbg);
   end if;
   Y := Ttoy[2];

   // if necessary, replace t^x by t^(xt) to make nonperp to t^y
   if (X, Y)  eq  One(bbg) then 
      if (X^t, Y)  eq  One(bbg) then 
           //"something is wrong in SpConjInQ";
         return "fails";         
      else 
         conj := t;
         X := X^t;
      end if;
   else
      conj := One(bbg);
   end if;

   // find the intersection of the line <X,Y> and alpha^perp
   i := 1; 
   stop := false;
   repeat 
     u :=  X^Ttoy[i];
     if (t, u)  eq  One(bbg) then
        stop := true;
     end if;
     i := i+1;
   until stop or i eq q+1;
   if not stop then 
      return "fails";
   end if;
   uinv := u^(-1);

   // find size q^2 subgroup of Q containing the conjugating element
   if Type(sg) eq SeqEnum then 
      if p gt 2 then 
         // from 4 dimensions, 2e generators came; these were conjugated 
         // to get generators for Q
         limit := 1 + #sg div (2*e);
      else 
         i:=1; ///////////////////////
      end if;
      genlist := [Generic(bbg) | ];
      i := 1; 
      stop := false;
      repeat 
         if (not (uinv * sg[2*e*(i-1)+1] * u eq sg[2*e*(i-1)+1])) or
            (not (uinv * sg[2*e*(i-1)+2] * u eq sg[2*e*(i-1)+2]))  then
            stop := true;
            for j in [1..2*e] do
                comm := (u, sg[2*e*(i-1)+j]);
                if (not comm eq One(bbg)) then 
                   Append(~genlist, comm);
                end if;
            end for;
         end if;
         i := i+1;
      until stop or i eq limit; 
   else  //generators for Q are stored in a record
      limit := 1 + #sg`pQ div (e);
      genlist := [Generic(bbg) | ];
      i := 1; 
      stop := false;
      repeat 
         if (not (uinv * sg`pQ[e*(i-1)+1] * u eq sg`pQ[e*(i-1)+1])) then
            stop := true;
            for j in [1..e] do
                comm := (u, sg`pQ[e*(i-1)+j]);
                if (not comm eq One(bbg)) then 
                   Append(~genlist, comm);
                end if;
            end for;
         end if;
         i := i+1;
      until stop or i eq limit; 
   end if;  // IsList(sg)
   if not stop then 
      // T must have the conjugating element
      // SpConjInQ will exit from this if statement in any case
      i := 2; 
      repeat 
         if (X^T[i],Y)  eq  One(bbg) then
            return T[i];
         end if;
         i := i+1;
      until i eq q+1; 
//"could not construct A";
      return "fails";
   end if;

   // genlist and Tgen generate A (in the notation of sec. 5.3.2)
   // modify genlist to be in X^perp
   for j in [1..#genlist] do
      i := 1;
      stop := false;
      repeat 
         newgen := genlist[j]*T[i];
         if (X^newgen, X)  eq  One(bbg) then 
            stop := true; 
            genlist[j] := newgen;
         end if;
         i := i+1;
      until stop or i eq q+1;
      if not stop then 
//"could not modify genlist";
         return "fails";
      end if;
   end for;

   // find v in T which conjugates Y to X^perp
   i := 2;
   stop := false;
   repeat 
      if (Y^T[i],X)  eq  One(bbg) then 
         stop := true;
         v := T[i];
      end if;
      i := i+1;
   until stop or i eq q+1;
   if not stop then 
//"could not find v";
      return "fails";
   end if;
   vinv := v^(-1);

   // list the group generated by genlist
   B := {@ One(bbg) @};
   limit := 1+#genlist;
   i := 1; 
   stop := false;
   repeat 
      if not IsInTranGroup(bbg,B,genlist[i]) then 
         AppendTran(bbg,~B,genlist[i],p);
      end if;
      i := i+1;
   until #B eq q or i eq limit;
   if #B lt q then 
      return "fails";
   end if; 

   if q le 3 then 
      i := 2;
      stop := false;
      repeat 
         if IsInTranGroup(bbg,Ttoy,X^(B[i]*vinv)) then 
            return conj*B[i]*vinv;
         end if;
         i := i+1;
      until i eq q+1;
      return "fails";
   end if;

   conj := conj * vinv;
   X := v * X * vinv;

   findsi := function(bbg, X, w, T)
      local i, stop;
      i := 2;
      stop := false;
      repeat 
         if (X,w^T[i])  eq  One(bbg) then
            stop := true;
         else
            i := i+1;
         end if;
      until stop or i eq q+1;
      if stop then 
         return T[i];
      else
//"could not find si";
         return "fails";
      end if;
   end function; 

   X1 := T[2]^(x*conj);
   w1 := t^X1;
   s1x := findsi(bbg, X, w1, T);

   X2 := T[3]^(x*conj);
   w2 := t^X2;
   s2x := findsi(bbg, X, w2, T);
   g := X1*s1x*X1*X2*s2x*X2;

   Y1 := T[2]^y;
   w1 := t^Y1;
   s1y := findsi(bbg, Y, w1, T);

   Y2 := T[3]^y;
   w2 := t^Y2;
   s2y := findsi(bbg, Y, w2, T);
   h := Y1*s1y*Y1*Y2*s2y*Y2;

   // find element of B conjugating g to h. If we used different 
   // T[k],T[j] values for Xi and Yi then only the condition 
   // (g^b,h) eq One(bbg) would be true
   // Important: T[3] is not the inverse of T[2] (because of way of T-listing)
   i := 2; 
   repeat
      if g^B[i]  eq  h then 
         return conj * B[i];
      end if;
      i := i+1;
   until i eq q+1;
//"could not find b in B";
//for b in B do  IsInTranGroup(bbg,Ttoy,X^b) ); end for;
//for b in B do  g^b eq h ); end for;
//for b in B do  (g^b,h) eq One(bbg) ); end for;
   return "fails";

end function;


///////////////////////////////////////////////////////////////////////////
//
//F SpFindGenerators( <bbg>, <J data str>, <rand elmt>, <p>, <e>, <dim> )
//
// Finds generators for L, and GF(p)-generators for Q

SpFindGenerators := function(bbg, data1, r, p, e, d)
   local tau,        // p'-part of r
          Q,         // generators for Q
         len,        // length of Q (before extension)
         i,j,        // loop variables
         y1,y2,      // conjugating elements
         T,Tgamma,   // transvection groups
          t,         // element of T
          L,         // generators for L
         lgen,       // a generator of L, before modification
          x,         // conjugating element
          u,         // element of Q, for conjugation
        jgamma,      // conjugating element, alpha->gamma
         conj;       // another conjugating element

   tau := r^p; 
   Q := data1`Q;
   //ChangeUniverse(~Q,Generic(bbg));
   len := #Q;
   for i in [1..d-4] do
       for j in [1..len] do
          Q[i*len+j] := Q[(i-1)*len+j]^tau;
       end for;
   end for;

   // we modify the generators of L so they fix <gamma>
   L := [Generic(bbg)|];
   y1 := data1`y1;
   y2 := data1`y2;
   Tgamma := data1`algadata`trangpgamma[1];
   T := data1`algadata`trangp[1];
   t := T[2];
   jgamma := data1`algadata`c[2];

   for i in [0 .. d-4] do
      // the method is described in 5.6.1; we have to modify the generators
      // of L so that they are not perp to T 
      lgen := t^y1; 
      if (lgen^y1,t) eq One(bbg) then
         x := y2*y1;
      else 
         x := y1*y1;
      end if;
      u := SpConjInQ(bbg,x,jgamma,T,Tgamma,Q,p,e);
      if u  cmpeq  "fails" then
         return "fails";
      else 
         conj := y1 * u;
         for j in [2..e+1] do 
            Append(~L, T[j]^(conj));
         end for;
      end if;
      // repeat with the other transvection group generating SL(2,q)
      lgen := t^y2;
      if (lgen^y2,t) eq One(bbg) then
         x := y1*y2;
      else 
         x := y2*y2;
      end if;
      u := SpConjInQ(bbg,x,jgamma,T,Tgamma,Q,p,e);
      if u  cmpeq  "fails" then
         return "fails";
      else 
         conj := y2 * u;
         for j in [2..e+1] do 
            Append(~L, T[j]^(conj));
         end for;
      end if;
      // modify y1,y2
      y1 := y1 * tau;
      y2 := y2 * tau;
   end for;

   return rec< SLdata | L:=L, Q:=Q >;
end function;


////////////////////////////////////////////////////////////////////////////
//
//F SpConstructBasisQ( <bbg>, <data>, <Q>, <data1>, <dim>, <field size> )
// 
// <data> is the data structure of L to construct straight-line programs
// <data1> is the data structure of SL(2,q) acting on <alpha,gamma>
// output is the listing of the first root group of Q

SpConstructBasisQ := function(bbg,data, Q, data1, d, q)
   local t21,         // transvection in 5.4.1
         t21invtran,  // its inverse transpose
         c,           // as in 5.4.1
         baseQ,       // GF(q)-basis of Q
         k,stop,      // loop variables
         h, hinv,     // as in 5.4.1
         s,           // as in 5.4.2
         sinv,        // the inverse of s
         newtrangp,   // re-listing of data1`trangp[1]
         pos,         // position in data1`trangp[1]
         pow,         // an exponent of rho
         i,           // power of s to compute
         u,uinv,      // element of SL(2,q) acting on <alpha,gamma> and inverse
         R,           // first short root group of Q
         b1,          // first basis vector of Q
         b1prime,     // second basis vector of Q
         comm,        // [b1,b1prime]
         b1image;     // b1^h

   t21 := data`t21;
   sinv := data1`sinv;
   s := sinv^(-1);
   hinv := data`sinv;
   h := hinv^(-1);

   // find a nontrivial element of the first transvection group of Q
//////////////////////////
// may change when we know how long blocks Q has in even characteristic
//////////////////////////
   stop := false;
   i := 1;
   w := PrimitiveElement(GF(q));
   repeat 
     b1 := (Q[i],t21);
     if not One(bbg)  eq  b1 then 
        if (q mod 2)  eq 1  then 
           b1 := (b1,h);
        end if;
        stop := true; 
     else
        i := i+1;
     end if;
   until stop or (i  gt  #Q);
   if not stop then 
      return "fails";
   end if;

   // adjust s, listings in data1
   b1image := hinv * b1 * h;
   stop := false;
   i := 1;
   repeat 
      b1image := s * b1image *sinv;
      if b1  eq  b1image then
         stop := true;
      else 
         i := i+1;
      end if;
   until stop or i eq q;
   if not stop or (GCD(q-1,i) gt 1) then 
      return "fails";
   end if;
//"found adjusting power i=",i;
   // conjugation by s^i has the same effect as conjugation by h;
   // we have to replace multiplication by rho with rho^i in data1
   if i gt 1 then 
      newtrangp := [Generic(bbg) | One(bbg), data1`trangp[1][2]];
      for k in [1..q-2] do 
         pos := k*i mod (q-1);
         newtrangp[k+2] := data1`trangp[1][2+pos];
      end for;
      data1`trangp[1] := newtrangp;

      newtrangp := [Generic(bbg) | One(bbg), data1`trangpgamma[1][2]];
      for k in [1..q-2] do 
         pos := k*i mod (q-1);
         newtrangp[k+2] := data1`trangpgamma[1][2+pos];
      end for;
      data1`trangpgamma[1] := newtrangp;
   end if;

   // adjust T so that b1 has 1 as non-diagonal entries
   if q mod 2  eq  1 then
      b1prime := b1^data`c[2];
      comm := (b1,b1prime);
      pos := Position(data1`trangp[1],comm);
      if pos eq 0 then
//"error at adjusting b1"; 
         return "fails";
      end if;
      pow := Log(w, GF(q)!(-2));
      if pos  lt  pow+2 then 
         newtrangp := [ Generic(bbg) | One(bbg) ];
         newtrangp cat:= [data1`trangp[1][i] : i in [q+pos-pow-1 .. q]];
         newtrangp cat:= [data1`trangp[1][i] : i in [2..q+pos-pow-2]];
         data1`trangp[1] := newtrangp;
      elif pos  gt  pow+2 then 
         newtrangp := [ Generic(bbg) | One(bbg) ];
         newtrangp cat:= [data1`trangp[1][i] : i in [pos-pow .. q]];
         newtrangp cat:= [data1`trangp[1][i] : i in [2..pos-pow-1]];
         data1`trangp[1] := newtrangp;
      end if; 
   end if;
   // shift data1`trangpgamma so that the first nontriv. element is mapped to
   // [[1,1],[0,1]]
   // what we do below is to compute the label of the point alpha^Tgamma[2]
   // and replace Tgamma[2] by an element of its transvection group
   // This piece of code is copied from SL2ReOrder
   u := data1`trangp[1][2]^data1`trangpgamma[1][2];
   uinv := u^(-1);
   k := 2; 
   stop := false;
   repeat 
     if data1`trangpgamma[1][2]^data1`trangp[1][k]  eq  
           uinv * (data1`trangpgamma[1][2]^data1`trangp[1][k]) * u   then 
        stop := true;
        if k gt 2 then 
           newtrangp := [ Generic(bbg) | One(bbg)];
           newtrangp cat:= [data1`trangpgamma[1][i] : i in [k..q]];
           newtrangp cat:= [data1`trangpgamma[1][i] : i in [2..k-1]];
AdjustSeqenceUniverse(~data1`trangpgamma,newtrangp);
           data1`trangpgamma[1] := newtrangp;
        end if;
     else 
        k := k+1;
     end if;
   until stop or (k eq q+1);
   if not stop then 
      return "fails";
   end if;

   for k in [1..data1`power] do
      data1`gens[k][1] := data1`trangp[1][k+1];
      data1`gens[data1`power + k][1] := data1`trangpgamma[1][k+1];
   end for;
   data1`sinv := EvaluateBBGp(data1`bbg, data1`gens, data1`sprog[2]);
   data1`c[2] := EvaluateBBGp(data1`bbg, data1`gens, data1`cprog[2]);
   data1`t21 := data1`gens[1][1];
   data1`t21invtran := data1`t21^data1`c[2];

   // list first short root group of Q
   R := [ Generic(bbg) | One(bbg), b1];
   for k in [2..q-1] do
      R[k+1] := hinv * R[k] * h;
   end for;
   return R, data1;
end function;

////////////////////////////////////////////////////////////////////////////
//
//F SpLinearCombQ(<rootgp>, <t21>, <j>, <c>, <hinv>, <dim>, <w>)
//
// <rootgp> is the listed root group in Q
// t21, c, j, h as in section 5.4.1 
// <w> is the vector to decompose

SpLinearCombQ := function(R,t21,j,c,hinv,d,w)
   local cinv,      // the inverse of c
         jinv,      // the inverse of j
           h,       // inverse of hinv; conjugation by rho
         wconj,     // conjugate of w
         coord,     // a component of w
         coord2,    // coord without the T-part
         i,k,stop,  // loop variables
         vec,       // output vector
         q,         // field size
         rho;       // generator of GF(q)^*

   cinv := c^(-1); 
   jinv := j^(-1);
   h := hinv^(-1);
   q := #R;
   rho := PrimitiveElement(GF(q));
   wconj := w;
   vec := [GF(q)|];
   for i in [1..(d-2) div 2] do
      coord := (wconj, t21); 
      if (q mod 2)  eq  1 then 
         coord2 := (coord, h);
      else 
         coord2 := coord;
      end if;
      stop := false; 
      k := 1;
      repeat 
        if R[k]  eq  coord2 then
           stop := true;
           if k  eq  1 then 
              vec[2*i] := 0;
           else 
              vec[2*i] := rho^(k-2);
              if (q mod 2)  eq  1 then 
                 vec[2*i] := vec[2*i] * (rho -1)^-1;
              end if;
           end if;
        else 
           k := k+1;
        end if;
      until stop or (k eq q+1);
      if not stop then 
//"even position";
         return "fails";
      end if;
      // divide out component just found, get (2i-1)st component into position
      wconj := wconj * jinv * coord^(-1) * j;
      wconj := jinv * wconj * j;
      coord := (wconj, t21); 
      if (q mod 2)  eq  1 then 
         coord2 := (coord, h);
      else 
         coord2 := coord;
      end if;
      stop := false; 
      k := 1;
      repeat 
        if R[k]  eq  coord2 then
           stop := true;
           if k  eq  1 then 
              vec[2*i-1] := 0*rho;
           else 
              vec[2*i-1] := rho^(k-2);
              if (q mod 2)  eq  1 then 
                 vec[2*i-1] := vec[2*i-1] * (rho -1)^-1;
              end if;
           end if;
        else 
           k := k+1;
        end if;
      until stop or (k eq q+1);
      if not stop then 
//"odd position";
         return "fails";
      end if;
      // divide out component just found, get next two components into position
      wconj := wconj * coord^(-1);
      wconj := c * wconj * cinv;
   end for;

   return vec;

end function;


forward SpSLP;

/////////////////////////////////////////////////////////////////////////
//
//F SpFinishConstruction( <bbg>, <data2>, <algadata>, <Q>, <dim> )
//
// data2 is the data structure of L, to be augmented
// algadata is the SL(2,q) data structure on <alpha,gamma>
// <Q> is a generator list of Q 

SpFinishConstruction := function(bbg, data2, algadata, Q, d)
   local p,e,q,rho,    // as usual
           R,          // first short root group of Q
           j,jinv,     // conjugating e1->e2->-e1 and its inverse
           c,cinv,     // conjugating W1->W2-> ... ->W(d-1)->W1 and inverse
           i,k,        // loop variables
      jgamma,jgammainv,// conjugating e(d-1)->e(d)->-e(d-1) and inverse
         centgen,      // generator of center in matrix form
         centslp,      // slp to centgen
          mat,         // matrix used in construction of c in 5.4.1
         cprog;        // slp to mat

   p := data2`prime;
   e := data2`power;
   q := p^e;
   rho := PrimitiveElement(GF(q));

   R, algadata := SpConstructBasisQ(bbg, data2, Q, algadata, d, q);
   if R  cmpeq  "fails" then 
      return "fails";
   else 
      if d eq 4 then 
         data2`rootgp := [];
         data2`rootgp[2] := R;
      else 
         AdjustSeqenceUniverse(~data2`rootgp,R);
         data2`rootgp[d div 2] := R;
      end if;
   end if;

   // add new generators
   j := data2`c[2];
   jinv := j^(-1);
   data2`gens cat:=
     [< R[i+1],[<d,1,rho^(i-1)>,<2,d-1,rho^(i-1)>] > : i in [1..e]];
   data2`gens cat:=
    [< jinv * R[i+1] * j, [<d,2,rho^(i-1)>,<1,d-1,-rho^(i-1)>] > : i in [1..e]];
/*
   for i in [1..e] do 
      data2`gens[e*(d-2)^2 div 2+i]:=
                < R[i+1],[<d,1,rho^(i-1)>,<2,d-1,rho^(i-1)>] >;
      data2`gens[e*(d-2)^2 div 2+e+i]:= < jinv * R[i+1] * j,
                               [<d,2,rho^(i-1)>,<1,d-1, -rho^(i-1)>] >;
   end for; 
*/
   c := data2`c[d-3];
   cinv := c^(-1);
   for k in [1..(d-4) div 2] do 
      data2`gens cat:=
       [< cinv * data2`gens[e*(d-2)^2 div 2+2*e*(k-1)+i][1] * c,
             [<d,2*k+1,rho^(i-1)>,<2*k+2,d-1,rho^(i-1)>] > : i in [1..e]];
      data2`gens cat:=
       [< cinv * data2`gens[e*(d-2)^2 div 2+2*e*(k-1)+e+i][1] * c,
               [<d,2*k+2,rho^(i-1)>,<2*k+1,d-1,-rho^(i-1)>] > : i in [1..e]];
/*
      for i in [1..e] do 
         data2`gens[e*(d-2)^2 div 2+2*e*k+i]:= 
         < cinv * data2`gens[e*(d-2)^2 div 2+2*e*(k-1)+i][1] * c, 
                   [<d,2*k+1,rho^(i-1)>,<2*k+2,d-1,rho^(i-1)>] >; 
         data2`gens[e*(d-2)^2 div 2+2*e*k+e+i]:= 
         < cinv * data2`gens[e*(d-2)^2 div 2+2*e*(k-1)+e+i][1] * c, 
                   [<d,2*k+2,rho^(i-1)>,<2*k+1,d-1,-rho^(i-1)>] >; 
      end for;
*/
   end for;
   jgamma := algadata`c[2];
   jgammainv := jgamma^(-1);
   for i in [1..(d-2)*e] do
      data2`gens[e*d*(d-2) div 2+i] := 
         < jgammainv * data2`gens[e*(d-2)^2 div 2+i][1] * jgamma,
           data2`gens[e*(d-2)^2 div 2+i][2] >;
      data2`gens[e*d*(d-2) div 2+i][2][1][1] := d-1;
      data2`gens[e*d*(d-2) div 2+i][2][1][3]:=
                -data2`gens[e*d*(d-2) div 2+i][2][1][3];
      data2`gens[e*d*(d-2) div 2+i][2][2][2] := d;
   end for;
   for i in [1..e] do
      data2`gens[e*d^2 div 2 -2*e+i]:=
            < algadata`gens[i][1],[<d,d-1,rho^(i-1)>] >;
      data2`gens[e*d^2 div 2 -e+i]:=
            < algadata`gens[e+i][1],[<d-1,d,rho^(i-1)>] >;
   end for;

   data2`bbg := bbg;
   data2`form := ZeroMatrix(GF(q),d,d);
   for i in [1..d div 2] do
      data2`form[2*i-1][2*i] := 1;
      data2`form[2*i][2*i-1] := -1;
   end for;

   mat := IdentityMatrix(GF(q), d);
   mat[1][1] := 0;
   mat[1][d-1] := 1;
   mat[2][2] := 0;
   mat[2][d] := 1;
   mat[d-1][d-1] := 0;
   mat[d-1][1] := 1;
   mat[d][d] := 0;
   mat[d][2] := 1;
   oldSG := data2`slpgrp;
   SG := SLPGroup(e * d^2 div 2);
   hslp := hom<oldSG->SG | [SG.i : i in [1..Ngens(oldSG)]] >;
   sprog := [];
   for i in [1 .. #data2`sprog] do
        if IsDefined(data2`sprog, i) then
            sprog[i] := hslp(data2`sprog[i]);
        end if;
   end for;
   data2`sprog := sprog;

   cprog:=[];
   for i in [1 .. #data2`cprog] do
        if IsDefined(data2`cprog, i) then
            cprog[i] := hslp(data2`cprog[i]);
        end if;
   end for;
   data2`cprog := cprog;
   data2`slpgrp := SG;

   cprog := SpSLP(data2, mat, d, true);
   data2`cprog[d-1] := data2`cprog[d-3] * cprog;
   data2`cprog[d] := SG.(e*d^2 div 2 -2*e+1)^-1 * SG.(e*d^2 div 2 -e+1) *
                     SG.(e*d^2 div 2 -2*e+1)^-1;
   //data2`cprog[d] := [ [ "g", e*d^2 div 2 -2*e+1 ], [ "i", 1 ], 
   //      [ "g", e*d^2 div 2 -e+1 ], [ "p", [ 2, 3 ] ], [ "p", [ 4, 2 ] ] ];
   data2`c[d-1] := data2`c[d-3]*EvaluateBBGp(bbg,data2`gens,cprog);
   data2`c[d] := algadata`c[2];

   AdjustSeqenceUniverse(~data2`trangp, algadata`trangp[1]);
   AdjustSeqenceUniverse(~data2`trangpgamma, algadata`trangpgamma[1]);

   data2`trangp[d div 2] := algadata`trangp[1];
   data2`trangpgamma[d div 2] := algadata`trangpgamma[1];
   if p eq 2 then 
      data2`centre := One(bbg);
      data2`centreprog := [];
   else
      centgen := - IdentityMatrix(GF(q), d);
      centslp := SpSLP(data2, centgen, d, true);
      data2`centre := EvaluateBBGp(bbg, data2`gens, centslp);
      if data2`centre  eq  One(bbg) then 
         data2` centreprog := [];
      else 
         data2`centreprog := centslp;
      end if;
   end if;

   return data2;
end function;


////////////////////////////////////////////////////////////////////////
//
//F SpOddDataStructure( <bbgroup>, <prime>, <power>, <dim> )
//

SpOddDataStructure := function(bbg, bbrand, p, e, d)
   local   q,      // field size
         data1,    // record w/ lots of goodies
           r,      // random element of bbg
           L,      // the d-2 dimensional subgroup
           t,      // p-part of r
        u1,u2,u3,  // conjugates of t
          sp4,     // subgroup <t,u1,u2,u3>
          limit,   // number of iterations
          i,stop,  // loop variables
          genrec,  // record w/ generators of L,Q
          data2;   // the output record 

//"with d eq ",d;
   q := p^e; 
   if d eq 4 then 
      data1 := Sp4OddConstructQ(bbg, bbrand, p, e); 
      if data1  cmpeq  "fails" then 
         return "fails";
      end if;
      // define dummy variable for SpFindGenerators
      r := One(bbg); 
   else 
      r:=FindGoodElement( bbg, bbrand, p, e, d, 4 * q * (d-2) * Ilog2(d) );
      if r cmpeq "fails" then 
//"FindGoodElement could not find r";
         return( "fails" ); 
      end if;
   
      t:= r^(p^(e*(d-2)) -1); 
      limit := Floor( 2+2*q^6 div ( (q-1)*(q^2-1)^2*(q-2) )); 
      stop := false;
      i := 1;
      repeat 
        u1 := t^Random(bbrand);
        if (not ((t,u1)^p eq One(bbg))) then 
              u2 := t^Random(bbrand);
              u3 := t^Random(bbrand);
              sp4 := sub<Generic(bbg) | [Generic(bbg)|t,u1,u2,u3] >;
              Psp4 := RandomProcess(sp4);
              data1 := Sp4OddConstructQ(sp4, Psp4, -p, e); 
              if not data1  cmpeq  "fails" then
//"constructed L with i eq ",i,"  limit=",limit;
                 stop := true;
              end if;
        else 
           i := i+1;
        end if;
      until stop or (i  eq  limit);
      if not stop then 
//"could not construct L";
         return "fails";
      end if; 
   end if; // d eq 4
   
   genrec := SpFindGenerators(bbg,data1,r,p,e,d);
   if genrec  cmpeq  "fails" then
      return "fails";
   end if;

   L := sub< Generic(bbg) | genrec`L >;
   LP := RandomProcess(L);
   if d eq 4 then 
      data2 := SL2DataStructure(L, LP, p, e); 
   else 
      data2 := $$(L, LP, p, e, d-2);
   end if; 
   if data2  cmpeq  "fails" then 
      return "fails";
   end if; 

   data2 := SpFinishConstruction(bbg, data2, data1`algadata, genrec`Q, d); 
   return data2;

end function;


/////////////////////////////////////////////////////////////////////////////
//
//F SpSLP( <data structure>, <matrix or bbg element>, <dim> )
//
// constructs straight-line program reaching the given element

SpSLP := function(data,x,d,ismat)
   local p,e,q,bbg,    // as usual; q=p^e
         form,         // the form associated with the group
         W,            // copy of x to modify
         slp,          //
         blockslp,     // the modifying slp's
         smallslp,
         i,j,k,stop,   // loop variables
         seed,         // position in a slp
         sprog,        // element of data`sprog
         a,            // element of GF(q)     
         FB,           // list of coeff of linear combinations in GF(q)
         gens,         // generator list in data
         coeffs,       // an element of FB
         xinv,         // inverse of x
         Q,Qgamma,     // GF(q) basis for Q and Q(gamma)
         Qrec,         // record, with component pQ = GF(p)-base of Q
         y,            // element of Q
         temp,         // element of Q
         u,            // generator of Qgamma or One(bbg)
         vec,          // coordinate vector of an element of Q 
         mat,          // matrix of the action on Q
         det,          // determinant of the action on Q
         W2,           // power of W
         exp,          // integer, which power of s is needed to make det=1
         slprog,       // slp to s^exp
         smat,         // the matrix of s^exp
         gcd,          // GCD(d-2,q-1)
         t;            // element of data`trangp[d div 2]


   p := data`prime;
   e := data`power;
   q := p^e;
   FB := data`FB;
   gens := data`gens;
   bbg := data`bbg;
   SG := data`slpgrp;
   w := PrimitiveElement(GF(q));

   if ismat then 
     form := ZeroMatrix(GF(q),d,d);
     for i in [1..d div 2] do
        form[2*i-1][2*i] := w^0;
        form[2*i][2*i-1] := -w^0;
     end for;
     mat := x * form * Transpose(x);
     if not mat  eq  mat[1][2]*form then 
//"does not respect form";
        return "fails";
     end if;
     slp := Id(SG);
     // in slp we collect an slp for the right multiplier matrix

     W:= Matrix(x);
     for i in [0..(d-4) div 2] do
         // put non-zero element in lower right corner
         if W[d-2*i][d-2*i]  eq  0 then 
            j := rep{ a : a in [1..d-2*i] | not W[d-2*i][a]  eq  0};
            if j eq  d-2*i-1 then 
               slp *:= SG.(e*(d-2*i)^2 div 2 -e+1);
               //Add(slp,["g",e*(d-2*i)^2/2 -e+1]); 
               for k in [1..d-2*i] do
                  W[k][d-2*i] := W[k][d-2*i] + W[k][j];
               end for;
            elif (j mod 2)  eq  0 then
               slp *:= SG.(e*(d-2*i)*(d-2*i-2) div 2+(j-2)*e+1);
               //Add(slp,["g",e*(d-2*i)*(d-2*i-2)/2+(j-2)*e+1]); 
               for k in [1..d-2*i] do
                  W[k][d-2*i] := W[k][d-2*i] + W[k][j];
                  W[k][j-1] := W[k][j-1] - W[k][d-2*i-1];
               end for;
            else 
               slp *:= SG.(e*(d-2*i)*(d-2*i-2) div 2+ j*e+1);
               //Add(slp,["g",e*(d-2*i)*(d-2*i-2)/2+ j*e+1]); 
               for k in [1..d-2*i] do
                  W[k][d-2*i] := W[k][d-2*i] - W[k][j];
                  W[k][j+1] := W[k][j+1] - W[k][d-2*i-1];
               end for;
            end if;
            //if #slp  gt  1 then 
            //  Add(slp,["p",[#slp -1,#slp]]);
            //end if;
         end if;
//"check1: corner ok ", W eq x*EvaluateMat(data`gens,slp,d,q); W;
         // clear last row
         for j in [1..d-2*i-2] do 
          if not W[d-2*i][j]  eq  0 then
           // a is the nontriv element in last row of the multiplying matrix
           a := -W[d-2*i][j] * W[d-2*i][d-2*i]^-1;
           coeffs := FB[Log(w, a)+1];
           for k in [1..e] do
             if coeffs[k]  ne  0 then 
               slp *:= SG.((d-2*i-2)^2*e div 2 + (j-1)*e + k) ^ coeffs[k];
               //Add(slp, ["g", (d-2*i-2)^2*e/2 + (j-1)*e + k]);
               //seed := #slp;
               //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
               //if seed  gt  1 then 
               //  Add(slp, ["p", [seed -1, #slp]]);
               //end if;
             end if;
           end for;
           for k in [1..d-2*i] do
              W[k][j] := W[k][j] + a * W[k][d-2*i];
              if (j mod 2)  eq  0 then 
                 W[k][d-2*i-1] := W[k][d-2*i-1] - a * W[k][j-1];
              else
                 W[k][d-2*i-1] := W[k][d-2*i-1] + a * W[k][j+1];
              end if;
           end for;
          end if; // W[d-2*i][j]  eq  0;
         end for;
         if not W[d-2*i][d-2*i-1]  eq  0 then 
            a := - W[d-2*i][d-2*i-1] * W[d-2*i][d-2*i]^-1;
            coeffs := FB[Log(w, a)+1];
            for k in [1..e] do
               if coeffs[k]  ne  0 then 
                  slp *:= SG.((d-2*i)^2*e div 2 - 2*e + k) ^ coeffs[k];
                  //Add(slp, ["g", (d-2*i)^2*e/2 - 2*e + k]);
                  //seed := #slp;
                  //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
                  //if seed  gt  1 then 
                  //   Add(slp, ["p", [seed -1, #slp]]);
                  //end if;
               end if;
            end for;
            for k in [1..d-2*i] do
              W[k][d-2*i-1] := W[k][d-2*i-1] + a * W[k][d-2*i];
            end for;
         end if; // W[d-2*i][d-2*i-1]  eq  0*Z(q);
//"check2: last row ok ", W eq x*EvaluateMat(data`gens,slp,d,q); W;
         // clear row d-2*i-1
         if W[d-2*i-1][d-2*i-1]  eq  0 then 
            // necessarily W[d-2*i-1][d-2*i] is nonzero
            slp *:= SG.(e*(d-2*i)^2 div 2 -2*e+1);
            //Add(slp,["g",e*(d-2*i)^2/2 -2*e+1]); 
            //for k in [1..d-2*i] do
            //    W[k][d-2*i-1] := W[k][d-2*i-1] + W[k][d-2*i];
            //end for;
            //if #slp  gt  1 then 
            //  Add(slp,["p",[#slp -1,#slp]]);
            //end if;
         end if;
//"check2.5: second corner ok", W eq x*EvaluateMat(data`gens,slp,d,q); W;
         for j in [1..d-2*i-2] do 
          if not W[d-2*i-1][j]  eq  0 then 
           // a is the nontriv element of the multiplying matrix
           a := -W[d-2*i-1][j] * W[d-2*i-1][d-2*i-1]^-1;
           // in the generators, the negatives are in this row; take -a
           coeffs := FB[Log(w, -a)+1];
           for k in [1..e] do
             if coeffs[k]  ne  0 then 
               slp *:=
         SG.((d-2*i-2)^2*e div 2 + (d-2*i-2)*e + (j-1)*e + k) ^ coeffs[k];
               //Add(slp, ["g", (d-2*i-2)^2*e/2 + (d-2*i-2)*e + (j-1)*e + k]);
               //seed := #slp;
               //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
               //if seed  gt  1 then 
               //  Add(slp, ["p", [seed -1, #slp]]);
               //end if;
             end if;
           end for;
           for k in [1..d-2*i] do
              W[k][j] := W[k][j] + a * W[k][d-2*i-1];
              if (j mod 2)  eq  0 then 
                 W[k][d-2*i] := W[k][d-2*i] + a * W[k][j-1];
              else
                 W[k][d-2*i] := W[k][d-2*i] - a * W[k][j+1];
              end if;
           end for;
          end if; // W[d-2*i-1][j]  eq  0*Z(q);
         end for;
//"check2.75: last two rows ok", W eq x*EvaluateMat(data`gens,slp,d,q); W;
     end for; // i-loop
//"check3: ", W eq x*EvaluateMat(data`gens,slp,d,q); W;
     // now we have a block-diagonal matrix with 2x2 blocks
     blockslp := Id(SG);
     for i in [1 .. d div 2] do 
        mat := Matrix(GF(q),2,2,
            [  W[2*i-1][2*i-1],W[2*i-1][2*i], W[2*i][2*i-1], W[2*i][2*i] ] );
        det := Determinant(mat);
        exp := Log(w, det);
        if exp mod 2  eq  0 then 
           smallslp := SLSLP(data, w^(-exp div 2)*mat, 2, true);
        elif q mod 2  eq  0 then
           smallslp := SLSLP(data, w^(-(exp+q-1) div 2)*mat, 2, true);
        else 
//"trouble at 2x2 determinants";
           return "fails";
        end if;
        slph := hom<SG->SG | [SG.(j+2*i^2*e - 2*e) : j in [1..2*e]] cat
                             [Id(SG) : j in [2*e+1..Ngens(SG)]] >;
        smallslp := smallslp @ slph;
        //for k in [1..#smallslp] do 
        //   if smallslp[k][1]  eq  "g" then 
        //      smallslp[k][2] := smallslp[k][2] + 2*i^2*e - 2*e;
        //   end if;
        //end for;
        //blockslp := ProdProg(blockslp, smallslp);
        blockslp *:= smallslp;
     end for; 

     slp := slp^-1;
     //if #slp  gt  0 then 
     //   Add(slp, ["i", #slp]);
     //end if;
//"check3.5: ", W eq EvaluateMat(data`gens,blockslp,d,q);
//EvaluateMat(data`gens,blockslp,d,q);
//mat:= EvaluateMat(data`gens,blockslp*slp,d,q) * x^-1;
//"final check:",mat eq mat[1][1]*IdentityMatrix(GF(q),d);

     return blockslp * slp;

   else // we have a bbg element 

     if d eq 2 then 
        return SLSLP(data,x,2,false);
     end if;

     slp := Id(SG); 
     // GF(p)-generators for Q
     Q := [ gens[i][1] : i in [(d-2)^2*e div 2 + 1 .. d*(d-2)*e div 2] ];
     //Q := List(gens{[(d-2)^2*e div 2 + 1 .. d*(d-2)*e div 2]}, j->j[1]);
     // we shall pass the generators as a record to SpConjInQ
     Qrec := rec<SLdata | pQ := Q >;
     // GF(q)-generators for Qgamma
     //Qgamma := List([1..d-2], j -> gens[d*(d-2)*e/2 + (j-1)*e +1][1]);
     Qgamma := [ gens[d*(d-2)*e div 2 + (i-1)*e +1][1]: i in [1..d-2] ];
     t := data`trangp[d div 2][2];

     // first modify x to carry t to a non-perp point
     if (t,t^x)  eq  One(bbg) then 
        if not (t,t^(x*data`c[d]))  eq  One(bbg) then
           u := data`c[d];
           //slp := ProdProg(slp, data`cprog[d]);
           slp := slp * data`cprog[d];
        else
           i := 1;
           stop := false;
           repeat
              if not ((t,t^(x*Qgamma[i]))  eq  One(bbg)) then 
                 stop := true; 
                 slp *:= SG.(d*(d-2)*e div 2 + (i-1)*e + 1);
                 //Add(slp, ["g", d*(d-2)*e/2 + (i-1)*e +1]);
                 //if #slp  gt  1 then 
                 //   Add(slp, ["p", [#slp-1,#slp]]);
                 //end if;
                 u := Qgamma[i];
              else 
                 i := i+1;
              end if;
           until stop or i eq d-1;
           if not stop then 
//"could not find u";
              return "fails";
           end if;
        end if;
     else
        u := One(bbg);
     end if;
//"handled u";
     // y will be in <Q>, conjugating T^(x*u) to T^jgamma eq T^data`c[d]
     y := SpConjInQ(bbg,x*u,data`c[d],data`trangp[d div 2],
                       data`trangpgamma[d div 2],Qrec,p,e);
     if y  cmpeq  "fails" then 
//"could not find y";
        return "fails";
     end if;
//"handled y";
     // x*u*y*jgamma^(-1) fixes T and so Q
     vec := SpLinearCombQ(data`rootgp[d div 2],data`t21,data`c[2],
                          data`c[d-3],data`sinv,d,y);
     if vec  cmpeq  "fails" then
//"could not find vec";
        return "fails";
     end if;
     // temp will be used to find the T-part of y
     temp := One(bbg);
     for j in [1..d-2] do 
        if not (vec[j]  eq  0) then
           coeffs := FB[Log(w, vec[j])+1];
           for k in [1..e] do
              if coeffs[k]  ne  0 then 
                 slp *:= SG.((d-2)^2*e div 2 + (j-1)*e + k) ^ coeffs[k];
                 //Add(slp, ["g", (d-2)^2*e/2 + (j-1)*e + k]);
                 //seed := #slp;
                 //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
                 //if seed  gt  1 then 
                 //   Add(slp, ["p", [seed -1, #slp]]);
                 //end if;
                 temp *:= gens[(d-2)^2*e div 2 + (j-1)*e + k][1]^coeffs[k];
              end if;
           end for;
        end if;
//"handled j eq ",j;
     end for;  
//"added y to slp";
     temp := temp^(-1)*y;
     i := 1;
     stop := false;
     repeat 
        if temp  eq  data`trangp[d div 2][i] then
           stop := true;
           if i gt 1 then 
              coeffs := FB[Log(w, w^(i-2))+1];
              for k in [1..e] do
                 if coeffs[k]  ne  0 then 
                    slp *:= SG.(d^2*e div 2 - 2*e + k) ^ coeffs[k];
                    //Add(slp, ["g", d^2*e/2 - 2*e + k]);
                    //seed := #slp;
                    //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
                    //if seed  gt  1 then 
                    //   Add(slp, ["p", [seed -1, #slp]]);
                    //end if;
                 end if;
              end for;
           end if;
        else
           i := i+1;
        end if;
     until stop or i eq q+1;
     if not stop then 
//"could not find T-part";
        return "fails";
     end if;
     //smallslp := InvProg(data`cprog[d]);
     smallslp := data`cprog[d]^-1;
     slp *:= smallslp;
     W := x * u * y * (data`c[d])^(-1);
//"check4: ", W eq x*EvaluateBBGp(data,gens,slp);
     // now make sure that W centralizes T
     exp := Position(data`trangp[d div 2],t^W);
     if exp eq 0 or (exp mod 2  eq 1) then 
//"could not centralize T";
        return "fails";
     end if;
     if exp  gt  2 then 
        slprog := data`sprog[2] ^((exp-2) div 2);
        slprog := data`cprog[d-1] * slprog;
        slprog := slprog * data`cprog[d-1]^-1;
        slp *:= slprog;
        W := W * data`c[d-1]*(data`sinv^((exp-2) div 2))*(data`c[d-1])^(-1);
     end if;
T:=data`trangp[d div 2];
//"check4.25: ",ForAll(T,z->IsInTranGroup(bbg,T,z^W));
//"check4.25: ", t^W eq t;
     // compute the matrix for the action of W on Q
     mat := []; 
     for j in [1..d-2] do
        vec := SpLinearCombQ(data`rootgp[d div 2],data`t21,data`c[2],
                             data`c[d-3],data`sinv,d,Q[e*(j-1)+1]^W);
        if vec  cmpeq  "fails" then 
//"could not compute matrix";
           return "fails";
        else 
           mat := mat cat vec;
        end if;
     end for;
     mat := GL(d-2,q)!mat;
//    det := Determinant(mat);
//     if not (det  eq  Z(q)^0) then 
//        gcd := GCD(d-2,q-1);
//        exp := (LogFFE(det, Z(q))/gcd) / ((d-2)/gcd) mod ((q-1)/gcd); 
//        slprog := PowerProg(data`sprog[2],exp);
//        slprog := ProdProg(data`cprog[d-1], slprog);
//        slprog := ProdProg(slprog, InvProg(data`cprog[d-1]));
//        slp := ProdProg(slp, slprog);
//        W := W * data`c[d-1]*(data`sinv^exp)*(data`c[d-1])^(-1);
//        smat := Z(q)^(- exp)*IdentityMatrix(GF(q),d-2);
//        mat := mat * smat;
//     end if;
//"check4.5: ", W eq x*EvaluateBBGp(data,gens,slp);
     smallslp := SpSLP(data, mat^(-1), d-2, true);
     slp *:= smallslp;
     W := W * EvaluateBBGp(bbg,gens,smallslp);
//"check5: ", W eq x*EvaluateBBGp(data,gens,slp);
     // now W acts trivially on Q
     W2 := W^(-q);
     if not (One(bbg)  eq  W2) then 
        if W2  eq  data`centre then 
           W := W * W2;
           slp *:= data`centreprog;
        else 
           return "fails";
        end if;
     end if;
//"check6: ", W eq x*EvaluateBBGp(data,gens,slp);
     // now W is in Q
     vec := SpLinearCombQ(data`rootgp[d div 2],data`t21,data`c[2],
                          data`c[d-3],data`sinv,d,W^(-1));
     if vec  cmpeq  "fails" then
//"failed to decompose in Q";
        return "fails";
     end if;
     // temp will be used to find the T-part of W
     temp := One(bbg);
     for j in [1..d-2] do 
        if not (vec[j]  eq  0) then
           coeffs := FB[Log(w, vec[j])+1];
           for k in [1..e] do
              if coeffs[k]  ne  0 then 
                 slp *:= SG.((d-2)^2*e div 2 + (j-1)*e + k) ^ coeffs[k];
                 //Add(slp, ["g", (d-2)^2*e/2 + (j-1)*e + k]);
                 //seed := #slp;
                 //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
                 //if seed  gt  1 then 
                 //   Add(slp, ["p", [seed -1, #slp]]);
                 //end if;
                 temp *:= (gens[(d-2)^2*e div 2 + (j-1)*e + k][1]^coeffs[k]);
              end if;
           end for;
        end if;
     end for;  
     temp := temp^(-1)*(W^(-1));
     i := 1;
     stop := false;
     repeat 
        if temp  eq  data`trangp[d div 2][i] then
           stop := true;
           if i gt 1 then 
              coeffs := FB[Log(w, w^(i-2))+1];
              for k in [1..e] do
                 if coeffs[k]  ne  0 then 
                    slp *:= SG.(d^2*e div 2 - 2*e + k) ^ coeffs[k];
                    //Add(slp, ["g", d^2*e/2 - 2*e + k]);
                    //seed := #slp;
                    //Append(slp, PowerofElmtProg(slp[seed], coeffs[k],seed));
                    //if seed  gt  1 then 
                    //   Add(slp, ["p", [seed -1, #slp]]);
                    //end if;
                 end if;
              end for;
           end if;
        else
           i := i+1;
        end if;
     until stop or i eq q+1;
     if not stop then 
        "does not stop in Q";
        return "fails";
     end if;

     //if #slp  gt  0 then
     //   Add(slp, ["i", #slp]);
     //end if;
     slp := slp^-1;
//"final check2  ",x eq EvaluateBBGp(bbg,data`gens,slp);
     return slp;
 
   end if; // ismat

end function;

intrinsic RecogniseSpOdd(G :: Grp, d :: RngIntElt, q :: RngIntElt) -> BoolElt, Map, Map
{Try to find an isomorphism between G and Sp(d, q)}
    require IsOdd(q) : "Characteristic must be odd in RecogniseSpOdd";
    require d gt 2 : "Dimension must be at least 4 in RecogniseSpOdd";
    RPG := RandomProcess(G);
    f := Factorization(q);

    p := f[1][1];
    e := f[1][2];

    assert #f eq 1 and p ne 2;

    count := 0;

    data := "fails";
    Limit := q eq 3 select Floor (10 * Log(d)) else Floor (6 * Log(d));
    while count lt Limit and data cmpeq "fails" do
      count +:= 1;
      data := SpOddDataStructure(G, RPG, p, e, d);
    end while;
    if data cmpeq "fails" then
        return false, _, _;
    end if;
    for x in Generators(G) do if SpSLP(data, x, d, false) cmpeq "fails" then
       return false, _, _;
    end if; end for;

    H := Sp(d, q);
    X:=PermutationMatrix(GF(q),
       Sym(d)!([2*i-1:i in [1..d div 2]] cat [2*i: i in [d div 2..1 by -1]]) ); 
    H := sub<GL(d,q)|[X^-1*H.i*X:i in [1..Ngens(H)]]>;
    // we use SL(d,q) as domain and codomain in following to avoid Magma
    // doing membership tests
    forw := hom<G -> SL(d,q) | x :->
      X*EvaluateMat(data`gens, SpSLP(data, x, d, false), d, q)*X^-1 >;
    back := hom<SL(d,q) -> Generic(G) | x :->
        EvaluateBBGp(G, data`gens, SpSLP(data, X^-1*x*X, d, true))>;

    return true, forw, back;
end intrinsic;

intrinsic RecognizeSpOdd(G :: Grp, d :: RngIntElt, q :: RngIntElt) -> BoolElt, Map, Map
{Try to find an isomorphism between G and Sp(d, q)}
  return RecogniseSpOdd(G,d,q);
end intrinsic;
