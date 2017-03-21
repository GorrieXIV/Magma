freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: core.m (core reduction routines.)

   $Header: /home/was/magma/packages/ModSym/code/RCS/core.m,v 1.13 2002/10/01 06:01:13 was Exp $

   $Log: core.m,v $
   Revision 1.13  2002/10/01 06:01:13  was
   nothing.

   Revision 1.12  2001/10/06 00:35:50  was
   nothing.

   Revision 1.11  2001/08/29 23:07:10  was
   Fixed the comment to convergent.

   Revision 1.10  2001/07/13 23:31:25  was
   Fixed handling of a special case of P1GeneralizedWeightedAction that
   didn't make it into the C.

   Revision 1.9  2001/07/06 00:02:55  was
   Turned off XXXP1GeneralizedWeightAction again, because Allan
   fixed a trivial little N=1 case bug.

   Revision 1.8  2001/07/03 20:00:59  was
   ..

   Revision 1.7  2001/07/03 20:00:13  was
   Reverted to my XXXP1...

   Revision 1.6  2001/06/07 01:45:07  was
   P1GeneralizedWeightedAction is now in the C.

   Revision 1.5  2001/05/21 07:14:41  was
   Replaced hP := h(P) by Evaluate(P,[...]);

   Revision 1.4  2001/05/14 04:57:13  was
   Changed an assertion in P1GeneralizedWeightedAction.

   Revision 1.3  2001/05/14 03:14:55  was
   Made the ConvertFromManinSymbol comment better.

   Revision 1.2  2001/05/13 03:46:14  was
   Changed verbose flag ModularForms to ModularSymbols.

   Revision 1.1  2001/04/20 04:44:55  was
   Initial revision

   Revision 1.7  2001/02/07 01:49:12  was
   nothing.

   Revision 1.6  2000/07/03 07:42:44  was
   Fixed bug in ConvFromManinSymbol; wasn't giving 0 when gcd(a,b,N) =/= 0.
   Added    elif s eq 0 then
               P := 0;
            end if;

   Revision 1.5  2000/06/20 07:28:26  was
   added "ConvertFromManinSymbol."

   Revision 1.4  2000/06/03 04:48:20  was
    SetVerbose

   Revision 1.3  2000/05/25 21:34:36  was
   Added !F0 in coef[i] := F!0.

   Revision 1.2  2000/05/02 07:58:20  was
   Added $Log: core.m,v $
   Added Revision 1.13  2002/10/01 06:01:13  was
   Added nothing.
   Added
   Added Revision 1.12  2001/10/06 00:35:50  was
   Added nothing.
   Added
   Added Revision 1.11  2001/08/29 23:07:10  was
   Added Fixed the comment to convergent.
   Added
   Added Revision 1.10  2001/07/13 23:31:25  was
   Added Fixed handling of a special case of P1GeneralizedWeightedAction that
   Added didn't make it into the C.
   Added
   Added Revision 1.9  2001/07/06 00:02:55  was
   Added Turned off XXXP1GeneralizedWeightAction again, because Allan
   Added fixed a trivial little N=1 case bug.
   Added
   Added Revision 1.8  2001/07/03 20:00:59  was
   Added ..
   Added
   Added Revision 1.7  2001/07/03 20:00:13  was
   Added Reverted to my XXXP1...
   Added
   Added Revision 1.6  2001/06/07 01:45:07  was
   Added P1GeneralizedWeightedAction is now in the C.
   Added
   Added Revision 1.5  2001/05/21 07:14:41  was
   Added Replaced hP := h(P) by Evaluate(P,[...]);
   Added
   Added Revision 1.4  2001/05/14 04:57:13  was
   Added Changed an assertion in P1GeneralizedWeightedAction.
   Added
   Added Revision 1.3  2001/05/14 03:14:55  was
   Added Made the ConvertFromManinSymbol comment better.
   Added
   Added Revision 1.2  2001/05/13 03:46:14  was
   Added Changed verbose flag ModularForms to ModularSymbols.
   Added
   Added Revision 1.1  2001/04/20 04:44:55  was
   Added Initial revision
   Added
   Added Revision 1.7  2001/02/07 01:49:12  was
   Added nothing.
   Added
   Added Revision 1.6  2000/07/03 07:42:44  was
   Added Fixed bug in ConvFromManinSymbol; wasn't giving 0 when gcd(a,b,N) =/= 0.
   Added Added    elif s eq 0 then
   Added             P := 0;
   Added          end if;
   Added
   Added Revision 1.5  2000/06/20 07:28:26  was
   Added added "ConvertFromManinSymbol."
   Added
   Added Revision 1.4  2000/06/03 04:48:20  was
   Added  SetVerbose
   Added
   Added Revision 1.3  2000/05/25 21:34:36  was
   Added Added !F0 in coef[i] := F!0.
   Added

                                                                            
 ***************************************************************************/


import "linalg.m" : Pivots;

import "multichar.m" : MC_ConvToModularSymbol, 
                       MC_ManinSymToBasis,
                       MC_ModSymToBasis;;

/* ZZ Dangerous bend ZZ
   The code in this files lies at the very core of all of the other modular
   forms routines.  It is delicate code that was very difficult to write
   correctly.  Use *extreme* caution when changing anything in this file.
 
*/


forward convergent,
        ConvFromManinSymbol ,
        ConvFromModSym,
        ConvFromModularSymbol,
        ConvFromModularSymbol_helper,
        ConvToManinSymbol,
        ConvToModSym,
        ConvToModularSymbol,
        LiftToCosetRep,
        ManinSymbolApply,
        ManinSymbolList,
//      ManinSymbolRepresentation,     // commented out
        ManSym2termQuotient,
        ManSym3termQuotient,
        ManSymGenListToRep,
//      ManSymGenListToSquot,          // commented out
//      ModularSymbolApply,            // now an intrinsic
//      ModularSymbolRepresentation,   // now an intrinsic
        ModularSymbolsBasis,
        Quotient,
        Sparse2Quotient,
        UnwindManinSymbol,
        WindManinSymbol;


/************************************************************************
 *                                                                      *
 *          DATA STRUCTURES                                             *
 *                                                                      *
 ************************************************************************/

/************************************************************************
 *  CQuotient:                                                          *
 *  First we motivate the format.                                       *
 *  To save memory and space we mod out by the S, T, and possibly I     *
 *  relations in two phases.  First mod out by the S,I relations        *
 *          x + xS = 0,  x - xI = 0.                                    *
 *  by identifying equivalent pairs.  Next mod out by the T relations   *
 *          x + xT + xT^2 = 0.                                          *
 ************************************************************************/
CQuotient := recformat<
       Sgens,     // * List of the free generators after modding out 
                  //   by the 2-term S and possibly I relations.
       Squot,     // * The i-th Manin symbol is equivalent to
       Scoef,     //     Scoef[i]*(Squot[i]-th free generator). 
       Tgens,     // * List of the free generators after modding
                  //   out the S-quotient by the T-relations. 
       Tquot,     // * The i-th Sgen is equal to Tquot[i], which
                  //   is a vector on Tgens. 
       Tquot_scaled, scalar	// Scaled version over rationals
>;

// The standard manin symbols list.
CManSymList := recformat<
      k,      // weight 
      F,      // base field
      R,      // F[X,Y].
      p1list, // List of elements of P^1(Z/NZ).
      n       // size of list of Manin symbols = #p1list * (k-1).
> ;



/////////////////////////////////////////////////////////////////////////
// P1Normalize  (written by Allan Steel)                               //
// INPUT: [u,v] in Z/N x Z/N.                                          //
// OUTPUT:  1) the *index* of a fixed choice [a,b] of representative   //
//             in the P^1(Z/NZ) equivalence class of [u,v].            //
//             If gcd(u,v,N)>1 then the index returned is 0.           //
//          2) a scalar s such that                                    //
//                    [a*s,b*s] = [u,v].                               //
//             The character relation is thus                          //
//                  eps(s) [a,b] == [u,v].                             //
/////////////////////////////////////////////////////////////////////////

/*
// This is now in the C.
function P1Normalize(x) 
   Z := IntegerRing();
   u := x[1];
   v := x[2];
   R := Parent(u);
   N := Modulus(R);
   if u eq 0 then
      return [R | 0, 1], v;
   else
      u := Z ! u;
      g, s := XGCD(u, N);
      if g ne 1 then
         d := N div g;
	 while GCD(s, N) ne 1 do
	    s := (s + d) mod N;
	 end while;
      end if;
      // Multiply (u, v) by s; new u = g
      u := R!g;
      v := v*s;
      minv := Z!v;
      mint := 1;
      if g ne 1 then
	 Ng := N div g;
	 vNg := v*Ng;
	 t := R!1;
	 for k := 2 to g do
	    v +:= vNg;
	    t +:= Ng;
	    if Z!v lt minv and IsUnit(t) then
	       minv := Z!v;
	       mint := t;
	    end if;
	 end for;
      end if;
      if GCD([Z | u, minv, N]) ne 1 then
	 printf "Bad x=%o, N=%o, u=%o, minv=%o, s=%o, mint=%o\n",
	     x, N, u, minv, s, mint;
	 error "";
      end if;
      return [R|u, minv], 1/(R!(s*mint));
   end if;
end function;
*/      


//////////////////////////////////////////////////////////////////////////
//  P1Classs:                                                           //
//  Construct a list of distinct normalized representatives for         //
//  the set of equivalence classes of P^1(Z/NZ).                        //
//  The output of this function is used by P1Reduce.                    //
//////////////////////////////////////////////////////////////////////////

/*
// This is now in the C.
function EnumerateP1(N)
   R := (N gt 1) select IntegerRing(N) else quo<Integers()|1>;
   return {@ P1Normalize([R|c,1]) : c in [0..N-1] @} join
          {@ P1Normalize([R|1,d]) : d in [0..N-1] | Gcd(d,N) gt 1 @} join
	  {@ P1Normalize([R|c,d]) : c in Divisors(N), d in [0..N-1] | 
                       c ne 1 and c ne N and Gcd(c,d) eq 1 
                       and Gcd(d,N) gt 1 @};
end function;
*/


//////////////////////////////////////////////////////////////////////////
//  P1Reduce:                                                           //
//  INPUT: [u,v] in Z/N x Z/N.                                          //
//  OUTPUT:  1) the *index* of a fixed choice [a,b] of representative   //
//              in the P^1(Z/NZ) equivalence class of [u,v].            //
//              If gcd(u,v,N)>1 then the index returned is 0.           //
//           2) a scalar s such that                                    //
//                     [a*s,b*s] = [u,v].                               //
//              so the character relation is                            //
//                   eps(s) [a,b] == [u,v].                             //
//////////////////////////////////////////////////////////////////////////

/*
// This is now in the C.
function P1Reduce(x, list)
   N := Characteristic(Parent(x[1]));
   if N eq 1 then 
      return 1, 1;
   end if;
   if Gcd([x[1], x[2], N]) ne 1 then
      return 0, 1;
   end if;

   u,v, s := P1Normalize(Integers()!x[1],Integers()!x[2],N);
   return Index(list, RSpace(IntegerRing(N),2)![u,v]), s;
end function;
*/



//////////////////////////////////////////////////////////////////////////
// ManinSymbolList:                                                     //
// Construct a list of distinct Manin symbols.  These are               //
// elements of the Cartesion product:                                   //
//     {0,...,k-2} x P^1(Z/NZ).                                         //
// In fact, we only store a list of the elements of P^1(Z/NZ),          //
// as the full Cartesion product can be stored using                    //
// the following scheme.                                                //
//                                                                      //
// There are Manin symbols 1,...,#({0,..,k-2}xP^1) indexed by i.        //
// Thus i is an integer between 1 and the number of generating Manin    //
// symbols.  Suppose P^1(N) = {x_1, ..., x_n}.  The encoding is         //
// as follows:                                                          // 
//   1=<X^0Y^(k-2),x_1>,  2=<0, x_2>, ..., n=<0,x_n>,                   //
// n+1=<X^1Y^(k-3),x_1>,n+2=<1, x_2>, ...,2n=<1,x_n>,                   //
// ...                                                                  //
//////////////////////////////////////////////////////////////////////////

function ManinSymbolList(k,N,F) 
   p1list := P1Classes(N);
   n      := (k-1)*#p1list;
   R<X,Y> := PolynomialRing(F,2);
   return rec<CManSymList |
      k      := k,            // weight
      F      := F,            // base field
      R      := R,            // polynomial ring F[X,Y]
      p1list := p1list,     
      n      := n             
   >;
end function;




///////////////////////////////////////////////////////////////////////////
// Unwind -- Given an int i, this function gives back the                //
// ith generating Manin symbol.                                          //
///////////////////////////////////////////////////////////////////////////
function UnwindManinSymbol(i, mlist)
   // P^1(N) part.
   p1list := mlist`p1list;
   n := #p1list;
   /*
   ind := (i mod n);
   if ind eq 0 then 
      ind := n; 
   end if;
   */
   ind := ((i - 1) mod n) + 1;
   uv := p1list[ind];
   //w := Integers()!((i - ind)/n);
   w := ExactQuotient(i - ind, n);
   return uv, w, ind;
end function;


// Wind -- Given w in the range 0<=w<=k-2, and an index ind
//   into the P^1-list, this function gives back
//   the number of the generating Manin symbol.
function WindManinSymbol(w, ind, mlist) 
   return w*#(mlist`p1list) + ind;
end function;


///////////////////////////////////////////////////////////////////////////
// ManinSymbolApply                                                      //
// Apply an element g=[a,b, c,d] of SL(2,Z) to the i-th                  //
// standard Manin symbol.  The definition of the action is               //
//       g.(X^i*Y^j[u,v]) :=                                             //
//                     (aX+bY)^i*(cX+dY)^j [[u,v]*g].                    //
// The argument "manin" should be as returned by                         //
// the function ManinSymbolsList above.                                  //
///////////////////////////////////////////////////////////////////////////

function XXXManinSymbolApply(g, i, mlist, eps)
// Apply g to the ith Manin symbol.
   k := mlist`k;
   uv, w, ind := UnwindManinSymbol(i,mlist);     // not time critical

   p1list := mlist`p1list;

   if Type(g) eq SeqEnum then
      g := <g, MatrixAlgebra(Integers(Modulus(eps)),2)!g> ;
   end if;


// Method 1: *very* *very* slow
//   uvg    := Parent(uv) ! [g[1]*uv[1]+g[3]*uv[2], g[2]*uv[1]+g[4]*uv[2]];

// Method 2: 60% less time. 
//   G := MatrixAlgebra(Integers(Modulus(eps)),2)![g[1],g[2],g[3],g[4]];
//   uv := uv*G;

// Method 3: Do the coercision once and for all (even better)
   uvg    := uv*g[2];
   act_uv, scalar := P1Reduce(uvg, p1list);


   if act_uv eq 0 then
      return [<0,1>];
   end if;

   if k eq 2 then
      if not IsTrivial(eps) then
         return [<Evaluate(eps,scalar),act_uv>];
      else
         return [<1,act_uv>];
      end if;
   end if;

   // Polynomial part. 
   R := PolynomialRing(mlist`F); x := R.1;    // univariate is fine for computation
   hP := (g[1][1]*x+g[1][2])^w*(g[1][3]*x+g[1][4])^(k-2-w);
 
   if not IsTrivial(eps) then
      hP *:= Evaluate(eps,scalar);
   end if;
   pol := ElementToSequence(hP);

   // Put it together
   n   := #p1list;
   ans := [<pol[w+1],  w*n + act_uv> : w in [0..#pol-1]];
   return [x : x in ans | x[1] ne 0];
end function;


function ManinSymbolApply(g, i, mlist, eps, k)
// Apply g to the ith Manin symbol.
   uv, w, ind := UnwindManinSymbol(i,mlist);  

   p1list := mlist`p1list;

   if Type(g) eq SeqEnum then
      g := <g, MatrixAlgebra(Integers(Modulus(eps)),2)!g> ;
   end if;

   uvg    := uv*g[2];
   act_uv, scalar := P1Reduce(uvg, p1list);

   if act_uv eq 0 then
      return [<0,1>];
   end if;

   if k eq 2 then
      if not IsTrivial(eps) then
         return [<Evaluate(eps,scalar),act_uv>];
      else
         return [<1,act_uv>];
      end if;
   end if;
   
   // Polynomial part. 
   R := PolynomialRing(mlist`F); x := R.1;    // univariate is fine for computation
   hP := (g[1][1]*x+g[1][2])^w*(g[1][3]*x+g[1][4])^(k-2-w);
 
   if not IsTrivial(eps) then
      hP *:= Evaluate(eps,scalar);
   end if;
   pol := ElementToSequence(hP);

   // Put it together
   n   := #p1list;
   ans := [<pol[w+1],  w*n + act_uv> : w in [0..#pol-1]];
   return [x : x in ans | x[1] ne 0];
end function;


function ImageOfRep(M,i,Heil,Tmat,W)
   eps := DirichletCharacter(M);
   mlist := M`mlist;
   k := Weight(M);

   Scoef := M`quot`Scoef;
   Squot := M`quot`Squot;
   v := W!0;

   for h in Heil do
      m := ManinSymbolApply(h,i,mlist,eps,k);
      for t in m do
         v[Squot[t[2]]] +:= t[1]*Scoef[t[2]];
      end for;
   end for;
   return v;
end function;


// This is now handled by P1Action; see right after this function, below.
function XXXP1GeneralizedWeightedAction(
                              uv,  // element of P1(Z/NZ)
                               w,  // weight of symbol
                               k,  // weight of action
                            list, 
                               S, 
                             phi, 
                           coeff, 
                               M, 
                               W,
                             eps,
                               R,
                               t)

   assert Type(uv) in {ModTupRngElt, ModTupFldElt} ;
   assert Type(w) eq RngIntElt;
   assert Type(k) eq RngIntElt;
   assert Type(list) eq SetIndx;
   assert Type(S) eq SeqEnum;
   assert Type(phi) eq SeqEnum;
   assert Type(coeff) eq SeqEnum;
   assert Type(M) eq SeqEnum;
   assert Type(W) eq SeqEnum;
   assert Type(eps) eq SeqEnum;
   assert Type(R) eq RngUPol;
   assert Type(t) eq RngIntElt;

   Z := Integers();
   p1list_size := #list;
   K := Parent(eps[1]);
   v := VectorSpace(K,#S)!0;
   if #S eq 0 then 
      return v;
   end if;
  
   for i in [1..#M] do
      uvM := uv*M[i];
      a,b := Explode(Eltseq(uvM));
      a := Z!a; b := Z!b;
      if a mod t ne 0 or  b mod t ne 0 then
         continue;
      end if;
      uvM := Parent(list[1])![a div t, b div t];

      ind, s := P1Reduce(uvM,list);

      // The following "if" statement is for more than just efficiency;
      // if it is not there then the function will be incorrect, because
      // phi[i+1+#p1list_size] is *not* 0.
      if ind eq 0 then
         continue;    
      end if;
      e := eps[Z!s];
      H := W[i];
      h := e*(R![H[1,2],H[1,1]])^w*(R![H[2,2],H[2,1]])^(k-2-w);
      j := ind+1;
      for a in Eltseq(h) do
         v[phi[j]] +:= a*coeff[j];
         j +:= p1list_size;
      end for;
   end for;
   return v * RMatrixSpace(K,Degree(v),Degree(S[1]))!S;
end function;



function P1GeneralizedWeightedAction(
                              uv,  // element of P1(Z/NZ)
                               w,  // weight of symbol
                               k,  // weight of action
                            list, 
                               S, 
                             phi, 
                           coeff, 
                               M, 
                               W,
                             eps,
                               R,
                               t)
  
   // return XXXP1GeneralizedWeightedAction(uv,w,k,list,S,phi,coeff,M,W,eps,R,t);
   if #S eq 0 then 
      K := Parent(eps[1]);
      return VectorSpace(K,#S)!0;;
   end if;

   return P1Action(<list, S, phi, coeff, eps, t>, uv, w, M, W, k);
end function;


/////////////////////////////////////////////////////////////////
//  ModularSymbolApply                                         //
//  Apply an element g=[a,b, c,d] of GL(2,Q) to the given      //
//  modular symbol.  The definition of the action is           //
//       g.(X^i*Y^j{u,v}) :=                                   //
//                     (dX-bY)^i*(-cX+aY)^j {g(u),g(v)}.       //
//  A modular symbol is represented as a sequence of pairs     //
//  <P,x>, where P is a polynomial in X and Y,                 //
//  and x=[[a,b],[c,d]] is a pair  of elements of P^1(Q),      //
//     where [a,b] <--> a/b and [c,d] <--> c/d.                //
//  After computing the action, no further reduction is done.  //
/////////////////////////////////////////////////////////////////

// TO DO: get rid of unused argument M

intrinsic ModularSymbolApply(M::ModSym, g::SeqEnum, s::SeqEnum) -> SeqEnum
{Apply an element g=[a,b, c,d] of GL(2,Q) to the modular symbol s,
 given as a sequence of tuples <coeff,[cusp1,cusp2]> (as returned by
 ModularSymbolRepresentation).  The result is returned in the same format.
 The argument M plays no role and is ignored.}

   // TO DO: checks ...

   if IsEmpty(s) then return []; end if;

   R := Parent(s[1][1]); 
   require ISA(Type(R), RngMPol) and Rank(R) eq 2: 
          "The coefficients of the given modular symbols should live in a polynomial ring in 2 variables";

   A,B,C,D := Explode(g);
   subst := [D*R.1-B*R.2, -C*R.1+A*R.2];
   ans := [];
   for t in s do
      hP := Evaluate(t[1], subst);
      a,b := Explode(t[2][1]); 
      c,d := Explode(t[2][2]);
      gx := [[A*a+B*b, C*a+D*b],
             [A*c+B*d, C*c+D*d]];
      Append(~ans, <hP,gx>);
   end for;
   return ans;
end intrinsic;


/////////////////////////////////////////////////////////////////
//  Sparse2Quotient:                                           //
//   Performs Sparse Gauss elimination on a matrix all of      //
//   whose columns have at most 2 nonzero entries.  I just     //
//   use the fairly obvious algorithm.   It runs fast          //
//   enough.  Example:                                         //
//   rels := [[1,2], [1,3], [2,3], [4,5]];                     //
//   relc := [[3,-1],[1,1], [1,1], [1,-1]];                    //
//   n    := 5;                // x1,...,x5                    //
//   corresponds to 3*x1-x2=0, x1+x3=0, x2+x3=0, x4-x5=0.      //
/////////////////////////////////////////////////////////////////


function Sparse2Quotient (rels, relc, n, F)
   free := [1..n];
   coef := [F|1 : i in [1..n]];
   related_to_me := [[] : i in [1..n]];
   for i in [1..#rels] do
      t := rels[i];
      c1 := relc[i][1]*coef[t[1]];
      c2 := relc[i][2]*coef[t[2]];
      // Mod out by the relation 
      //    c1*x_free[t[1]] + c2*x_free[t[2]] = 0.
      die := 0;
      if c1 eq 0 and c2 eq 0 then
         // do nothing.
      elif c1 eq 0 and c2 ne 0 then  // free[t[2]] --> 0
         die := free[t[2]];
      elif c2 eq 0 and c1 ne 0 then
         die := free[t[1]];
      elif free[t[1]] eq free[t[2]] then
         if c1+c2 ne 0 then
            // all xi equal to free[t[1]] must now equal to zero.
            die := free[t[1]];
         end if;
      else   // x1 = -c2/c1 * x2.
         x := free[t[1]];
         free[x] := free[t[2]];
         coef[x] := -c2/c1;
         for i in related_to_me[x] do
	     free[i] := free[x];
             coef[i] *:= coef[x];
	     Append (~related_to_me[free[t[2]]], i);
         end for;
	 Append (~related_to_me[free[t[2]]], x);
      end if;

      if die gt 0 then
         for i in related_to_me[die] do
            free[i] := 1;
            coef[i] := F!0;
         end for;
	 free[die] := 1 ;
	 coef[die] := F!0;
      end if;
   end for;

   // Enumerate the subscripts of free generators that survived.
   // x_{i_1}  <----> y_1
   // x_{i_2}  <----> y_2, etc.

   for i in [1..#free] do
      if coef[i] eq 0 then
         free[i] := -1;
      end if;     
   end for;
   ykey := {@ x : x in Set(free) | x ne -1 @};
   for i in [1..#free] do
      if free[i] eq -1 then
         free[i] := 1;
      else
         free[i] := Index(ykey,free[i]);
      end if;
   end for;
   return ykey, free, coef;
end function;

function Fake_Sparse2Quotient (rels, relc, n, F)
   free := [1..n];
   coef := [F|1 : i in [1..n]];
/*
   related_to_me := [[] : i in [1..n]];
   for i in [1..#rels] do
      t := rels[i];
      c1 := relc[i][1]*coef[t[1]];
      c2 := relc[i][2]*coef[t[2]];
      // Mod out by the relation 
      //    c1*x_free[t[1]] + c2*x_free[t[2]] = 0.
      die := 0;
      if c1 eq 0 and c2 eq 0 then
         // do nothing.
      elif c1 eq 0 and c2 ne 0 then  // free[t[2]] --> 0
         die := free[t[2]];
      elif c2 eq 0 and c1 ne 0 then
         die := free[t[1]];
      elif free[t[1]] eq free[t[2]] then
         if c1+c2 ne 0 then
            // all xi equal to free[t[1]] must now equal to zero.
            die := free[t[1]];
         end if;
      else   // x1 = -c2/c1 * x2.
         x := free[t[1]];
         free[x] := free[t[2]];
         coef[x] := -c2/c1;
         for i in related_to_me[x] do
	     free[i] := free[x];
             coef[i] *:= coef[x];
	     Append (~related_to_me[free[t[2]]], i);
         end for;
	 Append (~related_to_me[free[t[2]]], x);
      end if;

      if die gt 0 then
         for i in related_to_me[die] do
            free[i] := 1;
            coef[i] := F!0;
         end for;
	 free[die] := 1 ;
	 coef[die] := F!0;
      end if;
   end for;

   // Enumerate the subscripts of free generators that survived.
   // x_{i_1}  <----> y_1
   // x_{i_2}  <----> y_2, etc.

   for i in [1..#free] do
      if coef[i] eq 0 then
         free[i] := -1;
      end if;     
   end for;
*/

   ykey := {@ x : x in Set(free) | x ne -1 @};
   for i in [1..#free] do
      if free[i] eq -1 then
         free[i] := 1;
      else
         free[i] := Index(ykey,free[i]);
      end if;
   end for;
   return ykey, free, coef;
end function;



/*********************************************************
  Quotient:
  The INPUT is a list of (sparse) relations 
    [[<c_1, i_1>, <c_2, i_2>, ... <c_r,i_r>], ... ]
  The first listed spare relation is
     c_1*e_{i_1} + c_2*e_{i_2} + ... c_r*e_{i_r} = 0.
  The integer n denotes the total number of basis 
  elements e_i. 
  The field K is the field over which the c_i are defined.
  The OUTPUT is (1) an indexed set of g free generators, and
  (2) an expression for each e_i in terms of the free 
  generators.  These expressions are elements of the
  g-dimensional vector space over K.
       generators,   quotient 
 *********************************************************/

function XXXQuotient(rels, n, K)

   vprintf ModularSymbols, 2 : "\t Computing quotient by %o relations.\n", #rels;

   V := VectorSpace(K, n);
   Rels := [ &+[t[1]*V.t[2] : t in r] : r in rels];
   S := sub<V|Rels>;
   m := n - Dimension(S);
   B := Basis(S);
   pivots := Set(Pivots(B));
   gens := {@ i : i in [1..n] | i notin pivots @};

   vprintf ModularSymbols : "Form quot and then images";
   WW, f, X := V / S;
   quot := [X[i]: i in [1 .. Nrows(X)]];

   return gens, quot; 
end function;

function Quotient(rels, n, K)

    // AKS: improved 23/05/05 by use of Sparse matrices

   //if 1 eq 1 then

    
       S := SparseMatrix(K, #rels, n, []);
       for i in [1..#rels] do
	  for t in rels[i] do
	      //S[i, n+1 - t[2]] +:= t[1];
	      S[i, t[2]] +:= t[1];
	  end for;
       end for;

       EchelonNullspace(~S, ~N);

       pivots := {Min(Support(S, i)): i in [1 .. Nrows(S)]};
       delete S;
       gens := {@ i : i in [1..n] | i notin pivots @};

       Oquot := [N[i]: i in [1 .. Nrows(N)]];
       return gens, Oquot;

   //end if;

/*
   vprintf ModularSymbols, 2 : 
      "\t Computing quotient by %o relations.\n", #rels;

printf "Quotient rels: %o\n", rels;
printf "Quotient n: %o\n", n;
printf "Quotient K: %o\n", K;

   "S:", Matrix(S);
OS := S;

   V := VectorSpace(K, n);
   Rels := [ &+[t[1]*V.t[2] : t in r] : r in rels];

printf "Rels: %o\n", Rels;

   M := RMatrixSpace(K,#Rels,n)!0;
   for i in [1..#Rels] do
      M[i] := Rels[i];
   end for;
"M:", M;
   EF := EchelonForm(M);
"EF:", EF;
   S := sub<V| [EF[i] : i in [1..#Rels] | EF[i] ne V!0]>;
   m := n - Dimension(S);
   B := Basis(S);
   pivots := Set(Pivots(B));

   gens := {@ i : i in [1..n] | i notin pivots @};
"gens:", gens;
"ogens:", ogens;
assert gens eq ogens;

   vprintf ModularSymbols : "Form quot and then images";
"S:", S;
"T Null:", Transpose(BasisMatrix(NullspaceOfTranspose(EF)));
   WW, f, X := V / S;
   quot := [X[i]: i in [1 .. Nrows(X)]];

"gens:", gens;
"X quot:", X;

"Ech S:", Matrix(OS);
"N:", N;

assert BasisMatrix(S)*N eq 0;
assert N eq X;

   return gens, quot; 
*/

end function;

////////////////////////////////////////////////////////////////////
//  CONSTRUCT QUOTIENT BY 2 AND 3 TERM RELS                       //
////////////////////////////////////////////////////////////////////

function ManSym2termQuotient (mlist, eps, sign)
     n := mlist`n;
     K := mlist`F;
     k := mlist`k;
     S := [0,-1,  1,0];
     I := [-1,0,  0,1];
     xS := [ManinSymbolApply(S,i,mlist,eps,k) : i in [1..n]];
     S_rels := [ [i,   (xS[i][1])[2]] : i in [1..n]| #xS[i] gt 0];
     S_relc := [ [K!1, (xS[i][1])[1]] : i in [1..n]| #xS[i] gt 0];
     if sign ne 0 then
        xI := [ManinSymbolApply(I,i,mlist,eps,k) : i in [1..n]];
        I_rels := [ [i,    (xI[i][1])[2]] : i in [1..n]];
        I_relc := [ [K!1, -sign*(xI[i][1])[1]] : i in [1..n]];
     else
        I_rels := [];
        I_relc := [];
     end if;
     rels  := S_rels cat I_rels;
     relc  := S_relc cat I_relc;
     return Sparse2Quotient(rels,relc,n,K);

// FOR DEBUGING:
//    return Fake_Sparse2Quotient(rels,relc,n,K);

end function;


function ManSym3termQuotient (mlist, eps, Sgens, Squot, Scoef)
   // Construct the subspace of 3-term relations.
   n := mlist`n;
   F := mlist`F;
   k := mlist`k;
   T := [0,-1,  1,-1];
   TT:= [-1,1, -1,0];

   if k eq 2 then
      mask := [false : i in [1..n]];   // to avoid redundant 3-term relations.
      rels := [];
      for j in [1..n] do
         if not mask[j] then
            t  := ManinSymbolApply(T,j,mlist,eps,2)[1];
            tt := ManinSymbolApply(TT,j,mlist,eps,2)[1];
            mask[t[2]] := true;
            mask[tt[2]] := true;
            Append(~rels,  [<Scoef[j],Squot[j]>,
               <t[1]*Scoef[t[2]],Squot[t[2]]>,
               <tt[1]*Scoef[tt[2]],Squot[tt[2]]>]);
         end if;
      end for;
   else 
      rels := [&cat[
               [<Scoef[i],Squot[i]>], 
               [<x[1]*Scoef[x[2]],Squot[x[2]]>
                 : x in ManinSymbolApply(T,i,mlist,eps,k)],
               [<x[1]*Scoef[x[2]],Squot[x[2]]>
                 : x in ManinSymbolApply(TT,i,mlist,eps,k)]
              ]
             : i in [1..n]];
   end if;

   return Quotient(rels, #Sgens, F);
end function;

function XXXManSym3termQuotient (mlist, eps, Sgens, Squot, Scoef)
   // Construct the subspace of 3-term relations.
   n := mlist`n;
   F := mlist`F;
   k := mlist`k;
   T := [0,-1,  1,-1];
   TT:= [-1,1, -1,0];

   if k eq 2 then
      mask := [false : i in [1..n]];
      rels := [];
      for j in [1..n] do
         if not mask[j] then
            t  := ManinSymbolApply(T,j,mlist,eps,2)[1];
            tt := ManinSymbolApply(TT,j,mlist,eps,2)[1];
            mask[t[2]] := true;
            mask[tt[2]] := true;
            Append(~rels,  [<Scoef[j],Squot[j]>,
               <t[1]*Scoef[t[2]],Squot[t[2]]>,
               <tt[1]*Scoef[tt[2]],Squot[tt[2]]>]);
         end if;
      end for;
   else 
      rels := [&cat[
               [<Scoef[i],Squot[i]>], 
               [<x[1]*Scoef[x[2]],Squot[x[2]]>
                 : x in ManinSymbolApply(T,i,mlist,eps,k)],
               [<x[1]*Scoef[x[2]],Squot[x[2]]>
                 : x in ManinSymbolApply(TT,i,mlist,eps,k)]
              ]
             : i in [1..n]];
/*  FOR DEBUGING
      S := [0,-1,  1, 0];
      relsS := [
            &cat[
               [<Scoef[i],Squot[i]>], 
               [<x[1]*Scoef[x[2]],Squot[x[2]]>
                 : x in ManinSymbolApply(S,i,mlist,eps,k)]
              ]
             : i in [1..n]];
      rels :=  rels cat relsS;
*/
   end if;

   return Quotient(rels, #Sgens, F);
end function;


/**********************************************************
  CONVERSIONS:
        Modular symbols <-------> Manin symbols
 **********************************************************/

/********************************************************** 
   LiftToCosetRep
   x = [u,v] is an element of Z/NZ x Z/NZ such that
   gcd (u,v,N) = 1.  This function finds a 2x2 matrix
   [a,b,  c,d] such that c=u, d=v both modulo N, and
   so that ad-bc=1. 
   **********************************************************/  
function LiftToCosetRep(x, N) 
   c:=Integers()!x[1]; d:=Integers()!x[2];
   g, z1, z2 := Xgcd(c,d);
   // We're lucky: z1*c + z2*d = 1.
   if g eq 1 then  
      return [z2, -z1, c, d];
   end if ; 
      
   // Have to try harder.
   if c eq 0 then
      c +:= N;
   end if;
   if d eq 0 then
      d +:= N;
   end if;
   m := c;

   // compute prime-to-d part of m.
   repeat
      g := Gcd(m,d);
      if g eq 1 then 
         break;
      end if;
      m div:= g;
   until false;
   // compute prime-to-N part of m.
   repeat
      g := Gcd(m,N);
      if g eq 1 then 
         break;
      end if;
      m div:= g;
   until false;
   
   d +:= N*m;
   g, z1, z2 := Xgcd(c,d);
   if g eq 1 then  
      return [z2, -z1, c, d];
   else
      error "LiftToCosetRep: ERROR!!!";
   end if ; 
end function;


function ConvToManinSymbol(M, i)
   mlist := M`mlist;
   uv, w:= UnwindManinSymbol (
              M`quot`Sgens[M`quot`Tgens[i]], mlist);
   R := mlist`R;
   return <R.1^w*R.2^(Weight(M)-2-w),uv>;
end function;


function ConvToModSym(M, i) 
   mlist := M`mlist;
   uv, w, ind   := UnwindManinSymbol (
        M`quot`Sgens[M`quot`Tgens[i]], mlist);
   g     := LiftToCosetRep(uv, M`N);
   k := M`k;
   R := mlist`R;   
   if k eq 2 then 
      return <R!1,[[g[2],g[4]], [g[1],g[3]]]>;   // {g(0), g(oo)}
   end if; 
   h  := hom <R -> R  |  g[4]*R.1-g[2]*R.2, -g[3]*R.1+g[1]*R.2>; 
   P  := R.1^w*R.2^(k-2-w);
   hP := h(P);
   return <hP, [[g[2],g[4]], [g[1],g[3]]]>;  
end function;



/**********************************************************
  ConvToModularSymbol
  returns i-th freely generating Manin symbol
  written as a sum of modular symbols
    sum  X^i*Y^(k-2-i)*{alp,beta}
 **********************************************************/

function ConvToModularSymbol(M, v) 
/* 
    Returns an expression in terms of modular symbols of 
    the element v in the space M of modular symbols.  We
    represent a point in P^1(Q) by a pair [a,b].  Such a 
    pair corresponds to the point a/b in P^1(Q).
*/
   assert v in M;

   if IsMultiChar(M) then
      return MC_ConvToModularSymbol(M,v); 
   end if;

   M := AmbientSpace(M);
   w := Representation(v);
   nz := [i : i in [1..Dimension(M)] | w[i] ne 0];
   return [ <w[i]*x[1],x[2]> : i in nz | true where x is ConvToModSym(M, i)];
end function;


function ModularSymbolsBasis(M) 
// Return the basis of M in terms of modular symbols.
   if not assigned M`modsym_basis then
       M`modsym_basis := 
            [ConvToModularSymbol(M, M.i) 
                             : i in [1..Dimension(M)]];
   end if;
   return M`modsym_basis;
end function;


function ManSymGenListToRep(M,m) 
   quot := AmbientSpace(M)`quot;
   Scoef := quot`Scoef;
   Tquot := quot`Tquot;
   if IsEmpty(Tquot) then
      return M!0;
   end if;
   Squot := quot`Squot;
   ans := Universe(Tquot)!0;
   for t in m do 
      ans +:= t[1]*Scoef[t[2]]*Tquot[Squot[t[2]]];
   end for;
   return ans;
end function;

/*
// m is a sequence <alp, i> representing sum alp*e_i,
// where e_i runs through the initial list of 
// generating Manin symbols. 
function ManSymGenListToSquot(m,M,Tmat)
   Tquot := M`quot`Tquot;
   V:=Parent(Tquot[1]);
   Sgens := M`quot`Sgens;
   Scoef := M`quot`Scoef;
   Squot := M`quot`Squot;
   // Tmat is a map from W to V, where W is
   W:=VectorSpace(Field(V),#Sgens);
   v := W!0;
   for t in m do
      v[Squot[t[2]]] +:= t[1]*Scoef[t[2]];
   end for;
   return v;
end function;
*/

intrinsic ConvertFromManinSymbol(M::ModSym, x::Tup) -> ModSymElt
{The modular symbol in the ambient space of M 
associated to the 2-tuple x=<P(X,Y),[u,v]>, 
where P(X,Y) is homogeneous of degree k-2 and 
[u,v] is a sequence of 2 integers
that defines an element of P^1(Z/NZ), 
where N is the level of M.
}
   if IsMultiChar(M) then
      return M!MC_ManinSymToBasis(M,x);
   end if;
   return M!ConvFromManinSymbol(M,x[1],x[2]);
end intrinsic;


/**********************************************************
  FromManinSymbol:
  Given a Manin symbol [P(X,Y),[u,v]], this function
  computes the corresponding element of the space M
  of Modular symbols.
 **********************************************************/
function ConvFromManinSymbol (M, P, uv)
   //Given a Manin symbol [P(X,Y),[u,v]], this function
   //computes the corresponding element of VectorSpace(M).
   if IsMultiChar(M) then
      return MC_ManinSymToBasis(M, <P, uv>);
   end if;
   mlist := AmbientSpace(M)`mlist;
   R   := mlist`R;
   P   := R!P;
   k   := M`k;
   p1list := mlist`p1list;
   n   := #p1list;
   ind,s := P1Reduce(Parent(p1list[1])!uv, p1list);
   char := DirichletCharacter(M);
   if not IsTrivial(char) then
      P := R!Evaluate(char,Integers()!s) * P;
   elif s eq 0 then
      P := 0;
   end if;
   if k eq 2 then    // case added 04-09, SRD
      if P eq 0 then
         ans := [];
      else
         ans := [<BaseRing(R)!P, ind>];
      end if;
   else
      ans := [<mc, w*n + ind> : w in [0..k-2] | mc ne 0
              where mc is MonomialCoefficient(P,R.1^w*R.2^(k-2-w))];
   end if;
   v := ManSymGenListToRep(M, ans);
   return v;
end function;

/*
   Same as previous, but for several symbols [u,v] at once
   (only for weight 2)
*/
function ConvFromManinSymbols (M, mlist, P, uvs)
   if IsMultiChar(M) then
      return &+ [MC_ManinSymToBasis(M, <P, uv>) : uv in uvs];
   end if;
   R := mlist`R;
   P := BaseRing(R)!P;
   p1list := mlist`p1list;
   p1parent := Parent(p1list[1]);
   char := DirichletCharacter(M);
   trivial :=  IsTrivial(char);
   symbols := [];
   if P ne 0 then
      for uv in uvs do 
         ind,s := P1Reduce(p1parent!uv, p1list);
         if s ne 0 then 
            if trivial then
               a := 1;
            else
               a := Evaluate(char,Integers()!s); 
            end if;
            Append(~symbols, <a*P,ind>);
         end if;
      end for;
   end if;
   return ManSymGenListToRep(M, symbols);
end function;

// Compute P*{0,a/b}
function ConvFromModSym(M, V, ZN, P, a, b)
   if Dimension(M) eq 0 then
      return Representation(M)!0;
   end if;
   if b eq 0 then        // {0,oo}
      assert a ne 0;
      return ConvFromManinSymbol(M, P, [ZN|0,1]);      
   end if;
   v  := ContinuedFraction(a/b) cat [1];
   convergents_v := ConvergentsSequence(v, #v);
   mlist := M`mlist;

   if M`k eq 2 then
      seq := [];
/*
      p  := 0; 
      q  := 1;
      pp := 1;
      qq := 0;
//    ans := V!0;
//    R  := mlist`R;

      for j:= 1 to #v do 
         if q*pp-p*qq lt 1 then
            q *:= -1; // switches every j
         end if;
         Append(~seq, [ZN|qq, q]);
         p  := pp;
         q  := qq;
         cn := convergents_v[j];
         pp := Numerator(cn);
         qq := Denominator(cn);
      end for;
*/
      C:=ChangeUniverse([1,0] cat [Denominator(c) : c in convergents_v],ZN);
      seq2:=[[C[i+1],C[i]*(-1)^(i-1)] : i in [1..#C-2]];
      // assert seq eq seq2;
      ans := ConvFromManinSymbols(M, mlist, P, seq2); 

   else

      p  := 0; 
      q  := 1;
      pp := 1;
      qq := 0;
      ans := V!0;
      R  := mlist`R;

      for j:= 1 to #v do 
         det := q*pp-p*qq;
         g := [pp, p, qq, q];
         if det lt 1 then
            g[2] *:= -1;
            g[4] *:= -1;
         end if;
         hP := Evaluate(P,[ g[1]*R.1+g[2]*R.2, g[3]*R.1+g[4]*R.2]);
         ans +:= ConvFromManinSymbol(M, hP, [ZN|g[3], g[4]]);
         if j le #v then
            p  := pp;
            q  := qq;
            cn := convergents_v[j];
            pp := Numerator(cn);
            qq := Denominator(cn);
         end if;
      end for;
   end if;
   return ans;
end function;

/*
function ConvFromModularSymbol_helper(M, alpha, beta) 
// Returns the modular symbol \{alpha,beta\} in M.
   if Dimension(M) eq 0 then
      return M!0;
   end if;
   return ConvFromModularSymbol(M,<AmbientSpace(M)`mlist`R!1,[alpha,beta]>);
end function;
*/

function ConvFromModularSymbol_helper(M, V, ZN, Px) 
// Given a modular symbol P(X,Y)*\{alp,beta\},
//    FromModularSymbol returns the corresponding 
//    element of M.  The input is a pair <P,x>, where
//    P is a polynomial in X and Y, and
//    x=[[a,b],[c,d]] is a pair of elements of P^1(Q),
//    where [a,b] <--> a/b and [c,d] <--> c/d.} 

   // P(X,Y) in F[X,Y] is homogeneous of degree k-2.
   // Using the relation
   //   P*{a/b,c/d}=P*{a/b,0}+P*{0,c/d}=-P*{0,a/b} + P*{0,c/d}
   // we break the problem into two subgroups. 
   P, x := Explode(Px);
   a,b := Explode(Eltseq(x[1]));
   c,d := Explode(Eltseq(x[2]));
   return ConvFromModSym(M,V,ZN,P,c,d)
           -ConvFromModSym(M,V,ZN,P,a,b);
          
end function;


/**********************************************************
  Given a modular symbol P(X,Y)*{alp,beta},
  ConvFromModularSymbol returns the corresponding 
  element of M.  The input is a pair <P,x>, where
  P is a polynomial in X and Y, and
  x=[[a,b],[c,d]] is a pair of elements of P^1(Q),
     where [a,b] <--> a/b and [c,d] <--> c/d.
 **********************************************************/

function ConvFromModularSymbol(M, Px) 
/* Given a sequence of modular symbols P(X,Y)*\{alp,beta\},
    FromModularSymbol returns the corresponding 
    element of M.  The input is a sequence of pairs <P,x>, where
    P is a polynomial in X and Y, and x=[[a,b],[c,d]] is a 
    pair of elements of P^1(Q), where [a,b] <--> a/b and [c,d] <--> c/d.*/
   
   if IsMultiChar(M) then
      return M!MC_ModSymToBasis(M, Px);
   end if;

   R := AmbientSpace(M);
   V := VectorSpace(R);
   ZN:=quo<Integers()|Level(M)>;
   if Type(Px) eq Tup then
      w := ConvFromModularSymbol_helper(R, V, ZN, Px);
   else
      w := &+[ConvFromModularSymbol_helper(R, V, ZN, Px[i])
                : i in [1..#Px]];
   end if;
   return R!w;
end function;


intrinsic ModularSymbolRepresentation(x::ModSymElt) -> SeqEnum
{The standard represenation of the modular symbol x,
 as a sequence of tuples <coeff,[cusp1,cusp2]>.}
   if not assigned x`modsym_rep then
      x`modsym_rep := ConvToModularSymbol(Parent(x),x);
   end if;
   return x`modsym_rep;
end intrinsic;

/* This is never called; and apparently ConvToManinSymbol 
   expects an index i, not an element x   -- SRD
function ManinSymbolRepresentation(x) 
   if not assigned x`maninsym_rep then
      x`maninsym_rep := ConvToManinSymbol(Parent(x),x);
   end if;
   return x`maninsym_rep;
end function;
*/

