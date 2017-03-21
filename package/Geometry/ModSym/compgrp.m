freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: compgrp.m (Component groups)                                       

   $Header: /home/was/magma/packages/modsym/code/RCS/compgrp.m,v 1.4 2002/01/20 04:15:28 was Exp $

   $Log: compgrp.m,v $
   Revision 1.4  2002/01/20 04:15:28  was
   fixed a little spot where TamagawaNumber would compute cp correctly,
   then raise an error, because the error wasn't in the else part of an
   if.

   Revision 1.3  2001/07/14 01:31:52  was
   nothing..

   Revision 1.2  2001/05/13 03:45:36  was
   Changed verbose flags.

   Revision 1.1  2001/04/20 04:44:46  was
   Initial revision

   Revision 1.14  2001/01/28 09:33:50  was
   Allow computing Tamagawa number when sign=/=0, because if its a power
   of 2, we don't *care* what the power is.

   Revision 1.13  2001/01/25 13:36:32  was
   Fixed that sentence again.

   Revision 1.12  2001/01/25 13:35:48  was
   Changed ComponentGroup to ComponentGroupOrder in an error message.

   Revision 1.11  2000/08/01 21:10:31  was
   Made the change
         return [ Integers()!(A[i,i]/2) : i in [1..Nrows(A)]];
   to
         return [ Integers() | A[i,i] : i in [1..Nrows(A)]];
   because David renormalized.

   Revision 1.10  2000/07/29 04:57:02  was
   I don't know...

   Revision 1.9  2000/06/24 09:39:50  was
   Use a new function BasisX0, since X is no longer X0!

   Revision 1.8  2000/06/12 16:49:02  was
   Added a new intrinsic!

     intrinsic OrderOfImageOfComponentGroupOfJ0N(A::ModSym, p::RngIntElt)
      -> RngIntElt
     {Compute the order of the image of the component group of J_0(N)
       in the component group of A, all at p.}

   Revision 1.7  2000/06/03 04:47:51  was
   verbose

   Revision 1.6  2000/05/03 16:10:59  was
   I was being dumb about IsNew; the thing must be purely toric!

   Revision 1.2  2000/05/02 07:56:52  was
   Added $Log: compgrp.m,v $
   Added Revision 1.4  2002/01/20 04:15:28  was
   Added fixed a little spot where TamagawaNumber would compute cp correctly,
   Added then raise an error, because the error wasn't in the else part of an
   Added if.
   Added
   Added Revision 1.3  2001/07/14 01:31:52  was
   Added nothing..
   Added
   Added Revision 1.2  2001/05/13 03:45:36  was
   Added Changed verbose flags.
   Added
   Added Revision 1.1  2001/04/20 04:44:46  was
   Added Initial revision
   Added
   Added Revision 1.14  2001/01/28 09:33:50  was
   Added Allow computing Tamagawa number when sign=/=0, because if its a power
   Added of 2, we don't *care* what the power is.
   Added
   Added Revision 1.13  2001/01/25 13:36:32  was
   Added Fixed that sentence again.
   Added
   Added Revision 1.12  2001/01/25 13:35:48  was
   Added Changed ComponentGroup to ComponentGroupOrder in an error message.
   Added
   Added Revision 1.11  2000/08/01 21:10:31  was
   Added Made the change
   Added       return [ Integers()!(A[i,i]/2) : i in [1..Nrows(A)]];
   Added to
   Added       return [ Integers() | A[i,i] : i in [1..Nrows(A)]];
   Added because David renormalized.
   Added
   Added Revision 1.10  2000/07/29 04:57:02  was
   Added I don't know...
   Added
   Added Revision 1.9  2000/06/24 09:39:50  was
   Added Use a new function BasisX0, since X is no longer X0!
   Added
   Added Revision 1.8  2000/06/12 16:49:02  was
   Added Added a new intrinsic!
   Added
   Added   intrinsic OrderOfImageOfComponentGroupOfJ0N(A::ModSym, p::RngIntElt)
   Added    -> RngIntElt
   Added   {Compute the order of the image of the component group of J_0(N)
   Added     in the component group of A, all at p.}
   Added
   Added Revision 1.7  2000/06/03 04:47:51  was
   Added verbose
   Added
   Added Revision 1.6  2000/05/03 16:10:59  was
   Added I was being dumb about IsNew; the thing must be purely toric!
   Added

                                                                            
 ***************************************************************************/


import "arith.m": 
   PrimeDivPos;

import "linalg.m": 
   IntegerKernelZ, 
   MakeLattice,
   Restrict, 
   TrivialLattice;

import "mestre.m": 
   Mestre,
   MonodromyWeights,
   TpD, 
   BasisX0;

forward
   HeckeOperator_brandt,      
   MestreEigenvector,
   MestreGroup,
   MestreGroupV,
   MonodromyWeights_brandt,
   PhiX,
   PhiX_and_mX,
   PhiX_and_mX_brandt,
   XDimension,
   XGroup,
   XGroup_p,
   XGroup_M,
   XGroup_of_ModSym,
   XGroupV,
   XModularDegree;



/****************************************************************
 * FUNCTIONS FOR COMPUTING ORDERS OF COMPONENT GROUPS           *
 * Ref. Conrad-Stein, "Component groups of optimal quotients of * 
 * Jacobians".  and Kohel-Stein                                 *
 ****************************************************************/

intrinsic ComponentGroupOrder(M::ModSym, p::RngIntElt) -> RngIntElt
{The order of the component group at p.  This is the
order of the group of Fpbar-points of the component 
group of the reduction modulo p of the Neron model of the abelian
variety attached to M. At present, it is necessary that 
p exactly divides the level.   If Sign(M) is not equal to 0, 
then only the odd part of the order is returned.}
   require IsNew(M) and IsCuspidal(M) and Weight(M) eq 2 and
           Type(BaseField(M)) eq FldRat : 
           "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   require IsPrime(p) : "Argument 2 must be prime.";

   if Valuation(Level(M),p) eq 0 then
      return 1;
   end if;
   if Valuation(Level(M),p) gt 1 then
      error "Do not know how to compute component group at ",p;
   end if;
   if not assigned M`compgrp_orders then
      M`compgrp_orders := [];
   end if;
   if not exists(t) { t[2] : t in M`compgrp_orders | t[1] eq p } then
      phiX:= PhiX(M,p);
      mH  := ModularDegree(M);
      if Sign(M) ne 0 then
         mH /:= 2^Valuation(mH,2);
         if IsVerbose("ModularSymbols") then
            print "WARNING: Because working in +1 or -1 quotient, the component group order is only correct up to a power of 2.";
         end if;
      end if;
      mX  := XModularDegree(M,p);
      ans := phiX * mH / mX;   
      if Sign(M) ne 0 then
         ans /:= 2^Valuation(ans,2);
      end if;
      ans := Integers()!ans;
      Append(~M`compgrp_orders,<p,ans,mX,phiX>);
      return ans;
   end if;
   return t;
end intrinsic;


intrinsic TamagawaNumber(M::ModSym, p::RngIntElt) -> RngIntElt
{The order of the group of Fp rational points of
 the component group of M.}
//  WARNING: I (Stein) have not yet nailed down the power 
//  of 2 when Wp=+1!
   require IsNew(M) and IsCuspidal(M) and Weight(M) eq 2 and
           Type(BaseField(M)) eq FldRat : 
           "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   require HasAssociatedNewSpace(M) : "Argument 1 must correspond to a single newform.";
   require IsPrime(p) : "Argument 2 must be prime.";

   if Valuation(Level(M),p) eq 0 then
      return 1;
   end if;
   if Valuation(Level(M),p) gt 1 then
      error "Don't know how to compute Tamagawa number at ",p;
   end if;

   if not assigned M`tamagawa_numbers then
      M`tamagawa_numbers := [];
   end if;
   if not exists(t) { t[2] : t in M`tamagawa_numbers | t[1] eq p } then
      c := ComponentGroupOrder(M,p);
      w := AtkinLehner(M,p);
      cp := c;
      if w[1,1] eq +1 then
         if DimensionComplexTorus(M) eq 1 then
            cp := IsEven(cp) select 2 else 1;
         else
            if IsOdd(cp) then
               cp := 1;
            else 
               if IsOdd(cp div 2) then
                  cp := 2;
               elif Sign(M) ne 0 then
                  return 1;
               else
                  error "No algorithm known to compute the Tamagawa number at 2.  Use ComponentGroupOrder instead.";
               end if;
            end if;
         end if;
      end if;
      Append(~M`tamagawa_numbers,<p,cp>);
      return cp;
   end if;
   return t;
end intrinsic;



/////////////////////////////////////////////////////////////////
// The "XGroup" functions depend on the availability of        //
// David Kohel's functions:                                    //
//         QuaternionOrder, BrandtModule, HeckeOperator        //
// At present (10 Apr 2000) these three functions are defined  //
// in the following files of David Kohel:                      //
//   basis_reduction.m  hecke_modules.m   quadratic_modules.m  //
//   quaternion_ideals.m brandt_modules.m   linear_algebra.m   //
//   quaternion_algebras.m                                     //
//                                                             //
// Mestre's method of graphs, as implemented in mestre.m       //
/////////////////////////////////////////////////////////////////

declare attributes ModED:
          B,           // Brandt Modules
          p, M;

function XGroup(p,  M) 
/*{Return the character group X of the toric part of the
    closed fiber of the Neron model of J_0(pM) over F_p,
    along with the Eisenstein part.}*/
   tm := Cputime();
   assert IsPrime(p);// : "Argument 2 must be prime.";
   assert (M ge 1 and Gcd(p,M) eq 1);
          //  "Argument 2 must be greater than 1 and coprime to argument 1.";
   if IsVerbose("ModularSymbols") then
      if M gt 1 then
         printf "Computing character group of torus of J_0(%o*%o)/F_%o.\n",
               p, M, p;
      else
         printf "Computing character group of torus of J_0(%o).\n", p;
      end if; 
      t:=Cputime();
   end if; 
   B := BrandtModule(QuaternionOrder(p,M));
   X := RModule(Integers(), Dimension(B));
   X`B := B;
   if IsVerbose("ModularSymbols") then   
      Cputime(t), " seconds.";
   end if;
   X`p:=p;
   X`M:=M;
   return X;
end function;


function XGroup_p(X) 
//{Return the characteristic p of the character group of X_0(pM)/F_p.}
   return X`p;
end function;

function XGroup_M(X)
//{Return the level M of the character group of X_0(pM)/F_p.}
   return X`M;
end function;


function HeckeOperator_brandt(X, n) 
/* Compute the n-th Hecke operator on the toric part (+Eisenstein series) 
    of the closed fiber of the Neron model of J_0(pM) over F_p. */

   return HeckeOperator(X`B, n);

end function;


function MonodromyWeights_brandt(X)
// Returns the monodromy weights of the Brandt module X.
   A := GramMatrix(X`B);
   return [ Integers()!(A[i,i]) : i in [1..Nrows(A)]];

/*
  I believe that the only change necessary is that:

      return [ Integers()!(A[i,i]/2) : i in [1..Nrows(A)]];

  on line 245 of compgrp.m should become:

      return [ Integers() | A[i,i] : i in [1..Nrows(A)]];

*/

end function;


// Using quaternion algebras module.
function PhiX_and_mX_brandt(X, V) 
// Computes the quantities PhiX and mX associated to V.
   dummy := HeckeOperator_brandt(X,2);  // so that TM is defined. 
   n  := Dimension(X`B);
   m  := Dimension(V);
   W  := DiagonalMatrix(MatrixAlgebra(Integers(),n),
                        MonodromyWeights_brandt(X));
   L  := LatticeWithGram(W);
   B  := [ L.i - L.n : i in [1..n-1] ];
   C  := [ L!v : v in Basis(V) ];
   S  := Eltseq( LLL( RMatrixSpace(Integers(),n-1,m)! 
          &cat[ [ InnerProduct(u,v) : v in C ] : u in B ]) );
   PhiXmat := MatrixAlgebra(Integers(),m)![ S[i] : i in [1..m^2] ];
   PhiX := AbsoluteValue(Determinant(PhiXmat));
   disc := Determinant( MatrixAlgebra(Integers(),m)!
             [ InnerProduct(u,v) : u in C, v in C ] );
   mX := AbsoluteValue(disc/PhiX);
   return Integers()!PhiX, Integers()!mX; 
end function;



function XDimension(X)
// {Returns the dimension of the character group X.}
   return Dimension(X);
end function;


function XGroup_of_ModSym(M, p)
/*{Returns the character group of the toric part of the
    closed fiber at p of the space M of modular symbols.
    This only makes sense when p exactly divides the level
    of M and M has weight two.}*/
   assert Weight(M) eq 2;// : "Argument 1 must have weight 2.";
   assert IsPrime(p) and Valuation(Level(M),p) eq 1 ;//: "Argument 2 must be prime and exactly divide the level of argument 1.";
   fac := {@ x[1] : x in Factorization(M`N) @};
   if not assigned M`X then
      M`X := SequenceToList([0 : i in [1..#Factorization(M`N)]]);
   end if;
   i := Index(fac, p);
   if Type(M`X[i]) eq RngIntElt then
      M`X[i] := XGroup(p,Integers()!(M`N/p));
   end if;
   return M`X[i];
end function;


function XGroupV(A, p)
// Return the factor of the character group corresponding
// to the p-adic rigid analytic optimal and co-optimal quotient 
// associated to A.
   assert IsNew(A) and IsCuspidal(A) and Weight(A) eq 2 and
           Type(BaseField(A)) eq FldRat;// : "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   i := PrimeDivPos(p, Level(A));
   if not assigned A`X then
      A`X := SequenceToList([0 : j in [1..#Factorization(Level(A))]]);
   end if;
   if Type(A`X[i]) eq RngIntElt then
      Z := XGroup_of_ModSym(AmbientSpace(A),p);
      A`X[i] := RSpace(Integers(),XDimension(Z));
      d := DimensionComplexTorus(A);
      p := 2; 
      while Dimension(A`X[i]) gt d do
         T := HeckeOperator_brandt(Z, p);   // compute p-th Hecke operator. 
         f := CharacteristicPolynomial(HeckeOperator(A, p)); 
         A`X[i] := A`X[i] meet IntegerKernelZ(Evaluate(f,T));
         p := NextPrime(p);
         if p ge 23 and IsVerbose("ModularSymbols") then
             "XGroupV: Warning -- space taking more than 23 Hecke";
             "         operators to break up...";
         end if;
      end while;
   end if;
   return A`X[i];
end function;

intrinsic OrderOfImageOfComponentGroupOfJ0N(A::ModSym, p::RngIntElt) -> RngIntElt
{Compute the order of the image of the component group of J_0(N) 
 in the component group of A, all at p.}

   require IsPrime(p) : "Argument 2 must be prime.";

   require IsNew(A) and IsCuspidal(A) and Weight(A) eq 2 and
           Type(BaseField(A)) eq FldRat 
           : "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   require Valuation(Level(A),p) eq 1 
           : "Argument 2 must exactly divide the level of argument 1.";

   return PhiX(A,p);

end intrinsic;

intrinsic ImageOfComponentGroupOfJ0N(A::ModSym, p::RngIntElt) -> GrpAb, Map, Map
{The image Phi of the component group of J_0(N) at p in the component 
group of A at p, the natural map from F=Hom(X[I_A],Z) to Phi, and a map
that send an integer n to a matrix that gives the Hecke operator T_n on F 
with respect to Basis(F).}

   require IsPrime(p) : "Argument 2 must be prime.";
   require IsNew(A) and IsCuspidal(A) and Weight(A) eq 2 and
           Type(BaseField(A)) eq FldRat 
           : "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   require Valuation(Level(A),p) eq 1 
           : "Argument 2 must exactly divide the level of argument 1.";

   if not assigned A`component_group_image then
      A`component_group_image := SequenceToList([0 : i in [1..#Factorization(Level(A))]]);
   end if;
   i := PrimeDivPos(p,Level(A));
   if A`component_group_image[i] cmpeq 0 then
      if false and IsPrime(Level(A)) then  // can use the much faster Mestre module -- AND Emerton's theorem.
         error "Not programmed.";
      else
         X := XGroup_of_ModSym(AmbientSpace(A),p);
         V := XGroupV(A,p);
         dummy := HeckeOperator_brandt(X,2);  // so that TM is defined. 

         n  := Dimension(X`B);
         m  := Dimension(V);
         W  := DiagonalMatrix(MatrixAlgebra(Integers(),n), MonodromyWeights_brandt(X));
         L  := LatticeWithGram(W);
         B  := [ L.i - L.n : i in [1..n-1] ];   // basis for degree 0 subspace
         C  := [ L!v : v in Basis(V) ];

         hom_YI_Z := TrivialLattice(m);
         image_of_Y := MakeLattice([hom_YI_Z![ InnerProduct(u,v) : v in C ] : u in B ]);
         G, pi := quo< hom_YI_Z | image_of_Y>;
         Mat_m := MatrixAlgebra(Integers(),m);
         hecke := map<Integers() -> Mat_m | n :-> Transpose(Restrict(HeckeOperator_brandt(X, n),V))>;
         A`component_group_image[i] := <G, pi, hecke>;
      end if;
   end if;
   return Explode(A`component_group_image[i]);
end intrinsic;


function PhiX(A, p) 
//{Compute the order of the image of the component group of
//    J_0(N) in the component group of A, all at p.}
   assert IsNew(A) and IsCuspidal(A) and Weight(A) eq 2 and
           Type(BaseField(A)) eq FldRat;
         //  "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   assert Valuation(Level(A),p) eq 1;
         //  "Argument 2 must exactly divide the level of argument 1.";
   if not assigned A`xdata then
      A`xdata := SequenceToList([[0,0] : i in [1..#Factorization(Level(A))]]);
   end if;
   i := PrimeDivPos(p,Level(A));
   if A`xdata[i] eq [0,0] then
      if IsPrime(Level(A)) then  // can use the much faster Mestre module.
         x, y := PhiX_and_mX(MestreGroup(AmbientSpace(A)),MestreGroupV(A));
      else
         x, y := PhiX_and_mX_brandt(XGroup_of_ModSym(AmbientSpace(A),p), XGroupV(A,p));        
      end if;
      A`xdata[i] := [x,y];
   end if;
   return A`xdata[i][1];
end function;


function XModularDegree(A, p) 
//{Compute the p-adic modular degree of A.}
   assert IsNew(A) and IsCuspidal(A) and Weight(A) eq 2 and
           Type(BaseField(A)) eq FldRat ;
          // "Argument 1 must be new, cuspidal, of weight 2, and defined over Q.";
   assert Valuation(Level(A),p) eq 1 ;
          // "Argument 2 must exactly divide the level of argument 1.";
   if not assigned A`xdata or A`xdata[PrimeDivPos(p,Level(A))][1] eq 0 then
      dummy := PhiX(A,p);
   end if;
   return A`xdata[PrimeDivPos(p,Level(A))][2];
end function;



///////////////////////////////////////////////////////////////////
// COMPONENT GROUPS USING MESTRE'S CONSTRUCTION (see mestre.m)   //
///////////////////////////////////////////////////////////////////

function PhiX_and_mX(X, V)
//{Computes the quantity PhiX associated to V.}
   n      := Degree(X);
   m      := Dimension(V);
   weights:= MonodromyWeights(X);
   W      := MatrixAlgebra(Integers(),n)!0;
   for i in [1..n] do W[i,i] := weights[i]; end for;
   L      := LatticeWithGram(W);
   B      := [ L!v : v in BasisX0(X)];   // it is very important to move to L!
   C      := [ L!v : v in Basis(V) ];
   S      := Eltseq( LLL( RMatrixSpace(Integers(),n-1,m)! 
                &cat[ [ InnerProduct(u,v) : v in C ] : u in B ]) );
   PhiX   := AbsoluteValue( 
              Determinant( MatrixAlgebra(Integers(),m)!
                  [ S[i] : i in [1..m^2] ] ) );
   disc   := Determinant( MatrixAlgebra(Integers(),m)!
             [ InnerProduct(u,v) : u in C, v in C ] );
   mX     := AbsoluteValue(disc/PhiX);
   return Integers()!PhiX, Integers()!mX; 
end function;



//////////////////////////////////////////////////////////////
// Functions to obtain the Mestre modules associated        //
// to certain spaces of modular symbols.                    //
// These call the functions defined in mestre.m             //
//////////////////////////////////////////////////////////////

function MestreGroup(M)
//{Returns the Mestre module of M.  The level must be prime
//and the weight must be two.}
   assert Weight(M) eq 2 ;  // :"Argument 1 must have weight 2.";
   assert IsPrime(Level(M)); // : "Argument 1 must have prime level.";

   if not assigned M`mestre then
      M`mestre := Mestre(Level(M),1);
   end if;
   return M`mestre;
end function;


function MestreGroupV(M) 
/*{Return the factor of the character group corresponding
 to the p-adic rigid analytic optimal quotient 
 associated to M. The representation is via the 
 Mestre construction.}   */
   assert IsCuspidal(M) and Weight(M) eq 2 and IsNew(M);
         // "Argument 1 must have weight 2, and be cuspidal and new.";
   assert IsPrime(Level(M)); // : "Argument 1 must have prime level.";
   if not assigned M`mestre then
      Z := MestreGroup(AmbientSpace(M));
      M`mestre := RSpace(Integers(),Degree(Z));
      d := DimensionComplexTorus(M);
      p := 2; 
      while Dimension(M`mestre) gt d do
         T := TpD(Z, p);   // compute p-th Hecke operator. 
         f := PolynomialRing(Integers())!
               CharacteristicPolynomial(HeckeOperator(M, p)); 
         M`mestre := M`mestre meet Kernel(Evaluate(f,T));
         p := NextPrime(p);
         if p gt 7 and IsVerbose("ModularSymbols") then
             "MestreGroupV: Warning -- space not breaking up.";;
         end if;
      end while;
   end if;
   return M`mestre;
end function;


function MestreEigenvector(M) 
   return MestreEigenvector(MestreGroup(AmbientSpace(M)), 
                            MestreGroupV(M));
end function;



