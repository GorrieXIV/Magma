freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************

                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: intersection_pairing.m -- The intersection pairing.

   $Header: /home/was/magma/modsym/RCS/intersection_pairing.m,v 1.5 2001/05/17 18:31:37 was Exp $
   $Log: intersection_pairing.m,v $
   Revision 1.5  2001/05/17 18:31:37  was
   nothing.

   Revision 1.4  2001/05/17 18:26:55  was
   Helena messed with it!


   Revision by Helena Verrill: update to improved version of
   ST word functions.
   

   Revision 1.2  2001/05/13 03:49:41  was
   Changed ModularForms flag to ModularSymbols.

   Revision 1.1  2001/04/20 04:46:58  was
   Initial revision

   Revision 1.5  2001/04/10 23:49:03  was
   Restricted IntersectionPairing so that both arguments must be cuspidal.

   Revision 1.4  2001/01/16 11:09:03  was
   Removed some spurious time commands.

   Revision 1.3  2001/01/16 11:04:05  was
   done with version 1.

   Revision 1.2  2001/01/16 10:59:06  was
   Header info.

   
   William A. Stein   (was@math.harvard.edu),
   with significant input from Helena Verrill.

   13--16 January 2001

   DESCRIPTION: We compute the intersection pairing 

        H_1(X_0(N),{cusps};Q) x H_1(X_0(N)-{cusps};Q) ---> Q

   restricted to weight-2 cuspidal modular symbols.  
   Our algorithm builds on the paper of MEREL,
   "Intersections sur des courbes modulaires", 
   manuscripta math. 80, 283 -- 289 (1993). 
   See, in particular, the last sentence of that paper.
   WARNING: There is a mistake in Proposition 4 of 
   that paper!  (See below.)

   Acknowledgment: Georg Weber provided many helpful insights that
   helped the authors implement this algorithm.

 *********************************************************/


import "core.m": LiftToCosetRep;

forward GeneratingSTprods,
        GeneratorsForGamma0,
        HR_ptesI, 
        FullIntersectionPairingMatrix,
        Intersect_modsym_HR_ptesI,
        Intersect_modsym_STprod,
        MatrixToWord,
        ModSymPivots,
        Validate_modsym,
        Validate_modsymspace,
        Validate_STprod;


intrinsic IntersectionPairing(x::ModSymElt, y::ModSymElt) -> FldRatElt
   {The intersection pairing (x,y) of the homology classes corresponding
   to the weight-2 cuspidal modular symbols x and y.}

   M := Parent(x);
   require Weight(M) eq 2 : "Weight must be 2.";
   require BaseField(M) cmpeq Rationals(): "Base field must be rationals.";
   require IsTrivial(DirichletCharacter(M)) : "Dirichlet character must be trivial.";
   require Sign(M) eq 0: 
         "The parent of x must be a full space of modular symbols; "*
         "in particular, it should not have sign = +1 or -1.";
   require y in M : "Arguments 1 and 2 must have the same parent.";
   require x in CuspidalSubspace(M) : "Argument 1 must be cuspidal.";
   require y in CuspidalSubspace(M) : "Argument 2 must be cuspidal.";

   I := FullIntersectionPairingMatrix(M);
   return InnerProduct(Representation(x)*I,Representation(y));

end intrinsic;

intrinsic IntersectionPairing(M::ModSym) -> AlgMatElt
{Matrix of intersection pairing with respect to the basis of M.}
   require IsCuspidal(M) : "Argument 1 must be cuspidal.";
   require Type(BaseField(M)) eq FldRat : "Argument 1 must be over the rational field.";
   if not assigned M`int_pairing then
      I := FullIntersectionPairingMatrix(AmbientSpace(M));   
      B := RMatrixSpace(BaseField(M), Dimension(M), Degree(M))!Basis(VectorSpace(M));
      M`int_pairing := B*I*Transpose(B);
   end if;
   return M`int_pairing;
end intrinsic;

function FullIntersectionPairingMatrix(M)
   Validate_modsymspace(M);
   assert IsAmbientSpace(M);
   if not assigned M`int_pairing then
      n := Dimension(M);
      N := Level(M);
      vprint ModularSymbols, 2: "Intersection pairing: Finding generating products.";
      genST := GeneratingSTprods(M);
      vprint ModularSymbols, 2: "Intersection pairing: Lifting generating ST-products to H^R_{cusps,I}.";
      y := [HR_ptesI(g[2],N) : g in genST];
      p1 := P1Classes(Level(M));

      // Make a matrix whose columns are the vectors in genST[i][1], 
      // then extend it to an invertible matrix.
      vd := [Representation(g[1]) : g in genST];    // actual generators
      d  := #vd;
      W := VectorSpaceWithBasis(vd);
      vn := ExtendBasis(W,VectorSpace(M));          // extended
      V := Transpose(MatrixAlgebra(BaseField(M),n)!vn)^(-1);
 
      // Make the matrix whose i,j entry is <e_i, v_j>, where 
      // <,> is the intersection pairing and <e_i,v_j> is 0 when j > d.
      manin := [ManinSymbol(M.i) : i in [1..n]];
      vprint ModularSymbols, 2 : "Intersection pairing: Computing the pairing on a basis.";
      t := Cputime();
      I0 := MatrixAlgebra(BaseField(M),n)!0;
      for i in [1..n] do
         for j in [1..d] do
            I0[i,j] := Intersect_modsym_HR_ptesI(manin[i], y[j], p1);
         end for;
      end for;
      M`int_pairing := I0*V;
      vprint ModularSymbols, 2: "Time:", Cputime(t);
   end if;

   return M`int_pairing;
end function;


////////// validation code ////////////////////////////////////

procedure Validate_modsymspace(M)
   assert Type(M) eq ModSym;
   assert Sign(M) eq 0;
   k := Weight(M);
   F := BaseField(M);
   N := Level(M);
   assert k eq 2;
   assert Type(F) eq FldRat;
   assert IsTrivial(DirichletCharacter(M));
end procedure;


procedure Validate_modsym(x)
   assert Type(x) eq ModSymElt;
   M := Parent(x);
   Validate_modsymspace(M);
end procedure;


procedure Validate_STprod(ST)
// simply check that the ST product is a possibly-empty
// sequence of integers in the set {-2,2,-1,1}.
   for x in ST do
      assert x in {-2,2,-1,1};
   end for;
end procedure;

////////// end validation ////////////////////////////////////


function Coset(g, p1)
   return P1Reduce(Parent(p1[1])!g[2],p1);
end function;

function Intersect_modsym_HR_ptesI(x,y,p1)
   // x is supposed to be a Manin symbol, as output by ManinSymbol(ModSym).
   // y is an element of HR_ptesI
   // p1 = P1List.
   // There is no error checking for efficiency sake. 

   i := 0;   // will equal the intersection number.
   for m in x do
      g  := m[2];
      gsigma := Parent(g)![g[2],-g[1]];
      i +:= m[1]*(y[Index(p1,g)] - y[P1Reduce(gsigma, p1)]);
   end for;

   return i;
end function;



function Intersect_modsym_STprod(x, ST)   // for testing...
   Validate_modsym(x);
   N := Level(Parent(x));
   p1 := P1Classes(N);   // reps for cosets of Gamma_0(N) in SL_2(Z).
   y := HR_ptesI(ST,N);
   return Intersect_modsym_HR_ptesI(x,y,p1);
end function;


/*********************************************************
  Each element g in SL_2(Z) can be written as a product 
     prod_{i=1}^n   W_i^{e_i}, where
   for i=1,..n, W_i in {S,T} and e_i in {1,-1}. 
   S = [0,-1,1,0], T = [1,1,0,1]  (infinite order).

   Such an "ST product" is coded for the computer as follows:
   It is a sequence of integers from the set {-1,1,-2,2},
   where -2 <--> S^{-1}, 2 <--> S,  -1 <--> T^{-1}, 
   and 1 <--> T.
 *********************************************************/

function HR_ptesI(STprod, N)
/***************************************
  Given a length n ST-product, i.e., a list of 
  integers from {-1,1,-2,2}, compute the
  following linear combination of the 
  cosets of Gamma_0(N) in SL_2(Z):

    - sum_{k=1}^n [ (prod_{i=1}^{k-1} W_i^(eps_i)) W_k^{alpha_k} ]

   where alpha_k = 1 if eps_k = +1, otherwise alpha_k = 0.
 
   WARNING: This comes from Proposition 4 of Merel's paper, which
   contains an INCORRECT variant of the above formula!

  OUTPUT: Recall that the function "P1Classes" outputs 
  an indexed set R of representatives for the cosets 
  of Gamma_0(N), in some order.   The output of the 
  present function is a sequence v such that v[i] is 
  the coefficient of the coset represented by R[i]. 

 ***************************************/

   assert Type(N) eq RngIntElt;
   assert N ge 1;
   Validate_STprod(STprod);

   p1 := P1Classes(N);
   v := [0 : x in p1];

   M2 := MatrixAlgebra(Integers(),2);
   T := M2![1,1,0,1];
   S := M2![0,-1,1,0];   

   // W and eps are a little trick so that, e.g., 
   // W[STprod[i]+3] gives the matrix W_i and
   // eps[STprod[i]+3] is eps_i.
   W   := [ S,  T, 0, T, S];  
   Weps:= [ S^(-1),  T^(-1), 0, T, S];  
   eps := [-1, -1, 0, 1, 1];

   last := M2!1;
   P := M2!1;
   for k in [1..#STprod] do
      // compute the product (prod_{i=1}^{k-1} W_i) W_k^{alpha_k}.

      if k gt 1 then
         P := last*Weps[STprod[k-1]+3];
         last := P;
      end if;

      if eps[STprod[k]+3] eq +1 then  // eps_k=+1
         P := P*W[STprod[k]+3];
      end if;

      assert eps[STprod[k]+3] ne 0;

      // determine the coset:
      coset := Coset(P,p1);
      v[coset] +:= eps[STprod[k]+3];
   end for;   
   return [-v[i] : i in [1..#v]];
end function;



function ModularSymbolOfSTprod(M, STprod)
   Validate_modsymspace(M);

   // mat -- a little trick so that
   // mat[STprod[i]+3] gives the matrix S^(-1), T^(-1), T, S.
   M2 := MatrixAlgebra(Integers(),2);
   T := M2![1,1,0,1];
   S := M2![0,-1,1,0];   
   mat := [S^(-1), T^(-1), 0, T, S];

   g := M2!1;
   for i in [1..#STprod] do
      g := g * mat[STprod[i]+3];
   end for;

   assert g ne 0;

   N := Level(M);
   assert g[2,1] mod N eq 0;    // matrix should be in Gamma_0(N).
   // (Note: g[2,2] can not be 0, because then g would have determinate
   //  divisible by p, which is contrary to det(g)=1.)

   return M!<1, [0, g[1,2]/g[2,2]]>;    // return {0,g(0).}
end function;


function GeneratingSTprods(M)
   Validate_modsymspace(M);   

   S := CuspidalSubspace(M);
   N := Level(M);
   n := Dimension(S);

   gens := GeneratorsForGamma0(N);
   
   V := VectorSpace(BaseField(M),Dimension(M));
   W := sub<V|0>;
   i := 1;
   prods := [];
   while Dimension(W) lt n and i le #gens do   
      g := gens[i];
      s := M!<1, [0, g[1,2]/g[2,2]]>;
      x := Representation(s);  // {0,g(0)} in V.
      if not (x in W) then
         W := W + sub<V|x>;
         Append(~prods, <s, MatrixToWord(g)>);
      end if;
      i +:= 1;
   end while;
   return prods;

end function;




// Given a sequence X of modular symbols, find a subset
// that forms a basis for the space they all together span.
// The reason this function is called "Pivots" is that it
// is accomplished by chosing a basis and writing each
// element of X as a *column* of a matrix.  Then the columns 
// in which the pivots of the reduced *row*-echelon form of 
// the matrix are the generators. 
function ModSymPivots(X)
   assert Type(X) eq SeqEnum;
   assert #X gt 0;
   assert Type(X[1]) eq ModSymElt;
   M := Parent(X[1]);
   Validate_modsymspace(M);
   V := VectorSpace(M);   

   A := RMatrixSpace(Rationals(),#X,Dimension(M))!0;
   for i in [1..#X] do
      A[i]  := V!Eltseq(X[i]);
   end for;
   A := Transpose(A);
   A := EchelonForm(A);

   /* The code below is really messy and shouldn't be needed (?!) */
   pivots := [];
   c := 0;
   B := Transpose(A);   // to get columns.
   for i in [1..NumberOfColumns(A)] do
      b := B[i];  // ith column of A.
      if b ne 0 then
         d := Min(Support(b));
         if d gt c then
            Append(~pivots, i);
            c := d;
         end if;
      end if;
   end for;
   return pivots;

end function;


function GeneratorsForGamma0(N)
   // return generators for Gamma_0(N).
   assert Type(N) eq RngIntElt;
   assert N ge 1;

   M2 := MatrixAlgebra(Integers(),2);
   Mmod := MatrixAlgebra(Integers(N),2);
   S := M2![0,-1,1,0];   
   T := M2![1,1,0,1];
   I := M2!1;
   Smod := Mmod![0,-1,1,0];   
   Tmod := Mmod![1,1,0,1];

   p1 := P1Classes(N);
   reps := [M2!LiftToCosetRep(uv, N) : uv in p1];
   ans := [];
   for i in [1..#p1] do
      x := reps[i];
      y := reps[P1Reduce(p1[i]*Smod, p1)];
      z := reps[P1Reduce(p1[i]*Tmod, p1)];
      Append(~ans,x*S*y^(-1));
      Append(~ans,x*T*z^(-1));
   end for;
   ans := [x : x in ans | x ne I];
   
   return [x : x in Set(ans)];
end function;
 
//     FracToWord;     (function of a continued fraction)
//     MatrixToWord;   (function of a matrix)
//     WordToMatrix;   (function of a word in T,S)  ("word" meaning as below)
//   also some functions for testing this program at the end.  
//
//  given a matrix A in SL_2(Z), the rest of this file
//  continued fractions to give the expression
//  for A as a product of matrices S, T, S^{-1}, T^{-1}
//
//  a sequence of numbers in {-2,-1,1,2}
//  corresponds to a sequence of {S^{-1},T^{-1},T,S},
//  in the corresponding order.
//  e.g., [1,2,-1,2,1,1,1,1] -> TST^(-1)ST^4
//  such a sequence is called a "word"
//
//  for theorem/example see bottom of this file


/////////////////////////////////////////////////
//
//   Function to Convert from 
//   a continued fraction to the corresponding S,T list
//   i.e., a vector with entries in {-2,-1,1,2}
//   example:
//   entering:   FracToWord([1,3,5,2]);
//   returns:    [ 1, 2, -1, -1, -1, 2, 1, 1, 1, 1, 1, 2, -1, -1 ]
//
/////////////////////////////////////////////////

function FracToWord(cf)
   assert Type(cf) eq SeqEnum;

   word := [];
   sign := 1;
   for i in cf do
      lim := i;
      sgn := sign; 
      if i lt 0 then 
         sgn := -sign; 
         lim := -i; 
      end if;
      for j in [1..lim] do
         Append(~word,sgn);
      end for;
      Append(~word,sign*2);
      sign:=-sign;
   end for;
   return word;

end function;


/////////////////////////////////////////////////
//
// 
//  WordToMatrix 
//  Given a word in terms of S and T, (given as 
//  a sequence of numbers in {-2,-1,1,2}),
//  this function returns the matrix obtained by
//  taking the product
//
//
/////////////////////////////////////////////////

/*
function WordToMatrix(word)
   assert Type(word) eq SeqEnum;
   M2 := MatrixAlgebra(Integers(),2);
   T  := M2![1,1,0,1];
   S  := M2![0,-1,1,0];
   A  := M2!1;
   for i in word do
      case i:
         when 1:
            A:=A*T;
         when 2:
            A:=A*S;
         when -1:
            A:=A*T^(-1);
         when -2:
            A:=A*S^(-1);
      end case; 
   end for;
   return A;
end function;
*/


/////////////////////////////////////////////////
// 
//  MatrixToWord
//  
//  this function writes an expression for
//  a matrix A in terms of matrices S and T
//  outputing a sequence of numbers in {-2,-1,1,2}
//
// where:
// M2:=MatrixAlgebra(Integers(),2);
// T:=M2![1,1,0,1];
// S:=M2![0,-1,1,0];
// 
/////////////////////////////////////////////////

function MatrixToWord(m)
   assert m in MatrixAlgebra(Integers(),2);
   // first deal with a trivial case:
   if m[2,1] eq 0 then 
      r := m[1,2]*m[1,1];
      sign := Sign(r);
      word := [sign : i in [1..Floor(Abs(r))]]; 
      if m[1,1] lt 0 then 
         word := word cat [ -2,-2 ]; 
      end if;
      return word;
   end if;

   sign := Sign(m[1,1]);
   if sign eq 0 then 
      sign := 1; 
   end if;
   m := sign*m;               // (sign change for simplicity; corrected later)
   leftfrac := m[1,1]/m[2,1];   // (i.e., fraction from left half of matrix)

   if Sign(leftfrac) ne -1 then
      word := FracToWord(ContinuedFraction(leftfrac));
   else 
      S := MatrixAlgebra(Integers(),2)![0,-1,1,0];
      m := S*m;       // (another sign change for simplicity; corrected later)
      word := FracToWord(ContinuedFraction(-1/leftfrac));
   end if;

   length:=#word;
   odd:=Sign(word[length]);

   a := m[1,1];  b := m[1,2]; c := m[2,1];  d := m[2,2];
   if (a ne 0)  then
      r := (b - (b mod a))/a  + (odd+1)/2;
   else 
      r := (d - (d mod c))/c  + (odd+1)/2;
   end if;
   word := word cat [Sign(r):i in [1..Floor(Abs(r))]];
   
   // fix the first sign change:
   if sign eq -1 then 
      word[length] := -word[length]; 
   end if;
   // fix the second sign change:
   if Sign(leftfrac) eq -1 then 
      word := [-2] cat word; 
   end if;

   return word;
end function;



/////////////////////////////////////////////////
//
//    Continued fractions and S-T words:
//
//    Let M2:=MatrixAlgebra(Integers(),2);
//    Let T:=M2![1,1,0,1];
//    Let S:=M2![0,-1,1,0];
//    Let A:=M2![a,b,c,d];
//
//    Theorem:
//    If the continued fraction expansion for a/c
//    is given by
//    ContinuedFraction(a/c) = [a_0,a_1,a_2,...,a_m]
//    Then A*T^r = T^(a_0).S.T^(-a_1).S.T^(a_2).....S.T^((-1)^m.a_m).S
//    where: r is such that:
//        A.T^r = M2![a,b',c,d'], with 
//        
/////////////////////////////////////////////////























