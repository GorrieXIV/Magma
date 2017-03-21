freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//    function for writing elements of SL2(Z) in                  //
//         terms of S = [0,1;-1,0] and T = [1,1,0,1]              //
//      uses continued fractions algorithm, and is also           //
//      contained in code for computing interesction pairing      //
//      of weight 2 modular symbols                               //
//                                                                //
////////////////////////////////////////////////////////////////////

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

function MatrixToWord(n)
   m := Matrix(n);
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
      assert word eq [2];
      r := d/c;
   end if;
   word := word cat [Sign(r):i in [1..Floor(Abs(r))]];
   
   // fix the first sign change:
   if sign eq -1 then 
      assert Abs(word[length]) eq 2;
      word[length] := -word[length]; 
   end if;
   // fix the second sign change:
   if Sign(leftfrac) eq -1 then 
      word := [-2] cat word; 
   end if;

   return word;
end function;

