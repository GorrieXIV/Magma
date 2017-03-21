freeze;

function ZeroMatrix(q, d_1, d_2)
return Matrix(GF(q), d_1, d_2, []);
end function;

/*
 * The following function takes as input the 4 matrices A, B, C, D,
 * defined over the same field, and returns the matrix
 * A B
 * C D
 */

function BlockMatrix(A, B, C, D)
  mat1:= HorizontalJoin(A, B);
  mat2:= HorizontalJoin(C, D);
  return VerticalJoin(mat1, mat2);
end function;

//This function will accept entry 0 to mean the zero matrix, provided
//that at least one entry in each row and column is not zero.
function SquareBlockMatrix(input_list, q);
 blocks:= #input_list;
 list:= [* *];
 for x in input_list do
   Append(~list, x);
 end for;

 bool, rows:= IsSquare(blocks);
 if not bool then return false; end if;
 
 
 rowmats:= [* *];
 for i in [1..rows] do
   range:= [(i-1)*rows+1..i*rows];
   zeroset:= [x: x in range | list[x] cmpeq 0];
   if #zeroset gt 0 then
     for x in zeroset do
       if not exists(rowmat){y : y in range | not list[y] cmpeq 0} then
         "each row must contain a nonzero entry";
         return 0;
       end if;
       nrows:= Nrows(list[rowmat]);
       colset:= [j : j in [1..blocks] | (j mod rows) eq (x mod rows)];
       if not exists(colmat){z : z in colset | not list[z] cmpeq 0} then
         "each column must contain a nonzero entry";
         return 0;
       end if;
       ncols:= Ncols(list[colmat]);
       list[x]:= ZeroMatrix(q, nrows, ncols);
     end for;
   end if;
   temp:= Matrix(HorizontalJoin(<list[((i-1)*rows)+j] : j in
        [1..rows]>));
   Append(~rowmats, temp);
 end for;

 finalmat:= VerticalJoin(<rowmats[i]: i in [1..rows]>);

 return finalmat;
end function;

