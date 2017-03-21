freeze;

/*
**  Multiplication and Inversion for unipotent elements for Classical types.
** 
**  $Id: classic_mul.m 18797 2008-11-29 07:51:42Z murray $
** 
**  Sergei Haller
** 
**  August 2006 
** 
*/

import "../Root/RootDtm.m" : toType;
forward class_mul, class_inv;

/*
**  This function is called from within Unip_Product.
**  R     -- Root datum
**  x,y   -- sequences of field elts representing the uipotent elts.
**  order -- the collectionOrder of the group
**
**  return sequence z representing the product of x and y
*/
Unip_ProductByClassic := function( R, x, y, order ) 
    // all these assumptions are met before we get here:
    //      assume extraspecial signs are -1                                         // otherwise Classical not chosen
    //      assume classical type, indecomposable                                    // true for all sparse data
    //      assume collectionOrder corresponds to the order-by-columns as in paper!  // true for all sparse data

    t := toType(R)[1][1];
    n := Rank(R);
    N := NumPosRoots(R);
    perm  := Sym(N)!order;

    x := PermuteSequence(x,perm);
    y := PermuteSequence(y,perm);

    z := class_mul(t,n,x,y);

    z  := PermuteSequence(z,perm^-1);

    return z;
end function;

/*
**  This function is called from within Unip_Inverse.
**  R     -- Root datum
**  x     -- sequence of field elts representing the uipotent elts.
**  order -- the collectionOrder of the group
**
**  return sequence z representing the inverse of x
*/
Unip_InverseByClassic := function( R, x, order ) 
    // all these assumptions are met before we get here:
    //      assume extraspecial signs are -1                                         // otherwise Classical not chosen
    //      assume classical type, indecomposable                                    // true for all sparse data
    //      assume collectionOrder corresponds to the order-by-columns as in paper!  // true for all sparse data

    t := toType(R)[1][1];
    n := Rank(R);
    N := NumPosRoots(R);
    perm  := Sym(N)!order;

    x := PermuteSequence(x,perm);

    z := class_inv(t,n,x);

    z  := PermuteSequence(z,perm^-1);

    return z;
end function;





forward fill_up1, fill_up2, un_fill;

/*
**  This is the actual multiplication function.
**  t   -- type 
**  n   -- rank
**  x,y -- are sequences of field elts representing the uipotent elts.
**         field elts must be ordered w.r.t. collectionOrder
**
**  return sequence z (ordered w.r.t. collectionOrder) representing the product of x and y
*/
function class_mul(t,n,x,y)
    R := Universe(x);
    deg := case<t| "A":n+1, "B":2*n+1, "C":2*n, "D":2*n, default:0>; 
    M := MatrixAlgebra(R,deg);
    X := M!1;
    Y := M!1;

    r := 1; // just a counter for roots, not the rth root of Root datum!
    case t:
    when "A":
        // i is row, j is column
        for j in [1..n], i in [1+j..n+1] do 
            X[i,j] := x[r];
            Y[i,j] := y[r];
            r+:=1;
        end for;
    when "B":
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            X[i,j] := x[r];
            Y[i,j] := y[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
        fill_up2(t,n,~Y);
    when "C":
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            X[i,j] := x[r];
            Y[i,j] := y[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
        fill_up2(t,n,~Y);
    when "D":
        // i is row, j is column
        for j in [1..n-1], i in [1+j..2*n-j] do
            X[i,j] := x[r];
            Y[i,j] := y[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
    else:
        error "this should not happen! All types A-D are implemented";
    end case;
    
    if GetVerbose("SHdebugGrpLie") ge 2 then
        return X,Y;
    end if;
    Z := X*Y;

    z := [R|];
    r := 1; // just a counter for roots, not the rth root of R!
    case t:
    when "A":
        // i is row, j is column
        for j in [1..n], i in [1+j..n+1] do 
            z[r] := Z[i,j];
            r+:=1;
        end for;
    when "B":
        un_fill(t,n,~Z);
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    when "C":
        un_fill(t,n,~Z);
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    when "D":
        // i is row, j is column
        for j in [1..n-1], i in [1+j..2*n-j] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    else:
        error "this should not happen! All types A-D are implemented";
    end case;

    return z;
end function;

/*
**  This is the actual inversion function.
**  t   -- type 
**  n   -- rank
**  x   -- sequence of field elts representing the uipotent elt.
**         field elts must be ordered w.r.t. collectionOrder
**
**  return sequence z (ordered w.r.t. collectionOrder) representing the inverse of x
*/
function class_inv(t,n,x)
    R := Universe(x);
    deg := case<t| "A":n+1, "B":2*n+1, "C":2*n, "D":2*n, default:0>; 
    M := MatrixAlgebra(R,deg);
    X := M!1;

    r := 1; // just a counter for roots, not the rth root of Root datum!
    case t:
    when "A":
        // i is row, j is column
        for j in [1..n], i in [1+j..n+1] do 
            X[i,j] := x[r];
            r+:=1;
        end for;
    when "B":
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            X[i,j] := x[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
    when "C":
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            X[i,j] := x[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
    when "D":
        // i is row, j is column
        for j in [1..n-1], i in [1+j..2*n-j] do
            X[i,j] := x[r];
            r+:=1; 
        end for;
        fill_up1(t,n,~X);
    else:
        error "this should not happen! All types A-D are implemented";
    end case;

    Z := X^-1;

    z := [R|];
    r := 1; // just a counter for roots, not the rth root of R!
    case t:
    when "A":
        // i is row, j is column
        for j in [1..n], i in [1+j..n+1] do 
            z[r] := Z[i,j];
            r+:=1;
        end for;
    when "B":
        un_fill(t,n,~Z);
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    when "C":
        un_fill(t,n,~Z);
        // i is row, j is column
        for j in [1..n], i in [1+j..2*n-j+1] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    when "D":
        // i is row, j is column
        for j in [1..n-1], i in [1+j..2*n-j] do
            z[r] := Z[i,j];
            r+:=1; 
        end for;
    else:
        error "this should not happen! All types A-D are implemented";
    end case;

    return z;
end function;


/*
**  This procedure fills the necessary entries of the first matrix
**  t   -- type 
**  n   -- rank
**  X   -- matrix
*/
procedure fill_up1(t,n,~X);
    R := BaseRing(X);

    case t:
    when "B":
        n1 := n+1;
        n2 := 2*n+2;

        for j in [n..1 by -1] do
            j1 := j+1;

            // fill the a'' entries
                v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
                w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
                X[n2-j,j] := - (v,w);

            // fill lower triangular part.
            for i in [j1 .. n2-j1] do
                v := Vector([R| X[k,j] : k in [n2-i ..    j1 by -1]]);
                w := Vector([R| X[k,i] : k in [   i .. n2-j1      ]]);
                X[n2-j,i] := - (v,w);
            end for;

            // double the 0 line
            X[n1,j] *:= 2;
        end for;

    when "C":
        n1 := n+1;
        n2 := 2*n+1;

        for j in [n..1 by -1] do
            j1 := j+1;

            // fill the a'' entries
                v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
                w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
                X[n2-j,j] -:= (v,w);

            // fill lower triangular part.
            for i in [j1 .. n] do
                v := Vector([R|-X[k,j] : k in [n2-i ..    n1 by -1]]
                         cat[R| X[k,j] : k in [   n ..    j1 by -1]]   );
                w := Vector([R| X[k,i] : k in [   i .. n2-j1      ]]);
                X[n2-j,i] := - (v,w);
            end for;
            for i in [n1 .. n2-j1] do
                v := Vector([R| X[k,j] : k in [n2-i ..    j1 by -1]]   );
                w := Vector([R| X[k,i] : k in [   i .. n2-j1      ]]);
                X[n2-j,i] := - (v,w);
            end for;
        end for;
        
    when "D":
        n1 := n+1;
        n2 := 2*n+1;

        for j in [n..1 by -1] do
            j1 := j+1;

            // fill the a'' entries
                v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
                w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
                X[n2-j,j] := - (v,w);

            // fill lower triangular part.
            for i in [j1 .. n2-j1] do
                v := Vector([R| X[k,j] : k in [n2-i ..    j1 by -1]]);
                w := Vector([R| X[k,i] : k in [   i .. n2-j1      ]]);
                X[n2-j,i] := - (v,w);
            end for;
        end for;
        
    else:
        error "fill_up1 only used for types B, C and D";
    end case;

end procedure;

/*
**  This procedure fills the necessary entries of the second matrix
**  t   -- type 
**  n   -- rank
**  X   -- matrix
*/
procedure fill_up2(t,n,~X);
    R := BaseRing(X);
    n1 := n+1;
    case t:
    when "B":
        if Characteristic(R) ne 2 then
            // double the 0 line
            for j in [1..n] do
                X[n1,j] *:= 2;
            end for;
        else
            // have to fill the b' entries to recover the 0 line later
            n2 := 2*n+2;
            for j in [n..1 by -1] do
                j1 := j+1;

                // fill the a'' entries
                v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
                w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
                X[n2-j,j] := - (v,w);

                // double the 0 line
                X[n1,j] := 0;
            end for;
        end if; // char //

    when "C":
        n2 := 2*n+1;

        for j in [n..1 by -1] do
            j1 := j+1;

            // fill the a'' entries
            v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
            w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
            X[n2-j,j] -:= (v,w);
        end for;
        
    else:
        error "fill_up2 only used for types B and C";
    end case;
end procedure;

/*
**  This procedure unfills the necessary entries of the resulting matrix,
**  t   -- type 
**  n   -- rank
**  X   -- matrix
*/
procedure un_fill(t,n,~X);
    R := BaseRing(X);
    case t:
    when "B":
        n1 := n+1;
        n2 := 2*n+2;

        if Characteristic(R) ne 2 then
            // easy: halve the 0 line
            for j in [1..n] do
                X[n1,j] /:= 2;
            end for;
        else // char 2 //
            // recover the 0 line from the a' entries

            for j in [n..1 by -1] do
                    j1 := j+1;
                v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
                w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
                sc := (v,w);
                X[n1,j] := Sqrt(X[n2-j,j] + sc);
            end for;
        end if; // char //

    when "C":
        n1 := n+1;
        n2 := 2*n+1;

        for j in [n..1 by -1] do
            j1 := j+1;

            // un_fill the a'' entries
            v := Vector([R| X[k,j] : k in [n2-j1 ..    n1 by -1]]);
            w := Vector([R| X[k,j] : k in [   j1 .. n2-n1      ]]);
            X[n2-j,j] +:= (v,w);
        end for;
        
    else:
        error "un_fill only used for type B and C";
    end case;
end procedure;



