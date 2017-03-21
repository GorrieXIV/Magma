freeze;
 
/*******************************************************************
* functions for symplectic groups                                  *
*******************************************************************/

SymplecticFormIGLC := function(G)

//G should be matrix group acting (absolutely?) irreducibly.
//Decide whether G preserves symplectic form.
  
local M, D, bool, mat;
M:=GModule(G);
D:=Dual(M);
bool, mat:= IsIsomorphic(M,D);
if bool then
    if mat eq -Transpose(mat) then
        return bool, mat;
    end if;
end if;
return false, _;
end function;

/********************************************************************
* functions for orthogonal groups.                                  *
********************************************************************/

/*******************************************************
* This function computes the quadratic form preserved by
* an orthogonal group in characteristic 2.
*/

ClassicalForms_QuadraticForm2 := function(field,form,gens,scalars)

    // raise and error if char is not two
    error if Characteristic(field) ne 2, "ERROR: characteristic must be two";

    // construct the upper half of the form
    R := MatrixRing(field,NumberOfRows(form));
    H := 0*form;
    for i in [1..NumberOfRows(form)] do
        for j in [i+1 .. NumberOfRows(form)] do
            H[i,j] := form[i,j];
        end for;
    end for;

    // store the linear equations in <e>
    e := [];
   
    // loop over all generators
    b := [];
    for y in [1..#gens] do

        // remove scalars
        x := R!gens[y]*scalars[y]^-1;

        // first the right hand side
        r := x*H*Transpose(x)+H;

        // check <r>
        for i in [1..NumberOfRows(form)] do
            for j in [1..NumberOfRows(form)] do
                if r[i,j]+r[j,i] ne Zero(field) then
                   return false;
                end if;
            end for;
        end for;

        // and now the diagonals
        for i in [1..NumberOfRows(form)] do
            l := [];
            for j in [1..NumberOfRows(form)] do
                l[j] := x[i,j]^2;
            end for;
            l[i] +:= 1;
            Append(~b,r[i,i]);
            Append(~e,l);
        end for;
    end for;

    // and return a solution
    V := VectorSpace(field,#gens*NumberOfRows(form));
    h := RMatrixSpace(field,Degree(V),NumberOfRows(form));
    b := V!b;
    e := h![e[i,j]:j in [1..NumberOfRows(form)],i in [1..#e]];

    flag, e := IsConsistent (Transpose (e), b);
    if flag then
       for i in [1..NumberOfRows(form)] do
           H[i,i] := e[i];
       end for;
       return H;
    else
       return false;
    end if;

end function;

/******************************************************************
* This one computes the type of an orthogonal form in Characteristic
* 2. It seems to do an awful lot f unneccesary sutff, I'm not really
* sure.... 
*/

ClassicalForms_Signum2 := function(field,form,quad)

     // compute a new basis, such that the symmetric form is standard
     base := form^0;
     avoid := [];
     for i in [1..NumberOfRows(form)-1] do

         // find first non zero entry
         d := 1;
         while d in avoid or form[i,d] eq Zero(field) do
               d +:= 1;
         end while;
         Append(~avoid,d);

         // clear all other entries in this row & column
         for j in [d+1..NumberOfRows(form)] do
             c := form[i,j]/form[i,d];
             if c ne Zero(field) then
                for k in [1..NumberOfRows(form)] do
                    form[k,j] := form[k,j] - c*form[k,d];
                end for;
                form[j] := form[j] - c*form[d];
                base[j] := base[j] - c*base[d];
             end if;
         end for;
      end for;

      // reshuffle basis
      c := [];
      j := [];
      for i in [1..NumberOfRows(form)] do
          if not i in j then
             k := form[i][avoid[i]];
             Append(~c,base[i]/k);
             Append(~c,base[avoid[i]]);
             Append(~j,avoid[i]);
          end if;
      end for;
      base := c;

      // and try to fix the quadratic form (this not really necessary)
      R := PolynomialRing(field);
      x := R![0,1];
      sgn := 1;
      for i in [1..NumberOfRows(form)-1 by 2] do
          c := InnerProduct(base[i]*quad,base[i]);
          if c eq Zero(field) then
             c := InnerProduct(base[i+1]*quad,base[i+1]);
             if c ne Zero(field) then
                base[i+1] := base[i+1] - c*base[i];
             end if;
          else
             j := InnerProduct(base[i+1]*quad,base[i+1]);
             if j eq Zero(field) then
                base[i] := base[i] - c*base[i+1];
             else
                pol := [y[1]:i in [1..y[2]],y in Factorisation(x^2+x/j + c/j)];
                if #pol eq 2 then
                   pol := [-Coefficients(y)[1]:y in pol];
                   base[i] := base[i]+pol[1]*base[i+1];
                   base[i+1] := (base[i]+pol[2]*base[i+1])/(pol[1]+pol[2]);
                else
                   sgn := -sgn;
                end if;
             end if;
          end if;
     end for;

     // and return
     return sgn;

end function;

/********************************************************************
 * This next one is actually a magma intrinsic. Works for odd 
 * characteristic. Doesn't use the third input.
 */

ClassicalForms_Signum := function(field, form, quad)

        // if dimension is odd, the signum must be 0
        if NumberOfRows(form) mod 2 eq 1 then
            return [0];
 
        // hard case: characteristic is 2
        elif Characteristic(field) eq 2 then
            error "ERROR : characteristic must be odd";
        end if;
 
        // easy case
        det := Determinant(form);
        sqr := Log(det) mod 2 eq 0;
        size := #field;
        if Integers()!(NumberOfRows(form)*
                 (Characteristic(field)^Degree(field)-1)/4) mod 2 eq 0 then
            if sqr then  sgn := +1;
            else         sgn := -1;
            end if;
        else
            if sqr then  sgn := -1;
            else         sgn := +1;
            end if;
         end if;

         // and return
         return sgn;

end function;


/*************************************************************
 * This one is also a magma intrinsic. Finds a quadratic form
 * when over a field of characteristic 2.
 * Hmm, I may wait actually.
 */



OrthogonalFormIGLC:= function(G, d, q)

// G should be a matrix group acting (absolutely?) irreducibly.
// Decide whether G preserves a symmetric bilinear form.

local M, D, bool, mat;
M:= GModule(G);
D:= Dual(M);
bool, mat:= IsIsomorphic(M, D);
if bool then
    if mat eq Transpose(mat) then
        if IsOdd(d) then
            return true, "orth", mat;
        end if;
        if IsOdd(q) then
            sign:= ClassicalForms_Signum(GF(q), mat, 0);
        else
            gens:= SetToSequence(Generators(G));
            scals:= [Identity(G) : i in [1..#gens]];
            quad:= ClassicalForms_QuadraticForm2(GF(q), mat, gens,
	    scals);
            if quad cmpeq false then
                 return false, _, _;
            end if;
            sign:= ClassicalForms_Signum2(GF(q), mat, quad);
        end if;
        if sign eq 1 then
            return true, "orth+", mat;
        elif sign eq -1 then
            return true, "orth-", mat;
        else
            "Signum failed";
            return false, _, _;
        end if;
    end if;
end if;
return false, _, _;
end function;


/********************************************************************
* functions for unitary groups                                      *
********************************************************************/

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power. 
list:= Eltseq(a);
for i in [1..#list] do
    list[i]:= list[i]^q;
end for;
return list;
end function;

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    A[i][j] := A[i][j]^q;
  end for; end for;
  return A;
end function;

ModToQ := function(M,q)
// same for GModule M
  local G;
  G := Group(M);
  return GModule(G,
    [ MatToQ(m,q): m in [ActionGenerator(M,i): i in [1..Ngens(G)]]]);
end function;

UnitaryFormIGLC := function(G, dim, q)
//G should be matrix group over GF(q^2) acting (
//absolutely?) irreducibly.
//Decide whether G preserves unitary form.
local  M, D, DD;
//dim := Dimension(G);
//q2 := #BaseRing(G);
//f := Factorisation(q2);
//if f[1][2] mod 2 eq 1 then return false,_; end if;
//q := f[1][1]^(f[1][2] div 2);
M:=GModule(G);
D:=Dual(M);
DD:=ModToQ(D,q);
bool, mat:= IsIsomorphic(M,DD);
if not bool then 
    return bool, _;
end if;
  /* We now need to ensure that mat is actually the matrix of a/
   * unitary form, which can be achieved by multiplying it by a scalar
   */
  if mat ne Transpose(MatToQ(mat, q)) then
    c := Representative(
        { <i,j>: i in [1..dim], j in [1..dim] | mat[i][j] ne GF(q^2)!0 } );
    x := mat[c[1]][c[2]]*mat[c[2]][c[1]]^-q;
    z := Root(x,q-1);
    scal:= DiagonalMatrix([z : i in [1..dim]]);
    mat *:= scal;
    assert mat eq Transpose(MatToQ(mat, q));
  end if;

  return bool, mat;

end function;
