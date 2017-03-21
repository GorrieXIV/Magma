freeze;

/*
  (2012-11-06) Don Taylor
  Removed this file from ClassicalSylow.spec and renamed 
  import "form.m" to import "../Forms/form.m" in all relevant files.

  (2012-01-24) Don Taylor
  
  The intrinsics which were in this file:
    ClassicalFormsCS
    OrthogonalFormCS
    QuadraticFormCS
    SymmetricBilinearFormCS
    SymplecticFormCS
    UnitaryFormCS

  are not used anywhere else in the system and have counterparts
  (without the CS suffix) in Group/GrpMat/Forms/form.m.
  
  Some functions are imported into other files in this package. That is,

      ClassicalForms_QuadraticForm2, 
      ClassicalForms_Signum, 
      ClassicalForms_Signum2, 
      MatToQ

  are imported into
  
      ClSylowNorm.m
      ClassicalSylow.m
      SylowConjClassical.m
      conj_form.m [not active]
      
  All intrinsics and all functions other than the above have been removed.
  See old_form.m for the original code.
*/



/*******************************************************
* This function computes the quadratic form preserved by
* an orthogonal group in characteristic 2.

 IDENTICAL to the function in ../Forms/form.m
*/

ClassicalForms_QuadraticForm2 := function(field,form,gens,scalars)

    local R, H, e, b, x, r, l, V;
    // raise an error if char is not two
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
* 2. It seems to do an awful lot of unneccesary stuff, I'm not really
* sure.... 

 IDENTICAL to the function in ../Forms/form.m
*/

ClassicalForms_Signum2 := function(field,form,quad)

     local base, avoid, d, c, j, k, R, x, sgn, pol;
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

/*
 Except for the spurious use of 'size' this is
 IDENTICAL to the function in ../Forms/form.m
*/
ClassicalForms_Signum := function(field, form)

        local det, sqr, size;
        // if dimension is odd, the signum must be 0
        if NumberOfRows(form) mod 2 eq 1 then
            return 0;
 
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

/*
 IDENTICAL to the function in ../Forms/form.m
 (And it occurs in many other places, sometimes with
 the name changed.)
*/
MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  local B;
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;


