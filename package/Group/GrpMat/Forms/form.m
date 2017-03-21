freeze;

ApproximateDerivedGroup := function(G)
/* G must act absolutely irreducibly. This functions attempts to compute
 * a subgroup of [G,G] that acts absolutely irreducibly.
 * If it succeeds, it returns true and the subgroup.
 * If it fails (perhaps because [G,G] is not absolutely irreducible),
 * then it reurns false.
 */
  local d,F,H,oldl,done,ct,l,P;

  if not IsAbsolutelyIrreducible(G) then
    error "Group is not acting absolutely irreducibly";
  end if;

  d := Dimension(G);
  F := BaseRing(G);
  P := RandomProcess(G : Scramble:=Max(50,Ngens(G)) );

  H := sub< GL(d, F) | (Random(P),Random(P)), (Random(P),Random(P)),
                                                 (Random(P),Random(P)): Check := false >;
  oldl := d;
  done := false;
  ct := 0;
  repeat
    l := #CompositionSeries(GModule(H));
    if l lt oldl then //making progress!
      oldl := l;
      ct := 0;
    end if;
    if l eq 1 then
      if IsAbsolutelyIrreducible(H) then
        done := true;
      else
        H := sub< GL(d, F) | H, (Random(P),Random(P)) >;
        ct +:= 1;
      end if;
    else
      H := sub< GL(d, F) | H, (Random(P),Random(P)) >;
      ct +:= 1;
    end if;
  until done or ct eq Max(20,Ngens(G));

  if done then
    return true, H;
  end if;
  return false, _;
end function;
 
/*******************************************************************
* functions for symplectic groups                                  *
*******************************************************************/


intrinsic SymplecticForm(G::GrpMat : Scalars:=false ) -> BoolElt, AlgMatElt, MonStgElt
{Assuming that G acts absolutely irreducibly, try to find a symplectic
form which is G-invariant (modulo scalars if Scalars is true) or prove
that no such form exists.}

//G should be matrix group acting (absolutely?) irreducibly.
//Decide whether G preserves symplectic form.
  
local M, D, bool, mat, scals, tmat, d, z, s;
  if not IsIrreducible(G) then
    error "SymplecticForm: G must be irreducible";
  end if;
  M:=GModule(G);
  D:=Dual(M);
  d := Dimension(G);
  bool, mat:= IsIsomorphic(M,D);
  if bool then
   if mat eq -Transpose(mat) then
    /* To get a unique result, we make the first nonzero entry
     * in mat 1 */
    for i in [1..d] do if mat[1][i] ne 0 then
      mat *:= mat[1][i]^-1;
      break;
    end if; end for;
    if Scalars then return bool, mat, [mat[1][1]^0 : i in [1..Ngens(G)]];
    else return bool, mat;
    end if;
   end if; //if mat eq -Transpose(mat)
   if not Scalars then
    if IsAbsolutelyIrreducible(G) then
      return false, _;
    else
      error "SymplecticForm failed - group is not absolutely irreducible";
      //return "unknown", _;
    end if;
   end if;
  end if; //if bool
  if not Scalars then
    return false, _;
  end if;

  bool, D := ApproximateDerivedGroup(G);
  if not bool then
    error
   "SymplecticForm failed - derived group may not be absolutely irreducible";
    //return "unknown",_,_;
  end if;
  bool, mat := $$(D);
  if bool then
    scals := [];
    z := 0*mat[1][1];
    for g in [G.i: i in [1..Ngens(G)]] do
      tmat := g*mat*Transpose(g);
      s := z;
      for i in [1..d] do for j in [1..d] do
        if tmat[i][j] ne z then
          if mat[i][j] eq z then return false, _, _; end if;
          if s eq z then s := tmat[i][j]*mat[i][j]^-1;
          elif s ne tmat[i][j]*mat[i][j]^-1 then return false, _, _;
          end if;
        elif mat[i][j] ne z then return false, _, _;
        end if;
      end for; end for;
      Append(~scals,s);
    end for;
    return true, mat, scals;
  end if;
  return false, _, _;
end intrinsic;

/********************************************************************
* functions for orthogonal groups.                                  *
********************************************************************/

/*******************************************************
* This function computes the quadratic form preserved by
* an orthogonal group in characteristic 2.
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

/********************************************************************
 * This next one is actually a magma intrinsic. Works for odd 
 * characteristic.
 */

ClassicalForms_Signum := function(field, form)

        local det, sqr;
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

intrinsic OrthogonalForm( G::GrpMat ) -> BoolElt, MonStgElt, AlgMatElt
{Assuming that G acts absolutely irreducibly, try to find a symmetric
bilinear form which is G-invariant, or a quadratic form in characteristic 2.}

// G should be a matrix group acting (absolutely?) irreducibly.
// Decide whether G preserves a symmetric bilinear form.

  local M, F, D, bool, mat;
  if not IsIrreducible(G) then
    error "SymmetricBilinearForm: G must be irreducible";
  end if;
  M:= GModule(G);
  d := Dimension(G);
  F := BaseRing(G);
  q := #F;
  D:= Dual(M);
  bool, mat:= IsIsomorphic(M, D);
  if bool then
      if mat eq Transpose(mat) then
  /* To get a unique result, we make the first nonzero entry
   * in mat 1 */
          for i in [1..d] do if mat[1][i] ne 0 then
            mat *:= mat[1][i]^-1;
            break;
          end if; end for;
          if IsOdd(d) then
              return true, "orth", mat;
          end if;
          if IsOdd(q) then
              sign:= ClassicalForms_Signum(F, mat);
          else
              gens:= SetToSequence(Generators(G));
              scals:= [Identity(G) : i in [1..#gens]];
              quad:= ClassicalForms_QuadraticForm2(F, mat, gens, scals);
              if quad cmpeq false then
                if IsAbsolutelyIrreducible(G) then
                  return false, _, _;
                else
      error "OrthogonalForm failed - group is not absolutely irreducible";
                  //return "unknown", _, _;
                end if;
              end if;
              sign:= ClassicalForms_Signum2(F, mat, quad);
          end if;
          if sign eq 1 then
              return true, "orth+", mat;
          elif sign eq -1 then
              return true, "orth-", mat;
          else
              "Signum failed";
              return false, _, _;
          end if;
      end if; //if mat eq Transpose(mat)
      if IsAbsolutelyIrreducible(G) then
          return false, _, _;
      else
  error "OrthogonalForm failed - group is not absolutely irreducible";
        //return "unknown", _, _;
      end if;
  end if; //if bool
  return false, _, _;
end intrinsic;

/* Plus a couple of others to replace existing Magma functions */

intrinsic SymmetricBilinearForm(G::GrpMat : Scalars:=false ) -> BoolElt, AlgMatElt, MonStgElt
{Assuming that G acts absolutely irreducibly, try to find a symmetric
bilinear form which is G-invariant (modulo scalars if Scalars is true) or
prove that no such form exists.}

  local M, D, bool, mat, d, F, q, sign, type;
  if not IsIrreducible(G) then
    error "SymmetricBilinearForm: G must be irreducible";
  end if;
  d := Dimension(G);
  F := BaseRing(G);
  q := #F;
  M:=GModule(G);
  D:=Dual(M);
  bool, mat:= IsIsomorphic(M,D);
  if bool then
   if mat eq Transpose(mat) then
    for i in [1..d] do if mat[1][i] ne 0 then
      mat *:= mat[1][i]^-1;
      break;
    end if; end for;
    if IsOdd(q) then
      sign:= IsEven(d) select ClassicalForms_Signum(F, mat) else 0;
    else
      gens:= SetToSequence(Generators(G));
      scals:= [Identity(G) : i in [1..#gens]];
      quad:= ClassicalForms_QuadraticForm2(F, mat, gens, scals);
      if quad cmpeq false then
        //should only happen in characteristic 2
        if Scalars then return bool, mat, "symplectic",
                                      [mat[1][1]^0 : i in [1..Ngens(G)]];
        else return bool, mat, "symplectic";
        end if;
      end if;
      sign:= ClassicalForms_Signum2(F, mat, quad);
    end if;
    type := sign eq 1 select "orthogonalplus" else sign eq -1
                      select "orthogonalminus" else "orthogonalcircle";
    if Scalars then return bool, mat, type, [mat[1][1]^0 : i in [1..Ngens(G)]];
    else return bool, mat, type;
    end if;
   end if; //if mat eq Transpose(mat)
   if not Scalars then
     if IsAbsolutelyIrreducible(G) then
       return false, _, _;
     else
 error "SymmetricBilinearForm failed - group is not absolutely irreducible";
       //return "unknown", _, _;
     end if;
   end if;
  end if; //if bool
  if not Scalars then return false, _, _; end if;

  bool, D := ApproximateDerivedGroup(G);
  if not bool then
   error
"SymmetricBilinearForm failed - derived group may not be absolutely irreducible";
    //return "unknown",_,_,_;
  end if;
  bool, mat, type := $$(D);
  if bool then
    scals := [];
    z := 0*mat[1][1];
    d := Dimension(G);
    for g in [G.i: i in [1..Ngens(G)]] do
      tmat := g*mat*Transpose(g);
      s := z;
      for i in [1..d] do for j in [1..d] do
        if tmat[i][j] ne z then
          if mat[i][j] eq z then return false,_,_,_; end if;
          if s eq z then s := tmat[i][j]*mat[i][j]^-1;
          elif s ne tmat[i][j]*mat[i][j]^-1 then return false,_,_,_;
          end if;
        elif mat[i][j] ne z then return false,_,_,_;
        end if;
      end for; end for;
      Append(~scals,s);
    end for;
    return true, mat, type, scals;
  end if;
  return false,_,_,_;
end intrinsic;

intrinsic QuadraticForm(G::GrpMat : Scalars:=false ) -> BoolElt, AlgMatElt, MonStgElt
{Assuming that G acts absolutely irreducibly, try to find a quadratic form
which is G-invariant (modulo scalars if Scalars is true) or prove that no
such form exists.}

// G should be a matrix group acting (absolutely?) irreducibly.
// Decide whether G preserves a quadratic form

  local d, F, q, M, D, bool, mat, sign, type;
  if not IsIrreducible(G) then
    error "QuadraticForm: G must be irreducible";
  end if;
  
  d := Dimension(G);
  F := BaseRing(G);
  q := #F;
  M:= GModule(G);
  D:= Dual(M);
  bool, mat:= IsIsomorphic(M, D);
  if bool then
   if mat eq Transpose(mat) then
    for i in [1..d] do if mat[1][i] ne 0 then
      mat *:= mat[1][i]^-1;
      break;
    end if; end for;
    if IsOdd(q) then
        sign := IsOdd(q) select ClassicalForms_Signum(F, mat) else 0;
        for i in [2..d] do for j in [1..i-1] do
           mat[i][j] := 0*mat[i][j];
        end for; end for;
        for i in [1..d] do mat[i][i] /:= 2; end for;
        type := sign eq 1 select "orthogonalplus" else sign eq -1
                      select "orthogonalminus" else "orthogonalcircle";
        if Scalars then
          return bool, mat, type, [mat[1][1]^0 : i in [1..Ngens(G)]];
        else return bool, mat, type;
        end if;
    end if;
    gens:= SetToSequence(Generators(G));
    scals:= [Identity(G) : i in [1..#gens]];
    quad:= ClassicalForms_QuadraticForm2(F, mat, gens, scals);
    if quad cmpne false then
      sign:= ClassicalForms_Signum2(F, mat, quad);
    elif Scalars then return false, _, _, _;
    else return false, _, _;
    end if;
    type := sign eq 1 select "orthogonalplus" else sign eq -1
                      select "orthogonalminus" else "orthogonalcircle";
    if Scalars then return bool, quad, type, [mat[1][1]^0 : i in [1..Ngens(G)]];
    else return bool, quad, type;
    end if;
   end if; //if mat eq Transpose(mat)
   if not Scalars then
     if IsAbsolutelyIrreducible(G) then
       return false, _, _;
     else
           error "QuadraticForm failed - group is not absolutely irreducible";
       //return "unknown", _, _;
     end if;
   end if;
  end if; //if bool
  if not Scalars then return false, _, _; end if;

  bool, D := ApproximateDerivedGroup(G);
  if not bool then
   "QuadraticForm failed - derived group may not be absolutely irreducible";
     //return "unknown",_,_,_;
  end if;
  bool, mat, type := $$(D);
  if bool then
    scals := [];
    z := 0*mat[1][1];
    d := Dimension(G);
    for g in [G.i: i in [1..Ngens(G)]] do
      tmat := g*mat*Transpose(g);
      for i in [2..d] do for j in [1..i-1] do
           tmat[j][i] +:= tmat[i][j];
           tmat[i][j] := 0*tmat[i][j];
      end for; end for;
      s := z;
      for i in [1..d] do for j in [i..d] do
        if tmat[i][j] ne z then
          if mat[i][j] eq z then return false, _, _, _; end if;
          if s eq z then s := tmat[i][j]*mat[i][j]^-1;
          elif s ne tmat[i][j]*mat[i][j]^-1 then return false, _, _, _;
          end if;
        elif mat[i][j] ne z then return false, _, _, _;
        end if;
      end for; end for;
      Append(~scals,s);
    end for;
    return true, mat, type, scals;
  end if;
  return false, _, _, _;
end intrinsic;


/********************************************************************
* functions for unitary groups                                      *
********************************************************************/

ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power. 
  local list;
  list:= Eltseq(a);
  for i in [1..#list] do
      list[i]:= list[i]^q;
  end for;
  return list;
end function;

MatToQ := function(A,q)
// raise every element of matrix A to q-th power
  local B;
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

ModToQ := function(M,q)
// same for GModule M
  local G;
  G := Group(M);
  return GModule(G,
    [ MatToQ(m,q): m in [ActionGenerator(M,i): i in [1..Ngens(G)]]]);
end function;

intrinsic UnitaryForm(G::GrpMat : Scalars:=false ) -> BoolElt, AlgMatElt
{Assuming that G acts absolutely irreducibly, try to find a unitary form
which is G-invariant (modulo scalars if Scalars is true) or prove that no
such form exists.}

//G should be matrix group over GF(q^2) acting (absolutely?) irreducibly.
//Decide whether G preserves unitary form.
  local d, F, q2, q, M, D, DD;
  d := Dimension(G);
  F := BaseRing(G);
  q2 := #F;
  f := Factorisation(q2);
  if f[1][2] mod 2 eq 1 then
    if Scalars then return false,_,_; else return false,_; end if;
  end if;
  q := f[1][1]^(f[1][2] div 2);
  M:=GModule(G);
  D:=Dual(M);
  DD:=ModToQ(D,q);
  bool, mat:= IsIsomorphic(M,DD);
    /* We now need to ensure that mat is actually the matrix of a/
     * unitary form, which can be achieved by multiplying it by a scalar
     */
  if bool then
    if mat ne Transpose(MatToQ(mat, q)) then
      c := Representative(
          { <i,j>: i in [1..d], j in [1..d] | mat[i][j] ne F!0 } );
      if mat[c[2]][c[1]] ne F!0 then
        x := mat[c[1]][c[2]]*mat[c[2]][c[1]]^-q;
        isp, z := IsPower(x,q-1);
      end if;
      if mat[c[2]][c[1]] eq F!0 or not isp then
        if not IsAbsolutelyIrreducible(G) then
          error "UnitaryForm failed - group is not absolutely irreducible";
          //return "unknown", _, _;
        end if;
        error "IsPower failed in UnitaryForm";
      end if;
      scal:= DiagonalMatrix([z : i in [1..d]]);
      mat *:= scal;
    end if;
    for i in [1..d] do if mat[1][i] ne 0 then
        x := mat[1][i];
        if x eq x^q then mat *:= x^-1; end if;
        break;
    end if; end for;
    if mat ne Transpose(MatToQ(mat, q)) and not IsAbsolutelyIrreducible(G) then
       error "UnitaryForm failed - group is not absolutely irreducible";
    end if;
    assert mat eq Transpose(MatToQ(mat, q));
    if Scalars then return bool, mat, [mat[1][1]^0 : i in [1..Ngens(G)]];
    else return bool, mat;
    end if;
  end if;
  if not Scalars then return false,  _; end if;

  bool, D := ApproximateDerivedGroup(G);
  if not bool then
   "UnitaryForm failed - derived group may not be absolutely irreducible";
    //return "unknown",_,_;
  end if;
  bool, mat := $$(D);
  if bool then
    scals := [];
    z := 0*mat[1][1];
    d := Dimension(G);
    for g in [G.i: i in [1..Ngens(G)]] do
      tmat := g*mat*Transpose(MatToQ(g, q));
      s := z;
      for i in [1..d] do for j in [i..d] do
        if tmat[i][j] ne z then
          if mat[i][j] eq z then return false, _, _; end if;
          if s eq z then s := tmat[i][j]*mat[i][j]^-1;
          elif s ne tmat[i][j]*mat[i][j]^-1 then return false, _, _;
          end if;
        elif mat[i][j] ne z then return false, _, _;
        end if;
      end for; end for;
      Append(~scals,s);
    end for;
    return true, mat, scals;
  end if;
  return false, _, _;
end intrinsic;

intrinsic ClassicalForms(G::GrpMat : Scalars:=false ) -> Rec
{Assuming that G acts absolutely irreducibly, try to find a classical form
which is G-invariant (modulo scalars if Scalars is true) or prove that no
such form exists.}
  local bool, form, scals, scalsq, type, typeq;
  if not IsIrreducible(G) then
   error "ClassicalForms: G must be irreducible";
  end if;

  ans := rec<recformat<bilinearForm, quadraticForm, sesquilinearForm,
                           scalars, formType, sign> | >;
  ans`formType := "linear";
  ans`bilinearForm := false;
  ans`quadraticForm := false;
  ans`sesquilinearForm := false;
  ans`scalars := false;

  if Scalars then
     bool, form, type, scals := SymmetricBilinearForm(G:Scalars:=true);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`bilinearForm := form;
       bool, form, type, scalsq := QuadraticForm(G:Scalars:=true);
       if bool cmpeq "unknown" or bool eq false then
         //should only happen in characteristic 2
         ans`formType := "symplectic";
         ans`scalars := scals;
         return ans;
       else
         ans`formType := type;
         if type eq "orthogonalplus" then signq := 1;
         elif type eq "orthogonalminus" then signq := -1;
         elif type eq "orthogonalcircle" then signq := 0;
         end if;
         ans`quadraticForm := form;
         ans`scalars := scals;
         ans`sign := signq;
         return ans;
       end if;
     end if;
     bool, form, scals := SymplecticForm(G:Scalars:=true);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`formType := "symplectic";
       ans`bilinearForm := form;
       ans`scalars := scals;
       return ans;
     end if;
     bool, form, scals := UnitaryForm(G:Scalars:=true);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`formType := "unitary";
       ans`sesquilinearForm := form;
       ans`scalars := scals;
       return ans;
     end if;
  else
     bool, form, type := SymmetricBilinearForm(G);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`bilinearForm := form;
       bool, form, typeq := QuadraticForm(G);
       if bool cmpeq "unknown" or bool eq false then
         //should only happen in characteristic 2
         ans`formType := "symplectic";
         ans`scalars := [Id(G)[1][1] : i in [1..Ngens(G)] ];
         return ans;
       else
         ans`formType := type;
         if type eq "orthogonalplus" then signq := 1;
         elif type eq "orthogonalminus" then signq := -1;
         elif type eq "orthogonalcircle" then signq := 0;
         end if;
         ans`quadraticForm := form;
         ans`scalars := [Id(G)[1][1] : i in [1..Ngens(G)] ];
         ans`sign := signq;
         return ans;
       end if;
     end if;
     bool, form := SymplecticForm(G);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`formType := "symplectic";
       ans`bilinearForm := form;
       ans`scalars := [Id(G)[1][1] : i in [1..Ngens(G)] ];
       return ans;
     end if;
     bool, form := UnitaryForm(G);
     if bool cmpeq "unknown" then
       ans`formType := "unknown";
     elif bool then
       ans`formType := "unitary";
       ans`sesquilinearForm := form;
       ans`scalars := [Id(G)[1][1] : i in [1..Ngens(G)] ];
       return ans;
     end if;
  end if;
  return ans;
end intrinsic;

intrinsic FormType(G::GrpMat : Scalars:=false ) -> MonStgElt
{Return the type of any classical form (mod scalars if Scalars is true)
 fixed by G.}
  local cf;
  cf := ClassicalForms(G: Scalars:=Scalars );
  if assigned cf`formType then
    return cf`formType;
  end if;
  return "unknown";
end intrinsic;

intrinsic SymmetricBilinearFormType(form::AlgMatElt : field:=0) -> MonStgElt
{Return the type ("orthogonalplus" or "orthogonalminus") of symmetric bilinear form in odd characteristic}
  if field cmpeq 0 then 
    field := BaseRing(form);
  else
    assert BaseRing(form) subset field;
    form := MatrixAlgebra(field,NumberOfRows(form))!form;
  end if; 
  if ClassicalForms_Signum(field, form) eq 1 then
    return "orthogonalplus";
  else return "orthogonalminus";
  end if;
end intrinsic;

intrinsic QuadraticFormType(form::AlgMatElt : field:=0) -> MonStgElt
{Return the type ("orthogonalplus" or "orthogonalminus") of quadratic form in even characteristic}
  if field cmpeq 0 then 
    field := BaseRing(form);
  else
    assert BaseRing(form) subset field;
    form := MatrixAlgebra(field,NumberOfRows(form))!form;
  end if; 
  if ClassicalForms_Signum2(field, form+Transpose(form), form) eq 1 then
    return "orthogonalplus";
  else return "orthogonalminus";
  end if;
end intrinsic;

intrinsic InternalGetOrthogonalForm(G::GrpMat) -> AlgMatElt
{Internal}
    /* SH, Oct 07 */

    /* this intrinsic just calls ClassicalForms and checks the result */
    /* used from within the C-code membership test                    */
    /* it is only called with groups generated by one of GO*, SO*, Omega*, (CO*) intrinsics */

    /* if it wasnt for the CO*, which are not yet implemented, we could use OrthogonalForm intrinsic */

    r := ClassicalForms(G:Scalars);
    assert Type(r`bilinearForm) ne BoolElt;
    assert r`formType[1..4] eq "orth";
    return Matrix(r`bilinearForm);

end intrinsic;

intrinsic InternalOrthTestQuadForm(x::GrpMatElt) -> BoolElt
{Internal}
    /* billu, Nov 08 */
    
    G := Parent(x);
    r := ClassicalForms(G:Scalars);
    assert Type(r`bilinearForm) ne BoolElt;
    assert r`formType[1..4] eq "orth";
    Q := r`quadraticForm;
    assert Type(Q) ne BoolElt;
    T := x*Q*Transpose(x) - Q;
    return forall{i:i in [1..Degree(G)] | IsZero(T[i,i])};

end intrinsic;

