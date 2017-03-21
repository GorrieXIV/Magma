freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

// 18/11/04	Nicole Sutherland
//		Use extended types in signatures and more robust error checking

////////////////////////////////////////////////////////////////////////
//                                                                    
//  This computes the multi dimensional theta function as defined in Mumford's 
//  Tata lectures.
//
//  Paul van Wamelen (August 2002)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//   Theta (with two signatures)
//     
//     
////////////////////////////////////////////////////////////////////////

// Tests if tau is in Siegel upper-half space
function tsttau(tau)
  g := NumberOfRows(tau);
  dum := ElementToSequence(tau - Transpose(tau));
  dum := Max([Abs(d) : d in dum]);
  if dum gt 10^-5 then
    return false;
  end if;
  Itau := Matrix(ComplexField(16),g,g,[Im(t) : t in ElementToSequence(tau)]);
  eig := Eigenvalues(Itau);
  e := Min([Re(e[1]) : e in eig]);
  return e gt 0;
end function;

// char should be a (2g)x1 matrix: the characteristic
// z    should be a gx1 matrix: the argument in C^g
// tau  should be an element of g-dimensional Siegel upper half space 
//      (symmetric gxg complex matrix with positive definite imaginary part)
// All entries of char and z should be coercible into the BaseRing of tau 
// which should be some fixed precision complex field.
intrinsic Theta(char::Mtrx,z::Mtrx,tau::Mtrx[FldCom]) -> FldComElt
{ Computes the multidimensional theta function with characteristic char (a (2g)x1 matrix) at z (a gx1 matrix) and tau (a symmetric gxg matrix with positive definite imaginary part).}
  C := BaseRing(tau);
  //require Type(C) eq FldCom:
    //"BaseRing of third argument must be a fixed precision complex field.";
  require tsttau(tau):
    "The third argument should be a symmetric complex matrix with positive definite imaginary part.";
  g := NumberOfRows(tau);
  require NumberOfRows(char) eq 2*g:
    "The first argument must have 2g rows.";
  require NumberOfColumns(char) eq 1:
    "The first argument must have 1 column.";
  require NumberOfRows(z) eq g:
    "The second argument must have g rows.";
  require NumberOfColumns(z) eq 1:
    "The second argument must have 1 column.";
  require IsCoercible(KMatrixSpace(C, 2*g, 1), char):
    "The first argument must be coercible into the BaseRing of the third argument.";
  require IsCoercible(KMatrixSpace(C, g, 1), z):
    "The second argument must be coercible into the BaseRing of the third argument.";
  char := Matrix(C,char);
  z := Matrix(C,z);
  return InternalTheta(char,z,tau);
end intrinsic;

// This checks for and caches theta nulls at half integer characteristics
intrinsic Theta(char::Mtrx,z::Mtrx,A::AnHcJac) -> FldComElt
{ Computes the multidimensional theta function with characteristic char (a (2g)x1 matrix) corresponding to the analytic Jacobian given by A at z (a gx1 matrix).}
  tau := SmallPeriodMatrix(A);
  C := BaseRing(tau);
  require Type(C) eq FldCom:
    "BaseRing of third argument must be a fixed precision complex field.";
  g := NumberOfRows(tau);
  require NumberOfRows(char) eq 2*g:
    "The first argument must have 2g rows.";
  require NumberOfColumns(char) eq 1:
    "The first argument must have 1 column.";
  require NumberOfRows(z) eq g:
    "The second argument must have g rows.";
  require NumberOfColumns(z) eq 1:
    "The second argument must have 1 column.";
  require IsCoercible(KMatrixSpace(C, 2*g, 1), char):
    "The first argument must be coercible into the BaseRing of the third argument.";
  require IsCoercible(KMatrixSpace(C, g, 1), z):
    "The second argument must be coercible into the BaseRing of the third argument.";

  z := Matrix(C,z);
  if z eq Matrix(C,g,1,[]) and IsCoercible(RMatrixSpace(IntegerRing(),4,1),2*char) then
    Echar := Matrix(RationalField(),Matrix(IntegerRing(),2*char))/2;
    ind := Index(A`ThetaNullCharacteristics,Echar);
    if ind gt 0 then
      return A`ThetaNullValues[ind];
    else
      Append(~A`ThetaNullCharacteristics,Echar);
      char := Matrix(C,char);
      ans := InternalTheta(char,z,tau);
      Append(~A`ThetaNullValues,ans);
      return ans;
    end if;
  else
    char := Matrix(C,char);
    return InternalTheta(char,z,tau);
  end if;
end intrinsic;


