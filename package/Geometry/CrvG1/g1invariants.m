freeze;

/////////////////////////////////////////////////////
//                                                 //
//     INVARIANT THEORY FOR GENUS ONE CURVES       //
//              "g1invariants.m"                   //
//                                                 //
//                T. A. Fisher                     //
//                                                 //
//           Version: 13th April 2006              //
//                                                 //
/////////////////////////////////////////////////////


/*****************

     CHANGE LOG 
               
              **** Please record all changes here ****
                                --- Thanks! Steve
  
  May 2006 (pre-release), Steve:
     * Cosmetic changes, too numerous to mention
  Aug 2006, for V2.13-4
     * Laboriously change everything to the new Hackobj type 
     * IsGenusOneModel(model)  now returns bool, model
  November 2006, Tom:
     * Added version of GenusOneModel taking arguments CoeffRing,n,seq 
     * Repaired nCovering for n = 4. (The function returns C,E,pi where
          pi is map from C to E. Previously another copy of C got used.)
     * Extended MultiplyTransformations to treat cross terms.
     * Modified RandomTransformation to give output over Q (not Z).
     * Added new intrinsic : InverseTransformation
     * Fixed a bug in ModelToString
     * Caching bug in CoveringCovariants fixed when ComputeY is false.

  January 2007, Tom
     * ApplyTransformation (for n=5) changed so as not to complain 
       for floating point examples.
     * Corrected sign error in HyperellipticCurve for binary quartics 
       without cross terms.

  July 2008 
     * Copy in bug fix from Tom in ApplyTransformation 

  March 2010, Tom
     *  SL4Covariants now an intrinsic
     *  CoveringMap added (variant of nCovering)
     *  Version of GenusOneModel that takes a degree 5 curve as 
                input now clears denominators (if over Q)

  April 2010, Tom
     *  Hessian for degree 2 models with cross terms now completes
           the square, rather than gives an error message.
     *  Added new function "TransformationToMap"
     *  Made changes for new TransG1 type
     *  GenusOneModel(C::Crv) in case n = 2 now returns model 
           without cross terms if the cross terms are zero.
     *  CompleteTheSquare returns transformation
     *  New intrinsics : RemoveCrossTerms, AddCrossTerms
     *  Correction to RandomGLnZ
     *  GenusOneModel(n,string) now returns a model over Q (not Z)
     *  Genus one models now have vector space operations + and *
            (this is convenient for visibility)
 

                                         *************/ 

// This file contains intrinsics :-  
//
//   RandomSLnZ(n,k,l)
//   RandomGLnZ(n,k,l)
//   IsGenusOneModel(model)  now returns bool, model
//   ModelParent(n)
//   GenusOneModel(n,seq)
//   GenusOneModel(n,string)
//   GenusOneModel(mats)
//   GenusOneModel(phi)  (where phi is a 5 by 5 matrix)
//   GenusOneModel(eqn)
//   GenusOneModel(eqns)  (intersection of quads)
//   GenusOneModel(curve)
//   GenusOneModel(n,E)
//   Eltseq(model) 
//   ModelToString(model) 
//   GenericModel(n)
//   RandomModel(n)
//   Degree(model)
//   BaseRing(model)
//   PolynomialRing(model)
//   Equations(model)
//   Matrix(model)
//   Curve(model)
//   ChangeRing(model,B)
//   CompleteTheSquare(model)
//   ModelToMatrices(model)
//   IsTransformation(n,g)
//   ScalingFactor(n,g)
//   RandomTransformation(n)
//   MultiplyTransformations(g1,g2) 
//   ApplyTransformation(g,model)
//   *(g,model)
//   HesseModel(n,ab)
//   DiagonalModel(n,coeffs)
//   SL4Invariants(model)
//   DoubleSpaceQuartic(model)
//   DoubleGenusOneModel(model)
//   FourToTwoCovering(model)
//   aInvariants(model)
//   bInvariants(model)
//   cInvariants(model)
//   Invariants(model)
//   Discriminant(model)
//   Jacobian(model)
//   Hessian(model)
//   CoveringCovariants(model)
//   nCovering(model)
//   Contravariants(model)
//   HesseCovariants(model,r)

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
EQ := ExactQuotient;
Deriv := Derivative;
Coeffs := func<poly,d|[MC(poly,mon):mon in mons]
   where mons is MD(R,d) where R is Parent(poly)>;
MultiFact := func<mon|&*[Factorial(Degree(mon,i)):i in [1..n]]
   where n is Rank(R) where R is Parent(mon)>;
CanDivideBy := func<x|not(x eq 0 or IsZeroDivisor(x))>;
myEQ := func<f,d|&+[EQ(Coefficients(f)[i],d)*Monomials(f)[i] 
   : i in [1..#Terms(f)]]>;

/*
intrinsic Invariants(E::CrvEll) -> RngElt,RngElt,RngElt
{The invariants c4, c6 and Delta of the elliptic curve E.}
  c4,c6 := Explode(cInvariants(E));
  Delta := Discriminant(E);
  return c4,c6,Delta;
end intrinsic;
*/

////////////////////////////////////////////////////////
//                                                    //
//              Basic matrix functions                //
//                                                    //
////////////////////////////////////////////////////////

function MatDelete(mat,d)
   n := Nrows(mat);
   seq := Exclude([1..n],d);
   return Matrix(BaseRing(mat),n-1,n-1,[mat[i,j]: i,j in seq]);
end function;

function Pfaffian(mat)
   n := Nrows(mat);
   if n eq 0 then return 1; end if;
   if n eq 1 then return 0; end if;
   mat1 := MatDelete(mat,1);
   return &+[(-1)^i*mat[1,i]*Pfaffian(MatDelete(mat1,i-1)):i in [2..n]];
end function;

function PfSubmax(mat)
   n := Nrows(mat);
   return [(-1)^i*Pfaffian(MatDelete(mat,i)):i in [1..n]];
end function;

function QuadricToMatrix(q)
  R := Parent(q);
  B := BaseRing(R);
  n := Rank(R);
  seq := [(i eq j select 2 else 1)*MC(q,R.i*R.j):i,j in [1..n]];
  return Matrix(B,n,n,seq);
end function;

function MatrixToQuadric(mat:
    CoeffRing := BaseRing(mat),
    PolyRing := PolynomialRing(CoeffRing,Nrows(mat)))
  assert CanDivideBy(CoeffRing!2);
  R := PolyRing;  
  n := Rank(R);
  quadric := &+[mat[i,j]*R.i*R.j: i,j in [1..n]| i lt j]
           + &+[ExactQuotient(mat[i,i],2)*R.i^2: i in [1..n]];
  return quadric;
end function;

function RandomShear(n,S)
  M := IdentityMatrix(Integers(), n);
  i := Random([1..n]);
  j := Random(Exclude([1..n],i));
  M[i,j] := Random(S);
  return M;
end function;

// called by RandomTransformation
function RandomGLnQ(n,k,l) 
  S := [1 .. k] cat [-1 .. -k by -1];
  M := IdentityMatrix(Integers(), n);
  for i := 1 to l do
    M *:= RandomShear(n,S);
    j := Random([1..n]);
    M[j] := Random(S)*M[j];
  end for;
  return M;
end function;

intrinsic RandomSLnZ(n::RngIntElt,k::RngIntElt,l::RngIntElt) -> AlgMatElt
{A random element in SL(n,Z), obtained as the product of l matrices each with
a single nondiagonal entry of absolute value at most k}
  M := IdentityMatrix(Integers(), n);
  for i := 1 to l do 
    M *:= RandomShear(n,[-k..k]);
  end for;
  return M;
end intrinsic;

intrinsic RandomGLnZ(n::RngIntElt,k::RngIntElt,l::RngIntElt) -> AlgMatElt
{A random element in GL(n,Z), obtained as the product of l matrices each with
a single nondiagonal entry of absolute value at most k}
  M := IdentityMatrix(Integers(), n);
  for i := 1 to l do 
    M *:= RandomShear(n,[-k..k]);
    j := Random([1..n]);
    M[j] := Random([1,-1])*M[j];
  end for;
  return M;
end intrinsic;

////////////////////////////////////////////////////////
//                                                    //
//              Genus one models                      //
//                                                    //
////////////////////////////////////////////////////////

intrinsic IsGenusOneModel(f::RngMPolElt) -> BoolElt,ModelG1
{Determines whether f specifies a genus one model of degree n = 2 or n = 3; 
if true the model is also returned. A genus one model of degree 2 is a binary quartic. 
A genus one model of degree 3 is a ternary cubic. 
A genus one model of degree 2 may also be given in the form y^2 + f(x,z) y - g(x,z) 
where f and g homogenous of degrees 2 and 4, and the variables x, z, y are assigned degrees 1, 1, 2.}
  if not IsHomogeneous(f) then return false,_; end if;
  R := Parent(f);
  flag := false;
  case VariableWeights(R) :
    when [1,1] :
      flag := f eq 0 or TotalDegree(f) eq 4;
      n := 2;
    when [1,1,2] :
      flag := MonomialCoefficient(f,R.3^2) eq 1 and WeightedDegree(f) eq 4;
      n := 2;
    when [1,2,1] :
      flag := MonomialCoefficient(f,R.2^2) eq 1 and WeightedDegree(f) eq 4;
      n := 2;
      // switch y and z
      RR := PolynomialRing(BaseRing(R),[1,1,2]); 
      f := Evaluate(f, [RR.1,RR.3,RR.2]);
    when [1,1,1] :
      flag := f eq 0 or TotalDegree(f) eq 3;
      n := 3;
  end case;
  if flag then 
    model := New(ModelG1);
    model`Degree := n;
    model`Equation := f;
    return true,model;
  else
    return false,_;
  end if;
end intrinsic;

intrinsic IsGenusOneModel(f::RngUPolElt) -> BoolElt,ModelG1
{"} //"
  if Degree(f) ne 4 then return false,_; end if;
  R := BaseRing(f);
  _<X,Z> := PolynomialRing(R,2);
  c := Coefficients(f);
  ff := c[1]*Z^4 + c[2]*X*Z^3 + c[3]*X^2*Z^2 + c[4]*X^3*Z + c[5]*X^4;
  return IsGenusOneModel(ff);
end intrinsic;

intrinsic IsGenusOneModel(phi::SeqEnum[RngMPolElt]) -> BoolElt,ModelG1
{Determines whether phi defines a genus one model of degree 4; if true the model is also returned. 
The input should be a sequence of 2 quadratic forms in 4 variables.}
  if #phi eq 1 then return IsGenusOneModel(phi[1]); end if;
  R := Universe(phi);
  if Rank(R) ne 4 then return false,_; end if;
  if VariableWeights(R) ne [1: i in [1..4]] 
    or not forall{ f : f in Eltseq(phi) | f eq 0 or TotalDegree(f) eq 2}
    or not forall{ f : f in Eltseq(phi) | IsHomogeneous(f)}
      then return false,_; 
  end if;
  model := New(ModelG1);
  model`Degree := 4;
  model`Equations := phi;
  return true, model;
end intrinsic;

intrinsic IsGenusOneModel(phi::Mtrx) -> BoolElt,ModelG1
{Determines whether phi defines a genus one model of degree 5; if true the model is also returned. 
The input should be a 5 by 5 alternating matrix whose entries are linear forms in 5 variables.}
  R := BaseRing(phi);
  if Rank(R) ne 5 then return false,_; end if;
  if Nrows(phi) ne 5 or Ncols(phi) ne 5 or VariableWeights(R) ne [1: i in [1..5]] 
    or not forall{ f : f in Eltseq(phi) | f eq 0 or TotalDegree(f) eq 1}
    or not forall{ f : f in Eltseq(phi) | IsHomogeneous(f)}
    or not forall{ i : i in [1..5] | phi[i,i] eq 0} 
    or not (Transpose(phi) eq -phi)
      then return false,_; 
  end if;
  model := New(ModelG1);
  model`Degree := 5;
  model`DefiningMatrix := phi;
  return true, model;
end intrinsic;

intrinsic Degree(model::ModelG1) -> RngIntElt
{The degree of the given genus one model}
  return model`Degree;
end intrinsic;

intrinsic BaseRing(model::ModelG1) -> Rng
{The coefficient ring of the given genus one model}
  return BaseRing(PolynomialRing(model));
end intrinsic;

intrinsic PolynomialRing(model::ModelG1) -> RngMPol
{The polynomial ring used to define the given genus one model.}
  n := model`Degree;
  if n in {2,3} then return Parent(model`Equation);
  elif n eq 4 then return Universe(model`Equations);
  else return BaseRing(model`DefiningMatrix); 
  end if;
end intrinsic;

intrinsic ModelParent(n::RngIntElt:
  CrossTerms := false,
  CoeffRing := Rationals(),
  PolyRing := PolynomialRing(CoeffRing,
    n eq 2 and CrossTerms select [1,1,2] else n))
    -> Any
{Obsolete}
  require n in [2..5] : "Degree must be in range [2..5]"; 
  if n in [2..3] then return PolyRing; 
  elif n eq 4 then return Parent([ PolyRing| ]);
  else return RMatrixSpace(PolyRing,5,5);
  end if;
end intrinsic;

intrinsic GenusOneModel(seq::SeqEnum[RngElt]: CoeffRing := Universe(seq), PolyRing := 0,  Parent := 0) 
   -> ModelG1
{Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5.}
  require #seq in{5,8,10,20,50} : "The given sequence has the wrong length to define a genus one model";
  n := case<#seq|5:2,8:2,10:3,20:4,50:5,default:0>;
  if PolyRing cmpeq 0 then PolyRing := PolynomialRing(CoeffRing, n eq 2 and #seq eq 8 select [1,1,2] else n); end if;
  if Parent cmpeq 0 then Parent := ModelParent(n:PolyRing := PolyRing); end if;
  return GenusOneModel(n, seq : CoeffRing :=CoeffRing, PolyRing := PolyRing, Parent :=Parent );
end intrinsic;

intrinsic GenusOneModel(CoeffRing::Rng,n::RngIntElt,seq::SeqEnum[RngElt]: PolyRing := 0, Parent := 0) -> ModelG1
{Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5.}
  if PolyRing cmpeq 0 then PolyRing := PolynomialRing(CoeffRing, n eq 2 and #seq eq 8 select [1,1,2] else n); end if;
  if Parent cmpeq 0 then Parent := ModelParent(n:PolyRing := PolyRing); end if;
  return GenusOneModel(n, ChangeUniverse(seq,CoeffRing): PolyRing := PolyRing, Parent := Parent );
end intrinsic;

intrinsic GenusOneModel(n::RngIntElt,seq::SeqEnum[RngElt]:
  CoeffRing := Universe(seq),
  PolyRing := PolynomialRing(CoeffRing,
    n eq 2 and #seq eq 8 select [1,1,2] else n),
  Parent := ModelParent(n:PolyRing := PolyRing)) 
  -> ModelG1
{Converts a sequence of coefficients to a genus one model of degree n, where n = 2,3,4 or 5.}
  require n in [2..5] : "Degree must be in range [2..5]"; 

  seq0 := seq;
  N := case<n|2:5,3:10,4:20,5:50,default:0>;
  wts := [1 : i in [1..n]];
  if n eq 2 then 
    require #seq in {5,8} : "Sequence must have length 5 or 8";
    if #seq eq 8 then wts := [1,1,2]; end if;
  else 
    require #seq eq N : "Sequence must have length",N;
  end if;
  require VariableWeights(PolyRing) eq wts 
     : "Polynomial ring should have weights",wts;
  MP := Parent;
  model := New(ModelG1);
  model`Degree := n;
  case n :
    when 2:
      if #seq eq 5 then 
        R := MP;
        x := R.1;
        z := R.2;
        basis := [x^4,x^3*z,x^2*z^2,x*z^3,z^4];
      else
        R := MP;
        x := R.1;
        z := R.2;
        y := R.3;
        basis := [y^2,x^2*y,x*z*y,z^2*y,-x^4,-x^3*z,-x^2*z^2,-x*z^3,-z^4];
        seq := [1] cat seq;
      end if;
      model`Equation := &+[MP|seq[i]*basis[i]:i in [1..#seq]];
    when 3:
      R := MP;
      x := R.1;
      y := R.2;
      z := R.3;
      basis := [x^3,y^3,z^3,x^2*y,x^2*z,y^2*x,y^2*z,z^2*x,z^2*y,x*y*z];
      model`Equation := &+[MP|seq[i]*basis[i]:i in [1..#seq]];
    when 4:
      R := Universe(MP![]);
      mons := [R.i*R.j :i,j in [1..4] | i le j];
      basis := [MP![m,0]: m in mons] cat [MP![0,m]: m in mons];
      model`Equations := [ &+[seq[i]*basis[i][1]:i in [1..#seq]],
                           &+[seq[i]*basis[i][2]:i in [1..#seq]] ];
    when 5:
      R := BaseRing(MP);
      mons := [R.i: i in [1..5]];
      ee := [MP!Matrix(R,5,5,[<i,j,1>,<j,i,-1>]): i,j in [1..5] | i lt j];
      basis := [m*e:m in mons,e in ee];  
      model`DefiningMatrix := &+[MP|seq[i]*basis[i]:i in [1..#seq]];
  end case;
  assert #seq eq #basis;

  model`Eltseq := seq0;
  return model;
end intrinsic;

intrinsic ModelToSequence(model::ModelG1) -> SeqEnum[RngElt]
{The sequence of coefficients determining the given model.}
  return Eltseq(model);
end intrinsic;

intrinsic Eltseq(model::ModelG1) -> SeqEnum[RngElt]
{"} // "
  if assigned model`Eltseq then
    return model`Eltseq;
  end if;

  n := model`Degree;
  case n:
    when 2:
      f := model`Equation;
      if VariableWeights(Parent(f)) eq [1,1] then 
        R := Parent(f);
        x := R.1;
        z := R.2;
        mons := [x^4,x^3*z,x^2*z^2,x*z^3,z^4];
        seq := [MC(f,mon): mon in mons];
      else
        R := Parent(f);
        x := R.1;
        z := R.2;
        y := R.3;
        mons := [x^2*y,x*z*y,z^2*y,x^4,x^3*z,x^2*z^2,x*z^3,z^4];
        signs := [1,1,1,-1,-1,-1,-1,-1];
        seq := [signs[i]*MC(f,mons[i]): i in [1..8]];
      end if;
    when 3:
      f := model`Equation;
      R := Parent(f);
      x := R.1;
      y := R.2;
      z := R.3;
      mons := [x^3,y^3,z^3,x^2*y,x^2*z,y^2*x,y^2*z,z^2*x,z^2*y,x*y*z];
      seq := [MC(f,mon): mon in mons];
    when 4:
      phi := model`Equations;
      R := Universe(phi);
      mons := [R.i*R.j:i,j in [1..4]|i le j];
      seq := [MC(q,m): m in mons,q in phi];
    when 5:
      phi := model`DefiningMatrix;
      R := BaseRing(phi);
      seq := [MC(phi[i,j],R.k): i,j,k in [1..5]| i lt j];
  end case;

  model`Eltseq := seq;
  return seq;
end intrinsic;

intrinsic GenusOneModel(n::RngIntElt,str::MonStgElt) -> ModelG1
{Converts a string of coefficients to a genus one model of degree n, 
where n = 2,3,4 or 5. } 
  ss := Split(str," ");
  seq := [StringToInteger(i): i in ss];
  return GenusOneModel(Rationals(),n,seq);
end intrinsic;

intrinsic ModelToString(model::ModelG1) -> MonStgElt
{Converts a genus one model to a string of coefficients. }
  seq := Eltseq(model);
  require &and[IsIntegral(cc) : cc in seq] : "Coefficients must be integers";
  return &cat[IntegerToString(Integers()!x) cat " ": x in seq];
end intrinsic;

NumberOfParameters := func<n|case<n|2:5,3:10,4:20,5:50,default:0>>;

intrinsic GenericModel(n::RngIntElt:
  CrossTerms := false,
  BaseRing := Rationals(),
  CoeffRing := PolynomialRing(BaseRing,
    n eq 2 and CrossTerms select 8 else NumberOfParameters(n)))
  -> ModelG1
{The generic genus one model of degree n, where n is 2,3,4 or 5.}
  require n in [2..5] : "Degree must be in range [2..5]";
  N := n eq 2 and CrossTerms select 8 else NumberOfParameters(n);
  require Rank(CoeffRing) eq N : "Coefficient ring must have rank",N;
  case N:
    when 5  : B<a,b,c,d,e>:=CoeffRing;
    when 8  : B<a0,a1,a2,a,b,c,d,e>:=CoeffRing;
    when 10 : B<a,b,c,a2,a3,b1,b3,c1,c2,m>:=CoeffRing;
    when 20 : B<a11,a12,a13,a14,a22,a23,a24,a33,a34,a44,
                b11,b12,b13,b14,b22,b23,b24,b33,b34,b44>:=CoeffRing;
    when 50 : B<[a]>:=CoeffRing;
  end case;
  seq:=[B.i: i in [1..N]];  
  return GenusOneModel(n,seq);
end intrinsic;

intrinsic RandomGenusOneModel(n::RngIntElt:
  Size := 100,
  CrossTerms := false,
  CoeffSet := n eq 5 select {-2+Size div 100 .. 2+Size div 100 } else {-Size..Size},
  CoeffRing := FieldOfFractions(Universe(CoeffSet)),
  PolyRing := PolynomialRing(CoeffRing,
    n eq 2 and CrossTerms select [1,1,2] else n),
  Parent := ModelParent(n:PolyRing := PolyRing),
  RequireNonsingular := false) 
   -> ModelG1
{A random genus one model of degree n, where n = 2,3,4 or 5.}
  return RandomModel(n : Size:=Size, CrossTerms:=CrossTerms, CoeffSet:=CoeffSet, CoeffRing:=CoeffRing,
                         PolyRing:=PolyRing, Parent:=Parent, RequireNonsingular:=RequireNonsingular);
end intrinsic;

intrinsic RandomModel(n::RngIntElt:
  Size := 100,
  CrossTerms := false,
  CoeffSet := n eq 5 select {-1+Size div 100 .. 1+Size div 100 } else {-Size..Size},
  CoeffRing := FieldOfFractions(Universe(CoeffSet)),
  PolyRing := PolynomialRing(CoeffRing,
    n eq 2 and CrossTerms select [1,1,2] else n),
  Parent := ModelParent(n:PolyRing := PolyRing),
  RequireNonsingular := false) 
   -> ModelG1
{Same as RandomGenusOneModel.}
  require n in [2..5] : "Degree must be in range [2..5]";
  N := n eq 2 and CrossTerms select 8 else NumberOfParameters(n);
  ctr := 0;
  repeat 
    ctr+:=1;
    seq := [CoeffRing|Random(CoeffSet): i in [1..N]];
    phi := GenusOneModel(n,seq:Parent := Parent);
  until not RequireNonsingular or Discriminant(phi) ne 0 or ctr gt 100;
  require ctr le 100:"Failed to find a non-singular model";
  return phi;
end intrinsic;

intrinsic ChangeRing(model::ModelG1,B::Rng) -> ModelG1
{The genus one model obtained by coercing the coefficients of the given model into B.}
  n := model`Degree;
  seq := Eltseq(model);
  return GenusOneModel(n, ChangeUniverse(seq, B));
end intrinsic;

intrinsic CompleteTheSquare(model::ModelG1:Scalar := 2) -> ModelG1, TransG1
{Given a genus one model y^2 + P(x,z)y = Q(x,z) returns the binary quartic P(x,z)^2 + 4 Q(x,z) obtained by completing the square. If the input is a binary quartic then this is immediately returned. The second returned argument is a transformation tr such that tr*oldmodel = newmodel.}
  require model`Degree eq 2: "Input must be a genus one model of degree 2";
  f := model`Equation;
  R := BaseRing(model);
  Id := IdentityMatrix;
  if VariableWeights(Parent(f)) eq [1,1] then
    _,tr := IsTransformation(2,<1,Id(R,2)>);
    return model,tr; 
  end if;
  RR := PolynomialRing(R);
  x := RR.1;
  a0,a1,a2,a,b,c,d,e := Explode(Eltseq(model));
  P := a0*x^2 + a1*x + a2;
  Q := a*x^4 + b*x^3 + c*x^2 + d*x + e;
  mu := Scalar;
  F := mu^2*((1/4)*P^2 + Q);
  seq := [Coefficient(F,i): i in [4,3,2,1,0]];
  model := GenusOneModel(2,seq:CoeffRing:=R);
  _,tr := IsTransformation(2,<mu,[-a0/2,-a1/2,-a2/2],Id(R,2)>);
  return model,tr;
end intrinsic;

intrinsic RemoveCrossTerms(model::ModelG1) -> ModelG1, TransG1
{Given a genus one model y^2 + P(x,z)y = Q(x,z) returns the binary quartic (1/4)*P(x,z)^2 + Q(x,z) obtained by completing the square. If the input is a binary quartic then this is immediately returned. The second returned argument is a transformation tr such that tr*oldmodel = newmodel.}
  return CompleteTheSquare(model:Scalar := 1);
end intrinsic;

intrinsic AddCrossTerms(model::ModelG1) -> ModelG1
{Converts a genus one model of degree 2 from the format without cross terms to the format with cross terms.}
  require model`Degree eq 2: "Input must be a genus one model of degree 2";
  seq := Eltseq(model);
  if #seq eq 8 then return model; end if;
  R := BaseRing(model);
  return GenusOneModel(2,[0,0,0] cat seq:CoeffRing:=R);
end intrinsic;

intrinsic Matrices(model::ModelG1) -> SeqEnum
{Converts a genus one model of degree 4 to a pair of 4 by 4 symmetric matrices. }
  require model`Degree eq 4: "Input must be a genus one model of degree 4";
  return [ QuadricToMatrix(q): q in model`Equations ];
end intrinsic;

intrinsic GenusOneModel( mats::SeqEnum[AlgMatElt] :
  CoeffRing := BaseRing(Universe(mats)),
  PolyRing := PolynomialRing(CoeffRing,4) ) -> ModelG1
{Converts a pair of 4 by 4 symmetric matrices to a genus one model of degree 4. }
  R<x1,x2,x3,x4> := PolyRing;
  require CanDivideBy(R!2): "Unable to divide by 2";
  require &and[ Type(mm) eq AlgMatElt and NumberOfRows(mm) eq 4 : mm in mats ] :
     "The given sequence must contain a pair of 4x4 matrices";
  quads := [MatrixToQuadric(mat:PolyRing := R) : mat in mats];
  flag, model := IsGenusOneModel(quads);
  require flag : "Something went wrong constructing a genus one model from given matrices";
  return model;
end intrinsic;

intrinsic GenusOneModel( mat::Mtrx ) -> ModelG1
{The genus one model of degree 5 defined by the given 5 by 5 matrix.}
  require Nrows(mat) eq 5 and Ncols(mat) eq 5 : "The matrix should be 5 by 5";
  model := New(ModelG1);
  model`Degree := 5;
  model`DefiningMatrix := mat;
  return model;
end intrinsic;

function PfaffianMatrix(ff,r)
  n := #ff;
  R := Universe(ff);
  K := BaseRing(R);
  assert IsField(K);
  zero := RMatrixSpace(R,n,n)![0: i in [1..n^2]];
  if not exists(t){TotalDegree(f):f in ff| f ne 0} then 
    return zero;
  end if;
  assert forall{f: f in ff |f eq 0 or IsHomogeneous(f)};
  assert forall{f: f in ff |f eq 0 or TotalDegree(f) eq t};
  mons1 := MD(R,r); 
  mons2 := MD(R,t); 
  mons := MD(R,r+t); 
  mat := ZeroMatrix(K,#mons1*n,#mons);
  for i in [1..#mons1] do
    for j in [1..#mons2] do
      pos := Position(mons,mons1[i]*mons2[j]);
      for k in [1..n] do
        mat[n*(i-1)+k,pos] := MC(ff[k],mons2[j]);
      end for;
    end for;  
  end for;
  ns := NullspaceMatrix(mat);
  if Nrows(ns) ne n then return zero; end if;
  m1 := #mons1;
  Psi := Matrix(R,n,n,[&+[ns[j,n*(i-1)+k]*mons1[i]: i in [1..m1]]
    : j,k in [1..n]]);
  mat := ZeroMatrix(K,n^2,m1*n^2);  
  for i in [1..n] do
    for j in [1..n] do
    for k in [[i,j],[j,i]] do
      for r in [1..n] do
      for s in [1..m1] do
        mat[n*(k[1]-1)+r,m1*n*(i-1)+m1*(j-1)+s]+:= MC(Psi[r,k[2]],mons1[s]);
      end for; end for; 
    end for; end for;  
    if Rank(mat) ge n^2-1 then break; end if; 
  end for;  
  ns := NullspaceMatrix(mat);
  if Nrows(ns) ne 1 then return zero; end if;
  B := Matrix(n,n,[ns[1,n*(i-1)+j]:i,j in [1..n]]);
  Phi := B*Psi;
  return RMatrixSpace(R,n,n)!(B*Psi);
end function;

intrinsic Matrix(model::ModelG1) -> AlgMatElt
{The defining matrix of the given genus one model of degree five.}
  require model`Degree eq 5 : "The given genus one model should have degree 5";
  return model`DefiningMatrix;
end intrinsic;

intrinsic DefiningMatrix(model::ModelG1) -> AlgMatElt
{The defining matrix of the given genus one model of degree five.}
  return model`DefiningMatrix;
end intrinsic;

intrinsic Equation(model::ModelG1) -> SeqEnum[RngMPolElt]
{The defining equation of the given genus one model, which must have degree 2 or 3.}
  require model`Degree in {2,3} : "The given model must have degree 2 or 3.";
  return model`Equation;
end intrinsic;

intrinsic DefiningEquation(model::ModelG1) -> SeqEnum[RngMPolElt]
{The defining equation of the given genus one model, which must have degree 2 or 3.}
  require model`Degree in {2,3} : "The given model must have degree 2 or 3.";
  return model`Equation;
end intrinsic;

intrinsic DefiningEquations(model::ModelG1) -> SeqEnum[RngMPolElt]
{A sequence containing defining equations for the given genus one model. }
  require model`Degree ne 5 : 
    "A genus one model of degree 5 is not defined by equations. Use DefiningMatrix instead.";
   return Equations(model);
end intrinsic;

intrinsic Equations(model::ModelG1) -> SeqEnum[RngMPolElt]
{A sequence containing defining equations for the curve (or scheme)
associated to the given genus one model. }
  n := model`Degree;
  if n eq 2 then
    seq := Eltseq(model);
    if #seq eq 5 then    
      seq := [0,0,0] cat seq;
      model := GenusOneModel(2,seq:CoeffRing:=BaseRing(Parent(model`Equation)));
    end if;
  end if;
  if n in {2,3} then return [model`Equation];
  elif n eq 4 then return model`Equations;
  else return PfSubmax(model`DefiningMatrix); 
  end if;
end intrinsic;

intrinsic Curve(model::ModelG1) -> Crv
{The curve defined by the given genus one model.}
  eqns := Equations(model);
  R := Universe(eqns);
  return Curve(Proj(R),eqns);
end intrinsic;

intrinsic HyperellipticCurve(model::ModelG1) -> CrvHyp
{The hyperelliptic curve defined by a genus one model of degree 2.}
  require model`Degree eq 2 : "The given genus one model must be of degree 2.";
  f := model`Equation;
  P := PolynomialRing(BaseRing(Parent(f)));
  if Rank(Parent(f)) eq 2 then  // f = q(x,z)
     F := Evaluate(f, [P.1,1]);
     H := 0;
  else  // order of variables is x,z,y 
     F := -Evaluate(f, [P.1,1,0]);  // minus sign included
     H := Evaluate(Derivative(f,3), [P.1,1,0]);
  end if;
  return HyperellipticCurve(F,H); // minus sign removed
end intrinsic;

intrinsic QuadricIntersection(model::ModelG1) -> Crv
{The curve defined by a genus one model of degree 4.} 
  return Curve(model);
end intrinsic;

intrinsic GenusOneModel(f::RngUPolElt) -> ModelG1
{The genus one model of degree 2 specified by the given polynomial of degree 4}
  flag, model := IsGenusOneModel(f);
  require flag : "The given polynomial does not determine a genus one model";
  return model;
end intrinsic;

intrinsic GenusOneModel(f::RngMPolElt) -> ModelG1
{The genus one model of degree 2 or 3 specified by the given polynomial, 
which can be a binary quartic or a ternary cubic.}
  flag, model := IsGenusOneModel(f);
  require flag : "The given polynomial does not determine a genus one model";
  return model;
end intrinsic;

intrinsic GenusOneModel(eqns::[RngMPolElt]) -> ModelG1
{The genus one model of degree 4 or 5 determined by the given sequence of polynomials.}
  if Rank(Universe(eqns)) eq 5 then 
     flag, model := IsGenusOneModel(PfaffianMatrix(eqns,1)); 
  elif #eqns eq 1 then flag, model := IsGenusOneModel(eqns[1]);
  else flag, model := IsGenusOneModel(eqns);
  end if;
  require flag : "The given equations do not determine a genus one model";
  return model;
end intrinsic;

intrinsic GenusOneModel(C::Crv) -> ModelG1
{The genus one model determined by the defining equation of the given curve.}
  K := BaseRing(C);
  require IsField(K): "Curve must be defined over a field.";
  P := AmbientSpace(C);
  R := CoordinateRing(P);
  n := case<VariableWeights(R)|
     [1,2,1]     : 2,
     [1,1,2]     : 2,
     [1,1,1]     : 3,
     [1,1,1,1]   : 4,
     [1,1,1,1,1] : 5,
     default     : 0>;
  require n ne 0 : "The curve does not define a genus one model " *
                   "(the ambient space might be of the wrong kind).";
  eqns := (n in {2,3}) select [DefiningEquation(C)]
                        else  MinimalBasis(Ideal(C));
  case n:
    when 2: phi := R!eqns[1];
            w,ii := Max(VariableWeights(R));  assert w eq 2;
            phi *:= (1/MC(phi,R.ii^2));
    when 3: phi := R!eqns[1];
    when 4: phi := ChangeUniverse(eqns,R);
    when 5: phi := PfaffianMatrix(eqns,1);
            if K cmpeq Rationals() then 
	      coeffs := &cat[Coefficients(m): m in Eltseq(phi)];
              d := RationalGCD(coeffs);
              phi := (1/d)*phi;
            end if;
  end case;
  flag, model := IsGenusOneModel(phi);
  if n eq 2 then 
    seq := Eltseq(model);
    if #seq eq 8 and forall{i: i in [1..3]| seq[i] eq 0} then
      model := GenusOneModel(2,[seq[i]: i in [4..8]]);
    end if;
  end if;
  require flag : "Failed to obtain a genus one model.";
  if n ne 2 or ii ne 2 then 
    I := ideal<R|Equations(model)>;
    require I eq Ideal(C) : "Error while constructing a genus one model.";
  end if;
  return model;
end intrinsic;

intrinsic '+'(model1::ModelG1,model2::ModelG1) -> ModelG1
{The vector sum of two genus one models}
  n := Degree(model1);
  require Degree(model2) eq n: "Models must have same degree";
  seq1 := Eltseq(model1);
  seq2 := Eltseq(model2);
  require (n ne 2) or (#seq1 eq 5 and #seq2 eq 5) :
    "Models of degree 2 must not have cross terms";
  R := BaseRing(model1);
  seq := [seq1[i]+seq2[i]: i in [1..#seq1]];
  return GenusOneModel(R,n,seq);
end intrinsic;

intrinsic '*'(lambda::RngElt,model::ModelG1) -> ModelG1
{The given genus one model with coefficients multiplied through by lambda}
  n := Degree(model);
  seq := Eltseq(model);
  require n ne 2 or #seq eq 5 :
    "Model of degree 2 must not have cross terms";
  R := BaseRing(model);
  return GenusOneModel(R,n,[lambda*c : c in seq]);
end intrinsic;

intrinsic IsTransformation(n::RngIntElt,g::Tup) -> BoolElt,TransG1
{True iff g is a transformation of the space genus one models of degree n. If true the transformation is also returned.}
  require n in [2..5] : "Degree of model must be in range [2..5].";
  nterms := n eq 2 select {2,3} else {2};
  if #g notin nterms then return false,_; end if;
  case n:
    when 2:
      if #g eq 2 then 
        mu,B := Explode(g);
        flag := Nrows(B) eq 2;
      else 
        mu,r,B := Explode(g);
        flag := #r eq 3 and Nrows(B) eq 2;
      end if;
    when 3:
      mu,B := Explode(g);
      flag := Nrows(B) eq 3;
    when 4:
      A,B := Explode(g);
      flag := Nrows(A) eq 2 and Nrows(B) eq 4;
    when 5:
      A,B := Explode(g);
      flag := Nrows(A) eq 5 and Nrows(B) eq 5;
  end case;
  if not flag then return false,_; end if;
  trans := New(TransG1);
  trans`Degree := n;
  if n in {2,3} then
    trans`Scalar := mu;
  else
    trans`EquationMatrix := A;
  end if;
  if n eq 2 and #g eq 3 then
    trans`Shift := r;
  end if;
  trans`Matrix := B;
  return true,trans;
end intrinsic;

intrinsic Tuple(trans::TransG1) -> Tup
{The tuple defining the transformation}
  n := trans`Degree;
  B := trans`Matrix;
  if n eq 2 and assigned trans`Shift then 
    return <trans`Scalar,trans`Shift,B>;
  elif n in {2,3} then 
    return <trans`Scalar,B>;
  else
    return <trans`EquationMatrix,B>;
  end if;
end intrinsic;

intrinsic Determinant(trans::TransG1) -> RngElt
{The "determinant" of the given transformation of genus one models. The discriminant of a model is multiplied by the 12th power of this factor.}
  n := trans`Degree;
  case n :
    when 2 : mu := trans`Scalar;
    when 3 : mu := trans`Scalar;
    when 4 : mu := Determinant(trans`EquationMatrix);
    when 5 : mu := Determinant(trans`EquationMatrix)^2;
  end case;
  return mu*Determinant(trans`Matrix);
end intrinsic;

intrinsic ScalingFactor(trans::TransG1) -> RngElt
{The "determinant" of the given transformation of genus one models. The discriminant of a model is multiplied by the 12th power of this factor.}
  return Determinant(trans);
end intrinsic;

intrinsic ScalingFactor(n::RngIntElt,trans::TransG1) -> RngElt
{The "determinant" of the given transformation of genus one models (of degree n). The discriminant of a model is multiplied by the 12th power of this factor.}
  require trans`Degree eq n : "Transformation does not have degree",n;
  return Determinant(trans);
end intrinsic;

intrinsic RandomTransformation(n::RngIntElt: CrossTerms := false,Unimodular := false, Size := 5) -> TransG1
{A random transformation of the space of genus one models of degree n.}
  require n in [2..5] : "Degree of model must be in range [2..5].";
  require Size gt 0 : "Size must be a positive integer.";
  s := Size;
  multset := [Rationals()| i : i in [-s..s] | i ne 0];
  if n in [2..3] then  
    mu := Unimodular select Rationals()!1 else Random(multset);
  else
    m := n eq 4 select 2 else 5;
    A := Unimodular select RandomSLnZ(m,s,s) else RandomGLnQ(m,s,s);
    A := ChangeRing(A,Rationals());
  end if;
  if n eq 2 and CrossTerms then 
    r := [Rationals()| Random([-s..s]): i  in [1..3]]; 
  end if;
  B := Unimodular select RandomSLnZ(n,s,s) else RandomGLnQ(n,s,s);
  B := ChangeRing(B,Rationals());
  case n:
    when 2: g := CrossTerms select <mu,r,B> else <mu,B>;
    when 3: g := <mu,B>;
    when 4: g := <A,B>;
    when 5: g := <A,B>;
  end case;
  flag,trans := IsTransformation(n,g);
  assert flag;
  return trans;
end intrinsic;

intrinsic '*'(tr1::TransG1,tr2::TransG1) -> TransG1
{The composition tr1*tr2 of two transformations of genus one models.}
   return MultiplyTransformations(tr1, tr2);
end intrinsic;

intrinsic ComposeTransformations(tr1::TransG1,tr2::TransG1) -> TransG1
{The composition tr1*tr2 of two transformations of genus one models.}
   return MultiplyTransformations(tr1, tr2);
end intrinsic;

intrinsic MultiplyTransformations(tr1::TransG1,tr2::TransG1) -> TransG1
{The composition tr1*tr2 of two transformations of genus one models.}
  n := tr1`Degree;
  require tr2`Degree eq n : "Transformations should have the same degree";
  tr := New(TransG1);
  tr`Degree := n;
  if n in {2,3} then 
    tr`Scalar := (tr1`Scalar)*(tr2`Scalar);
  else
    tr`EquationMatrix := (tr1`EquationMatrix)*(tr2`EquationMatrix);
  end if;
  tr`Matrix := (tr1`Matrix)*(tr2`Matrix);
  if n eq 2 and (assigned tr1`Shift or assigned tr2`Shift) then 
    r := assigned tr1`Shift select tr1`Shift else [0,0,0];
    s := assigned tr2`Shift select tr2`Shift else [0,0,0];
    u := 1/(tr2`Scalar);
    r0,r1,r2 := Explode(r);
    s0,s1,s2 := Explode(s);
    a,b,c,d := Explode(Eltseq(tr1`Matrix));
    R0 := u*r0 + a^2*s0 + a*b*s1 + b^2*s2;
    R1 := u*r1 + 2*a*c*s0 + a*d*s1 + b*c*s1 + 2*b*d*s2;
    R2 := u*r2 + c^2*s0 + c*d*s1 + d^2*s2;
    tr`Shift := [R0,R1,R2];
  end if;
  return tr;
end intrinsic;

intrinsic Inverse(trans::TransG1) -> TransG1
{The inverse of a transformation of genus one models.}
  inv := New(TransG1);
  n := trans`Degree;
  inv`Degree := n;
  if n in {2,3} then 
    inv`Scalar := (trans`Scalar)^(-1);
  else
    inv`EquationMatrix := (trans`EquationMatrix)^(-1);
  end if;
  inv`Matrix := (trans`Matrix)^(-1);
  if assigned trans`Shift then 
    mu := trans`Scalar;
    r0,r1,r2 := Explode(trans`Shift);
    a,b,c,d := Explode(Eltseq(inv`Matrix));
    R0 := -mu*(a^2*r0 + a*b*r1 + b^2*r2);
    R1 := -mu*(2*a*c*r0 + a*d*r1 + b*c*r1 + 2*b*d*r2);
    R2 := -mu*(c^2*r0 + c*d*r1 + d^2*r2);
    inv`Shift := [R0,R1,R2];
  end if;
  return inv;
end intrinsic;

intrinsic InverseTransformation(trans::TransG1) -> TransG1
{The inverse of a transformation of genus one models.}
  return Inverse(trans);
end intrinsic;

intrinsic IdentityTransformation(n::RngIntElt,R::Rng:CrossTerms:=false) -> TransG1
{The identity transformation on genus one models of degree n, defined over R.}
  idtr := New(TransG1);
  idtr`Degree := n;
  if n in {2,3} then 
    idtr`Scalar := R!1;
    if n eq 2 and CrossTerms then 
      idtr`Shift := [R|0,0,0];
    end if;
  else
    m := n eq 4 select 2 else 5;
    idtr`EquationMatrix := IdentityMatrix(R,m);
  end if;
  idtr`Matrix := IdentityMatrix(R,n);
  return idtr;
end intrinsic;
 
intrinsic '^'(trans::TransG1,n::RngIntElt) -> TransG1
{Computes the nth power of the transformation.}
// This gives a nice way of accessing the inverse.
  if n lt 0 then 
    trans := Inverse(trans);
    n := -n;
  end if;
  if n eq 1 then return trans; end if;
  ans := New(TransG1);
  ans`Degree := trans`Degree;
  if trans`Degree eq 2 and assigned trans`Shift then 
    ans`Scalar := Parent(trans`Scalar)!1;
    ans`Shift := Parent(trans`Shift)![0,0,0];
    ans`Matrix := IdentityMatrix(BaseRing(trans`Matrix),2);
    for i in [1..n] do
      ans := trans*ans;
    end for;
  else
    if trans`Degree in {2,3} then 
      ans`Scalar := (trans`Scalar)^n;
    else
      ans`EquationMatrix := (trans`EquationMatrix)^n;
    end if;
    ans`Matrix := (trans`Matrix)^n;
  end if;
  return ans;
end intrinsic;

intrinsic ApplyTransformation(trans::TransG1,model::ModelG1) -> ModelG1
{Apply the transformation trans to the given genus one model.}
   return trans * model;
end intrinsic;

intrinsic ChangeRing(trans::TransG1,B::Rng) -> TransG1
{The transformation of genus one models obtained by coercing into the ring B.}
  n := trans`Degree;
  ans := New(TransG1);
  ans`Degree := n;
  if n in {2,3} then 
    ans`Scalar := B!(trans`Scalar);
    if n eq 2 and assigned trans`Shift then
      ans`Shift := ChangeUniverse(trans`Shift,B);
    end if;
  else
    ans`EquationMatrix := ChangeRing(trans`EquationMatrix,B);
  end if;
  ans`Matrix := ChangeRing(trans`Matrix,B);
  return ans;
end intrinsic;

intrinsic '*'(trans::TransG1,model::ModelG1) -> ModelG1
{Apply the transformation trans to the given genus one model.}
  n := model`Degree;
  require trans`Degree eq n : 
    "Transformation should have same degree as model";
  if n in {2,3} then
    f := model`Equation;
    R := Parent(f);
    mu := trans`Scalar;
    B := trans`Matrix;
    r := assigned trans`Shift select trans`Shift else [0,0,0];
    if VariableWeights(R) eq [1,1] and assigned trans`Shift then
      f := Equations(model)[1];
      R := Parent(f);
    end if;
    subst := [&+[B[i,j]*R.i: i in [1..n]]: j in [1..n]];
    if VariableWeights(R) eq [1,1,2] then 
      R := Parent(f);
      x,z,y := Explode([R.i : i in [1..3]]);
      R0 := BaseRing(R);
      subst := subst cat [R0!(1/mu)*y + r[1]*x^2 + r[2]*x*z + r[3]*z^2];
    end if;
    f_new := (n eq 2 select mu^2 else mu)*Evaluate(f,subst);
    return GenusOneModel(f_new);
  elif n eq 4 then
    R := PolynomialRing(model);
    phi := model`Equations;
    A := trans`EquationMatrix;
    B := trans`Matrix;
    subst := [&+[B[i,j]*R.i :i in [1..4]]: j in [1..4]];
    phi_B := [ Evaluate(phi[j],subst) : j in [1..2] ];  
    return GenusOneModel([ A[1,1]*phi_B[1] + A[1,2]*phi_B[2], A[2,1]*phi_B[1] + A[2,2]*phi_B[2] ]);
  else 
    R := PolynomialRing(model);
    phi := model`DefiningMatrix;
    A := trans`EquationMatrix;
    B := trans`Matrix;
    A := MatrixRing(R,5)!A; 
    subst := [&+[B[i,j]*R.i :i in [1..5]]: j in [1..5]];
    phi_B := Parent(phi)![Evaluate(phi[i,j],subst):j in [1..5],i in [1..5]];
    phi1 := Parent(phi)!(A*phi_B*Transpose(A));
// the following tidying up is redundant if the ring is exact
    for i in [1..5] do  
      phi1[i,i] := 0; 
    end for;
    for i in [1..5] do 
      for j in [1..i-1] do 
        phi1[i,j] := -phi1[j,i]; 
      end for; 
    end for;
    model1 := GenusOneModel(phi1);
    if assigned model`GlobalLevel then 
      model1`GlobalLevel := model`GlobalLevel*ScalingFactor(trans);
    end if;
    return model1;
  end if;
end intrinsic;

// intrinsic TransformationToMap(model1::ModelG1,model2::ModelG1,trans::TransG1
//   : Codomain := Curve(model1),Domain := Curve(model2)) -> Map
// {Given a transformation of genus one models tr such that tr*model1 = model2 returns the corresponding map between the curves defined by model2 and model1.}
function TransformationToMap(model1,model2,trans
    : Codomain := Curve(model1),Domain := Curve(model2)) 
  n := Degree(model1);
  assert Degree(model2) eq n; // "Models must have the same degree";
  assert trans*model1 eq model2; // "We require tr*model1 = model2";
  assert n in {3,4,5}; // not yet implemented for n = 2
  R := CoordinateRing(Ambient(Domain));
  T := trans`Matrix;
  subst := [&+[T[i,j]*R.i: i in [1..n]]: j in [1..n]];
  return map<Domain->Codomain|subst>;
end function;

////////////////////////////////////////////////////////
//                                                    //
//                 Special Models                     //
//                                                    //
////////////////////////////////////////////////////////

intrinsic GenusOneModel(n::RngIntElt,E::CrvEll) -> ModelG1, Crv, Map, Map  
{A genus one model of degree n describing the image C of |n.O| : E -> P^\{n-1\},
where n is 2,3,4 or 5. Also returns the curve C and maps E -> C and C -> E.}
  require n in [2..5] : "Degree of model must be in range [2..5]";
  P := CoordinateRing(Ambient(E));
  X,Y,Z := Explode([P.i : i in [1..3]]);
  a1,a2,a3,a4,a6 := Explode(aInvariants(E));
  seq := case<n|
     2 : [0,a1,a3,0,1,a2,a4,a6],
     3 : [-1,0,-a6,0,-a2,0,1,-a4,a3,a1],
     4 : [0,0,0,1,-1,0,0,0,0,0,-a6,-a4,a3,0,-a2,a1,-1,1,0,0],
     5 : [-a6,-a4,a3,-a2,a1,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,1,
          0,0,0,1,0,0,0,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,0,0,0],
    default : 0>;
  phi := GenusOneModel(n,seq);
  C := Curve(phi);
  case n :
    when 2 :  
      R := PolynomialRing(phi);
      x,z,y := Explode([R.i : i in [1..3]]);
      mapEtoC := map<E->C|[X,Z,Y*Z] : Check:=false >;
      mapCtoE := map<C->E|[x*z,y,z^2] : Check:=false >;
    when 3 :
      R := PolynomialRing(phi);
      x,y,z := Explode([R.i : i in [1..3]]);
      mapEtoC := map<E->C|[X,Y,Z] : Check:=false >;
      mapCtoE := map<C->E|[x,y,z] : Check:=false >;
    when 4 :
      R := PolynomialRing(phi);
      x1,x2,x3,x4 := Explode([R.i : i in [1..4]]);
      mapEtoC := map<E->C|[Z^2,X*Z,Y*Z,X^2] : Check:=false >;
      mapCtoE := map<C->E|[x2,x3,x1] : Check:=false >;
    when 5 :
      R := PolynomialRing(phi);
      x1,x2,x3,x4,x5 := Explode([R.i : i in [1..5]]);
      mapEtoC := map<E->C|[Z^2,X*Z,Y*Z,X^2,X*Y] : Check:=false >;
      mapCtoE := map<C->E|[x2,x3,x1] : Check:=false >;
  end case;
  return phi,C,mapEtoC,mapCtoE;
end intrinsic;

intrinsic HesseModel(n::RngIntElt,ab::SeqEnum) -> ModelG1
{A genus one model of degree n invariant under the standard representation of the Heisenberg group}
  a,b := Explode(ab);
  seq := case<n|
     2 : [a,0,b/4,0,a],  
     3 : [a,a,a,0,0,0,0,0,0,b],
     4 : [a,0,0,0,0,0,-b,a,0,0,0,0,-b,0,a,0,0,0,0,a],
     5 : [a,0,0,0,0,0,b,0,0,0,0,0,-b,0,0,0,0,0,-a,0,0,0,a,0,0,
	   0,0,0,b,0,0,0,0,0,-b,0,0,0,0,a,b,0,0,0,0,0,a,0,0,0],
     default : 0>;
  return GenusOneModel(n,seq);
end intrinsic;

intrinsic DiagonalModel(n::RngIntElt,coeffs::SeqEnum) -> ModelG1
{A genus one model of degree n invariant under the diagonal action of mu_n.}
  require #coeffs eq n : "Sequence of coefficients must have length",n;
  la := coeffs;
  seq:=case<n|
    2 : [la[1],0,1,0,la[2]],
    3 : [la[1],la[2],la[3],0,0,0,0,0,0,1],
    4 : [la[1],0,0,0,0,0,-1,la[2],0,0,0,0,-1,0,la[3],0,0,0,0,la[4]],
    5 : [la[1],0,0,0,0,0,1,0,0,0,0,0,-1,0,0,0,0,0,-la[4],0,0,0,la[3],0,0,
	   0,0,0,1,0,0,0,0,0,-1,0,0,0,0,la[5],1,0,0,0,0,0,la[2],0,0,0],
    default : 0>;
  return GenusOneModel(n,seq);
end intrinsic;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 2                           //
//                                                         //
/////////////////////////////////////////////////////////////

function aInvariantsTwo(f)
  seq := Eltseq(GenusOneModel(f));
  if #seq eq 5 then 
    a0,a1,a2 := Explode([0,0,0]);
    a,b,c,d,e := Explode(seq);
  else
    a0,a1,a2,a,b,c,d,e := Explode(seq);
  end if;
  aa1 := a1;
  aa2 := -a0*a2 + c;
  aa3 := a0*d + a2*b;
  aa4 := -a0^2*e - a0*a2*c - a2^2*a - 4*a*e + b*d;
  aa6 := -a0^2*c*e + a0*a1*b*e - a0*a2*b*d - a1^2*a*e + a1*a2*a*d 
    - a2^2*a*c - 4*a*c*e + a*d^2 + b^2*e;
  return [aa1,aa2,aa3,aa4,aa6];
end function;

function HessianTwo(f)
  seq := Eltseq(GenusOneModel(f));
  assert #seq eq 5;
  a,b,c,d,e := Explode(seq);
  R := Parent(f);
  x := R.1; 
  z := R.2;
  hessian := (8*a*c - 3*b^2)*x^4 + (24*a*d - 4*b*c)*x^3*z 
    + (48*a*e + 6*b*d - 4*c^2)*x^2*z^2 + (24*b*e - 4*c*d)*x*z^3
    + (8*c*e - 3*d^2)*z^4;
  return hessian;
end function;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 3                           //
//                                                         //
/////////////////////////////////////////////////////////////

function aInvariantsThree(phi)
  a,b,c,a2,a3,b1,b3,c1,c2,m:=Explode(Eltseq(GenusOneModel(phi)));
  aa1 := m;
  aa2 := -(a2*c2 + a3*b3 + b1*c1);
  aa3 := 9*a*b*c - (a*b3*c2 + b*a3*c1 + c*a2*b1) - (a2*b3*c1 + a3*b1*c2);
  aa4 := -3*(a*b*c1*c2 + a*c*b1*b3  + b*c*a2*a3) 
    + a*(b1*c2^2 + b3^2*c1) + b*(a2*c1^2 + a3^2*c2) + c*(a2^2*b3 + a3*b1^2) 
    + a2*c2*a3*b3 + b1*c1*a2*c2 + a3*b3*b1*c1;
  aa6 := a*b*c*(-27*a*b*c + 9*(a*b3*c2 + c*a2*b1 + b*a3*c1) + m^3) 
    + 3*a*b*c*((a2*b3*c1 + a3*b1*c2) - (a2*c2 + a3*b3 + b1*c1)*m) 
    - a^2*(b*c2^3 + c*b3^3) - b^2*(c*a3^3 + a*c1^3) - c^2*(a*b1^3 + b*a2^3)
    + (a*b*c1*c2 + b*c*a2*a3 + a*c*b1*b3)*(2*(a2*c2 + a3*b3 + b1*c1) - m^2) 
    - 3*(a*b*a3*b3*c1*c2 + b*c*a2*a3*b1*c1 + a*c*a2*b1*b3*c2)
    - a*((b1*c1 + a2*c2)*b3^2*c1 + (c1*b1 + a3*b3)*b1*c2^2)
    - b*((c2*a2 + a3*b3)*c1^2*a2 + (a2*c2 + b1*c1)*c2*a3^2)
    - c*((a3*b3 + b1*c1)*a2^2*b3 + (b3*a3 + a2*c2)*a3*b1^2)
    - a2*a3*b1*b3*c1*c2 + a*b*(a3*c2^2 + b3*c1^2)*m 
    + b*c*(a2^2*c1 + a3^2*b1)*m + a*c*(a2*b3^2 + b1^2*c2)*m 
    + (a*b1*b3*c1*c2 + b*a2*a3*c1*c2 + c*a2*a3*b1*b3)*m;
  return [aa1,aa2,aa3,aa4,aa6];
end function;

// Sometimes this is much quicker than computing all the bInvariants.
function b2InvariantThree(phi)
  a,b,c,a2,a3,b1,b3,c1,c2,m:=Explode(Eltseq(GenusOneModel(phi)));
  aa1 := m;
  aa2 := -(a2*c2 + a3*b3 + b1*c1);
  return aa1^2+4*aa2;
end function;

// The partial derivatives of the reduced Hessian
function HessianQuadrics(f)
  R := Parent(f);
  x,y,z := Explode([R.i : i in [1..3]]);
  a,b,c,a2,a3,b1,b3,c1,c2,m := Explode(Eltseq(GenusOneModel(f)));
  coeffs := [
    a*a2*c2 + a*a3*b3 + 4*a*b1*c1 - a*m^2 - a2^2*c1 + a2*a3*m - a3^2*b1,
    4*b*a2*c2 + b*a3*b3 + b*b1*c1 - b*m^2 - a2*b3^2 - b1^2*c2 + b1*b3*m,
    c*a2*c2 + 4*c*a3*b3 + c*b1*c1 - c*m^2 - a3*c2^2 - b3*c1^2 + c1*c2*m,
    3*a*b*c1 + a*b1*c2 - a*b3*m - b*a3^2 + a2*a3*b3,
    3*a*c*b1 + a*b3*c1 - a*c2*m - c*a2^2 + a2*a3*c2,
    3*a*b*c2 - a*b3^2 + b*a2*c1 - b*a3*m + a3*b1*b3,
    3*b*c*a2 + b*a3*c2 - b*c1*m - c*b1^2 + b1*b3*c1,
    3*a*c*b3 - a*c2^2 - c*a2*m + c*a3*b1 + a2*c1*c2,
    3*b*c*a3 - b*c1^2 + c*a2*b3 - c*b1*m + b1*c1*c2,
    9*a*b*c - a*b3*c2 - b*a3*c1 - c*a2*b1 + a2*b3*c1 + a3*b1*c2];
  mons := [
    [x^2, 0, 0, 2*x*y, 2*x*z, y^2, 0, z^2, 0, y*z],
    [0, y^2, 0, x^2, 0, 2*x*y, 2*y*z, 0, z^2, x*z],
    [0, 0, z^2, 0, x^2, 0, y^2, 2*x*z, 2*y*z, x*y]];
  quads:=[&+[-mons[i][j]*coeffs[j]:j in [1..10]]: i in [1..3]];
  return quads;
end function;

// The reduced Hessian of f, i.e. (H + b2*f)/4 where H is the Hessian.
function ReducedHessianThree(f)
  R := Parent(f);
  quads := HessianQuadrics(f);
  return &+[quads[i]*R.i : i in [1..3]];
end function;

function CovariantConic(conic1,conic2)
  R := Parent(conic1);
  B := BaseRing(R);
  BB := PolynomialRing(B); 
  t := BB.1;
  RR := PolynomialRing(BB,3);
  x,y,z := Explode([RR.i : i in [1..3]]);
  mat1 := QuadricToMatrix(RR!conic1);
  mat2 := QuadricToMatrix(RR!conic2);
  mat := Adjoint(Adjoint(mat1)+t*Adjoint(mat2));
  ans := Matrix(B,3,3,[Coefficient(mat[i,j],1): i,j in [1..3]]);
  return &+[ans[i,j]*R.i*R.j: i,j in [1..3]];
end function;

function CovariantTheta(cubic,hess)
  R := Parent(cubic);
  RR := PolynomialRing(R,3);
  x,y,z := Explode([R.i : i in [1..3]]);
  u,v,w := Explode([RR.i : i in [1..3]]);
  U := Evaluate(cubic,[u,v,w]);
  H := Evaluate(hess,[u,v,w]);
  polarU := &+[R.i*Derivative(U,RR.i):i in [1..3]];
  polarH := &+[R.i*Derivative(H,RR.i):i in [1..3]];
  conic := CovariantConic(polarU,polarH);
  return R!Evaluate(conic,[x,y,z]);
end function;

function ContravariantsThree(f)
  R := Parent(f);
  x,y,z := Explode([R.i : i in [1..3]]);
  mons := [x^2,y^2,z^2,x*y,y*z,z*x];
  seq := [[&+[MC(mon,R.i*R.j)*R.j: j in [1..3]]:mon in mons]:i in [1..3]];
  seq cat:=[[MC(Deriv(f,R.i),mon): mon in mons]: i in [1..3]];
  mat := Matrix(R,6,6,seq);
  P := Determinant(mat);
  quads := HessianQuadrics(f);
  vecs := [Vector(R,6,[MC(q,mon): mon in mons]): q in quads];
  mats := [mat: i in [1..3]];
  for i in [1..3] do mats[i][3+i]:=vecs[i]; end for;
  Q := &+[Determinant(mm): mm in mats];
  return Parent(f)!P,Parent(f)!Q;
end function;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 4                           //
//                                                         //
/////////////////////////////////////////////////////////////

intrinsic SL4Invariants(model::ModelG1) -> SeqEnum[RngElt]
{The SL_4-invariants of a genus one model of degree 4.}
  phi := model`Equations;
  R := Universe(phi);
  B := BaseRing(R);
  P := PolynomialRing(B);
  t := P.1;
  RR<x1,x2,x3,x4> := PolynomialRing(P,4);
  quads := [Evaluate(phi[i],[x1,x2,x3,x4]) : i in [1..2]];
  det := Determinant(QuadricToMatrix(quads[1]+t*quads[2]));
  a,bb,c,dd,e := Explode([Coefficient(det,i) : i in [0..4]]); 
  qA,qB := Explode(Eltseq(phi)); 
  AA,BB := Explode([Adjoint(QuadricToMatrix(q)) : q in [qA,qB]]);
  b := &+[AA[i,j]*MC(qB,R.i*R.j): i,j in [1..4]| i le j];
  d := &+[BB[i,j]*MC(qA,R.i*R.j): i,j in [1..4]| i le j];
  assert bb eq 2*b;
  assert dd eq 2*d;
  return [a,b,c,d,e];
end intrinsic;

function ReducedDeterminant(q)
  R := Parent(q);
  coeffs := [MC(q,R.i*R.j): i,j in [1..4] | i le j];
  a11,a12,a13,a14,a22,a23,a24,a33,a34,a44 := Explode(coeffs);
  rdet := 4*a11*a22*a33*a44 
    - (a12*a13*a24*a34 + a12*a14*a23*a34 + a13*a14*a23*a24)
    + (a11*a23*a24*a34 + a12*a13*a23*a44 + a12*a14*a24*a33 + a13*a14*a22*a34)
    - (a11*a22*a34^2 + a11*a23^2*a44 + a11*a24^2*a33 
       + a12^2*a33*a44 + a13^2*a22*a44 + a14^2*a22*a33);
  return rdet;
end function;

intrinsic DoubleSpaceQuartic(model::ModelG1) -> ModelG1
{A special case (degree 4) of DoubleGenusOneModel}
  require model`Degree eq 4: "Input should be a genus one model of degree 4";
  phi := model`Equations;
  seq := Eltseq(model);
  a11,a12,a13,a14,a22,a23,a24,a33,a34,a44,
    b11,b12,b13,b14,b22,b23,b24,b33,b34,b44 := Explode(seq);
  a0 := a12*a34 + a13*a24 + a14*a23;
  a1 := a12*b34 + a13*b24 + a14*b23 + a23*b14 + a24*b13 + a34*b12;
  a2 := b12*b34 + b13*b24 + b14*b23;
  B := BaseRing(PolynomialRing(model));
  P := PolynomialRing(B);
  t := P.1;
  R<x1,x2,x3,x4> := PolynomialRing(P,4);
  quads := [Evaluate(phi[i],[x1,x2,x3,x4]):i in [1..2]];
  rdet := ReducedDeterminant(quads[1]+t*quads[2]);
  seq := [a0,a1,a2] cat [Coefficient(rdet,i): i in [0..4]];
  return GenusOneModel(2,seq);
end intrinsic;

function AdjointDiagonal(q)
  R := Parent(q);
  coeffs := [MC(q,R.i*R.j): i,j in [1..4] | i le j];
  a11,a12,a13,a14,a22,a23,a24,a33,a34,a44 := Explode(coeffs);
  dd := [4*a22*a33*a44 - a22*a34^2 - a23^2*a44 + a23*a24*a34 - a24^2*a33,
         4*a11*a33*a44 - a11*a34^2 - a13^2*a44 + a13*a14*a34 - a14^2*a33,
         4*a11*a22*a44 - a11*a24^2 - a12^2*a44 + a12*a14*a24 - a14^2*a22,
         4*a11*a22*a33 - a11*a23^2 - a12^2*a33 + a12*a13*a23 - a13^2*a22];
  return dd;
end function;

function AdjointQuadric(q)
  R := Parent(q);
  A := QuadricToMatrix(q);
  AA := Adjoint(A);
  dd := AdjointDiagonal(q);
  for i in [1..4] do 
     assert AA[i,i] eq 2*dd[i];
     AA[i,i] := dd[i]; 
  end for;
  return &+[AA[i,j]*R.i*R.j:i,j in [1..4]|i le j];
end function;

intrinsic SL4Covariants(model::ModelG1) -> SeqEnum
{Given a genus one model (Q1,Q2) of degree 4 returns a sequence of 4 quadrics [Q1,T1,T2,Q2] where T1 and T2 are the classical covariants used in FourToTwoCovering}
  R := PolynomialRing(model);
  phi := model`Equations;
  qA,qB := Explode(Eltseq(phi));
  A,B := Explode([QuadricToMatrix(q):q in [qA,qB]]);
  qAA := AdjointQuadric(qA);
  qBB := AdjointQuadric(qB);
  T1 := &+[MC(qBB,R.r*R.s)*&+[(A[i,j]*A[r,s]-A[i,s]*A[j,r])*R.i*R.j 
          : i,j in [1..4]]: r,s in [1..4] | r le s];
  T2 := &+[MC(qAA,R.r*R.s)*&+[(B[i,j]*B[r,s]-B[i,s]*B[j,r])*R.i*R.j 
          : i,j in [1..4]]: r,s in [1..4] | r le s];
  return [qA,T1,T2,qB];
end intrinsic;

function SL4Contravariants(model)
  R := PolynomialRing(model);
  phi := model`Equations;
  B := BaseRing(R);
  P := PolynomialRing(B);
  t := P.1;
  RR<x1,x2,x3,x4> := PolynomialRing(P,4);
  quads := [Evaluate(phi[i],[x1,x2,x3,x4]):i in [1..2]];
  adjquad := AdjointQuadric(quads[1] + t*quads[2]);
  return [&+[R|Coefficient(MC(adjquad,RR.i*RR.j),k)*R.i*R.j 
           : i,j in [1..4]|i le j] : k in [0..3]];
end function;

function CovariantsFour(model)
  R := PolynomialRing(model);
  A,T,T1,B := Explode(SL4Covariants(model));
  jmat := Matrix(R,4,4,[Deriv(f,R.i): f in [A,T,T1,B],i in [1..4]]);
  J := myEQ(Determinant(jmat),4);
  phi2 := DoubleSpaceQuartic(model);
  a0,a1,a2 := Explode(Eltseq(phi2));
  J := J - (a0*T^2 - a1*T*T1 + a2*T1^2);
  J := J + a1*(a0*B + a2*A)*(a0*T + a2*T1) + a0^2*a2^3*(A^2 + B^2);
  J := myEQ(J,2);
  return [T,-T1,J];
end function;

intrinsic FourToTwoCovering(C4::Crv : C2:=0) -> Crv,Crv,MapSch
{The curves C4, C2 and the 2-covering C4 -> C2, from the given genus one model of degree 4, 
or from a given curve C4, which must be an intersection of quadrics.} 
  flag, model := IsGenusOneModel(Equations(C4));
  require flag : "The given curve must be an intersection of quadrics in P^3";
  return FourToTwoCovering(model : C4:=C4,C2:=C2 );
end intrinsic;

intrinsic FourToTwoCovering(model::ModelG1: C4:=Curve(model),C2:=0) -> Crv,Crv,MapSch
{"} // "
  require model`Degree eq 4 : "Input must be a genus one model of degree 4.";
// C4 := Curve(model);
  require Discriminant(model) ne 0 : "Model must be nonsingular.";
  R := PolynomialRing(model);
  require CanDivideBy(R!2): "Unable to divide by 2.";
  forms := CovariantsFour(model);
  if C2 cmpeq 0 then 
     C2 := Curve(DoubleSpaceQuartic(model));
     C4toC2 := map<C4->C2|forms : Check:=false >;
  elif Type(C2) eq CrvHyp then
     C2_0 := HyperellipticCurve(DoubleSpaceQuartic(model));
     C2isOkay, C2_0toC2 := IsIsomorphic(C2_0, C2);
     require C2isOkay : "If C2 is given, it should be isomorphic (as a hyperelliptic curve)",
                        " to the relevant 2-covering";
     C4toC2_0 := map< C4 -> C2_0 | [forms[1],forms[3],forms[2]]  : Check:=false >;
     C4toC2 := Expand( C4toC2_0*C2_0toC2 );
  else
     C2Hyp := HyperellipticCurve(GenusOneModel(C2));
     C2_0 := HyperellipticCurve(DoubleSpaceQuartic(model));
     C2isOkay, C2_0toC2Hyp := IsIsomorphic(C2_0, C2Hyp);
     require C2isOkay : "If C2 is given, it should be isomorphic (as a hyperelliptic curve)",
                        " to the relevant 2-covering";
     C4toC2_0 := map< C4 -> C2_0 | [forms[1],forms[3],forms[2]]  : Check:=false >;
     Pr2_C2 := Ambient(C2);
     Pr2 := Ambient(C2Hyp);
     if Gradings(Pr2_C2) eq [[1,1,2]] then 
        C2HyptoC2 := map< C2Hyp -> C2 | [Pr2.1,Pr2.3,Pr2.2]  : Check:=false >;
     elif Gradings(Pr2_C2) eq [[1,2,1]] then 
        C2HyptoC2 := map< C2Hyp -> C2 | [Pr2.1,Pr2.2,Pr2.3]  : Check:=false >;
     require false: "C2 should be of the form y^2+h(x,z)y+f(x,z)",
                    " in a weighted projective space where y has weight 2";
     end if;
     C4toC2 := Expand( C4toC2_0*C2_0toC2Hyp*C2HyptoC2 );
  end if;
  return C4, C2, C4toC2;
end intrinsic;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 5                           //
//                                                         //
/////////////////////////////////////////////////////////////

function EvalQuads(qq,x1,x2)
  R := Universe(qq);
  mats := [Matrix(R,5,5,[Deriv(Deriv(q,R.j),R.k) :j,k in [1..5]]) :q in qq];
  elts := [(Matrix(1,5,x1)*mat*Matrix(5,1,x2))[1,1]: mat in mats]; 
  return &+[elts[i]*R.i: i in [1..5]];
end function;

function AuxiliaryQuadrics(p)
   R := Universe(p);
   K := BaseRing(R);
   assert IsField(K);
   S := Determinant(Matrix(R,5,5,[Deriv(p[i],j):i,j in [1..5]]));
   pp := [R|Evaluate(mon,p):mon in MD(R,2)];
   mat := Matrix(K,15,70,[Coeffs(pp[i],4):i in [1..15]]);
   if Rank(mat) lt 15 then return [R|0:i in [1..5]]; end if;
   vecs := [Vector(K,Coeffs(Deriv(S,i),4)):i in [1..5]];
   sols := Solution(mat,vecs);
   q := [R|&+[sols[i][j]*MD(R,2)[j]:j in [1..15]]:i in [1..5]];
   return q;
end function;

function InvariantsFive(phi)
  R := BaseRing(phi);
  K := BaseRing(R);
  assert IsField(K);
  assert Characteristic(K) notin [2,5];
  p := PfSubmax(phi);
  q := AuxiliaryQuadrics(p);
  RR := PolynomialRing(R);
  t := RR.1;
  U := Matrix(RR,5,5,[&+[MC(phi[j,k],R.i)*R.k : k in [1..5]]: i,j in [1..5]]);
  P := Matrix(R,5,5,[&+[MC(Deriv(p[k],j),R.i)*R.k : k in [1..5]]
     : i,j in [1..5]]);
  Q := Matrix(RR,5,5,[Deriv(q[i],j):i,j in [1..5]]);
  det1 := Determinant(P);
  det2 := Determinant(U+t*Q);
  T := [R|Coefficient(RR!det2,i): i in [1,3,5]];
  cc := [K|&+[MultiFact(mon)*MC(det1,mon)*MC(d2,mon):mon in MD(R,5)]:d2 in T];
  consts := [40,-320,128];
  c4,c6,c8 := Explode([K|cc[i]/consts[i]:i in [1..3]]);
  assert c8 eq c4^2; 
  return c4,c6;
end function;

function DiscriminantFive(phi)
  R := BaseRing(phi);
  B := BaseRing(R);
  P := PfSubmax(phi);
  Jmat := Matrix(R,5,5,[Derivative(P[i],R.j): i,j in [1..5]]);
  M1 := [Matrix(B,5,5,[MC(phi[i,j],R.k):i,j in [1..5]]): k in [1..5]];
  M2 := [Transpose(Jmat)*M*Jmat: M in M1];
  Qlist := P cat [R|M2[i][j,k]: i,j,k in [1..5]|i lt j and j lt k];
  mat := Matrix(B,15,15,[MC(q,m): m in MD(R,2),q in Qlist]);
  assert CanDivideBy(B!2);
  return B!ExactQuotient(Determinant(mat),32);
end function;

function ExactPfaffianMatrix(q1,r,c)
  phi := PfaffianMatrix(q1,r);
  q2 := PfSubmax(phi);
  assert exists(t){TotalDegree(f):f in q1| f ne 0};
  mons := MD(BaseRing(phi),t);
  mat := Matrix(2,#q1*#mons,[&cat([Coeffs(f,t): f in q]):q in [q1,q2]]);
  assert Rank(mat) eq 1;
  km := KernelMatrix(mat);
  d := -km[1,2]/km[1,1];
  assert Vector(q1) eq d*Vector(q2);
  flag,sqrt := IsSquare(c*d);
  error if not flag,c*d," is not a square.";
  phi*:= sqrt;
  return phi;
end function;

function HessianFive(phi,c4,c6)
  R := BaseRing(phi);
  K := BaseRing(R);
  assert IsField(K);
  assert Characteristic(K) notin [2,3];
  p := PfSubmax(phi);
  q := AuxiliaryQuadrics(p);
  RR<y1,y2,y3,y4,y5> := PolynomialRing(R,5);
  M := Determinant(Matrix(RR,5,5,[&+[MC(Deriv(p[k],j),R.i)*RR.k
                     : k in [1..5]]:i,j in [1..5]]));
  for ctr in [1..2] do
    M := &+[R.i*MC(q[i],R.j*R.k)*Deriv(Deriv(M,RR.j),RR.k)
	   : j,k in [1..5], i in [1..5] | j le k ];
  end for;
  q2m := [R|MC(M,RR.i): i in [1..5]];
  p22 := Eltseq(4*c4*Vector(p)-(3/16)*Vector(q2m));
  hessian := ExactPfaffianMatrix(p22,1,1);
  assert p22 eq PfSubmax(hessian);
  Umat := Matrix(K,10,5,[Coeffs(phi[i,j],1): i,j in [1..5] | i lt j]);
  Hmat := Matrix(K,10,5,[Coeffs(hessian[i,j],1): i,j in [1..5] | i lt j]);  
  Dmat := HorizontalJoin(Umat,Hmat);
  discr1 := Determinant(Dmat);
  discr2 := 12^2*(c4^3-c6^2);
  assert discr2 ne 0;
  assert discr1 in [discr2,-discr2];
  if discr1 eq -discr2 then hessian*:= -1; end if;
  return hessian;   
end function;

function CovariantsP(phi,hess)
   R := BaseRing(phi);
   RR := PolynomialRing(R);
   t := RR.1;
   U := Matrix(RR,5,5,[phi[i,j]+t*hess[i,j]:i,j in [1..5]]);
   P := PfSubmax(U);
   p2,p12,p22 := Explode([[Coefficient(P[j],i):j in [1..5]]: i in [0..2]]);
   assert p2 eq PfSubmax(phi);
   assert p22 eq PfSubmax(hess);
   p12 := [(1/2)*p:p in p12];
   return p2,p12,p22;
end function;   

function JacMat(p)
  R := Universe(p);
  return Matrix(R,5,5,[&+[Deriv(Deriv(p[k],R.i),R.j)*R.k
    :k in [1..5]]:i,j in [1..5]]);
end function; 

function JacobianZ(q,p22)
  R := Universe(q);
  return &+[R.i*Evaluate(q[i],p22):i in [1..5]];
end function;

function JacobianX(q,p12,p22)
  N := Determinant(Matrix(5,5,[Deriv(q[i],j):i,j in [1..5]]));
  H := Matrix(5,5,[Deriv(Deriv(N,i),j): i,j in [1..5]]);
  return &+[Evaluate(H[i,j],p12)*p22[i]*p22[j]: i,j in [1..5]];
end function;

function JacobianY(phi,q,p2,p22)
  R := BaseRing(phi);
  P2 := JacMat(p2);
  P22 := JacMat(p22);
  Rt := PolynomialRing(R);
  t := Rt.1;
  M30 := Coefficient(Determinant(P2+t*P22),1);
  Q := JacMat(q);
  T23 := Eltseq(Vector(p22)*phi);
  T28 := Eltseq(Vector(p22)*Q);
  return &+[T23[i]*Evaluate(Deriv(M30,i),T28): i in [1..5]];
end function;

function OmegaMatrixFive(phi)
  p := PfSubmax(phi);
  S := (1/2)*Determinant(Matrix(5,5,[Deriv(p[i],j):i,j in [1..5]]));
  omega := ExactPfaffianMatrix([Deriv(S,i):i in [1..5]],2,5); 
  pp := PfSubmax(omega);
  assert forall{i: i in [1..5]|pp[i] eq 5*Deriv(S,i)};
  return omega;
end function;

function CovariantsTwistTwo(phi)   
  R := BaseRing(phi); 
  c4,c6:=Invariants(GenusOneModel(phi));
  hess:=HessianFive(phi,c4,c6);
  p2,p12,p22 := CovariantsP(phi,hess);
  p22 := Eltseq(Vector(p22)+c4*Vector(p2));
  om := OmegaMatrixFive(phi);
  mons := MD(R,2);
  ijset := [[i,j]:i,j in [1..5]|i lt j];
  mat1 := Matrix(10,15,[[MC(om[ij[1],ij[2]],mon):mon in mons]:ij in ijset]);
  mat2 := Matrix(10,15,[[MC(f,mon):mon in mons]:f in p12 cat p22]);
  phi1 := &+[Matrix(R,5,5,[<ijset[k][1],ijset[k][2],soln[k]*R.l>
    : k in [1..10]]) where soln is Solution(mat1,mat2[l]): l in [1..5]];
  phi2 := &+[Matrix(R,5,5,[<ijset[k][1],ijset[k][2],soln[k]*R.l>
    : k in [1..10]]) where soln is Solution(mat1,mat2[l+5]): l in [1..5]];
  phi1 := Parent(phi)!(-phi1+Transpose(phi1));
  phi2 := (1/2)*Parent(phi)!(-phi2+Transpose(phi2));
  return phi1,phi2;
end function;

function CovariantsQ(p2,p12,p22)
  p12 := [2*p:p in p12];
  R := Universe(p2);
  q6 := AuxiliaryQuadrics(p2);
  mm := Matrix(5,5,[p2[i]*p12[j]:i,j in [1..5]]);  
  polys1 := [mm[i,i]: i in [1..5]];
  polys2 :=  [mm[i,j]+mm[j,i]: i,j in [1..5] | i lt j];
  polys := [R.i*p:p in polys1 cat polys2, i in [1..5]];
  mons := [R.i^2: i in [1..5]] cat [2*R.i*R.j: i,j in [1..5]| i lt j];
  mat := Matrix(#polys,126,[Coeffs(f,5):f in polys]);
  assert Rank(mat) eq #polys;
  S := EvalQuads(q6,p12,p12);
  for ctr in [1..2] do
    vec := Vector(Coeffs(S,5));
    soln := Solution(mat,vec);
    ans := [[soln[15*(i-1)+j]: j in [1..15]]:i in [1..5]];
    qq := [&+[aa[i]*mons[i] :i in [1..15]]: aa in ans];
    if ctr eq 1 then 
      q16 := qq;  
      S := 2*EvalQuads(q6,p12,p22)+EvalQuads(q16,p12,p12);
    else 
      q26 := qq; 
    end if;
  end for;
  q6 := [(1/2)*p:p in q6];
  q16 := [(1/8)*p:p in q16];
  q26 := [(1/40)*p:p in q26];
  return q6,q16,q26;
end function;

function ShuffleMult(mat,pp);
  R := Parent(mat[1,1]);
  mydata := [Matrix(5,5,[&+[MC(mat[i,j],R.k)*Derivative(p,R.k)
    : k in [1..5]] :i,j in [1..5]]): p in pp]; 
  ans := Matrix(5,5,
    [#ss eq 0 select 0 else &+[mydata[s[1]][s[2],s[3]]: s in ss] 
    where ss is [[i,j,k]: i,j,k in [1..5] | #{i,j,k,a,b} eq 5 
      and Sign(Sym(5)![i,j,k,a,b]) eq 1] 
    : a,b in [1..5]]); 
  assert Transpose(ans) eq -ans;
  return Parent(mat)!ans;
end function;

function CovariantsTwistThree(phi)
  c4,c6 := Invariants(GenusOneModel(phi));
  hess := HessianFive(phi,c4,c6);
  p2,p12,p22 := CovariantsP(phi,hess);
  q6,q16,q26 := CovariantsQ(p2,p12,p22);
  E7,E17 := CovariantsTwistTwo(phi);  
  R13 := (1/2)*ShuffleMult(E7,q6);
  R23 := (-1/2)*ShuffleMult(E7,q16);
  return R13,R23;
end function;
  
function ContravariantsFive(phi)
  R := BaseRing(phi);
  c4,c6 := Invariants(GenusOneModel(phi));
  hess := HessianFive(phi,c4,c6);
  p2,p12,p22 := CovariantsP(phi,hess);
  q6,q16,q26 := CovariantsQ(p2,p12,p22);
  RR := PolynomialRing(R);
  t := RR.1;
  U1 := Matrix(RR,5,5,[&+[MC(phi[j,k],R.i)*R.k: k in [1..5]]:i,j in [1..5]]);
  U11 := Matrix(RR,5,5,[&+[MC(hess[j,k],R.i)*R.k: k in [1..5]]:i,j in [1..5]]);
  Q6 := Matrix(RR,5,5,[Deriv(q6[i],R.j):i,j in [1..5]]);
  Q16 := Matrix(RR,5,5,[Deriv(q16[i],R.j):i,j in [1..5]]);
  DD := Determinant(U1 + t*Q6);
  M10,M20,M30 := Explode([R!Coefficient(RR!DD,i): i in [1,3,5]]);
  DD := Determinant(U11 + t*Q6);
  N50,N40,N30 := Explode([R!Coefficient(RR!DD,i): i in [1,3,5]]);
  DD := Determinant(U1 + t*Q16);
  T20,T50,T80 := Explode([R!Coefficient(RR!DD,i): i in [1,3,5]]);
  assert M20 eq -2*T20;
  assert M30 eq N30;
  F40 := 10*c6*M10 - 14*c4*M20 + N40; 
  F50 := 9*c4^2*M10 - 310*c6*M20 - 270*c4*M30 + N50 - 108*T50;
  mm := Matrix(5,5,[q6[i]*q16[j]:i,j in [1..5]]);
  polys1 := [mm[i,i]: i in [1..5]];
  polys2 := [mm[i,j]+mm[j,i]: i,j in [1..5] | i lt j];
  polys := [R.i*p:p in polys1 cat polys2, i in [1..5]];
  mons := [R.i^2: i in [1..5]] cat [2*R.i*R.j: i,j in [1..5]| i lt j];
  mat := Matrix(#polys,126,[Coeffs(T,5):T in polys]);
  assert Rank(mat) eq #polys;
  soln := Solution(mat,Vector(Coeffs(F40,5)));
  ans := [[soln[15*(i-1)+j] : j in [1..15]] : i in [1..5]];
  t18 := [(1/72)*&+[aa[i]*mons[i] : i in [1..15]] : aa in ans];
  soln := Solution(mat,Vector(Coeffs(F50,5)));
  ans := [[soln[15*(i-1)+j] : j in [1..15]] : i in [1..5]];
  t28 := [(1/1584)*&+[aa[i]*mons[i] : i in [1..15]]: aa in ans];
  d19 := (-1/2)*ShuffleMult(phi,t18);
  d29 := (-1/2)*ShuffleMult(phi,t28);
  return d19,d29;
end function;

/////////////////////////////////////////////////////////////
//                                                         //
//                    n = 2, 3, 4, 5                       //
//                                                         //
/////////////////////////////////////////////////////////////

intrinsic aInvariants(model::ModelG1) -> SeqEnum[RngElt]
{The invariants [a1, a2, a3, a4, a6] of the given genus one model 
(which must have degree 2, 3 or 4).}
  n := model`Degree;
  require n in {2,3,4} : "Input must be a genus one model of degree 2, 3 or 4.";
  case n:
    when 2: return aInvariantsTwo(model`Equation);
    when 3: return aInvariantsThree(model`Equation);
    when 4: return aInvariants(DoubleSpaceQuartic(model));
  end case;
end intrinsic;

intrinsic bInvariants(model::ModelG1) -> SeqEnum[RngElt]
{The invariants [b2, b4, b6, b8] of the given genus one model (of degree 2 or 3).}
  n := model`Degree;
  require n in {2,3,4} : "Input must be a genus one model of degree 2, 3 or 4.";
  a1,a2,a3,a4,a6 := Explode(aInvariants(model));
  b2 := a1^2 + 4*a2;
  b4 := 2*a4 + a1*a3;
  b6 := a3^2 + 4*a6;
  b8 := a1^2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3^2 - a4^2;
  return [b2,b4,b6,b8];
end intrinsic;

intrinsic cInvariants(model::ModelG1) -> SeqEnum[RngElt]
{The invariants [c4, c6] of the given genus one model.}
  n := model`Degree;
  if n in {2,3,4} then 
    a1,a2,a3,a4,a6 := Explode(aInvariants(model));
    b2 := a1^2 + 4*a2;
    b4 := 2*a4 + a1*a3;
    b6 := a3^2 + 4*a6;
    c4 := b2^2 - 24*b4;
    c6 := -b2^3 + 36*b2*b4 - 216*b6;
    return [c4,c6];
  else
    B := BaseRing(PolynomialRing(model));
    require IsDomain(B) : "Coefficient ring must be an integral domain.";
    p := Characteristic(B);
    require p notin {2,5} : "Coefficient ring has characteristic",p;
    K := FieldOfFractions(B);
    modelK := ChangeRing(model,K);
    c4,c6 := InvariantsFive(modelK`DefiningMatrix);
    return [B|c4,c6];
  end if;
end intrinsic;

intrinsic Invariants(pol::RngMPolElt)  -> RngElt,RngElt,RngElt
{Invariants c4, c6 and Delta of the genus one model determined by the given polynomial.}
  return Invariants(GenusOneModel(pol));
end intrinsic;

intrinsic Invariants(model::ModelG1) -> RngElt,RngElt,RngElt
{Invariants c4, c6 and Delta of the given genus one model.}
  n := model`Degree;
  if n in {2,3,4} then
    b2,b4,b6,b8 := Explode(bInvariants(model));
    c4 := b2^2 - 24*b4;
    c6 := -b2^3 + 36*b2*b4 - 216*b6;
    Delta := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
    return c4,c6,Delta;
  else
    B := BaseRing(PolynomialRing(model));
    require IsDomain(B) :"Coefficient ring must be an integral domain.";
    p := Characteristic(B);
    require p notin {2,3,5} :"Coefficient ring has characteristic",p;
    K := FieldOfFractions(B);
    modelK := ChangeRing(model,K);
    c4,c6 := InvariantsFive(modelK`DefiningMatrix);
    Delta := (c4^3-c6^2)/1728;
    return B!c4,B!c6,B!Delta;
  end if;
end intrinsic;

intrinsic Discriminant(model::ModelG1) -> RngElt
{The discriminant Delta of the given genus one model.}

  if assigned model`Discriminant then
    return model`Discriminant;
  end if;

  if model`Degree eq 5 then
    B := BaseRing(PolynomialRing(model));
    require CanDivideBy(B!2): "Unable to divide by 2 in the coefficient ring.";
    Delta := B!DiscriminantFive(model`DefiningMatrix);
  else
    b2,b4,b6,b8 := Explode(bInvariants(model));
    Delta := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
  end if;

  model`Discriminant := Delta;
  return Delta;
end intrinsic;

intrinsic Jacobian(poly::RngMPolElt) -> CrvEll
{The Jacobian of the genus one model determined by the given polynomial}
  return Jacobian(GenusOneModel(poly));
end intrinsic;

intrinsic Jacobian(C::Crv) -> CrvEll
{The Jacobian of the curve C, which must be a genus one normal curve 
of degree 2,3,4 or 5.}
  return Jacobian(GenusOneModel(C));
end intrinsic;

intrinsic Jacobian(model::ModelG1) -> CrvEll
{The Jacobian of the given genus one model.}
  require Discriminant(model) ne 0 :"Model is singular.";
  B := BaseRing(PolynomialRing(model));
  require IsField(B) or ISA(Type(B),RngInt): 
     "Only field types or Z are currently allowed.";
  n := model`Degree;
  if n in {2,3,4} then 
    a1,a2,a3,a4,a6 := Explode(aInvariants(model));
    E := EllipticCurve([a1,a2,a3,a4,a6]);
  else
    p := Characteristic(B);
    require p notin {2,3,5} : "Coefficient ring has characteristic",p;
    c4,c6 := Explode(cInvariants(model));
    E := EllipticCurve([-27*c4,-54*c6]);
  end if;
  return E;
end intrinsic;

intrinsic Hessian(pol::RngMPolElt) -> RngMPolElt
{The Hessian of the genus one model determined by the given polynomial}
  return Equation(Hessian(GenusOneModel(pol)));
end intrinsic;

intrinsic Hessian(model::ModelG1) -> ModelG1
{The Hessian H of the given genus one model.}
  n := model`Degree;
  if n eq 2 then
    f := model`Equation;
    if VariableWeights(Parent(f)) eq [1,1,2] then 
      f := CompleteTheSquare(model)`Equation;
    end if;
    hessian := HessianTwo(f);
    return GenusOneModel(Parent(f)!hessian);
  elif n eq 3 then
    f := model`Equation;
    b2 := b2InvariantThree(f);
    hessian := 4*ReducedHessianThree(f)-b2*f;
    return GenusOneModel(Parent(f)!hessian);
  elif n eq 4 then 
    a,b,c,d,e := Explode(SL4Invariants(model));
    A,T,T1,B := Explode(SL4Covariants(model));
    hessian := [6*T1 - c*A - 6*b*B, 6*T - c*B - 6*d*A];
    return GenusOneModel(ChangeUniverse(hessian,Universe(model`Equations)));
  else
    B := BaseRing(PolynomialRing(model));
    require IsDomain(B) :"Coefficient ring must be an integral domain.";
    p := Characteristic(B);
    require p notin {2,3,5} :"Coefficient ring has characteristic",p;
    K := FieldOfFractions(B);
    modelK := ChangeRing(model,K);
    c4,c6 := InvariantsFive(modelK`DefiningMatrix);
    require c4^3-c6^2 ne 0 :"Model is singular.";
    hessian := HessianFive(modelK`DefiningMatrix,c4,c6);
    return GenusOneModel(ChangeRing(hessian,PolynomialRing(model)));
  end if;
end intrinsic;

intrinsic CoveringCovariants(model::ModelG1:ComputeY:=true) -> SeqEnum[RngMPolElt]
{The covariants defining the n-covering map from the given genus one model.}
  if assigned model`CoveringCovariants then 
    answer := model`CoveringCovariants;
    if ComputeY then 
      if #answer eq 3 then return answer; end if;
    else
      Z,X := Explode(answer);
      return [Z,X];
    end if;
  end if;
  n := model`Degree;
  if n in {2,3} then
    f := model`Equation;
    R := Parent(f);
    if VariableWeights(R) eq [1,1] then 
      f := Equations(model)[1];
      R := Parent(f);
    end if;
    B := BaseRing(R);
    require CanDivideBy(B!2): "Unable to divide by 2.";
    require CanDivideBy(B!3): "Unable to divide by 3.";
  end if;
  if n eq 2 then
    Z := Deriv(f,R.3);
    g := CompleteTheSquare(GenusOneModel(f));
    X := -3*myEQ(Hessian(g)`Equation,4);
    g := Evaluate(g`Equation,[R.1,R.2]);
    X := Evaluate(X,[R.1,R.2]);
    if ComputeY then 
      jmat := Matrix(R,2,2,[Deriv(p,R.i): p in [g,X],i in [1..2]]);
      Y := 3*myEQ(Determinant(jmat),8);
    end if;
  elif n eq 3 then
    H := Hessian(model)`Equation;
    c4,c6 := Explode(cInvariants(model));
    Z := ReducedHessianThree(f);
    X := myEQ(CovariantTheta(f,H) + 24*c6*f^2,64);
    if ComputeY then
      jmat := Matrix(R,3,3,[Deriv(p,R.i): p in [f,Z,X],i in [1..3]]);    
      Y := myEQ(Determinant(jmat),3);
    end if;
  end if;

  // remaining cases n = 4 or 5 
  R := PolynomialRing(model);
  B := BaseRing(R);
  require CanDivideBy(B!2): "Unable to divide by 2.";
  require CanDivideBy(B!3): "Unable to divide by 3.";
  if n eq 4 then 
    cov1 := CovariantsFour(model);
    phi2 := DoubleSpaceQuartic(model);
    cov2 := CoveringCovariants(phi2:ComputeY:=ComputeY);
    Z,X,Y := Explode([Evaluate(f,cov1): f in cov2]);
  elif n eq 5 then
    require IsField(B) :"Coefficient ring must be a field.";
    p := Characteristic(B);
    require p notin {2,3,5} :"Coefficient field has characteristic",p;
    phi := model`DefiningMatrix;
    c4,c6 := Invariants(model);
    require c4^3-c6^2 ne 0 :"Model is singular.";
    H := HessianFive(phi,c4,c6);
    P2,P12,P22 := CovariantsP(phi,H); 
    Q := AuxiliaryQuadrics(P2);
    Z := EQ(JacobianZ(Q,P22),2);
    X := 3^3*EQ(JacobianX(Q,P12,P22),2^6);
    if ComputeY then 
      Y := 3^3*EQ(JacobianY(phi,Q,P2,P22),2^8); 
    end if;
  end if;
  answer := ComputeY select [Z,X,Y] else [Z,X];
  model`CoveringCovariants := answer; // [Z,X,Y];
  return answer;
end intrinsic;

function nCoveringInternal(model,C)
  c4,c6 := Explode(cInvariants(model));
  J := EllipticCurve([-27*c4,-54*c6]);
  if Degree(model) eq 4 then
    f := DoubleSpaceQuartic(model);
    C2 := Curve(f);
    forms := CovariantsFour(model);
    pi1 := map<C->C2|forms>;
    pi2 := nCoveringInternal(f,C2);
    pi := pi1*pi2;
  else
    covars := CoveringCovariants(model);
    covars := [CoordinateRing(Ambient(C))!f : f in covars];
    Z,X,Y := Explode([NormalForm(f,Ideal(C)): f in covars]);
    pi := map< C->J | [X*Z,Y,Z^3] : Check:=false >;
  end if;
  return pi;
end function;

intrinsic nCovering(model::ModelG1 : E:=0 ) -> Crv,CrvEll,MapSch
{The curve C, Jacobian E, and n-covering map C -> E, determined by the given genus one model. }  
  require Discriminant(model) ne 0 : "Model is singular.";  
  K := BaseRing(model);
  require IsField(K): "Coefficient ring must be a field.";
  p := Characteristic(K);
  n := Degree(model);
  require p notin {2,3,n} : "Coefficient field has characteristic",p;  
  C := Curve(model);
  pi := nCoveringInternal(model,C);
  J := Codomain(pi);
  if E cmpeq 0 then 
    return C,J,pi;
  else
    errormessage:="E must be an elliptic curve isomorphic to the Jacobian of the given model";
    require Type(E) eq CrvEll : errormessage;
    EisoJ, JtoE := IsIsomorphic(J, E);
    require EisoJ : errormessage;
    return C,E,Expand(pi*JtoE);
  end if;
end intrinsic;

intrinsic CoveringMap(model::ModelG1,E::CrvEll) -> MapSch
{The n-covering map C -> E, determined by the given genus one model.}
  _,_,pi := nCovering(model:E := E);
  return pi;
end intrinsic;

intrinsic CoveringMap(C::Crv,E::CrvEll) -> MapSch
{Given a genus one curve C defined by a genus one model of degree n = 2,3,4 or 5, computes the n-covering map C -> E, where E is the Jacobian of C.}
  if ISA(Type(C),CrvEll) then   
    flag,iso := IsIsomorphic(C,E); 
    assert flag;
    return iso;
  end if;
  model := GenusOneModel(C);
  require Discriminant(model) ne 0 : "Model is singular.";  
  K := BaseRing(model);
  require IsField(K): "Coefficient ring must be a field.";
  p := Characteristic(K);
  n := Degree(model);
  require p notin {2,3,n} : "Coefficient field has characteristic",p;  
  pi := nCoveringInternal(model,C);
  J := Codomain(pi);
  if E cmpeq 0 then 
    return pi;
  else
    errormessage:="E must be an elliptic curve isomorphic to the Jacobian of the given model";
    require Type(E) eq CrvEll : errormessage;
    EisoJ, JtoE := IsIsomorphic(J, E);
    require EisoJ : errormessage;
    return pi*JtoE;
  end if;
end intrinsic;

intrinsic Contravariants(model::ModelG1) -> ModelG1, ModelG1
{The contravariants P and Q of the given genus one model.}
  n := model`Degree;
  if n eq 2 then 
    f := model`Equation;
    if VariableWeights(Parent(f)) eq [1,1,2] then 
      f := CompleteTheSquare(f);
    end if;
    R := Parent(f);        
    x := R.1;
    z := R.2;
    h := HessianTwo(f);
    P := Evaluate(f,[-z,x]);
    Q := Evaluate(h,[-z,x]);
    return GenusOneModel(Parent(f)!P), GenusOneModel(Parent(f)!Q);
  elif n eq 3 then
    f := model`Equation;
    P,Q := ContravariantsThree(f);
    b2 := b2InvariantThree(f);
    Q := 4*Q - b2*P;
    return GenusOneModel(Parent(f)!P), GenusOneModel(Parent(f)!Q);
  elif n eq 4 then 
    a,b,c,d,e := Explode(SL4Invariants(model));
    TT := SL4Contravariants(model);
    PP := [[6*e,-3*d,c,-3*b],[-3*d,c,-3*b,6*a]];
    QQ := [[6*(2*c*e-3*d^2),3*(-6*b*e+c*d),12*a*e+6*b*d-c^2,3*(-6*a*d+b*c)],
           [3*(-6*b*e+c*d),12*a*e+6*b*d-c^2,3*(-6*a*d+b*c),6*(2*a*c-3*b^2)]];
    P := [&+[PP[i][j]*TT[j] : j in [1..4]] : i in [1..2]];
    Q := [&+[QQ[i][j]*TT[j] : j in [1..4]] : i in [1..2]];
    return GenusOneModel(P), GenusOneModel(Q);
  else
    B := BaseRing(PolynomialRing(model));
    require IsDomain(B) : "Coefficient ring must be an integral domain.";
    p := Characteristic(B);
    require p notin {2,5} : "Coefficient ring has characteristic",p;
    K := FieldOfFractions(B);
    modelK := ChangeRing(model,K);
    require Discriminant(model) ne 0 :"Model is singular.";
    P,Q := ContravariantsFive(modelK`DefiningMatrix);
    return GenusOneModel(ChangeRing(P,PolynomialRing(model))), 
           GenusOneModel(ChangeRing(Q,PolynomialRing(model)));
  end if;
end intrinsic;

intrinsic HesseCovariants(model::ModelG1,r::RngIntElt) -> ModelG1, ModelG1
{Covariants describing a twist of the Hesse family, for a given genus one model.}
  n := model`Degree;
  require GCD(r,n) eq 1: r,"and",n,"are not coprime.";
  if n in {2,3} then
    f := model`Equation;
    if VariableWeights(Parent(f)) eq [1,1,2] then 
      f := CompleteTheSquare(f);
    end if;
    if r mod n eq 1 then 
      U1 := model;
      U2 := Hessian(model);
    else
      U1,U2 := Contravariants(model);
    end if;
    return U1,U2;
  end if;

  require n eq 4 or Discriminant(model) ne 0 :"Model is singular.";
  r := r mod n;
  if n eq 4 and r eq 1 then 
    U1 := model;
    U2 := Hessian(model);
  elif n eq 4 and r eq 3 then 
    U1,U2 := Contravariants(model);
  elif n eq 5 then 
    phi := model`DefiningMatrix;
    case r:
      when 1: U1 := model;
              U2 := Hessian(model);
      when 2: U1,U2 := CovariantsTwistTwo(phi);
              U1,U2 := Explode([ GenusOneModel(cov) : cov in [U1,U2] ]);
      when 3: U1,U2 := CovariantsTwistThree(phi);
              U1,U2 := Explode([ GenusOneModel(cov) : cov in [U1,U2] ]);
      when 4: U1,U2 := Contravariants(model);
    end case;
  end if;
  return U1,U2;
end intrinsic;

/*
intrinsic OmegaMatrix(phi::ModMatRngElt) -> ModMatRngElt
{A covariant describing the invariant differential.}
  flag,n := IsGenusOneModel(phi);
  require flag and n eq 5 : "phi must be a genus one model of degree 5.";
  return OmegaMatrixFive(phi);
end intrinsic;
*/

intrinsic DoubleGenusOneModel(model::ModelG1) -> ModelG1
{Given a genus one model of degree 4 or 5, this function 
computes 2 times the associated element in the Weil-Chatelet group,
and returns the associated genus one model.}
  n := model`Degree;
  require n in {4,5} : "phi must be a genus one model of degree 4 or 5.";
  if n eq 4 then return DoubleSpaceQuartic(model); end if;
  c4,c6 := Explode(cInvariants(model));
  P,Q := Contravariants(model);
  return GenusOneModel( (c6*P`DefiningMatrix-c4*Q`DefiningMatrix)/144 );
end intrinsic;
 




