freeze;

///////////////////////////////////////////////////////////////////////////
// Simple program for reduction of point clusters
//
// Andreas-Stephan Elsenhans, Michael Stoll 
// March 2011
// 
// Intrinsics: ReduceCluster(vecs), ReducePlaneCurve
// TO DO: add ReduceCluster(Clstr)
///////////////////////////////////////////////////////////////////////////

import "../SrfDP/minred.m": PointsOfIdeal, MyKernelVector;
 
declare verbose ClusterReduction, 3;

function MatExp(mat : eps := 1e-6)
  n := NumberOfRows(mat);
  // matrix exponential
  result := Parent(mat)!1;
  k := 1;
  m := result;
  while (Real((v, v)) where v := Vector(Eltseq(m))) gt eps^2 do
    m *:= 1/k*mat;
    result +:= m;
    k +:= 1;
    vprintf ClusterReduction,3: ".";
  end while;
  vprintf ClusterReduction,3: "\n";
  return result;
end function;

// Points are given by coordinate vectors over a complex field

// TO DO: handle bad situations 
// (for a start, check for things like repeated vectors)

intrinsic ReduceCluster(S :: SeqEnum: eps := 1e-6, c := 1) -> SeqEnum,Mtrx,Mtrx
{Given a sequence of complex vectors representing points in projective space,
this returns a reduced cluster, together with the transformation and its inverse}

  cluster0 := S;
  if Precision(BaseRing(Universe(cluster0))) lt 30 then
    C := ComplexField(30);
    cluster0 := [ChangeRing(v,C) : v in cluster0];
  end if;

  require forall{v : v in S | not IsZero(v)}:
    "The given vectors must be nonzero (representing points in projective space)";

  // first normalize the points
  cluster := [s*pt where s := 1/Sqrt((pt,pt)) : pt in cluster0];
  // now ||P|| = 1 for all points
  n := Dimension(Universe(cluster));
  m := #cluster;
  // iterate until derivative is sufficiently small
  C := Parent(cluster[1][1]);
  c := C!c;
  Tr := IdentityMatrix(C, n);
  count := 0;
  while true do
    cols := [Vector([cluster[j][i] : j in [1..m]]) : i in [1..n]];
    // determine derivative
    der1 := [Real((col, col)) : col in cols];
    der2 := [[2*Real((cols[i], cols[j])) : j in [1..i-1]] : i in [1..n]];
    der1 := [d-t : d in der1] where t := &+der1/n;
    absd := &+[d^2 : d in der1 cat &cat der2];
    vprintf ClusterReduction,2: "|der| = %o\n", ChangePrecision(absd, 10);
    if absd lt eps^2 then break; end if;
    // vprintf ClusterReduction: "der1 = %o\n", der1;
    // vprintf ClusterReduction: "der2 = %o\n", der2;
    B1 := SymmetricMatrix(C, &cat[Append(der2[i], der1[i]) : i in [1..n]]);
    // vprintf ClusterReduction: "Trace(B1) = %o\n", Trace(B1);
    // c1 := Min(c, 10*c/absd);
    B := MatExp(-c*B1 : eps := eps*1e-10);
    B *:= Real(Determinant(B))^(-1/n);
    // vprintf ClusterReduction: "B = %o\n", B;
    cluster1 := [pt*B : pt in cluster];
    Tr := Tr*B;
    // evaluate function
    val := &+[Log(Real((pt, pt))) : pt in cluster1];
    vprintf ClusterReduction,2: "gain = %o\n", ChangePrecision(val, 10);
    if val gt 0 then
      // halve c
      c /:= 2;
      vprintf ClusterReduction,1: "  ==> new c = %o\n\n", ChangePrecision(c, 10);
    else
      vprintf ClusterReduction,2: "\n";
      count +:= 1;
      if count eq 10 then
        count := 0;
        // use original input and accumulated transformation
        Tr *:= Real(Determinant(Tr))^(-1/n);
        cluster1 := [pt*Tr : pt in cluster0];
      end if;
      // re-normalize
      cluster := [s*pt where s := 1/Sqrt((pt,pt)) : pt in cluster1];
    end if;
  end while;
/* The covariant is Tr*Transpose(Tr); */

 Tr := ChangeRing(Tr * Transpose(Tr), RealField(Precision(Parent(cluster0[1][1]))));
 Tr := (Tr + Transpose(Tr))/2;
 Trr, U1 := LLLGram(Tr);
 U1_inv := U1^(-1);
 
 return [v * ChangeRing(U1_inv,BaseRing(v)) : v in cluster0], U1_inv, U1;
end intrinsic;


intrinsic ReducePlaneCurve(C :: Crv) -> Crv, Mtrx
{Given a plane curve this computes a reduced model, by reducing the
point cluster given by the intersection points with its hessian}
 
 Pr2 := AmbientSpace(C);
 require IsProjective(Pr2) and Dimension(Pr2) eq 2: 
        "The argument must be a projective plane curve";
 require Degree(C) ge 3: "Curve must have at least degree 3";

 f, Trr := ReducePlaneCurve(Equation(C));
 return Curve(Pr2, f), Trr;
end intrinsic;

intrinsic ReducePlaneCurve(f :: RngMPolElt) -> RngMPolElt, Mtrx
{"} // "
 require TotalDegree(f) ge 3:"Curve must have at least degree 3\n";
 require IsHomogeneous(f):"Polynomial must be homogeneous.\n";
 require Rank(Parent(f)) eq 3:"Polynomial must have 3 variables.\n";

 mul := 3;
 prec := Round(100 + 4 * Log(1+Max([AbsoluteValue(i) : i in Coefficients(f)])));
 repeat
  mul := mul^2;
  vprintf ClusterReduction,1: "Starting reduction using precision %o\n",prec; 
  CC := ComplexField(prec);
  hes := Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..3]] : j in [1..3]]));

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1 - 1 >;
  i := GroebnerBasis(id);
  pl := PointsOfIdeal(id,CC);

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2, Parent(f).3-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  pts := [Vector([ChangePrecision(pl[i][j], prec div 2) : j in [1..3]]) : i in [1..#pl]];
  vprintf ClusterReduction,1:"Calling cluster reduction\n"; 
  _,_,Trr := ReduceCluster(pts : eps := 10^(-prec div  20));

  res := f^ChangeRing(Transpose(Trr), BaseRing(Parent(f)));  
  prec := prec * 2;
 until Max([AbsoluteValue(a) : a in Coefficients(res)]) le mul * Max([AbsoluteValue(a) : a in Coefficients(f)]);
  
 if Max([AbsoluteValue(a) : a in Coefficients(res)]) ge Max([AbsoluteValue(a) : a in Coefficients(f)]) then
  vprintf ClusterReduction,1:"Reduction without effect %o\n",res;
  return f,IdentityMatrix(BaseRing(Parent(f)),3);
 end if;

 return res,Transpose(Trr);
end intrinsic;

