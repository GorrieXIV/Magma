
freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//             Exterior powers of differential operators          //
//                               by                               //
//                            Nils Bruin                          // 
//                                                                //
////////////////////////////////////////////////////////////////////


//
// If this ever becomes an intrinsic the name should be changed
// to a more appropriate one.
// Main body written by Nils Bruin.
function MultipleExtension(L,d)
    // Make a formal differential ring with d independent solutions of L
    // and their derivatives as variables.
  assert ISA(Type(L), RngDiffOpElt);
  F:=BaseRing(Parent(L));
  assert IsDifferentialRing(F);
  r:=Degree(L);
  P:=PolynomialRing(F,d*r);
  cfs:=Eltseq(L);
  lst:=[];
    // Make a list containing the images of [y1, Dy1, D^2y1,...,y2, Dy2,...].
  for j in [0..r*(d-1) by r] do
    lst cat:=[P|P.(j+i) : i in [2..r]] 
               cat [-&+([cfs[i]*P.(j+i):i in [1..r]])/cfs[r+1]];
  end for;
  E:=DifferentialRingExtension(lst);
    // Return the extension ring and the r independent generators.
    // Note that D(E.1)=E.2, and D(E.r+1)=E.r+2, etc.
  return E,[E.j: j in [1..r*d by r]];
end function;  

// 
// Main body written by Nils Bruin.
// Some edits made by Alexa van der Waall.
intrinsic ExteriorPower(L::RngDiffOpElt,d::RngIntElt:MinimalDegree:=true) -> 
    RngDiffOpElt
  {The d-th exterior power of L. As default the monic operator with minimal 
   degree is returned.}
    // By definition the d-th exterior power is of minimal degree,
    //   see V.d. Put - Singer, Galois theory of linear differential
    //   equations, Definition 2.26. 
  R := Parent(L);
  require IsDifferentialField(BaseRing(R)):
    "The operator must be defined over a differential field.";
  require d gt 0:
    "The second argument must be a positive integer.";
  degL := Order(L);
  require degL ge 0:
    "The operator must be non-zero";     
  if d gt degL then
    return (R!1);
  end if;   
    // Get d formal solutions of L and compute their Wronskian determinant. 
  E,ys:=MultipleExtension(L,d);
  Z:=WronskianDeterminant(ys);
    // We define co as the number of coefficients in the new operator.
    // It is one more than the dimension of the exterior power space.   
  co:=Binomial(degL,d)+1;
    // The derivatives of the wronskian.
  cfs:=[i eq 1 select Z else Derivation(E)(Self(i-1)): i in [1..co]];
  mons:=Setseq(&join[Seqset(Monomials(l)):l in cfs]);
    // Per coefficient make a row w.r.t to all monomials appearing.
  if MinimalDegree then
    eqs:=Matrix([[MonomialCoefficient(l,m): m in mons]:l in Reverse(cfs)]);
  else      
    eqs:=Matrix([[MonomialCoefficient(l,m): m in mons]:l in cfs]);
  end if;  
  sol:=Basis(Kernel(eqs));
  print "Dimension of the solution space of exterior operators:", #sol; 
  error if #sol eq 0, "Exterior power could be computed."; 
  if MinimalDegree then
      // You should have ended up with monic operators.
    op := R!Reverse(Eltseq(sol[#sol]));
    basis := [R| Reverse(Eltseq(v)): v in sol];
  else  
    op := MonicDifferentialOperator(R!(Eltseq(sol[#sol])));
    basis := [R| MonicDifferentialOperator(R!Eltseq(v)): v in sol];
  end if;  
    //The following is a silly and potentially expensive test.
  ER:=DifferentialOperatorRing(FieldOfFractions(E));
  assert (ER!op)(Z) eq 0;
  return op, basis;
end intrinsic;







