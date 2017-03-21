freeze;
 
 
import "ForOtherTypes.m" : ReplaceColumn;


////////////////////////////////////////////////////////////////////
//                                                                //
//           Differential Operators GCD's and LCM's               //
//                               by                               //
//                      Alexa van der Waall                       // 
//                                                                //
//                    Created on 01 July 2009                     //
//                                                                //
////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////
//                                                                //
//               Euclidean Algorithms and GCD's                   //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic EuclideanRightDivision(Num::RngDiffOpElt,Den::RngDiffOpElt)->
      RngDiffOpElt, RngDiffOpElt
  {Operators Q (quotient) and R (remainder) are obtained with 
      Num = Q*Den + R, Degree(R) < Degree(Den). Returns Q, R, if they
      exists, otherwise returns an error message.}
  require Parent(Num) cmpeq Parent(Den): 
    "Arguments have distinct parents."; 
  n:=Degree(Num);
  d:=Degree(Den);
  W:=Parent(Num);  
  require d gt -1:
    "Division by zero.";   
////////////////////
/******
  bl, invLCDen := IsInvertible(LeadingCoefficient(Den));
  if d gt -1 then
    require bl:
      "The leading coefficient of the second argument is not invertible.";
  end if;
******/
////////////////////
  assert IsField(BaseRing(W));
  if n eq -1 and d gt -1 then
    return W!0, W!0;        
  elif n eq 0 and d eq 0 then
    return W!(Coefficient(Num,0)/Coefficient(Den,0)), W!0;     
  elif n lt d then 
    return W!0, Num;
  end if;  
  assert d gt -1;
  invLCDen:=1/LeadingCoefficient(Den);
  D:=W.1;
  Q:=W!0;
  R:=Num;
  while Degree(R) ge d do
    S:=LeadingCoefficient(R)*invLCDen*D^(Degree(R)-d); 
    S:=W!S;
    Q:=Q+S;       
      // R:=R-S*Den;
    prod := S*Den;
      // Highest order terms of R and -S*Den need to cancel.
    assert IsWeaklyZero(LeadingCoefficient(R)-LeadingCoefficient(prod));
    seqdifference := Eltseq(R-prod);
    order := Minimum([#seqdifference, Degree(R)]);
    R:=Parent(R)![seqdifference[i]: i in [1..order]];   
      // Is operator of order le Degree(R)-1.   
       // CHANGE IMPLEMENTATION FOR C OR R.
       // ORDER OF MULTIPLICATION IS CORRECT.
  end while;
    // In the case that we have a series ring:
    // the precision of the leading coefficient of Q is the minimum of
    // the ring precision and the precision of the LC(R), or -1. 
  return Q,R;
end intrinsic;

intrinsic EuclideanLeftDivision(Den::RngDiffOpElt,Num::RngDiffOpElt)->
      RngDiffOpElt, RngDiffOpElt
  {Operators Q (quotient) and R (remainder) are obtained with 
      Num = Den*Q + R, Degree(R) < Degree(Den). Returns Q, R, if they
      exists, otherwise returns an error message.}
  require Parent(Num) cmpeq Parent(Den): 
    "Arguments have distinct parents.";
  n:=Degree(Num);
  d:=Degree(Den);
  W:=Parent(Num); 
  require d gt -1:
    "Division by zero.";      
////////////////////
/******
  bl, invLCDen := IsInvertible(LeadingCoefficient(Den));
  if d gt -1 then
    require bl:
      "The leading coefficient of the second argument is not invertible.";
  end if;
******/
//////////////////// 
  assert IsField(BaseRing(W));  
  if n eq -1 and d gt -1 then
    return W!0, W!0; 
  elif n eq 0 and d eq 0 then
    return W!(Coefficient(Num,0)/Coefficient(Den,0)), W!0;     
  elif n lt d then 
    return W!0, Num;
  end if;  
  assert d gt -1;
  invLCDen:=1/LeadingCoefficient(Den);
  D:=W.1;
  Q:=W!0;
  R:=Num;
  while Degree(R) ge d do
    S:=LeadingCoefficient(R)*invLCDen*D^(Degree(R)-d);     
    S:=W!S;
    Q:=Q+S;                             
      // R:=R-Den*S;       
    prod := Den*S;
      // Highest order terms of R and -Den*S need to cancel.
    assert IsWeaklyZero(LeadingCoefficient(R)-LeadingCoefficient(prod));
    seqdifference := Eltseq(R-prod);
    order := Minimum([#seqdifference, Degree(R)]);
    R:=Parent(R)![seqdifference[i]: i in [1..order]];   
      // Is operator of order le Degree(R)-1.    
       // CHANGE IMPLEMENTATION FOR C AND R.
       // ORDER OF MULTIPLICATION IS CORRECT.
  end while;
  return Q,R;
end intrinsic;

intrinsic GreatestCommonRightDivisor(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt
  {Returns monic GCRD Operator G.} 
    // This means that the leading coefficient is:
    //   * 0 if G is 0,
    //   * 1 otherwise.
    // This algorithm does not work in Characteristic 2.     
  require Parent(A) cmpeq Parent(B): 
    "Arguments have distinct parents.";
  require IsField(BaseRing(Parent(A))):
    "The BaseRing of the operators must be a field.";
  degA:=Degree(A);
  degB:=Degree(B);  
  W:=Parent(A);      
   if degA eq -1 and degB eq -1 then
     return W!0;      
   elif degA eq -1 and degB gt -1 then
     return (1/(LeadingCoefficient(B)))*B; 
   elif degA gt -1 and degB eq -1 then
     return (1/(LeadingCoefficient(A)))*A; 
   elif degA eq 0 and degB eq 0 then
     return W!1; 
       // THIS WOULD NOT WORK IN CHAR=2.
   end if;
   if degA ge degB then
     AA:=A;
     BB:=B;
   else
     AA:=B;
     BB:=A;
   end if;  
   U:=W!1;
   G:=AA;
   V1:=W!0;
   V3:=BB;
   while V3 ne W!0 do
     Q,R :=  EuclideanRightDivision(G,V3); 
     T:=W!(U-Q*V1); 
     U:=V1;
     G:=V3;
     V1:=T;
     V3:=R;
   end while;
   return (1/LeadingCoefficient(G))*G;
end intrinsic;

// abbreviation of the one above.
intrinsic GCRD(A::RngDiffOpElt,B::RngDiffOpElt)-> RngDiffOpElt
  {Returns monic GCRD Operator G.} 
  return GreatestCommonRightDivisor(A,B);
end intrinsic;  

intrinsic GreatestCommonLeftDivisor(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt
  {Returns monic GCLD Operator G.} 
    // This means that the leading coefficient is:
    //   * 0 if G is 0,
    //  * 1 otherwise.
    // This algorithm does not work in Characteristic 2.     
  require Parent(A) cmpeq Parent(B): 
    "Arguments have distinct parents.";
  require IsField(BaseRing(Parent(A))):
    "The BaseRing of the operators must be a field.";
  degA:=Degree(A);
  degB:=Degree(B);  
  W:=Parent(A);      
   if degA eq -1 and degB eq -1 then
     return W!0;      
   elif degA eq -1 and degB gt -1 then
     return B*W!(1/(LeadingCoefficient(B))); 
   elif degA gt -1 and degB eq -1 then
     return A*W!(1/(LeadingCoefficient(A))); 
   elif degA eq 0 and degB eq 0 then
     return W!1; 
       // THIS WOULD NOT WORK IN CHAR=2.
   end if;
   if degA ge degB then
     AA:=A;
     BB:=B;
   else
     AA:=B;
     BB:=A;
   end if;  
   U:=W!1;
   G:=AA;
   V1:=W!0;
   V3:=BB;
   while V3 ne W!0 do
     Q,R :=  EuclideanLeftDivision(V3,G); 
     T:=W!(U-V1*Q); 
     U:=V1;
     G:=V3;
     V1:=T;
     V3:=R;
   end while;
   return G*W!(1/LeadingCoefficient(G));
end intrinsic;

// abbreviation of the one above.
intrinsic GCLD(A::RngDiffOpElt,B::RngDiffOpElt)-> RngDiffOpElt
  {Returns monic GCLD Operator G.} 
  return GreatestCommonLeftDivisor(A,B);
end intrinsic; 

intrinsic ExtendedGreatestCommonRightDivisor(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt, RngDiffOpElt, RngDiffOpElt
  {Returns Operators G,U,V with U*A+V*B=G, where G is the monic Right GCD
   of A and B.} 
    // This means that the leading coefficient is:
    //  * 0 if G is 0,
    //  * 1 otherwise.
    // This algorithm does not work in Characteristic 2.
  require Parent(A) cmpeq Parent(B): 
    "Arguments have distinct parents.";  
  require IsField(BaseRing(Parent(A))):
    "The BaseRing of the operators must be a field.";    
  degA:=Degree(A);
  degB:=Degree(B);  
  R:=Parent(A);      
   if degA eq -1 and degB eq -1 then
     return R!0, R!1, R!1;      
   elif degA eq -1 and degB gt -1 then
     return R!(1/(LeadingCoefficient(B))*B),
               R!1, R!(1/(LeadingCoefficient(B)));
   elif degA gt -1 and degB eq -1 then
     return R!(1/(LeadingCoefficient(A))*A),
               R!(1/(LeadingCoefficient(A))), R!1; 
   elif degA eq 0 and degB eq 0 then
     return R!1, R!(1/(2*LeadingCoefficient(A))), 
              R!(1/(2*LeadingCoefficient(B)));
       // THIS WOULD NOT WORK IN CHAR=2.
   end if;
   if degA ge degB then
     AA:=A;
     BB:=B;
   else
     AA:=B;
     BB:=A;
   end if;
   U1:=R!1;
   V1:=R!0;
   G1:=AA;   
   U2:=R!0;
   V2:=R!1;
   G2:=BB;
   while G2 ne R!0 do
     U0:=U1;
     V0:=V1;
     G0:=G1; 
     U1:=U2;
     V1:=V2;
     G1:=G2;
     Q,G2 :=  EuclideanRightDivision(G0,G1); 
     if G2 ne R!0 then     
       U2:=U0-Q*U1; 
       V2:=V0-Q*V1; 
     end if;
   end while;   
   scalarG:=1/LeadingCoefficient(G1);
   if degA ge degB then
     return scalarG*G1, scalarG*U1, scalarG*V1;
     // Multiplication with scalars is this easy since we have U and V 
     // on the left side.
   else
     return scalarG*G1, scalarG*V1, scalarG*U1;
   end if;                  
end intrinsic;

intrinsic ExtendedGreatestCommonLeftDivisor(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt, RngDiffOpElt, RngDiffOpElt
  {Returns Operators G,U,V with A*U+B*V=G, where G is the monic Left GCD
   of A and B.}        
    // This means that the leading coefficient is:
    //  * 0 if G is 0,
    //  * 1 otherwise.
    // This algorithm does not work in Characteristic 2.
  require Parent(A) cmpeq Parent(B): 
    "Arguments have distinct parents.";
  require IsField(BaseRing(Parent(A))):
    "The BaseRing of the operators must be a field.";
  degA:=Degree(A);
  degB:=Degree(B);  
  R:=Parent(A);      
   if degA eq -1 and degB eq -1 then
     return R!0, R!1, R!1;      
   elif degA eq -1 and degB gt -1 then
     return B*R!(1/(LeadingCoefficient(B))),
                R!1, R!(1/(LeadingCoefficient(B)));
   elif degA gt -1 and degB eq -1 then
     return A*R!(1/(LeadingCoefficient(A))),
                R!(1/(LeadingCoefficient(A))), R!1; 
   elif degA eq 0 and degB eq 0 then
     return R!1, R!(1/(2*LeadingCoefficient(A))), 
              R!(1/(2*LeadingCoefficient(B)));
       // THIS WOULD NOT WORK IN CHAR=2.
   end if;
   if degA ge degB then
     AA:=A;
     BB:=B;
   else
     AA:=B;
     BB:=A;
   end if;
   U1:=R!1;
   V1:=R!0;
   G1:=AA;   
   U2:=R!0;
   V2:=R!1;
   G2:=BB;
   while G2 ne R!0 do
     U0:=U1;
     V0:=V1;
     G0:=G1; 
     U1:=U2;
     V1:=V2;
     G1:=G2;
     Q,G2 :=  EuclideanLeftDivision(G1,G0); 
     if G2 ne R!0 then     
       U2:=U0-U1*Q; 
       V2:=V0-V1*Q; 
     end if;
   end while;
   scalarG:=R!(1/LeadingCoefficient(G1));
   if degA ge degB then
     return G1*scalarG, U1*scalarG, V1*scalarG;
   else
     return G1*scalarG, V1*scalarG, U1*scalarG;
   end if;                  
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                            LCLM's                              //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic ExtendedLeastCommonLeftMultiple(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt, RngDiffOpElt, RngDiffOpElt
  {Returns L,Q,R, with monic LCLM Operator L = Q*A = R*B.} 
    // This means that the leading coefficient is:
    //   * 0 if L is 0,
    //   * 1 otherwise,
    // and that L=Q*A=R*B, for certain operators Q and R.
    // It is know that degree(L)<= degree(A)+degree(B).
    // Writing Q and R up to degree degree(B) and degree(A), respectively,
    // as operators with unknown coefficients induces a linear system
    // of equations. 
    // In matrix form this system looks naturally like v*M =0, where
    // v = Elsseq(Q) cat Eltseq (R) and M is a matrix with coefficients
    // in ConstantField(A)=ConstantField(B).
    // However, we choose to reverse the order of the sequences
    // to obtain an equivalent system w*N=0,where
    // v = Reverse(Elsseq(Q)) cat Reverse(Eltseq (R)).
    // The reason for this is that the Null space of N is given in an Echelon 
    // form, always. Then the last vector in the space corresponds to 
    // the operators Q and R of smallest degree.   
  require Parent(A) cmpeq Parent(B): 
    "Arguments have distinct parents.";
  require IsField(BaseRing(Parent(A))):
    "The BaseRing of the operators must be a field.";
  degA:=Degree(A);
  degB:=Degree(B);  
  W:=Parent(A);
  D:=W.1;   
  if degA eq -1 or degB eq -1 then
    return W!0, W!0, W!0;      
  elif degA eq 0 and degB eq 0 then
    F :=BaseRing(W);
    return W!1, W!(1/(F!Coefficient(A,0))), W!(1/(F!Coefficient(B,0))); 
  end if;  
    // Construct the matrix N and its nullspace.
  K:=BaseRing(W);
  rowdim:=degA+degB+1;
    // Remark: if we would know the degree of the greatest common right(!)
    // divisor than rowdim:= degA+degB-degree(GCRD)+1.
  rowop:=A;
  seqop:=Eltseq(rowop);
  row:=[K!0 : i in [1..degB]] cat Reverse(seqop); 
  mat1:=Matrix(K,1,rowdim,row);    
  for deg in [1..degB] do
    rowop:=D*rowop;
    seqop:=Eltseq(rowop);
    row:=[K!0 : i in [1..degB-deg]] cat Reverse(seqop); 
    mat1:=VerticalJoin(Matrix(K,1,rowdim,row),mat1);
  end for;
  rowop:=-B;
  seqop:=Eltseq(rowop);
  row:=[K!0 : i in [1..degA]] cat Reverse(seqop); 
  mat2:=Matrix(K,1,rowdim,row);
  for deg in [1..degA] do
    rowop:= D*rowop;
    seqop:=Eltseq(rowop);
    row:=[K!0 : i in [1..degA-deg]] cat Reverse(seqop); 
    mat2:=VerticalJoin(Matrix(K,1,rowdim,row),mat2);
  end for;   
  N:=VerticalJoin(mat1,mat2);
  
  Z:=NullSpace(N); 
  basisZ:=Basis(Z); 
  lastvector:=Eltseq(basisZ[#basisZ]); 
  VA:=Reverse(lastvector[1..degB+1]); 
  VB:=Reverse(lastvector[degB+2..rowdim+1]); 
return (W!VA)*A, W!VA, W!VB;
end intrinsic;

intrinsic ExtendedLeastCommonLeftMultiple(S::[RngDiffOpElt])->
     RngDiffOpElt, SeqEnum
  {Returns L,Q, with monic LCLM Operator L = Q[i]*S[i], for i in 1,2,..#S.} 
    // This means that the leading coefficient is:
    //   * 0 if L is 0,
    //   * 1 otherwise,
    // and that L=Q[i]*S[i], for certain operators Q[i].
    // It is know that degree(L)<= degree(S[1])+...degree(S[#S]).
  require #S ge 1:
    "The sequence must be non-empty.";
  require IsField(BaseRing(Universe(S))):
    "The BaseRing of the operators must be a field.";
  W:=Universe(S);
  degs:=[Integers()|Degree(s): s in S];
  if Minimum(degs) eq -1 then
    return W!0, [W|0:i in [1..#S]]; 
  elif #S eq 1 then
    lc := LeadingCoefficient(S[1]); 
    return (1/lc)*S[1], [W|1/lc];      
  elif Minimum(degs) eq 0 and Maximum(degs) eq 0 then
    F:=BaseRing(W);
    return W!1, [W| 1/(F!Coefficient(S[i],0)) : i in [1..#S]]; 
  end if;    
  L, Q1, Q2:=ExtendedLeastCommonLeftMultiple(S[1],S[2]);
  Q:=[Q1,Q2];
  for i in [3..#S] do
    Lnew, T1, T2 := ExtendedLeastCommonLeftMultiple(L,S[i]);
    Q:=[T1*Qi:Qi in Q];
    Append(~Q,T2);
    L:=Lnew;
  end for;
return L, Q;
end intrinsic;

intrinsic LeastCommonLeftMultiple(A::RngDiffOpElt,B::RngDiffOpElt)->
     RngDiffOpElt
  {Returns monic LCLM Operator L of A and B.} 
  require Parent(A) cmpeq Parent(B): "Arguments have distinct parents.";
  L,Q,R:=ExtendedLeastCommonLeftMultiple(A,B);
  return L;
end intrinsic;

// abbreviation of the one above.
intrinsic LCLM(A::RngDiffOpElt,B::RngDiffOpElt)-> RngDiffOpElt
  {Returns monic LCLM Operator L of A and B.} 
  return LeastCommonLeftMultiple(A,B);
end intrinsic;

// This only works for a direct extension, but might be implemented for towers.
// Does not work for differential laurent series ring as we cannot calculate
// a minimum polynomial.
// Note: This intrinsic uses the coercion map. 
intrinsic LeastCommonLeftMultiple(L::RngDiffOpElt) -> RngDiffOpElt
  {If L = D-r, where L is an operator in R=F[D], compute the LCLM of
   L and all its conjugates by using the coercion BaseRing(F) -> F.} 
     // Note: if r is algebraic of degree d, then the LCLM is also of degree d.
  R:=Parent(L);
  F:=BaseRing(R);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";
  require IsMonic(L) and Degree(L) eq 1:
    "The operator is not monic of degree 1.";
  bl, K := HasAttribute(F, "BaseField");
  require bl:
      "No basefield found.";
  require IsAlgebraicDifferentialField(K):
    "The  base field of differential operator is not an extension of",
    "an algebraic differential field.";
  mp := Coercion(K,F);
  r:=-Coefficient(L,0);  
  f:=MinimalPolynomial(r); 
  assert BaseRing(Parent(f)) eq K;   
  d:=Degree(f);
  if d eq 1 then
    return L;
  end if;
    // if derivation(r) =0, then der(sigma(r))=sigma(der(r))=0,
    // for any galois map sigma.
    // Also the multiplication (D-r)(D-sigma(r)) is commutative.
    // So the minimal polynomial is the LCLM. 
  if Derivation(F)(r) eq F!0 then
    return R![mp(v): v in Eltseq(f)];
  end if;
  dim:=d^2;
  M:= ZeroMatrix(K,dim,dim);
    // the matrix related to the right hand factor.
  zeromatrix := ZeroMatrix(K,d,d);
  rightopmatrix := zeromatrix;
    // Insert submatrices belonging to the right hand factor we want to compute.
    // It should not have any powers of r in the coefficients.
  for i in [0 .. d-1] do
    rightopmatrix[1,i+1]:= K!1;
    M:=InsertBlock(M,rightopmatrix,i*d+1,1);
    rightopmatrix := zeromatrix;
  end for;
    // the matrix related to -[1,r,...,r^(d-1)]*D.
  idmatrix :=-IdentityMatrix(K,d);
     // insert submatrices belonging to -[1,r,...,r^(d-1)]*D^i *D.
  for i in [0 .. d-2] do  
    M:=InsertBlock(M,idmatrix,(i+1)*d+1,(i+1)*d+1); 
  end for;
     // the matrix related to [1,r,...,r^(d-1)]*D^0*(r).
  derivmatrix:= Transpose(CompanionMatrix(f)); 
  M:=InsertBlock(M,derivmatrix,1,d+1);
  derivop := R!r; 
  for i in [1.. d-2] do
    N:=ZeroMatrix(K, d*(i+1), d);
    derivop := (R.1)*derivop;
      // So this is D^i*r.
    for j in [0 .. i] do
      c:=Coefficient(derivop,j);
        // this is a polynomial in r.
      V:=ZeroMatrix(K,d,d);
      for m in [0..d-1] do
        seqpol:= Eltseq(r^m*c); 
        V := ReplaceColumn(V,m+1,seqpol); 
      end for;
      N := InsertBlock(N,V, d*j+1,1);
    end for;
  M:=InsertBlock(M,N,1,(i+1)*d+1);
  end for; 
  derivop := (R.1)*derivop;
    // So this is D^(d-1)*r.
  seqop:=Eltseq(derivop) cat [F|0 : i in [Degree(derivop)+2..d]];
    // seqop has universe F. 
  seq := [K|];
  for c in seqop do
    seq := seq cat Eltseq(c);
  end for;
  V:= -Transpose(Matrix([seq]));  
  hassolution, S, N := IsConsistent(Transpose(M),Transpose(V));
  require hassolution: "Can not compute the operator.";
  require (Dimension(N) eq 0): "Cannot find unique operator.";
  S:=Eltseq(S);
  assert Universe(S) eq K;
  op := R![F| mp(S[i]) : i in [1..d]] + (R.1)^d;
  return op;
end intrinsic;





////////////////////////////////////////////////////////////////////
//                                                                //
//                              End                               //
//                                                                //
////////////////////////////////////////////////////////////////////

