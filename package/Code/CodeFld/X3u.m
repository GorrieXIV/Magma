freeze;

/* variations of ConstructionX
 
   v1.0 19.04.2002
   
   Markus Grassl
   IAKS
   Universitaet Karlsruhe
   Germany
   e-mail: grassl@ira.ua.de


*/

intrinsic ConstructionX3u(C1::CodeLinFld,C2::CodeLinFld,C3::CodeLinFld,D1::CodeLinFld,D2::CodeLinFld)->CodeLinFld,CodeLinFld
{Given two chains of codes C1=[n,k1] > C2=[n,k2] > C3=[n,k3] and D1=[n',k1-k3] > D2=[n',k2-k3], construct codes C=[n+n',k1] > C'=[n+n',k2] using Construction X with C1, C3, and D1 resp. C2, C3, and D2}

  F:=Alphabet(C1);
  n:=Length(C1);

  require Length(C2) eq n and Length(C3) eq n:
    "The first three codes must have the same length";

  require Alphabet(C2) cmpeq F and Alphabet(C3) cmpeq F and
          Alphabet(D1) cmpeq F and Alphabet(C2) cmpeq F:
    "All codes must have the same alphabet";

  require C2 subset C1:
    "C2 must be a subcode of C1";

  require C3 subset C2:
    "C3 must be a subcode of C2";

  n1:=Length(D1);

  require Length(D2) eq n1:
    "D1 and D2 must have the same length";

  require D2 subset D1:
    "D2 must be a subcode of D1";

  k1:=Dimension(C1);
  k2:=Dimension(C2);
  k3:=Dimension(C3);

  require Dimension(D1) eq k1-k3:
    "The sum of the dimensions of D1 and C3 must equal the dimension of C1";

  require Dimension(D2) eq k2-k3:
    "The sum of the dimensions of D2 and C3 must equal the dimension of C2";

  G:=Zero(KMatrixSpace(F,k1,n+n1));
  cosetsC1C2:=BasisMatrix(Complement(VectorSpace(C1),VectorSpace(C2)));
  cosetsC2C3:=BasisMatrix(Complement(VectorSpace(C2),VectorSpace(C3)));

  InsertBlock(~G,GeneratorMatrix(C3),1,1);
  InsertBlock(~G,cosetsC2C3,k3+1,1);
  InsertBlock(~G,cosetsC1C2,k2+1,1);

  cosetsD1D2:=BasisMatrix(Complement(VectorSpace(D1),VectorSpace(D2)));
  InsertBlock(~G,GeneratorMatrix(D2),k3+1,n+1);
  InsertBlock(~G,cosetsD1D2,k2+1,n+1);
 
  C:=LinearCode(G);
  D:=sub<C|LinearCode(Submatrix(G,1,1,k2,n+n1))>;
  //bounds?

  return C,D;

end intrinsic;

intrinsic ConstructionXChain(S::[CodeLinFld],C::CodeLinFld)->[]
{Given a sequence of codes S where all codes are subcodes of the first one, 
apply Construction X to S[1],S[2], and C. Then compute the resulting subcodes} 

  require #S ge 2:
    "The chain S must contain at least two codes";

  C1:=S[1];

  F:=Alphabet(C1);
  require &and{Alphabet(c) cmpeq F: c in S} and Alphabet(C) cmpeq F:
    "All codes must be defined over the same alphabet";

  n:=Length(C1);
  require &and{Length(c) eq n:c in S}:
    "All codes in the chain S must have the same length";

  require &and{c subset C1:c in S}:
    "All codes in the chain S must be a subcode of the first code";

  require Dimension(S[1]) eq Dimension(S[2])+Dimension(C):
    "The dimension of S[2] and C must equal the dimension of S[1]";

  D1:=ConstructionX(C1,S[2],C);
  G:=GeneratorMatrix(D1);

  res:=[D1];
  for c in S[2..#S] do;
     M:=Matrix([Coordinates(C1,g):g in Generators(c)]);
     Append(~res,sub<D1|LinearCode(M*G)>);
  end for;
 
  return res;

end intrinsic;

intrinsic ConstructionXXu(C1::CodeLinFld,C2::CodeLinFld,C3::CodeLinFld,
                                      D2::CodeLinFld,D3::CodeLinFld,i)->CodeLinFld
{C2 and C3 must be subcodes of C1, while the dimensions of D2 and D3 must
add with the dimensions to C2 and C3 to give the dimension of C1.
The returned code is constructed via the modified construction XX for UEP codes
of
Bierbrauer et al.}

/*

  J. Bierbrauer, Y. Edel, L. Tolhuizen
  New codes via the lengthening of BCH codes with UEP codes
  Finite Fields and their Applications., 5, 4, (1999), 345-353.

*/
  require C2 subset C1: "Argument 2 must be a subcode of argument 1";
  require C3 subset C1: "Argument 3 must be a subcode of argument 1";
  require Dimension(C1) eq Dimension(C2)+Dimension(D2):
    "The dimension of argument 1 must be the sum of the
     dimensions of argument 2 and 4";
  require Dimension(C1) eq Dimension(C3)+Dimension(D3):
    "The dimension of argument 1 must be the sum of the
     dimensions of argument 3 and 5";
  F:=Alphabet(C1);
  n1:=Length(C1);
  n2:=Length(D2);
  n3:=Length(D3);
  k:=Dimension(C1);
  k2:=Dimension(C2);
  k3:=Dimension(C3);
  C4:=C2 meet C3;
  k4:=Dimension(C4);

  B4:=Basis(C4);
  B42:=ExtendBasis(B4,RSpace(C2));
  B43:=ExtendBasis(B4,RSpace(C3));
  B421:=RMatrixSpace(F,k,n1)!ExtendBasis(B42,RSpace(C1));
  B431:=RMatrixSpace(F,k,n1)!ExtendBasis(B43,RSpace(C1));

  T:=Solution(B421,B431);

  G:=Zero(RMatrixSpace(F,k,n1+n2+n3-i));
  InsertBlock(~G,B421,1,1);
  InsertBlock(~G,GeneratorMatrix(D2),k2+1,n1+1);

  G:=T*G;

  m3:=GeneratorMatrix(D3);
  m3+:=Submatrix(G,k3+1,n1+n2+1-i,Nrows(m3),Ncols(m3));
  InsertBlock(~G,m3,k3+1,n1+n2+1-i);

  C:=LinearCode(G);

// compute bounds for minimum distance

  return C;

end intrinsic;

