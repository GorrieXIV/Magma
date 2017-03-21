freeze;

import "radical.m"        : ChangeOfBasisMatrixA;

intrinsic CondensedAlgebra(A::AlgMat) -> AlgMat
{Returns the algebra eAe where e is a sum of primitive idempotents, one
for each simple A-module} 

if assigned A`CondensedAlgebra then 
   return A`CondensedAlgebra;
end if;
N := SimpleQuotientAlgebras(A)`DegreesOverCenters;
R := AlgebraGenerators(A);
fgens := R`FieldGenerators;
radgens := R`SequenceRadicalGenerators;
pids := R`PrimitiveIdempotents;
fff := BaseRing(A);

uu := CondensationMatrices(A);
mat := uu[1];
mat1 := uu[2];
dim1 := Nrows(mat);

fgens1 := [mat*Matrix(x)*mat1:x in fgens];
radgens1 := [mat*Matrix(x)*mat1:x in radgens];
pids1 := [mat*Matrix(x)*mat1:x in pids];

AA := MatrixAlgebra<fff,dim1|[x: x in fgens1 cat radgens1]>;
A`CondensedAlgebra := AA;

//"Orig A:", A;
//"CondensedAlgebra:", AA;
//AA: Maximal;

K := CoefficientRing(A);
V := RModule(AA);
C := Constituents(V);
a_A := [Action(M): M in C];
s_A := [[x: x in a_A|not IsZero(x.i)][1]: i in [1 .. #C]];
d := [DimensionOfEndomorphismRing(RModule(x)):x in s_A];
n := [Degree(s_A[i]) div d[i] : i in [1..#d]];
p := Characteristic(CoefficientRing(A));
q := [d[i] eq 1 select  #K else (#K)^d[i] : i in [1..#d]];
     phi := NaturalFreeAlgebraCover(AA);
     t := Ngens(AA);
     F := Domain(phi);
ss := [hom<F -> X | [X.i: i in [1 .. t]]>: X in s_A];
SimQuots := recformat<SimpleQuotients     :SeqEnum,
                       DegreesOverCenters     :SeqEnum,
                       DegreesOfCenters       :SeqEnum,
                       OrdersOfCenters       :SeqEnum>;
sqq := rec< SimQuots | SimpleQuotients       := ss,
                       DegreesOverCenters     := n,
                       DegreesOfCenters       := d,
                       OrdersOfCenters       := q>;
AA`SimpleQuotientAlgebras := sqq;

m1, m2 := ChangeOfBasisMatrixA(AA, pids1, [], n);
rgens := R`RadicalGenerators;
for i := 1 to #rgens do
for j := 1 to #rgens[i] do
rgens[i,j] := [mat*x*mat1:x in rgens[i][j]];
end for;
end for;

AlgebraGens := recformat<
           FieldGenerators : SeqEnum,
           PermutationMatrices : SeqEnum,
           PrimitiveIdempotents :SeqEnum,
           RadicalGenerators : List,
           SequenceRadicalGenerators : SeqEnum,
           GeneratingPolynomialsForCenters :SeqEnum,
           StandardFormConjugationMatrices : Tup>;

agens := rec< AlgebraGens | FieldGenerators := fgens1,
	      PermutationMatrices := [],
	      PrimitiveIdempotents := pids1,
	      RadicalGenerators := rgens,
              SequenceRadicalGenerators := radgens1,
GeneratingPolynomialsForCenters := R`GeneratingPolynomialsForCenters,
	      StandardFormConjugationMatrices := <m1,m2>>;

AA`AlgebraGenerators := agens;

PrimIdList := [];
PrimIdData := recformat<AlgebraIdempotent:AlgMatElt,
                        PrimitiveIdempotent:AlgMatElt,
                        PrimitiveIdempotentOnQuotient:AlgMatElt,
                        FieldGenerator:AlgMatElt,
                        FieldGeneratorOnQuotient:AlgMatElt,
                        GeneratingPolForCenter:RngUPolElt>;

for j := 1 to #N do 

   uu := pids1[j];
   ww := fgens1[j];
   if j eq 1 then 
      vv := MatrixAlgebra(fff,d[1])!Submatrix(uu,1,1,d[1],d[1]);
      xx := MatrixAlgebra(fff,d[1])!Submatrix(ww,1,1,d[1],d[1]);
   else
      ddd := &+[Rank(pids[i]): i in [1 .. j-1]] +1;
      vv := MatrixAlgebra(fff,d[j])!Submatrix(uu,ddd,ddd,d[j],d[j]);
      xx := MatrixAlgebra(fff,d[j])!Submatrix(ww,ddd,ddd,d[j],d[j]);
   end if;
   gpd := R`GeneratingPolynomialsForCenters[j];

   pid := rec< PrimIdData |
      AlgebraIdempotent := MatrixAlgebra(fff, Nrows(uu))!uu,
      PrimitiveIdempotent := MatrixAlgebra(fff, Nrows(uu))!uu,
      PrimitiveIdempotentOnQuotient := vv,
      FieldGenerator := MatrixAlgebra(fff,Nrows(ww))!ww,
      FieldGeneratorOnQuotient := xx,
      GeneratingPolForCenter := gpd>;

   Append(~PrimIdList, pid);

end for;

AA`PrimitiveIdempotentData := PrimIdList;

        return AA;

end intrinsic;

//********************************************************************

RadicalLayers := function(V);

W := V;
radlst := [W];
while Dimension(W) ne 0 do
  W := JacobsonRadical(W);
  Append(~radlst,W);
end while;

       return radlst;

end function;

//*********************************************************************

FilterByRadicalLayers := function(V);

k := CoefficientRing(V);
p := Characteristic(k);
rll := RadicalLayers(V);
s := #rll;
n := Dimension(V);
mat := KMatrixSpace(k,n,n)!0;
rows := [];
A := Action(V);
idlst := [i: i in [1 .. Ngens(A)]|Rank(A.i) eq Rank(A.i^2)];

Iplst := [];
polst := [];
P := PolynomialRing(k); t := P.1;
if #idlst gt 1 then
   for j := 1 to #idlst do
      f := (P!MinimalPolynomial(A.idlst[j]) div t) - P!1;
      Iplst[j] := Evaluate(f,A.idlst[j]);
      polst[j] := f;
   end for;
elif #idlst eq 1 and p ne 2 then
   f := P!MinimalPolynomial(A.idlst[1]) - P!1;
   Iplst := [Evaluate(f,A.idlst[1])];
   polst := [f];
else
   Iplst := [A.idlst[1]];
   polst := [t];
end if;
for j := s-1 to 1 by -1 do
   Q, phi := quo<rll[j]|rll[j+1]>;
   for l := #idlst to 1 by -1 do
      rl := Rank(Action(Q).idlst[l]);
      if rl ne 0 then
         ww := Evaluate(polst[l],Action(Q).idlst[l]);
         BB := Basis(RowSpace(ww));
         rows := rows cat [(Vector(V!(x@@phi)))*Iplst[l]:
						 x in Basis(RowSpace(ww))];
      end if;
   end for;
end for;
for i := 1 to n do
mat[i] := rows[n-i+1];
end for;
 
return mat;

end function;

//////////////////////////////////////////////////////////////////////

intrinsic CondensedAlgebraSimpleModules(A::AlgMat,B::AlgMat) -> AlgBas
{Returns the sequence of simple modules for the the algebra B which is
the condensed algebra of the matrix algebra A.}

k := BaseRing(A);
phi := NaturalFreeAlgebraCover(B);
F := Domain(phi);
pid := PrimitiveIdempotentData(A);
dd := SimpleQuotientAlgebras(A)`DegreesOfCenters;
pols := [x`GeneratingPolForCenter:x in pid];
npols := [y div Parent(pols[1]).1: y in pols];
compm := [* CompanionMatrix(x): x in npols *];
IML := [];
for i := 1 to #dd do
   U := MatrixAlgebra(k, dd[i]);
   zz := U!0;
   XX := [zz:i in [1 .. Rank(F)]];
   XX[i] := compm[i];
   IML[i] := AModule(F, XX);
end for;

        return IML;

end intrinsic;

