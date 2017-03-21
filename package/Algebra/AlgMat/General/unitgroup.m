freeze;

// Jon F. Carlson, June 2012

BlockLocations := function(A);

AG := AlgebraGenerators(A);
n := #AG`FieldGenerators;
rank_idemps := [Rank(x):x in AG`PrimitiveIdempotents];
SG := SimpleQuotientAlgebras(A);
degrees_over := SG`DegreesOverCenters;
moddeg := [rank_idemps[i]*degrees_over[i]: i in [1 .. n]];
locs := [];
rowindex := 1;
internalindex := 1;
for i := 1 to n do 
   locs[i] := <rowindex,rank_idemps[i],internalindex>;
   rowindex +:= moddeg[i];
   internalindex +:= rank_idemps[i];
end for;

	return locs;

end function;

//////////////////////////////////////////////////////////////////////

LiftFromCondensedAlgebra := function(A,cmat,locs,stdform2,stdform1);
//  Returns the image of an element of the condensed algebra of the 
//  matrix algebra A under the stand embedding of the condensed algebra
// in A. The pair <stdform1,stdform2> are the StandardFormConjugation
// matrices. 

mat := KMatrixSpace(CoefficientRing(A), Dimension(A), Dimension(A))!0;
for i := 1 to #locs do
   for j := 1 to #locs do
      InsertBlock(~mat, 
          Submatrix(cmat,locs[i][3],locs[j][3],locs[i][2],locs[j][2]), 
          locs[i][1], locs[j][1]);
   end for;
end for;

	return mat;

end function;

///////////////////////////////////////////////////////////////////////

DeeplyCondensedRadicalGenerators := function(C, locs);
//  Gets the radical generators in the minimal form, these are as elements
// of the condensed algebra C of a basic algebra A. locs is the output
// function block locations applied to A. 

np := #locs;
SRG := AlgebraGenerators(C)`RadicalGenerators;
ww := [* *];
for i := 1 to np do
   xx := [* *];
   for j := 1 to np do
     yy := [];
     for y in SRG[i][j] do
       Append(~yy, Submatrix(y,locs[i][3],locs[j][3],locs[i][2],locs[j][2]));
     end for;
     Append(~xx, yy);
   end for;
   Append(~ww, xx);
end for;

	return ww;

end function;

//////////////////////////////////////////////////////////////////////////

DeepSpin := function(A, gens, loc);
// gets a basis for the radical in terms of small block matrices. The 
// must then be reinserted back into the algebra. 

k := CoefficientRing(A);
n := #loc;
basesp := [[KMatrixSpace(k,loc[i][2],loc[j][2]): j in [1..n]]: i in [1 ..n]];
spaces := [[sub<basesp[i][j]|gens[i][j]> : j in [1 ..n]]: i in [1 .. n]];
degofcent := SimpleQuotientAlgebras(A)`DegreesOfCenters;
for i := 1 to n do
   if degofcent[i] gt 1 then
      mat := Submatrix(AlgebraGenerators(A)`FieldGenerators[i],
                  loc[i][3],loc[i][3],loc[i][2],loc[i][2]);
      for j := 1 to n do 
         if Dimension(spaces[i][j]) ne 0 then 
            spaces[i][j] +:= sub<basesp[i][j]|
                               [mat*x: x in Basis(spaces[i][j])]>;
            if j ne i and Dimension(spaces[j][i]) ne 0 then 
               spaces[j][i] +:= sub<basesp[j][i]|
                               [x*mat: x in Basis(spaces[j][i])]>;
            end if;
         end if;
      end for;
   end if;
end for;
flag := true;
while flag do
   flag := false;
   for i := 1 to n do
      for j := 1 to n do
         newmats := [];
         for l := 1 to n do
            if Dimension(spaces[i][l]) ne 0 
                         and Dimension(spaces[l][j]) ne 0 then
               newmats cat:= [x*y: x in Basis(spaces[i][l]), 
                         y in Basis(spaces[l][j])];
            end if;
         end for;
         if #newmats ne 0 then 
            w := Dimension(spaces[i][j]);
            spaces[i][j] +:= sub<basesp[i][j]|newmats>;  
            if Dimension(spaces[i][j]) gt w then 
               flag := true;
            end if;
         end if;
      end for;
   end for;
end while;

	return spaces;

end function;

//////////////////////////////////////////////////////////////////////

CondensedBasisForRadical := function(A,locs)
// gets the condensed basis for the radical from the word problem data.

wdpbm := WordProblemData(A);
degofcent := SimpleQuotientAlgebras(A)`DegreesOfCenters; 
radbasis := [*  *];
for i := 1 to #locs do
   radibasis := [*  *];
   for j := 1 to #locs do
      if i eq j then
         s := 1 + degofcent[i];
      else
         s := 1;
      end if;
      matsp := KMatrixSpace(BaseRing(A), locs[i][2], locs[j][2]);
      if #wdpbm[i][j] gt 0 then 
         xx := [matsp!Eltseq(wdpbm[i][j][1][t]):t in [s .. #wdpbm[i][j][2]]];
      else
         xx := [];
      end if;
      Append(~radibasis,xx);
   end for;
   Append(~radbasis, radibasis);
end  for;

	return radbasis;

end function;

///////////////////////////////////////////////////////////////////////

intrinsic BasisOfJacobsonRadical(A::AlgMat) -> SeqEnum[AlgMatElt]
{Returns a basis of the Jacobson radical of the matrix algebra A.}

k := BaseRing(A);
locs := BlockLocations(A);
C := CondensedAlgebra(A);
degC := Degree(C);
degA := Degree(A);
n := #locs;
degover := SimpleQuotientAlgebras(A)`DegreesOverCenters;
mm := AlgebraGenerators(A)`StandardFormConjugationMatrices[1];
mmi := AlgebraGenerators(A)`StandardFormConjugationMatrices[2];
cbase := CondensedBasisForRadical(A,locs);

// Now we lift these to A
mat := MatrixAlgebra(k,degA)!0;
AList := [];
for i := 1 to n do
  for j := 1 to n do
    Y := cbase[i][j];
    for x in Y do
      for r := 1 to degover[i] do
        for t := 1 to degover[j] do
          nmat := InsertBlock(mat, x, 
                locs[i][1]+(r-1)*locs[i][2],locs[j][1]+(t-1)*locs[j][2]);
          Append(~AList,nmat);
        end for;
      end for;
    end for;
  end for;
end for;

	return [Generic(A)!mmi*x*mm: x in AList];

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic BasisOfCondensedJacobsonRadical(A::AlgMat) -> SeqEnum[AlgMatElt]
{Returns a basis of the Jacobson radical of the condensed algebra of 
matrix algebra A, viewed as a subalgebra of A.}

k := BaseRing(A);
locs := BlockLocations(A);
C := CondensedAlgebra(A);
degC := Degree(C);
degA := Degree(A);
n := #locs;
degover := SimpleQuotientAlgebras(A)`DegreesOverCenters;
mm := AlgebraGenerators(A)`StandardFormConjugationMatrices[1];
mmi := AlgebraGenerators(A)`StandardFormConjugationMatrices[2];
cbase := CondensedBasisForRadical(A,locs); mmt := 2;


// Now we lift these to A
mat := MatrixAlgebra(k,degA)!0;
AList := [];
for i := 1 to n do
  for j := 1 to n do
    for x in cbase[i][j] do
      nmat := InsertBlock(mat, x, locs[i][1],locs[j][1]);
      Append(~AList,nmat);
    end for;
  end for;
end for;

        return [Generic(A)!mmi*x*mm: x in AList];

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic UnitGroupCM(A::AlgMat) -> GrpMat, GrpMat, GrpMat, RngIntElt
{Returns the group of units in the algebra A, the group of units of 
the semisimple part of A, the group of radical generators and the order
of the group of units of A.}

k := CoefficientRing(A);
AG := AlgebraGenerators(A);
Q := SimpleQuotientAlgebras(A);
ords := Q`OrdersOfCenters;
dgo := Q`DegreesOfCenters;
fgens := [Matrix(AG`FieldGenerators[i]): i in [1 .. #AG`FieldGenerators]];
ids := [fgens[i]^(ords[i]-1): i in [1 .. #fgens]];
perms := [Matrix(AG`PermutationMatrices[i]):
                    i in [1 .. #AG`PermutationMatrices]];
k := CoefficientRing(A);
degs := Q`DegreesOverCenters;
isbasic := &and[x eq 1:x in degs];
if #ords gt 1 then
   bigE := [perms[i]^degs[i]:i in [1 .. #perms]];
end if;
grpgens := [];
for i := 1 to #ords do
   ngpgens := [];
   if #ords gt 1 then
      addE := IdentityMatrix(k, Degree(A)) - bigE[i];
   else
      addE := A!0;
   end if;
   if degs[i] eq 1 then
      a := fgens[i];
      Append(~ngpgens,a+addE);
   else
      if ords[i] eq 2 then
         Append(~ngpgens,bigE[i]+ids[i]*perms[i]^(degs[i]-1)+addE);
         Append(~ngpgens,perms[i]+addE);
      else
         a := bigE[i]+fgens[i]-ids[i];
         b := -perms[i]+2*ids[i]*perms[i]-ids[i];
         Append(~ngpgens,a+addE);
         Append(~ngpgens,b+addE);
      end if;
   end if;
   grpgens cat:= ngpgens;
end for;
d := DimensionOfAlgebra(A);
n := &+[degs[i]*ords[i]:i in [1 ..#ords]];
q := #k;
raddim := d-&+[degs[i]^2*dgo[i]:i in [1.. #degs]];
radbasis := BasisOfCondensedJacobsonRadical(A);
nilgens := [IdentityMatrix(k,Degree(A))+x: x in radbasis];
GP1 := sub<GL(Degree(A),k)|grpgens>;
GP2 := sub<GL(Degree(A),k)|nilgens>;
glm := &*[#GL(degs[i], GF(ords[i])): i in [1 .. #ords]];
N := glm*q^raddim;

        return sub<GL(Degree(A),k)|grpgens cat nilgens>, GP1, GP2, N;

end intrinsic;

//////////////////////////////////////////////////////////////////////

CondensedBasisForAlgebra := function(A,locs)
// gets the condensed basis for the algebra from the word problem data.

wdpbm := WordProblemData(A);
degofcent := SimpleQuotientAlgebras(A)`DegreesOfCenters;
radbasis := [*  *];
for i := 1 to #locs do
   radibasis := [*  *];
   for j := 1 to #locs do
      matsp := KMatrixSpace(BaseRing(A), locs[i][2], locs[j][2]);
      if #wdpbm[i][j] gt 0 then
         xx := [matsp!Eltseq(wdpbm[i][j][1][t]):t in [1 .. #wdpbm[i][j][2]]];
      else
         xx := [];
      end if;
      Append(~radibasis,xx);
   end for;
   Append(~radbasis, radibasis);
end  for;

        return radbasis;

end function;

///////////////////////////////////////////////////////////////////////

intrinsic BasisOfAlgebra(A::AlgMat) -> SeqEnum[AlgMatElt]
{Returns a basis of the matrix algebra A.}

k := BaseRing(A);
locs := BlockLocations(A);
C := CondensedAlgebra(A);
degC := Degree(C);
degA := Degree(A);
n := #locs;
degover := SimpleQuotientAlgebras(A)`DegreesOverCenters;
mm := AlgebraGenerators(A)`StandardFormConjugationMatrices[1];
mmi := AlgebraGenerators(A)`StandardFormConjugationMatrices[2];
cbase := CondensedBasisForAlgebra(A,locs); 

// Now we lift these to A
mat := MatrixAlgebra(k,degA)!0;
AList := [];
for i := 1 to n do
  for j := 1 to n do
    for x in cbase[i][j] do
      for r := 1 to degover[i] do
        for t := 1 to degover[j] do
          nmat := InsertBlock(mat, x,
                locs[i][1]+(r-1)*locs[i][2],locs[j][1]+(t-1)*locs[j][2]);
          Append(~AList,nmat);
        end for;
      end for;
    end for;
  end for;
end for;

        return [Generic(A)!mmi*x*mm: x in AList];

end intrinsic;




