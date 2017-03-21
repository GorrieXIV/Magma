freeze;



//   Jon F. Carlson, June 2012
 
intrinsic KIdentityMatrix(F::FldFin, n::RngIntElt) -> ModMatFldElt
{Returns the identity matrix as an element of the matrix space of the
n x n matrices over F.}

mat := KMatrixSpace(F,n,n)!0;
for i := 1 to n do
   mat[i,i] := 1;
end for;

	return mat;

end intrinsic;

////////////////////////////////////////////////////////////////////

/*
LocationOfGenerators := function(A);
// finds the location of the generators as elements of the standard basis
// of the underlying vector space of the algebra.

np := NumberOfProjectives(A);
PT := &cat[PathTree(A,i): i in [1 .. np]];
loc := [[j : j in [1 .. #PT]|PT[j][2] eq i and PT[j][1] eq 1][1]:
        i in [1 .. #Generators(A)]];

return loc;

end function;
*/

///////////////////////////////////////////////////////////////

DiagonalMatrix1 := function(Q)
// creates the matrix whose blocks are the matricies in the list Q

if #Q eq 1 then
       return Q[1];
end if;
rlst := [Nrows(x): x in Q];
clst := [Ncols(x): x in Q];
mat := KMatrixSpace(BaseRing(Q[1]), &+rlst, &+clst)!0;
rcount := 1;
ccount := 1;
for i := 1 to #Q do
   InsertBlock(~mat,Q[i],rcount,ccount);
   rcount +:= rlst[i];
   ccount +:= clst[i];
end for;

        return mat;

end function;

////////////////////////////////////////////////////////////////////
/*
AutosModuloRadicalSquared := function(A, socdims);
// we are assuming that A is in minimal generator form. 
// socdims is the dimensions of the socle. This
// is the outputs of the MinimalGeneratorForm2 function 

k := BaseRing(A);
p := Characteristic(k);
if Degree(k) gt 1 then
   VV := VectorSpace(PrimeField(k), Degree(k));
   Eltlist := [Seqelt(Eltseq(x),k):x in Basis(VV)];
end if;
B := TruncatedAlgebra(A,2);
dim := Dimension(B);
V := VectorSpace(k,dim);
np := NumberOfProjectives(A);
GLgens := [];     
                   //These are the generators of the general linear groups 
			//  that act on the generators of the algebras
Nilgens := [];
			// These are the generators of the nilpotent part 
                        //  of the group of automorphisms. 
Idchangegens := [];
			//   These are the generators coming form
                        //   alterations of the primitive idempotents
startrowindex := 1;
dproj := DimensionsOfProjectiveModules(B);
idrowindex := [1] cat [&+[dproj[i]: i in [1 .. j]]+1:j in [1 .. np]];
ID := KIdentityMatrix(k,dim);
id := KIdentityMatrix(k,1);
for i := 1 to np do
   for j := 1 to np do
                         // we are working on e_iAe_j
      sdij := socdims[i][j];
      sdijtot := &+sdij;
      if sdijtot ne 0 then 
         if sdijtot gt 1 then 
            if Degree(k) eq 1 then
               Nilgens cat:= &cat[[
                         InsertBlock(ID,id,startrowindex +i, 
                            startrowindex+i+j):
                               i in [1 .. sdijtot-j]]: 
                               j in [1 .. sdijtot-1]];
            else 
               Nilgens cat:= &cat[&cat[[
                         InsertBlock(ID,x*id,startrowindex +i, 
                             startrowindex+i+j):
                               x in Eltlist]: 
                               i in [1 .. sdijtot-j]]: 
                               j in [1 .. sdijtot-1]];
            end if;      // Degree(k) >1
         end if;
         if j ne i then
            if Degree(k) eq 1 then
               for t := 1 to sdijtot do
                  mat := ID;
                  mat[idrowindex[i]][startrowindex +t] := 1;
                  mat[idrowindex[j]][startrowindex +t] := -1;
                  Append(~Idchangegens, mat);
               end for;
            else    // Degree(k)>1
               for t := 1 to sdijtot do
                  for x in Eltlist do
                     mat := ID;
                     mat[idrowindex[i]][startrowindex +t] := x;
                     mat[idrowindex[j]][startrowindex +t] := -x;
                     Append(~Idchangegens, mat);
                  end for;
               end for;
            end if;
         end if;
         for l := 1 to #sdij do
            GLgens cat:= [InsertBlock(ID,
                Setseq(Generators(GL(sdij[l], k)))[t],
                startrowindex+1,startrowindex+1): 
                t in [1..Ngens(GL(sdij[l],k))]];
            startrowindex +:= sdij[l];
         end for;
      end if;
   end for;    // end of j loop
   startrowindex +:= 1;
end for;    // end of i loop

		return GLgens, Nilgens, Idchangegens, B;

end function;
*/
/////////////////////////////////////////////////////////////////

GradedAutosModuloRadicalSquared := function(A, socdims);
// we are assuming that A is graded

k := BaseRing(A);
p := Characteristic(k);
if Degree(k) gt 1 then
   VV := VectorSpace(PrimeField(k), Degree(k));
   Eltlist := [Seqelt(Eltseq(x),k):x in Basis(VV)];
end if;
B := TruncatedAlgebra(A,2);
dim := Dimension(B);
V := VectorSpace(k,dim);
np := NumberOfProjectives(A);
GLgens := [];
                   //These are the generators of the general linear groups
                        //  that act on the generators of the algebras
Nilgens := [];
                        // These are the generators of the nilpotent part
                        //  of the group of automorphisms.
startrowindex := 1;
dproj := DimensionsOfProjectiveModules(B);
idrowindex := [1] cat [&+[dproj[i]: i in [1 .. j]]+1:j in [1 .. np]];
ID := KIdentityMatrix(k,dim);
id := KIdentityMatrix(k,1);
for i := 1 to np do
   for j := 1 to np do
                         // we are working on e_iAe_j
      sdij := socdims[i][j];
      sdijtot := &+sdij;
      if sdijtot ne 0 then
         if sdijtot gt 1 then
            if Degree(k) eq 1 then
               Nilgens cat:= &cat[[
                         InsertBlock(ID,id,startrowindex +i,
                            startrowindex+i+j):
                               i in [1 .. sdijtot-j]]:
                               j in [1 .. sdijtot-1]];
           else
               Nilgens cat:= &cat[&cat[[
                         InsertBlock(ID,x*id,startrowindex +i,
                             startrowindex+i+j):
                               x in Eltlist]:
                               i in [1 .. sdijtot-j]]:
                               j in [1 .. sdijtot-1]];
            end if;      // Degree(k) >1
         end if;
         for l := 1 to #sdij do
            GLgens cat:= [InsertBlock(ID,
                Setseq(Generators(GL(sdij[l], k)))[t],
                startrowindex+1,startrowindex+1):
                t in [1..Ngens(GL(sdij[l],k))]];
            startrowindex +:= sdij[l];
         end for;
      end if;
   end for;    // end of j loop
   startrowindex +:= 1;
end for;    // end of i loop

                return GLgens, Nilgens, B;

end function;



//////////////////////////////////////////////////////////////////

AutoMatsOnSocle := function(autmats, psi, isp);
// autmats is a set of generators for the group of automorphism on
// the algebra. It fixes the space soc. Here we return the action of
// each element of autmats on soc. 

nautmats := [psi*y*isp: y in autmats];

	return nautmats;

end function;

////////////////////////////////////////////////////////////////////

AdditionalAutomorphisms := function(A,S);
// S is a subset of the socle of A. The function find the matrices of a
// set of generators of the group of automorphisms of A that are the
// the identity on A/S.

k := BaseRing(A);
if Degree(k) eq 1 then
   addlst := [k!1];
else 
   addlst := [k.1^i: i in [1 .. Degree(k)-1]] cat [k!1];
end if;
nproj := NumberOfProjectives(A);
dd := Dimension(A);
ends := GeneratorAssociatedIdempotents(A);
loc := PositionsOfGenerators(A);
bmat := KIdentityMatrix(BaseRing(A),dd);
V := VectorSpace(BaseRing(A), dd);
AUT := [];
for i := 1 to nproj do
   for j := 1 to nproj do
      if nproj eq 1 then
         W := S;
      else
         W := sub<V|[Vector(A.loc[i]*(A!x)*A.loc[j]):x in Basis(S)]>;
      end if;
      if Dimension(W) gt 0 then
         for t := nproj+1 to #ends do
            if ends[t] eq <i,j> then
               for s in Basis(W) do
                  for tt in addlst do
                     nmat := bmat;
                     nmat[loc[t]] +:= tt*s;
                     Append(~AUT,nmat);
                  end for;
               end for;
            end if;
         end for;
      end if;
   end for;
end for;

       return AUT;

end function;

////////////////////////////////////////////////////////////////////////

AdditionalAutomorphismsWithIdempotents := function(A, SS);

k := BaseRing(A);
if Degree(k) gt 1 then
   VV := VectorSpace(PrimeField(k), Degree(k));
   Eltlist := [Seqelt(Eltseq(x),k):x in Basis(VV)];
end if;
dim := Dimension(A);
V := VectorSpace(k,dim);
idgen := IdempotentGenerators(A);
U := SS;
ID := KIdentityMatrix(BaseRing(A),Dimension(A));
Idchangegens := [];
			//   These are the generators coming form
                        //   alterations of the primitive idempotents
np := NumberOfProjectives(A);
dproj := DimensionsOfProjectiveModules(A);
idrowindex := [1] cat [&+[dproj[i]: i in [1 .. j]]+1:j in [1 .. np]];
ID := KIdentityMatrix(k,dim);
for i := 1 to np do
   for j := 1 to np do
         if j ne i then
            Vij := sub<V|[Vector(idgen[i]*(A!x)*idgen[j]): x in Basis(U)]>;
            if Degree(k) eq 1 then
               for t := 1 to Dimension(Vij) do
                  mat := ID;
                  mat[idrowindex[i]] +:= Basis(Vij)[t];
                  mat[idrowindex[j]] +:= -Basis(Vij)[t];
                  Append(~Idchangegens, mat);
               end for;
            else    // Degree(k)>1
               for t := 1 to Dimension(Vij) do
                  for x in Eltlist do
                     mat := ID;
                     mat[idrowindex[i]] +:= x*Basis(Vij)[t];
                     mat[idrowindex[j]] +:= -x*Basis(Vij)[t];
                     Append(~Idchangegens, mat);
                  end for;
               end for;
            end if;
         end if;
   end for;
end for;

		return Idchangegens;

end function;

/////////////////////////////////////////////////////////////////////////
/*
TrivialOrNot := function(lst);
// lst is a sequence of square matrices. The function identifies those 
// that are not the identity matrix (first returned sequence), those 
// that are second returned sequence) and returns also the location of 
// the original matrices in the returned list.

nlst := [];
tlst := [];
boolst := [true:i in [1 .. #lst]];
id := KIdentityMatrix(BaseRing(lst[1]), Nrows(lst[1]));
for i :=  1 to #lst do
   if lst[i] eq id then
      Append(~tlst,i);
   else
      Append(~nlst,i);
      boolst[i] := false;
   end if;
end for;

	return nlst, tlst, boolst;

end function;
*/
/////////////////////////////////////////////////////////////////////

TruncationMatrix := function(A,B);
// The function assumes that the A is the truncation of basic algebra
// C at degree n and that B is the truncation of C at level n-1.

ddA := DimensionsOfProjectiveModules(A);
ddB := DimensionsOfProjectiveModules(B);
QQ := [* *];
k := BaseRing(A);
for i := 1 to #ddA do
   QQ[i] := VerticalJoin(Matrix(KIdentityMatrix(k,ddB[i])),
                  KMatrixSpace(k,ddA[i]-ddB[i], ddB[i])!0);
end for;

return DiagonalMatrix1(QQ);

end function;

//////////////////////////////////////////////////////////////////// 

RadicalDimensions := function(A);
//  Returns the dimensions of the successive radicals of the projective
// modules of A. The first entry in each list is the dimension of the
// projective module. The second is the dimension of its radical, etc.

np := NumberOfProjectives(A);
NN := [];
for i := 1 to np do
  P := ProjectiveModule(A,i);
  nn := [Dimension(P)];
  flag := true;
  while flag do
     P := JacobsonRadical(P);
     if Dimension(P) eq 0 then
       flag := false;
     else
       Append(~nn, Dimension(P));
     end if;
  end while;
  Append(~NN,nn);
end for;

        return NN;

end function;

////////////////////////////////////////////////////////////////////

LeftInverseMatrix := function(mat);
// Returns a left inverse of a matrix having more rows than columns.

if Nrows(mat) eq Ncols(mat) then 
	return mat^-1;
end if;
M := Transpose(RightInverseMatrix(Transpose(mat)));

	return M;

end function;


////////////////////////////////////////////////////////////////////

ExtendHomomorphism := function(A,CA,B,CB, rhoA,rhiB, mat);
// Here CA is the universal cover of A, and CB is a cover of B. mat is
// mat is an algebra homomorphism from A to B. The return is the extension
// of the homomorphism form CA to CB. rhoA is the quotient maps from CA 
// to A and rhiB is the left inverse of the quotient from CB to B.

nproj := NumberOfProjectives(A);
dp1 := DimensionsOfProjectiveModules(B);
dp2 := DimensionsOfProjectiveModules(CB);
np1 := DimensionsOfProjectiveModules(A);
np2 := DimensionsOfProjectiveModules(CA);
locA := PositionsOfGenerators(CA);
locB := PositionsOfGenerators(CB);
dsum1 := [0] cat [&+[dp1[j]: j in [1 .. i]]:i in [1 .. nproj]];
dsum2 := [0] cat [&+[dp2[j]: j in [1 .. i]]:i in [1 .. nproj]];
nsum1 := [0] cat [&+[np1[j]: j in [1 .. i]]:i in [1 .. nproj]];
nsum2 := [0] cat [&+[np2[j]: j in [1 .. i]]:i in [1 .. nproj]];
ieg := GeneratorAssociatedIdempotents(A);
newmat := KMatrixSpace(BaseRing(A), Dimension(CA), Dimension(CB))!0;
for i := 1 to nproj do
   newmat[locA[i]] := (rhoA[locA[i]]*mat)*rhiB;
end for;
for i := nproj+1 to #locA do
   newmat[locA[i]] := Vector(
                 CB!newmat[locA[ieg[i][1]]]*
                           CB!((rhoA[locA[i]]*mat)*rhiB)*
                 CB!newmat[locA[ieg[i][2]]]);
end for;

eid := GeneratorAssociatedIdempotents(CA);
ueid := [#[x:x in eid|x[1] eq i]: i in [1 .. nproj]];
for i := 1 to nproj do
   pt := PathTree(CA,i);
   for j := ueid[i]+1 to np2[i] do
      newmat[nsum2[i]+j] :=
         Vector(
                ( CB!newmat[nsum2[i]+pt[j][1]] )*
                        ( CB!newmat[locA[pt[j][2]]] )     );
   end for;
end for;

        return newmat;

end function;

////////////////////////////////////////////////////////////

LessThan := function(V,W);
// Decides if subspace V is less than W in the ordering.

k := BaseRing(V);
ll := [x:x in k];
m1 := BasisMatrix(V);
m2 := BasisMatrix(W);
m3 := m2 -m1;
for i := 1 to Nrows(m1) do
   if m3[i] ne 0 then 
      j := Depth(m3[i]);
      if m1[i,j] eq 0 then 
         return <V,W>, true;
      elif m2[i,j] eq 0 then 
         return <W,V>, false;
      else
         if Degree(k) eq 1 then 
            ll := [x:x in k];
            if Index(ll, m1[i,j]) lt Index(ll,m2[i,j]) then
               return <V,W>, true;
            else
               return <W,V>, false;
            end if;
         else 
            K := PrimeField(k);
            V := VectorSpace(K,Degree(k));
            x := V!Eltseq(m1[i,j]);
            y := V!Eltseq(m2[i,j]);
            z := x-y;
            a := Depth(z);
            if x[a] eq 0 then
               return <V,W>, true;
            elif y[a] eq 0 then
               return <W,V>, false;
            else
               ll := [t:t in K];
               if Index(ll, x[a]) lt Index(ll,y[a]) then
                  return <V,W>, true;
               else
                  return <W,V>, false;
               end if;
            end if;
         end if;
      end if;
   end if;
end for;

return <V,V>, false;

end function;

/////////////////////////////////////////////////////

Least := function(list);
// picks out the least vector space in the list.

lst := list;
if #lst eq 1 then
   return 1, lst[1];
else
   for i := 1 to #lst-1 do
      aa, bb := LessThan(lst[1], lst[2]);
      if bb then
         Remove(~lst,2);
      else
         Remove(~lst,1);
      end if;
   end for;
end if;

        return Index(list, lst[1]), lst[1];

end function;

//////////////////////////////////////////////////////////////////
/*
ReduceGroupSecond := function(GMats, ggMats);

if #GMats eq 0 then 
	return [],[],[];
end if;
k := Parent(GMats[1][1][1]);
p := Characteristic(k);
GGrp := sub<GL(Nrows(ggMats[1]),k)|ggMats>;
time Nor := NormalSubgroups(GGrp);
reduceflag := true;
for i := #Nor-1 to 1 by -1 do 
   if IsUnipotent(Nor[i]`subgroup) then 
      NN := Nor[i]`subgroup;
      if i eq 1 then 
         reduceflag := false;
      end if;
      break;
   end if;
end for;   
if not reduceflag then
   return [], [], sub<GGrp|>;
end if;
nuu := Setseq(Generators(NN));
WGrp, GTheta := WordGroup(GGrp);
AlgGL := sub<GL(Nrows(GMats[1]), k)|GMats>;
nuuM := [Evaluate(x@@GTheta, AlgGL):x in nuu];
Syl := sub<GGrp|nuu>;

	return nuuM, nuu, Syl;

end function;
*/
/////////////////////////////////////////////////////////////

ReduceGroupFirst := function(Alg, GMats);
if #GMats eq 0 then
        return [];
end if;
k := Parent(GMats[1][1][1]);
radn, radl := RadicalLayers(RightRegularModule(Alg));
n := radn[#radn-1];
psi := Submatrix(radl,radn[1]-n+1, 1, n, Ncols(radl));
isp := RightInverseMatrix(psi);
ggMats := [psi*x*isp: x in GMats];
GGrp := sub<GL(n,k)|ggMats>;
Nor := NormalSubgroups(GGrp);
reduceflag := true;
if #Nor eq 1 then 
   return [];
end if;
for i := #Nor-1 to 1 by -1 do
   if IsUnipotent(Nor[i]`subgroup) then
      NN := Nor[i]`subgroup;
      if i eq 1 then
         reduceflag := false;
      end if;
      break;
   end if;
end for;
if reduceflag then
   U := UnipotentMatrixGroup(NN);
else
   return GMats;
end if;
Q, phi := quo<GGrp|U>;
qq := #Q;
gens := [GGrp.i: i in [1 .. Ngens(GGrp)]];
newgens := [];
R := sub<Q|>;
r := #R;
for i := 1 to #gens do
   S := sub<Q|R,phi(gens[i])>;
   if #S gt r then
      R := S;
      Append(~newgens,i);
      r := #R;
      if r eq qq then
         break;
      end if;
   end if;
end for;
NewGmats := [GMats[i]: i in newgens];
nuu := Setseq(Generators(NN));
WGrp, GTheta := WordGroup(GGrp);
AlgGL := sub<GL(Nrows(GMats[1]), k)|GMats>;
MMM := Parent(GMats[1]);
nuuM := [MMM!Evaluate(x@@GTheta, AlgGL):x in nuu];

        return NewGmats cat nuuM;

end function;

/////////////////////////////////////////////////////////////////////////

UnipotentKernel := function(mats,chm, ichm);
k := Parent(chm[1][1]);
n := Nrows(chm);
m := Ncols(chm);
Wgrp := UnipotentMatrixGroup(sub<GL(m,k)|mats>);
Uumats := Setseq(Generators(Wgrp));
vvmats := [chm*x*ichm:x in Uumats];
n2 := [i: i in [1 .. #vvmats]|vvmats[i] eq KIdentityMatrix(k,n)];
if #n2 eq #vvmats then
   Lgrp := UnipotentMatrixGroup(sub<GL(n,k)|>);
   wrd := WordMap(Lgrp);
   return Uumats, [],[],Lgrp,wrd;
end if;
n1 := [i: i in [ 1 .. #vvmats]| not i in n2];
Lgrp := UnipotentMatrixGroup(sub<GL(n,k)|vvmats[n1[1]]>);
n3 := [n1[1]];
for i := 2 to #n1 do
   if not GL(n,k)!vvmats[n1[i]] in Lgrp then
      Append(~n3,n1[i]);
      Lgrp := UnipotentMatrixGroup(sub<GL(n,k)| [vvmats[x]:x in n3]>);
   end if;
end for;
n4 := [x: x in n1|not x in n3];
wrd := WordMap(Lgrp);
numats := [Evaluate(wrd(vvmats[x]),
      [Uumats[y]: y in n3])*Uumats[x]^-1:x in n4];
for i := #n3 to 1  by -1 do
   x := n3[i];
   NUU  := UnipotentMatrixGroup(sub<GL(n,k)|[vvmats[y]: y in Exclude(n3,x)]>);
   if GL(n,k)!vvmats[x] in NUU then
      Exclude(~n3,x);
      Lgrp := NUU;
      wrd := WordMap(Lgrp);
      Append(~numats, Evaluate(wrd(vvmats[x]),
               [Uumats[y]: y in n3])*Uumats[x]^-1);
   end if;
end for;

        return numats cat [Uumats[x]: x in n2], [Uumats[x]: x in n3],
               [vvmats[x]: x in n3], Lgrp, wrd;

end function;

////////////////////////////////////////////////////////////////////////

NongradedGenerators := function(A, socdims);
// we are assuming that A is in minimal generator form.
// socdims is the dimensions of the socle. This
// is the outputs of the MinimalGeneratorForm2 function

k := BaseRing(A);
p := Characteristic(k);
if Degree(k) gt 1 then
   VV := VectorSpace(PrimeField(k), Degree(k));
   Eltlist := [Seqelt(Eltseq(x),k):x in Basis(VV)];
end if;
B := TruncatedAlgebra(A,2);
dim := Dimension(B);
V := VectorSpace(k,dim);
np := NumberOfProjectives(A);
Idchangegens := [];
                        //   These are the generators coming form
                        //   alterations of the primitive idempotents
startrowindex := 1;
dproj := DimensionsOfProjectiveModules(B);
idrowindex := [1] cat [&+[dproj[i]: i in [1 .. j]]+1:j in [1 .. np]];
ID := IdentityMatrix(k,dim);
id := IdentityMatrix(k,1);
for i := 1 to np do
   for j := 1 to np do
                         // we are working on e_iAe_j
      sdij := socdims[i][j];
      sdijtot := &+sdij;
      if sdijtot ne 0 then
         if j ne i then
            if Degree(k) eq 1 then
               for t := 1 to sdijtot do
                  mat := ID;
                  mat[idrowindex[i]][startrowindex +t] := 1;
                  mat[idrowindex[j]][startrowindex +t] := -1;
                  Append(~Idchangegens, mat);
               end for;
            else    // Degree(k)>1
               for t := 1 to sdijtot do
                  for x in Eltlist do
                     mat := ID;
                     mat[idrowindex[i]][startrowindex +t] := x;
                     mat[idrowindex[j]][startrowindex +t] := -x;
                     Append(~Idchangegens, mat);
                  end for;
               end for;
            end if;
         end if;
         startrowindex +:= sdijtot;
      end if;
   end for;    // end of j loop
   startrowindex +:= 1;
end for;    // end of i loop

                return Idchangegens, B;

end function;

////////////////////////////////////////////////////////////

CreateTGroup := function(matlst, dp1, dp2, fld);

n := &+dp2 - #dp2;
Tmat := KMatrixSpace(fld, n, n)!0;
Tlst := [];
for y in matlst do
   X := Tmat;
   ri := 0;
   ro := 0;
   for i := 1 to #dp1 do
      InsertBlock(~X, Submatrix(y, ri +2, ri +2, dp2[i]-1, dp2[i]-1),
			ro +1, ro +1);
      ri +:= dp1[i];
      ro +:= dp2[i]-1;
   end for;
   Append(~Tlst, X);
end for;

Tgrp := sub<GL(n, fld)| [GL(n, fld)!x: x in Tlst]>;
Tord := [Order(GL(n,fld)!x): x in Tlst];
OO := #Tgrp;
p := Characteristic(fld);


max := Maximum(Tord);
plst := &cat[[j: j in [1 .. #Tord]| Tord[j] eq  max+1-i]: i in [1 .. max]];
oddlst := [plst[j]: j in [1 .. #Tord]| not IsPowerOf(Tord[plst[j]],p)];


newgenlst := [];

Ngrp := sub<GL(n, fld)|>;
NOO := 1;

if not #oddlst eq 0 then 
   for j := 1 to #oddlst do
      Ngrp := sub<GL(n, fld)|Ngrp, Tlst[oddlst[j]]>;
      nOO := #Ngrp;
      if not nOO eq NOO then 
         Append(~newgenlst, oddlst[j]);
      NOO := nOO;
      end if;
      if NOO eq OO then 
         break;
      end if;
   end for;
end if;

if not NOO eq OO then 
   for j := 1 to #Tord do
      if not j in oddlst then 
         Ngrp := sub<GL(n, fld)|Ngrp, Tlst[plst[j]]>;
         nOO := #Ngrp;
         if not nOO eq NOO then   
            Append(~newgenlst, plst[j]);
            NOO := nOO;
         end if;
         if NOO eq OO then    
            break;
         end if;
      end if;
   end for;
end if;

bflag := true;
while bflag do
   bflag := false;
   for i := 1 to #newgenlst do
      Wgrp := sub<GL(n,fld)| [Tlst[x]: x in Remove(newgenlst,i)]>;
      if #Wgrp eq OO then 
         Remove(~newgenlst,i);
         bflag := true;
         break;
      end if;
   end for;
end while;

newmatlst := [];
for t in newgenlst do
   if not IsDivisibleBy(Tord[t],p) then 
      m := Order(GL(Nrows(matlst[t]),fld)!matlst[t]);
      if IsDivisibleBy(m,p) then
         u := Factorization(m);
         r := [x[2]:x in u|x[1] eq p][1];
         W := matlst[t]^(p^r);
      else 
         W := matlst[t];
      end if;
   else 
      W := matlst[t];
   end if;
   Append(~newmatlst,W);
end for;

	return newmatlst, Tlst;

end function;



