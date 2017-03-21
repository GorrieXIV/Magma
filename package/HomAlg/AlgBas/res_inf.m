freeze;

import "resolve.m": ExpandBlock;
import "resolve.m": MatrixOfBoundaryMap;
import "resolve.m": TopOfMatrixOfBoundaryMap;

// **********************************************************************

CreateNewBoundaryMap := function(rkl,mpl,resin,nnn,M,MI);

// Creates the boundary map of a resolution, 
// but allows for a change of basis in the standard free
// module. The change of basis is accomplished by conjugating by M.
// MI should be the inverse of M. This function is used to restrict
// a resolution to a complex for a different group.

fld := CoefficientRing(mpl);
p := Characteristic(fld);
SZ := Ncols(mpl);
stlt := [0] cat [&+[rkl[i]*rkl[i+1]:i in [1 .. j]]:j in [1 .. #rkl-1]];
zvec := VectorSpace(fld,SZ)!0;
DD := MatrixOfBoundaryMap(resin`PCgenMats,mpl,stlt[nnn],rkl[nnn+1],
			  rkl[nnn],SZ,fld,p);
for k := 1 to rkl[nnn] do
   for j := 1 to rkl[nnn+1] do
      if mpl[stlt[nnn]+j+rkl[nnn+1]*(k-1)] ne zvec then
	  SM := Submatrix(DD, (j-1)*SZ+1,(k-1)*SZ+1,SZ,SZ);
	  InsertBlock(~DD,M*SM*MI,(j-1)*SZ+1,(k-1)*SZ+1);
       end if;
   end for;
end for;

return DD;

end function;

// ********************************************************************

RestrictionDataF := function(RD1,RD2);

// Creates standard input for doing restriction maps. It returns a list of
// representatives of the cosets of the groups and the transformation matrix
// which changes the standard free module of the overgroup into a sum of 
// freemodules for the subgroup. The input is the two resolution inputs 
// "RD1" for the overgroup, and "RD2" for the subgroup.

G := PCGroup(RD1`Algebra);
H := PCGroup(RD2`Algebra);
Mats := RD1`PCgenMats;
theta := hom<H -> G|[PCMap(RD1`Algebra)(H.i@@PCMap(RD2`Algebra)): 
                                        i in [1 .. NPCgens(H)]]>;
_, FM := GModule(RD1`Algebra);
fld := CoefficientRing(FM);
p := Characteristic(fld);
exp := Factorization(#G div #H)[1][2];
exp2 := FactoredOrder(H)[1][2];
w := sub<G|[theta(H.i):i in [1 .. Ngens(H)]]>;
cosets := [];
for i := #Mats to 1 by -1  do
    if G.i notin w then
        Append(~cosets,i);
        w := sub<G|w,G.i>;
    end if;
end for; 
Reverse(~cosets);
m1 := FM.1;
BB := KMatrixSpace(fld,1,#G)!m1;
trmat := KMatrixSpace(fld,#G,#G)!0;
id := IdentityMatrix(fld, #G);

if #cosets ne 0 then
for i := 1 to #cosets do
   x := Mats[cosets[i]];
   CC := BB;
   nn := Nrows(CC);
   BB := KMatrixSpace(fld,p*nn,#G)!0;
   InsertBlock(~BB,CC,1,1);
   for k := 1 to p-1 do
      InsertBlock(~BB,Submatrix(BB,nn*(k-1)+1,1,nn,#G)*x,nn*k+1,1);
   end for;
end for;
for j := 1 to #G div #H  do
    MM := Submatrix(BB,j,1,1,#G);
    for i := 1 to exp2 do
       x := Representation(FM)(theta(H.i));
       CC := MM;
       nn := Nrows(CC);
       MM := KMatrixSpace(fld, p*nn, #G)!0;
       InsertBlock(~MM,CC,1,1);
       for k := 1 to p-1 do
	  InsertBlock(~MM,Submatrix(MM,nn*(k-1)+1,1,nn,#G)*(x-id),nn*k+1,1);
	end for;
    end for;
    InsertBlock(~trmat,MM,#H*(j-1)+1,1);
end for;
else
    MM := BB;
    for i := 1 to exp do
       x := Representation(FM)(theta(H.i));
       CC := MM;
       nn := Nrows(CC);
       MM := KMatrixSpace(fld,p*nn.#G)!0;
       InsertBlock(~MM,CC,1,1);
       for k := 1 to p-1 do
          InsertBlock(~MM,Submatrix(MM,nn*(k-1)+1,1,nn,#G)*(x-id),nn*k+1,1);
       end for;
    end for;
    InsertBlock(~trmat,MM,1,1);
//print trmat,"";
end if;
trinv := trmat^-1;
return trmat,trinv, cosets;
end function;

// *************************************************************************

intrinsic RestrictionData(A::AlgBasGrpP, B::AlgBasGrpP) -> ModMatFldElt, 
             ModMatFldElt, SeqEnum
{Returns the change of basis matrix that make the standard free module
for A into a directs sume of standard free modules for B. Also returns
the inverse of the matrix and a set of coset representatives of the 
PCGroup(B) in PCGroup(A)}

require BaseRing(A) eq BaseRing(B): 
  "Algebras are defined over different fields";
//  RestrictionData := function(A,B);

G := Group(A);
H := Group(B);

if assigned A`ResolutionData then RR1 := A`ResolutionData; 
else RR1 := ResolutionData(A); end if;
if assigned B`ResolutionData then RR2 := B`ResolutionData;
else RR2 := ResolutionData(B); end if;
g := PCGroup(A);
h := PCGroup(B);
theta1 := PCMap(A);
theta2 := PCMap(B);
if Type(G) eq GrpPerm then 
mu := hom<h -> g|[theta1(h.i@@theta2): i in [1 .. NPCgens(h)]]>;
else 
phi := InclusionMap(G,H);
mu := hom<h -> g|[theta1(phi(h.i@@theta2)): i in [1 .. NPCgens(h)]]>;
end if;

         return RestrictionDataF(RR1,RR2);

// end function;

end intrinsic;

//*************************************************************************

CompactRestrictedResolution := function(rrr,RMap,RD1,RD2, numb);

// This function restricts the resolution of the overgroup (rrr,RMap) to a 
// resolution of the subgroup. The resolution data for the groups are 
// RD1 and RD2, and  "numb" is the number of steps desired. 

ff := CoefficientRing(RD1`PCgenMats[1]);
og := #Group(RD1`Algebra);
oh := #Group(RD2`Algebra);
ind := og div oh;
rlst := [rrr[i]*ind:i in [1 .. numb+1]];
stlt := [0] cat [rrr[i]*rrr[i+1]:i in [1 .. numb]];
newmat := KMatrixSpace(ff,&+stlt*ind^2, oh)!0;
resi,rinv := RestrictionDataF(RD1,RD2);
for i := 1 to numb do
   delta := CreateNewBoundaryMap(rrr,RMap,RD1,i,resi,rinv);
   for k := 1 to ind*rrr[i+1] do 
      for l := 1 to ind*rrr[i] do
	 InsertBlock(~newmat,
	     Submatrix(delta,(k-1)*oh+1,(l-1)*oh+1,1,oh),
	     &+[stlt[w]:w in [1 .. i]]*ind^2+ k+(l-1)*ind*rrr[i+1],1);
      end for;
   end for;
end for;

        return rlst,newmat;

end function;

//**********************************************************************

intrinsic RestrictResolution(PR1::Rec,RD2::Rec) -> ModCpx
{Takes the compact projective resolution PR1 of the basic algebra of a 
group G and resolution data RD2 for the basic algebra of a subgroup H 
and returns the restriction of the resolution to a complex over the 
basic algebra of H.} 

B := RD2`Algebra;
F := ProjectiveModule(B,1);
rrr := Reverse(PR1`BettiNumbers);
Mat1 := PR1`ResolutionRecord;
RD1 := Algebra(PR1`Module)`ResolutionData;
lll, CRR := CompactRestrictedResolution(rrr, Mat1,RD1,RD2,#rrr-1);
FL := [DirectSum([F:j in [1 .. lll[i]]]):i in [1 .. #lll]];
L := [* *];
stlt := [0] cat [lll[i]*lll[i+1]:i in [1 .. #rrr-2]];
for i := #rrr-1 to 1 by -1 do
   M := MatrixOfBoundaryMap(RD2`PCgenMats, CRR,&+[stlt[j]: j in [1 ..i]], 
          lll[i+1], lll[i], Ncols(CRR), BaseRing(Mat1), 
          Characteristic(BaseRing(Mat1)));
   Append(~L, Hom(FL[i+1],FL[i])!M);
end for;
C := Complex(L,0);

return C;

end intrinsic;
	
// *********************************************************************
		
CompactRestrictionChainMap := function(rr1,mat1,rr2,mat2,RD);

// This function computes the chain map which gives the restriction of the
// projective resolution of an overgroup g to a subgroup h. Notice that we 
// must restrict the kg-resolution to kh-resolution before calling this 
// function. rr1,mm1 is the restriction to h of a resolution of k as an 
// fg-module. rr2,mat2 is the resolution of k as an fh-module for h a 
// subgroup of g. RD is the resolution input for h := sgp and f := fld.

fld := CoefficientRing(mat1);
p := Characteristic(fld);
H := PCGroup(RD`Algebra);
snn := #H;
MMT := RD`PCgenMats;
ind := Ncols(mat1) div snn;
first := KMatrixSpace(fld,ind,snn)!0;
first[1,1] := fld!1;
                          //InsertBlock(~first,MatrixAlgebra(fld,1)!1,1,1);
stlt := [0] cat [&+[rr2[i]*rr1[i]:i in [1 .. j]]:j in [1 .. #rr1]];
stlt1 := [0] cat [&+[rr1[i]*rr1[i+1]:i in [1 .. j]]:j in [1 .. #rr1-1]];
stlt2 := [0] cat [&+[rr2[i]*rr2[i+1]:i in [1 .. j]]:j in [1 .. #rr2-1]];
zvec := VectorSpace(fld,snn)!0;
szero := KMatrixSpace(fld,snn,snn)!0;
nml := KMatrixSpace(fld, &+[rr1[i]*rr2[i]:i in [1 .. #rr1]], snn)!0;
InsertBlock(~nml,first,1,1);
for t:= 1 to Minimum(#rr1,#rr2)-1 do
gamma := KMatrixSpace(fld, snn*rr2[t], snn*rr1[t])!0;
for k := 1 to rr1[t] do
   for j := 1 to rr2[t] do
      if nml[stlt[t]+j+rr2[t]*(k-1)] ne zvec then
	 uuu := KMatrixSpace(fld,1,snn)!nml[stlt[t]+j+rr2[t]*(k-1)];
	 InsertBlock(~szero,uuu,1,1);
	 for i := 1 to #MMT do
	    for w := 1 to p-1 do
	       subm := Submatrix(szero*MMT[i],
		       p^(i-1)*(w-1)+1,1,p^(i-1),snn);
	       InsertBlock(~szero,subm,p^(i-1)*w+1,1);
	    end for;
	 end for;
         InsertBlock(~gamma,szero,(j-1)*snn+1,(k-1)*snn+1);
      end if;
   end for;
end for;

delta2 := KMatrixSpace(fld, rr2[t+1], rr2[t]*snn)!0;
for i:= 1 to rr2[t] do
   InsertBlock(~delta2,Submatrix(mat2,stlt2[t]+rr2[t+1]*(i-1)+1,1,\
      rr2[t+1],snn),1,(i-1)*snn+1);
end for;
uu := delta2*gamma;
delta := MatrixOfBoundaryMap(MMT, mat1,stlt1[t],rr1[t+1],
			     rr1[t],snn,fld,p);
qq,ww := IsConsistent(delta,uu);
for i := 1 to rr1[t+1] do
   InsertBlock(~nml,Submatrix(ww,1,snn*(i-1)+1,rr2[t+1],snn),stlt[t+1]+\
      rr2[t+1]*(i-1)+1,1);
end for;
end for;

               return [0] cat [rr1[i]*rr2[i]:i in [1.. #rr1]],nml;

end function;

//**********************************************

intrinsic RestrictionChainMap(PR1::Rec,PR2::Rec) -> MapChn
{Computes the chain map from the resolution PR2 of the trivial module
over the basic algebra of a subgroup to the restricted resolution PR1 
of the basic algebra of a the group. PR1 and PR2 are inputed in 
compact form.}
 
D1 := Algebra(PR1`Module)`ResolutionData;
D2 := Algebra(PR2`Module)`ResolutionData;
num := Maximum(#PR1`BettiNumbers,#PR2`BettiNumbers)-1;
sss, Mat1 := CompactRestrictedResolution(Reverse(PR1`BettiNumbers), 
     PR1`ResolutionRecord,D1,D2,num);
sss, Mat1 := CompactRestrictedResolution(Reverse(PR1`BettiNumbers),
     PR1`ResolutionRecord,D1,D2,num);
ttt, Mat2 := CompactRestrictionChainMap(sss, Mat1, Reverse(PR2`BettiNumbers),
     PR2`ResolutionRecord,D2);
U := RestrictResolution(PR1,D2);
V := ProjectiveResolution(PR2);
L := [* *];
for i := num+1 to 1 by -1 do
    delta := MatrixOfBoundaryMap(D2`PCgenMats,Mat2,
                  &+[ttt[j]:j in [1 .. i]],
		  Reverse(PR2`BettiNumbers)[i],sss[i],
		  Dimension(Algebra(PR2`Module)),
		  CoefficientRing(Mat1),
		  Characteristic(CoefficientRing(Mat1)));
    mu := Hom(Term(V,i-1),Term(U,i-1))!delta;
    Append(~L, mu);
end for;
MM := ChainMap(L,V,U,0);

     return MM;

end intrinsic;

//**********************************************************************

RestrictionChainMapInDegree := function(rr1,Mat,sss, PR2, N); 
// Gives the homomorphism in the chain map from the restriction of the 
// G-resolution to the H-resolution where H is a subgroup of G. rr1 and
// Mat are the and PR2 is the H-resolution in compact form. N is the 
// degree in which we are computing the homomorphism. sss is the 
// list of numbers of rows of the restricted resolution -- as returned
// by the function CompactRestrictedResolution.
 
D2 := Algebra(PR2`Module)`ResolutionData;
delta := MatrixOfBoundaryMap(D2`PCgenMats,Mat,
                  &+[rr1[j]:j in [1 .. N+1]],
		  Reverse(PR2`BettiNumbers)[N+1],sss[N+1],
		  Dimension(Algebra(PR2`Module)),
		  CoefficientRing(Mat),
		  Characteristic(CoefficientRing(Mat)));

     return delta;

end function;

//***********************************************************************

TopOfRestrictionChainMapInDegree := function(rr1,Mat,sss, PR2, N); 


// Gives the homomorphism in the chain map from the restriction of the 
// G-resolution to the H-resolution where H is a subgroup of G. rr1 and
// Mat are the and PR2 is the H-resolution in compact form. N is the 
// degree in which we are computing the homomorphism. sss is the 
// list of numbers of rows of the restricted resolution -- as returned
// by the function CompactRestrictedResolution.
 
D2 := Algebra(PR2`Module)`ResolutionData;
delta := TopOfMatrixOfBoundaryMap(D2`PCgenMats,Mat,
                  &+[rr1[j]:j in [1 .. N+1]],
		  Reverse(PR2`BettiNumbers)[N+1],sss[N+1],
		  CoefficientRing(Mat),
		  Characteristic(CoefficientRing(Mat)));

     return delta;

end function;

//************************************************************************

GetImagePolynomial := function(GR,v,d);

md := [x:x in GR`MonomialData|x[1] eq d];
R := GR`PolRing;
I := GR`RelationsIdeal;
LM := LeadingMonomialIdeal(I);
mm1 := [x:x in md|x[2] notin LM];
mm2 := [Transpose(ModuleMap(x[3],d)):x in mm1];
MM := KMatrixSpace(CoefficientRing(mm2[1]),#mm2,#mm2)!mm2;
a := Solution(MM, v);
pp := &+[a[i]*mm1[i][2]: i in [1 .. #mm2]];

return pp;

end function;

//************************************************************************

GetImagePolynomialList := function(GR,vlst,d);

md := [x:x in GR`MonomialData|x[1] eq d];
R := GR`PolRing;
I := GR`RelationsIdeal;
LM := LeadingMonomialIdeal(I);
mm1 := [x:x in md|x[2] notin LM];
mm2 := [Transpose(ModuleMap(x[3],d)):x in mm1];
MM := KMatrixSpace(CoefficientRing(mm2[1]),#mm2,#mm2)!mm2;
alst := Solution(MM, vlst);
pp := [&+[a[i]*mm1[i][2]: i in [1 .. #mm2]]:a in alst];

return pp;

end function;

//***********************************************************************

intrinsic RestrictionOfGenerators( PR1::Rec, PR2::Rec,
       AC1::Rec, AC2::Rec, REL2::Rec ) -> SeqEnum
{Computes the sequence of images of the generators of the 
cohomology of G restricted to a subgroup H. The input is the 
projective resolutions and cohomology generators for G (PR1 and AC1) 
and for its subgroup (PR2 and AC2), as well as the 
cohomology relations for the subgroup, REL2.} 

ing := Algebra(PR1`Module)`ResolutionData;
ins := Algebra(PR2`Module)`ResolutionData;
ind := Dimension(ing`Algebra) div Dimension(ins`Algebra);
rrg := Reverse(PR1`BettiNumbers);
mmg := PR1`ResolutionRecord;
rrs := Reverse(PR2`BettiNumbers);
mms := PR2`ResolutionRecord;
ggens := AC1`Cocycles;
pol := REL2`PolRing;
fff := CoefficientRing(pol);
numm := Maximum([xx[1]:xx in ggens]);  // the maximum degree of a coho gen.
rrr, mmm := CompactRestrictedResolution(rrg,mmg,ing,ins,numm);
rcr,mcr := CompactRestrictionChainMap(rrr,mmm,rrs,mms,ins);
remat := Transpose(mcr);
GEN := [];

for ww := 1 to numm do           // ww is the degree of the generators for G
   ggensw := [x:x in ggens|x[1] eq ww];
   if #ggensw ne 0 then
      V := VectorSpace(fff,rrs[ww+1]);
      bmat := TopOfRestrictionChainMapInDegree(rcr,mcr,rrr,PR2,ww);
                          // form the matrix of top of the generators
      zmat := KMatrixSpace(fff, ind*rrg[ww+1],1)!0;
      ggvecs := [];
      for x in ggensw do
         mmat := zmat;
         mmat[ind*(x[2]-1)+1][1] := 1;
         Append(~ggvecs, V!Transpose(bmat*mmat));
      end for;
      npols := GetImagePolynomialList(REL2,ggvecs,ww);
      GEN := GEN cat npols;
   end if;
end for;

return GEN;

end intrinsic;

//**********************************************************************

function CompactInflationChainMap(fff, og, oq, rgg, rqq,stlg,stlq, stgq,
				  matl,matq,p,mmg,mmq,numm);

szero := KMatrixSpace(fff,og,oq)!0;
nmm := KMatrixSpace(fff,&+[rgg[i]*rqq[i]:i in [1 .. numm+2]],oq)!0;
nmm[1,1] := 1;
zvec := VectorSpace(fff,oq)!0;
for t:= 1 to numm+1 do
gamma := KMatrixSpace(fff,og*rgg[t], oq*rqq[t])!0;
for k := 1 to rqq[t] do
	for j := 1 to rgg[t] do
	if nmm[stgq[t]+j+rgg[t]*(k-1)] ne 0 then
	uuu := KMatrixSpace(fff,1,oq)!nmm[stgq[t]+j+rgg[t]*(k-1)];
	InsertBlock(~szero,uuu,1,1);
		for i := 1 to #matl do
			for w := 1 to p-1 do
				subm := Submatrix(szero*matl[i],
					p^(i-1)*(w-1)+1,1,p^(i-1),oq);
				InsertBlock(~szero,subm,p^(i-1)*w+1,1);
			end for;
		end for;
	InsertBlock(~gamma,szero,(j-1)*og+1,(k-1)*oq+1);
	end if;
	end for;
end for;

delta2 := KMatrixSpace(fff,rgg[t+1],rgg[t]*og)!0;
for i:= 1 to rgg[t] do
   InsertBlock(~delta2,Submatrix(mmg,stlg[t]+rgg[t+1]*(i-1)+1,1,\
      rgg[t+1],og),1,(i-1)*og+1);
end for;
uu := delta2*gamma;
delta := MatrixOfBoundaryMap(matq, mmq,stlq[t],rqq[t+1],rqq[t],oq,fff,p);
qq,ww := IsConsistent(delta,uu);
for i := 1 to rqq[t+1] do
   InsertBlock(~nmm,Submatrix(ww,1,oq*(i-1)+1,rgg[t+1],oq),stgq[t+1]+\
      rgg[t+1]*(i-1)+1,1);
end for;
end for;

return nmm;

end function;

//*********************************************************************

TopOfInflationChainMap := function(ccm,rrg,rrq,ff,nnn);
//   ccm is the compact inflation chain map. 

tcm := Transpose(ccm);
infr :=  [rrq[i]*rrg[i]:i in [1.. nnn]];
locs := [0] cat [&+[infr[j]: j in [1 .. i]]: i in [1 .. nnn]];
L := [* *];
for j := 1 to nnn do
   mat := KMatrixSpace(ff, rrq[j], rrg[j])!0;
   for k := 1 to rrq[j] do
      InsertBlock(~mat,Submatrix(tcm,1,
	       locs[j]+(k-1)*rrg[j]+1,1,rrg[j]),k,1);
   end for;
   Append(~L,Transpose(mat));
end for;

          return L;

end function;

//*********************************************************************

GetImagePolynomialList := function(GR,vlst,d);

md := [x:x in GR`MonomialData|x[1] eq d];
R := GR`PolRing;
I := GR`RelationsIdeal;
J := [LeadingMonomial(x):x in Basis(I)];
		     // LM := LeadingMonomialIdeal(I);
LM := ideal<R|J>;
mm1 := [x:x in md|x[2] notin LM];
mm2 := [Transpose(ModuleMap(x[3],d)):x in mm1];
MM := KMatrixSpace(CoefficientRing(mm2[1]),#mm2,#mm2)!mm2;
alst := Solution(MM, vlst);
pp := [&+[a[i]*mm1[i][2]: i in [1 .. #mm2]]:a in alst];

return pp;

end function;

//******************************************************************

intrinsic InflationMap(PR2::Rec,  PR1::Rec,  AL2::Rec,
		       AL1::Rec,  RE1::Rec,  theta::Map) -> SeqEnum
{Creates the inflation map from the cohomology ring of a quotient group
with cohomology data (PR2, AC2) to the cohomology ring of the group 
G with cohomology ring data (PR1, AC1, RE1). theta is the quotient map
on the groups.}

A := Algebra(PR1`Module);
B := Algebra(PR2`Module);
inn1 := A`ResolutionData;
inn2 := B`ResolutionData;

pcg := PCGroup(A);
pcq := PCGroup(B);
ggg := Group(A);        // this is the groups G
qqq := Group(B);        // this is the group G/H
SM := GModule(B);
rho := Representation(SM);
id := Action(SM)!1;
phi := PCMap(A);
SMlst := [rho(theta(pcg.i@@phi))-id: i in [1 .. NPCgens(pcg)]];
// this is the list of matrices of the action of the PC generators for G on
// the standard free module for G/H.
rrg := Reverse(PR1`BettiNumbers);
mmg := PR1`ResolutionRecord;
rrq := Reverse(PR2`BettiNumbers);
mmq := PR2`ResolutionRecord;
ggens := AL2`Cocycles;
gchm := AL1`ChainMapRecord;
gchs := AL1`ChainSizes;
gchd := AL1`ChainDegrees;
pol := RE1`PolRing;
fld := CoefficientRing(pol);
p := Characteristic(fld);
numm := Maximum([xx[1]:xx in ggens]);
stlt := [0] cat [&+[rrg[i]*rrq[i]:i in [1 .. j]]:j in [1 .. numm+1]];
stlt1 := [0] cat [&+[rrg[i]*rrg[i+1]:i in [1 .. j]]:j in [1 .. numm]];
stlt2 := [0] cat [&+[rrq[i]*rrq[i+1]:i in [1 .. j]]:j in [1 .. numm]];
nml := CompactInflationChainMap(fld, #ggg, #qqq, rrg, rrq, stlt1,stlt2,
                           stlt, SMlst,inn2`PCgenMats, p, mmg, mmq, numm);
U := TopOfInflationChainMap(nml,rrg,rrq,fld,numm+1);
GEN := [];
for ww := 1 to numm do           // ww is the degree of the generators for G
ggensw := [x:x in ggens|x[1] eq ww];               // print ggensw;
   if #ggensw ne 0 then
      V := VectorSpace(fld,rrg[ww+1]);
      bmat := U[ww+1];
      zmat := KMatrixSpace(fld, rrq[ww+1],1)!0;
      ggvecs := [];
      for x in ggensw do
         mmat := zmat;
         mmat[x[2]][1] := 1;
         Append(~ggvecs, V!Transpose(bmat*mmat));
      end for;
      npols := GetImagePolynomialList(RE1,ggvecs,ww);
      GEN := GEN cat npols;
   end if;
end for;

return GEN;

end intrinsic;

