freeze;

//We need function for
//   BoundaryMap -- of a projective resolution
//   Complex -- turn the projective resolution into a complex
//   Chain map -- of a cohomology element
//   Chain map -- of a cohomology element in a certain degree
   

ChangeOfBasisMatrix := function(F,p,M,GNS,ex);

MM := MatrixAlgebra(F,Dimension(M));
id := MM!1;
uu := id;
RL := [Representation(M)(GNS[i])-id:i in [1 .. ex]];
for i := 1 to ex do
   x := RL[i];
   nn := p^(i-1);
   for k := 1 to p-1 do
      InsertBlock(~uu,Submatrix(uu,nn*(k-1)+1,1,nn,p^ex)*x,nn*k+1,1);
   end for;
end for;
NL := [uu*x*uu^-1:x in RL];

	return uu,NL;

end function;

//**********************************************************************

intrinsic ResolutionData(A::AlgBasGrpP) -> Rec
{The data needed to compute the projective resolution of an A-module}

G := PCGroup(A);
fac := FactoredOrder(G)[1][2];
mlst := [Action(ProjectiveModule(A,1)).i : i in [2 .. fac+1]];
H := FrattiniSubgroup(G);
glst := [];
for i := 1 to fac do
   H2 := sub<G | H, G.i>;
   if #H2 gt #H then 
      H := H2;
      Append(~glst,i);
   end if;
   if #H eq #G then 
      break;
   end if;
end for;
Mlst := [mlst[x]: x in glst];
rrff := recformat<PCgenMats:SeqEnum,MingenMats:SeqEnum,Algebra:AlgBasGrpP>; 
dta := rec<rrff|PCgenMats := mlst, MingenMats := Mlst, Algebra := A>;
A`ResolutionData := dta;

	return dta;

end intrinsic;


//*******************************************************************

ExpandBlock := function(ML, vec, og, F, p);
// ML is the list of matrices of the actions of the PC generators of G
// on the free kG module, vec is a vector in a copy of the group
// algebra kG, og is the order of G and F is the field. The function
// returns the matrix of kG -- > kG that takes the identity element to vec.

szero := KMatrixSpace(F,1,og)!Vector(vec);
vec := Vector(vec);
szero := vec;
for i := 1 to #ML do
   subm := szero;
   for j := 1 to p-1 do
        subm := subm*ML[i];
        szero := VerticalJoin(szero, subm);
   end for;
end for;

        return szero;

end function;

//**********************************************************************

MatrixOfBoundaryMap := function(ML, matrec, start, nor, noc, og, F, p);
// ML is the list of matrices of the actions of the PC generators of G
// on the free kG module, matrec, is the matrix that has the bounday
// maps encoded, start is the starting point for the boundary map that
// we are creating in terms of the rows of the matrix of matrec, nor and
// noc are the numbers of rows and columns of the boundary map. 
// The function returns the matrix of the boundary map. 

delta := KMatrixSpace(F,nor*og,noc*og)!0;
zvec := VectorSpace(F,og)!0;
for i := 1 to noc do
   for j := 1 to nor do
        aa := matrec[start+(i-1)*nor+j];
        if aa ne zvec then 
	    blk := ExpandBlock(ML,aa,og,F,p);
	    InsertBlock(~delta,blk,(j-1)*og+1,(i-1)*og+1);
	end if;
   end for;
end for;

	return delta;

end function;

//**********************************************************************

TopOfMatrixOfBoundaryMap := function(ML, matrec, start, nor, noc, F, p);
// ML is the list of matrices of the actions of the PC generators of G
// on the free kG module, matrec, is the matrix that has the bounday
// maps encoded, start is the starting point for the boundary map that
// we are creating in terms of the rows of the matrix of matrec, nor and
// noc are the numbers of rows and columns of the boundary map. 
// The function returns the matrix of the boundary map. 

delta := KMatrixSpace(F,nor,noc)!0;
for i := 1 to noc do
   for j := 1 to nor do
        delta[j,i] := matrec[start+(i-1)*nor+j][1];
   end for;
end for;

	return delta;

end function;

//******************************************************************

GeneratorsOfRadical := function(delta, GL, F, nor,og);
// delta is the compact form of the boundary map, GL is the list of
// actions of the minimal generators of the group on a free module
// as given in the ResolutionData part 2.


nullsp := NullSpace(delta);
dnull := Dimension(nullsp);
mker := BasisMatrix(nullsp);
www := KMatrixSpace(F,dnull*#GL,nor*og)!0;
for j := 1 to nor do
	subker := Submatrix(mker,1,(j-1)*og+1,dnull,og);
	for i := 1 to #GL do
	InsertBlock(~www,subker*GL[i],(i-1)*dnull+1,(j-1)*og+1);
	end for;
end for;
nullrad := RowSpace(www);
extra := ExtendBasis(nullrad,nullsp);
seqex := [extra[i]:i in [Dimension(nullrad)+1 .. #extra]];
corad := KMatrixSpace(BaseRing(delta),#seqex,nor*og)!seqex;

	return corad;

end function;

//********************************************************************

RecordBoundaryMap := function(RM, MM, rks, F, nor, og);

uu := Nrows(RM);
rks1 := Append(rks,uu);
if MM eq 0 then 
   MMM := Submatrix(RM,1,1,uu,og);
else
   MMM := VerticalJoin(MM,Submatrix(RM,1,1,uu,og));
end if;
if nor gt 1 then
for j := 2 to nor do
MMM := VerticalJoin(MMM,Submatrix(RM,1,(j-1)*og + 1,uu,og));
end for;
end if;

	return MMM,rks1;

end function;


//*******************************************************************

ResolutionStep := function(rks,MM,RD);

og := Ncols(MM);
F := Parent(MM[1][1]);
p := Characteristic(F);
nnr := rks[#rks];
nnc := rks[#rks-1];
star := Nrows(MM) - nnr*nnc;
Del := MatrixOfBoundaryMap(RD`PCgenMats,MM,star,nnr,nnc,og,F,p);
Rad := GeneratorsOfRadical(Del,RD`MingenMats,F,nnr,og);
NMM,nrks := RecordBoundaryMap(Rad,MM,rks,F,nnr,og);

	return nrks, NMM;

end function;

//*******************************************************************

LiftHomomorphismFromFreeModule := function(M,EL);
// Creates the matrix of the homomorphism from a free module to the
// given module M, having generators EL.

A := Algebra(M);
F := CoefficientRing(M);
p := Characteristic(F);
og := Dimension(A);
MM := KMatrixSpace(F,og*#EL,Dimension(M))!0;
RL := [Action(M).(i+1): i in [1 .. #NonIdempotentGenerators(A)]];
for t := 1 to #EL do
   SZ := KMatrixSpace(F,og,Dimension(M))!0;
   SZ[1] := EL[t];
   for i := 1 to #RL do
      for j := 1 to p-1 do
         subm := Submatrix(SZ*RL[i],p^(i-1)*(j-1)+1,1,p^(i-1),Dimension(M));
         InsertBlock(~SZ,subm,p^(i-1)*j+1,1);
      end for;
   end for;
   InsertBlock(~MM,SZ,(t-1)*og+1,1);
end for;

	return MM;

end function;

//***************************************************************

FirstResolutionStep := function(M, RD);
// Returns the first step in the resolution of the module M. RD is 
// the resolution data. 

A := Algebra(M);
nn := #NonIdempotentGenerators(A);
Mmm := RD`PCgenMats;
F := BaseRing(Mmm[1]);
p := Characteristic(F);
og := Nrows(Mmm[1]);
dim := Dimension(M);
RadMat := KMatrixSpace(F,dim*nn,dim)!0;
for i := 1 to nn do
   InsertBlock(~RadMat,Action(M).(i+1),(i-1)*dim+1,1);
end for;
Rad := RowSpace(RadMat);
Ex := ExtendBasis(Rad,VectorSpace(F,dim));
CE := [Ex[i] : i in [Dimension(Rad)+1 .. #Ex]];
rks := [#CE];

// CE is a complete set of generators for M. These should be the
// images of the generators of a free module. 

Map := LiftHomomorphismFromFreeModule(M,CE);
CR := GeneratorsOfRadical(Map,RD`MingenMats,F,#CE,og);
MMM,rks := RecordBoundaryMap(CR,0,rks,F,#CE,og);

	return rks, MMM, Map;

end function;

//*****************************************************************

intrinsic CompactProjectiveResolutionPGroup(M::ModAlgBas, n::RngIntElt ) -> Rec
{This routine runs the projective resolution of the module M
out to n steps.}

A := Algebra(M);
require Type(A) eq AlgBasGrpP: "Algebra is not the basic algebra of a p-group";
if assigned M`CompactProjectiveResolutionPGroup then 
   cpr1 := M`CompactProjectiveResolutionPGroup;
   RD := A`ResolutionData;
   aa := Reverse(cpr1`BettiNumbers);
   mu := cpr1`AugmentationMap;
   if #aa le n then
      bb := cpr1`ResolutionRecord;
      for i := #aa to n do
         aa, bb := ResolutionStep(aa,bb,Algebra(M)`ResolutionData);
      end for;
      rf := recformat<BettiNumbers:SeqEnum,ResolutionRecord:
            ModMatFldElt,Module:ModAlgBas,
            AugmentationMap:ModMatFldElt, Typ:MonStgElt>;
      cpr1 := rec<rf|BettiNumbers := Reverse(aa),ResolutionRecord := bb, 
            Module := M, AugmentationMap := mu, 
            Typ := "ProjectiveResolution">;
   end if;
   M`CompactProjectiveResolutionPGroup := cpr1;
   M`CompactProjectiveResolution := cpr1;

     return cpr1;

end if;
if assigned A`ResolutionData then
   RD := A`ResolutionData;
else 
   RD := ResolutionData(A);
end if;
aa, bb, mu := FirstResolutionStep(M,RD);
muu := AHom(DirectSum([ProjectiveModule(A,1):i in [1 .. aa[1]]]),M)!mu;
if aa eq [0] then
	return 0,0;
end if;
for i := 2 to n do
   aa, bb := ResolutionStep(aa,bb,RD);
end for;
   rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:
            ModMatFldElt,Module:ModAlgBas,
            AugmentationMap:ModMatFldElt, Typ:MonStgElt>;
   cpr1 := rec<rf|BettiNumbers := Reverse(aa),ResolutionRecord := bb, 
            Module := M, AugmentationMap := muu, 
            Typ := "ProjectiveResolution">;
   M`CompactProjectiveResolutionPGroup := cpr1;
   M`CompactProjectiveResolution := cpr1;
	return cpr1;    ;

end intrinsic;

//*******************************************************************

intrinsic ProjectiveResolutionPGroup(PR::Rec) -> ModCpx
{Takes the compact projective resolution PR1 and returns the resolution 
to a complex of G-modules}

B := Algebra(PR`Module);
F := ProjectiveModule(B,1);
rrr := Reverse(PR`BettiNumbers);
RD := B`ResolutionData;
Mat1 := PR`ResolutionRecord;
FL := [DirectSum([F:j in [1 .. rrr[i]]]):i in [1 .. #rrr]];
L := [* *];
stlt := [0] cat [rrr[i]*rrr[i+1]:i in [1 .. #rrr-2]];
for i := #rrr-1 to 1 by -1 do
   M := MatrixOfBoundaryMap(RD`PCgenMats,Mat1,&+[stlt[j]: j in [1 ..i]], 
          rrr[i+1], rrr[i], Ncols(Mat1), BaseRing(Mat1), 
          Characteristic(BaseRing(Mat1)));
   Append(~L, Hom(FL[i+1],FL[i])!M);
end for;
C := Complex(L,0);

return C;

end intrinsic;
	
//*******************************************************************

intrinsic BoundaryMapGrpP(PR::Rec,n::RngIntElt) -> ModMatFldElt
{Takes the compact projective resolution PR1 and returns the boundary
map in degree n as a map of G-modules}

B := Algebra(PR`Module);
F := ProjectiveModule(B,1);
rrr := Reverse(PR`BettiNumbers);
require n in [1 .. #rrr-1]:"Argument 2 must be in the range 1 .. rrr-1";
RD := B`ResolutionData;
Mat1 := PR`ResolutionRecord;
FD := DirectSum([F:j in [1 .. rrr[n+1]]]);
FR := DirectSum([F:j in [1 .. rrr[n]]]);
stlt := [0] cat [rrr[i]*rrr[i+1]:i in [1 .. #rrr-2]];
M := MatrixOfBoundaryMap(RD`PCgenMats,Mat1,&+[stlt[j]: j in [1 ..n]], 
          rrr[n+1], rrr[n], Ncols(Mat1), BaseRing(Mat1), 
          Characteristic(BaseRing(Mat1)));
MM := AHom(FD,FR)!M;
 
   return MM;

end intrinsic;
	
