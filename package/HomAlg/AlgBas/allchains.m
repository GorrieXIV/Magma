freeze;

import "resolve.m":MatrixOfBoundaryMap;
import "resolve.m":ExpandBlock;

intrinsic LiftHomomorphismGroupP(L::SeqEnum) -> ModMatFldElt
{Creates the function from the projective module with L elements
to the parent of the elements of the list L, such that the 
generators of the projective module go to the elements of L.
Note that the algebra must be the basic algebra of a p-group.}

     M := Parent(L[1]);
     A := Algebra(M);
     require Type(A) eq AlgBasGrpP:  "The algebra is not the group
                algebra of a p-group";
     og := Dimension(M);
     RD := ResolutionData(A);
     MM := [Action(M).(i+1): i in [1 .. Ngens(A)-1]];
     ff := BaseRing(A);
     p := Characteristic(ff);
     mat := ExpandBlock(MM, L[1], og, ff, p);
     if #L gt 1 then 
     for i := 2 to #L do
     mat := VerticalJoin(mat, ExpandBlock(MM,L[i],og,ff,p));
end for;
end if;

return mat;

end intrinsic;


//*****************************************************************

intrinsic CohomologyElementToChainMap(P::ModCpx,
 	    d::RngIntElt,n::RngIntElt) -> MapChn
{This function creates a chainmap from the projective resolution P
to itself for the element number n in degree d of cohomology. RD is
the module resolution data. }

A := Algebra(P);
require Type(A) eq AlgBasGrpP: "The algebra is not the group
      algebra of a p-group";

og := Dimension(A);
k := Dimension(Term(P,d)) div og;
vll := [Term(P,0)!0:i in [1 .. k]];
vll[n] := Term(P,0).1;
LL := [* AHom(Term(P,d), Term(P,0))!LiftHomomorphismGroupP(vll)  *];
a, b := Degrees(P);
if a gt d then 
for i := 1 to a-d do
   pd := BoundaryMap(P,d+i);
   p0 := BoundaryMap(P,i);
   mu := pd*LL[1];
   k := Dimension(Term(P,d+i)) div og;
   ull := [mu(Term(P,d+i).((j-1)*og+1)): j in [1 .. k]];
   boo, wll := IsConsistent(p0,ull);
   LL := [* AHom(Term(P,d+i), Term(P,i))!LiftHomomorphismGroupP(wll) *] 
            cat LL;
end for;
end if;

C := ChainMap(LL,P,P,-d);

    return C;

end intrinsic;

//*********************************************************************

FirstChainMaps := function(N,F,R);

// This function creates and stores the first step in the chain maps of 
// degree one. That is it stores the maps from P_1 to P_0 corresponding
// to the degree one cohomology elements. Note that P_0 is one copy of 
// the regular module kG, while P_1 is R[2] copies. The construction 
// here is cononical and we needn't know anything about the resolution
// other than R[2]. Here N is the dimension of the algebra, F is the 
// field of coefficients and R is the list of dimensions of the cohomology 
// groups.


CM := KMatrixSpace(F,R[2]^2,N)!0;
bv := Basis(VectorSpace(F,R[2]));
for i := 1 to R[2] do
   InsertBlock(~CM,Transpose(KMatrixSpace(F,1,R[2])!bv[i]),(i-1)*R[2]+1,1);
end for;

          return CM;

end function;

//********************************************************************




NextChainMapNM := function(RD, PR, CR, cdeg, mdeg, start, ff, og);
//                   res data, proj res, chain data, 
// This function creates and stores the data for the next step in the 
// chain map. It starts with the projective resolution data (rrr,mpp),
// and the chain map data to degree "deg1", the resolution input for
// the group is "rin". Actually it doesn't actually create "phi_{j+1}"
// but rather it stops at making the composition "b_i * phi_j". This
// routine is called by the AllChainMaps routine.

rrr := Reverse(PR`BettiNumbers);
mpp := PR`ResolutionRecord;
ff := CoefficientRing(mpp);
gamma := MatrixOfBoundaryMap(RD`PCgenMats,CR,start,
	       rrr[cdeg+mdeg],rrr[mdeg],og,ff,Characteristic(ff));
stl := [0] cat [&+[rrr[i]*rrr[i+1]:i in [1 .. j]]:j in [1 .. #rrr-1]];
delta := Submatrix(mpp,stl[cdeg+mdeg]+1,1,rrr[cdeg+mdeg+1],og);
for i := 2 to rrr[cdeg+mdeg] do 
    delta := HorizontalJoin(delta, 
               Submatrix(mpp,stl[cdeg+mdeg]+rrr[cdeg+mdeg+1]*(i-1)+1,
			 1,rrr[cdeg+mdeg+1],og));
end for;
uu := delta*gamma;

        return uu;

end function;

//******************************************************************

NextChainMap := function(RD, PR, CR, cdeg, mdeg, start, ff, og, Bdr); 

// This function returns the next map in a chain map starting with the 
// record to that point (CR), the projective resolution (PR) and the 
// ResolutionData (RD). The numbers cdeg and mdeg are the degree of the
// chain map and the degree of the target in the projective resolution.

rrr := Reverse(PR`BettiNumbers);
NCM := NextChainMapNM(RD, PR, CR, cdeg, mdeg, start, ff, og);
bool,LL := IsConsistent(Bdr, NCM);
ZZ := Submatrix(LL,1,1,rrr[mdeg+cdeg+1],og);
if rrr[mdeg+1] gt 1 then
   for i := 2 to rrr[mdeg+1] do
      ZZ := VerticalJoin(ZZ,Submatrix(LL,1,og*(i-1)+1,rrr[mdeg+cdeg+1],og));
   end for;
end if;

return ZZ;

end function;

//******************************************************************

NextChainMapWL := function(RD, PR, CR, cdeg, mdeg, start, ff, og, Bdr); 
       
//This function returns also a list of images. It will be used in 
//CatchUp routine.

rrr := Reverse(PR`BettiNumbers);
NCM := NextChainMapNM(RD, PR, CR, cdeg, mdeg, start, ff, og);
bool,LL := IsConsistent(Bdr, NCM);
ZZ := Submatrix(LL,1,1,rrr[mdeg+cdeg+1],og);
if rrr[mdeg+1] gt 1 then
   for i := 2 to rrr[mdeg+1] do
      ZZ := VerticalJoin(ZZ,Submatrix(LL,1,og*(i-1)+1,rrr[mdeg+cdeg+1],og));
   end for;
end if;
LLL := Transpose(LL);
CC := KMatrixSpace(ff,rrr[mdeg+1],Ncols(LLL))!0;
for i := 1 to rrr[mdeg+1] do 
   CC[i] := LLL[og*(i-1)+1];
end for;  

           return ZZ,CC;

end function;

//*****************************************************************

CatchUp := function(FM,dg,IM,IR,PR,RD,ff, og);

// This is the function to catch-up new generators that are found.
// FM is the matrix of the first step in the chain map, dg is the degree
// that we have to catch up. IM is the matrix of images that has been 
// computed to this point. PR is the projective resolution, RD is the 
// resolution data

img := IM;
imggl:=	IR;
chmat := FM;
rll := Reverse(PR`BettiNumbers);
starts := [0] cat [&+[rll[i]*rll[i+1]:i in [1 ..j]]:j in [1 .. dg]];
sts := [0] cat [&+[rll[i]*rll[i+dg]:i in [1 ..j]]:j in [1 .. #rll-dg]];
for i := 1 to dg-1 do
   delta := MatrixOfBoundaryMap(RD`PCgenMats,PR`ResolutionRecord,
       starts[i],rll[i+1],rll[i],og,ff, Characteristic(ff));
   if i+dg le #rll-1 then
      chmex, ggens := NextChainMapWL(RD, PR, 
		 chmat, dg, i, sts[i], ff, og,delta);
      chmat := VerticalJoin(chmat,chmex);
      immat := InsertBlock(KMatrixSpace(ff,Nrows(ggens),Ncols(IM))!0,ggens,
		     1,imggl[i+dg][1]+1);
      loc := &+[imggl[j][2]:j in [1..i+dg]];
      if loc eq Nrows(img) then 
         img := VerticalJoin(img, immat);
      else 
         img1 := VerticalJoin(Submatrix(img,1,1,loc,Ncols(img)),immat);
         img1 := VerticalJoin(img1, 
                Submatrix(img,loc+1,1, Nrows(img)-loc,Ncols(img)));
         img := img1;
      end if;
      imggl[i+dg] := <imggl[i+dg][1],imggl[i+dg][2]+Nrows(immat)>;
   end if; 
end for;

          return chmat, img, imggl;

end function;



//*****************************************************************

intrinsic CohomologyElementToCompactChainMap(PR::Rec,
	     d::RngIntElt,n::RngIntElt) -> ModMatFldElt

{This function creates a chainmap from the projective resolution PR 
in compact form to itself for the element number n in degree d of 
cohomology.} 

RD := PR`ResolutionData;
og := Ncols(PR`ResolutionRecord);
ff := CoefficientRing(PR`ResolutionRecord);
rll := Reverse(PR`BettiNumbers);
m := KMatrixSpace(ff,og,rll[d+1])!0;
m[1] := Basis(VectorSpace(ff,rll[d+1]))[n];
chmat:= Transpose(m);
starts := [0] cat [&+[rll[i]*rll[i+1]:i in [1 ..j]]:j in [1 .. #rll-1]];
sts := [0] cat [&+[rll[i]*rll[i+d]:i in [1 ..j]]:j in [1 .. #rll-d]];
for i := 1 to #rll-d do
   delta := MatrixOfBoundaryMap(RD`PCgenMats,PR`ResolutionRecord,
       starts[i],rll[i+1],rll[i],og,ff,Characteristic(ff));
   if i+d le #rll-1 then
      chmex := NextChainMap(RD, PR, 
		chmat, d, i, sts[i], ff, og,delta);
      chmat := VerticalJoin(chmat,chmex);
   end if; 
end for;

          return chmat;

end intrinsic;


//*********************************************************************


ChainMapExtension := function(alc,prj,resin,og,fld,rkl,sts,i)

mpl := prj`ResolutionRecord;
     chmat := alc[1];
     chmapsize := alc[2];
     chmapdeg := alc[3];
     genlst := alc[4];
     image := alc[5];
     imlst := alc[6];
     boolst := [];     
   for s := 1 to #chmapdeg do
      ttt := exists(t){x:x in [1 .. #rkl+1-chmapdeg[s]]|chmapsize[s] eq
         &+[rkl[k]*rkl[k+chmapdeg[s]]:k in [1 ..x]]};
      if t eq i then 
         boolst[s] := true;
      else boolst[s] := false;
      end if;
   end for;
   delta := MatrixOfBoundaryMap(resin`PCgenMats,mpl,sts[i],rkl[i+1],
	    rkl[i],og,fld, Characteristic(fld));
   trmapsize := [];
   nlst := [];
   for r := 1 to #chmapsize do 
      if i+chmapdeg[r] le #rkl-1 and boolst[r] then
         Append(~trmapsize,rkl[i+1]*rkl[i+chmapdeg[r]+1]);
         Append(~nlst,rkl[i+chmapdeg[r]+1]);
      else 
         Append(~trmapsize,0);
         Append(~nlst,0);
      end if;
   end for;

if &+nlst ne 0 then
   newmapsize := [chmapsize[j]+trmapsize[j]: j in [1 .. #chmapsize]];
   newmat := KMatrixSpace(fld,&+newmapsize,og)!0;
   trmat := KMatrixSpace(fld,&+[nlst[j]:j in [1 .. #nlst]],rkl[i]*og)!0;
   for j := 1 to #chmapdeg do
      d := chmapdeg[j];
      if i+d le #rkl-1 then
	 chmext := NextChainMapNM(resin,prj,chmat,d,i,
		&+[chmapsize[k]:k in [1 .. j]]-rkl[i]*rkl[i+d],fld,og);
	 InsertBlock(~trmat,chmext,
	       &+[nlst[k]:k in [1 ..j]]-nlst[j]+1,1);
      end if;
   end for;
   qq,ww := IsConsistent(delta,trmat);
   for j := 1 to #chmapdeg do
      d := chmapdeg[j];
      InsertBlock(~newmat,Submatrix(chmat, 
	   &+[chmapsize[k]:k in [1..j]]-chmapsize[j]+1,1,chmapsize[j],og),
	   &+[newmapsize[k]:k in [1..j]]-newmapsize[j]+1,1);
      if i +chmapdeg[j] le #rkl-1 and boolst[j] then
	 for l := 1 to rkl[i+1] do
	    InsertBlock(~newmat,Submatrix(ww,&+[nlst[k]:k in [1 ..j]]
                   -nlst[j]+1,(l-1)*og+1,rkl[i+d+1],og),&+[newmapsize[k]:k 
		   in [1..j]]-rkl[i+1]*rkl[i+d+1]+(l-1)*rkl[i+d+1]+1,1);
         end for;
      end if;
   end for;
   chmat := newmat;
   chmapsize := newmapsize;
   testmat := KMatrixSpace(fld,&+nlst,rkl[i+1])!0;
   for l := 1 to rkl[i+1] do
      InsertBlock(~testmat,Submatrix(ww,1,(l-1)*og+1,&+nlst,1),1,l);
   end for;
   testmat1 := Transpose(testmat);
   for l := 1 to #chmapdeg do
      d := chmapdeg[l];
      if i+d le #rkl-1 then
      loc := &+[imlst[j][2]:j in [1..i+d]];
	 amat := InsertBlock(KMatrixSpace(fld,Nrows(testmat1),
	         Ncols(image))!0, Submatrix(testmat1,1,
                 &+[nlst[k]:k in [1..l]]-nlst[l]+1,Nrows(testmat1),
	         nlst[l]),1,imlst[i+d][1]+1);
	 im1 := VerticalJoin(Submatrix(image,1,1,loc,Ncols(image)),
	         amat);
	 if &+[imlst[j][2]:j in [1..i+d]] ne Nrows(image) then
              im1 := VerticalJoin(im1, Submatrix(image,loc+1,1,
              Nrows(image)-loc,Ncols(image)));
         end if;
         image := im1;
         imlst[i+d] := <imlst[i+d][1],imlst[i+d][2]+Nrows(testmat1)>;
      end if;
   end for;
   if i+2 le #rkl then
      zz := VectorSpace(fld,rkl[i+2]);
            ngs := [x:x in genlst|x[1] eq i+1];
      uu:= Submatrix(image,&+[imlst[j][2]:j in [1..i]]+1, 
     		imlst[i+1][1]+1,imlst[i+1][2],rkl[i+2]);
      rspc := sub<zz|[uu[i]:i in [1 .. Nrows(uu)]] cat 
            [Basis(zz)[x[2]]:x in ngs]>;
      extr := ExtendBasis(rspc,zz);
      exb := [extr[k]: k in [Dimension(rspc)+1 .. Dimension(zz)]];
      cmatt := KMatrixSpace(fld,rkl[i+2],og)!0;
      for k := 1 to #exb do
         InsertBlock(~cmatt,Transpose(Hom(VectorSpace(fld,1),
                VectorSpace(fld,rkl[i+2]))!exb[k]),1,1);
         newcmp, newimage, newimlst := 
                CatchUp(cmatt,i+1,image,imlst,prj,resin,fld,og);
         ddd := Nrows(newcmp);
         chmat1 := KMatrixSpace(fld,ddd+Nrows(chmat),og)!0;
         InsertBlock(~chmat1,chmat,1,1);
         InsertBlock(~chmat1,newcmp,Nrows(chmat)+1,1);
         chmat := chmat1;
         image := newimage;
         imlst := newimlst;
         chmapdeg := chmapdeg cat [i+1];
         chmapsize := chmapsize cat [ddd];
      end for;
      if #exb ne 0 then
         numlst := [];
         BB := Basis(zz);
         for q := 1 to #exb do
            for j := 1 to #BB do 
               if exb[q] eq BB[j] then 
	          Append(~numlst,<i+1,j>);
	       end if;
	    end for;
         end for;
         genlst := genlst cat numlst;
      end if;
   end if;
   end if;

return <chmat,chmapsize,chmapdeg,genlst,image,imlst>;

end function;

//*********************************************************************


intrinsic AllCompactChainMaps(pror::Rec) -> Rec
{Computes the information about the chain maps for all generators of the
cohomology of the simple module for the basic algebra of the group algebra
in degrees within the limits of the compact projective resolution data.}

M := pror`Module;
rkl := Reverse(pror`BettiNumbers);
resin := Algebra(M)`ResolutionData;
if assigned M`AllCompactChainMaps then
   aaa := M`AllCompactChainMaps;
      if #pror`BettiNumbers le #aaa`ProductLocations+1 then
               return aaa;
   else 
      A := Algebra(M);
      fld := CoefficientRing(resin`PCgenMats[1]);
      sts := [0] cat [&+[rkl[i]*rkl[i+1]:i in [1 .. j]]: j in [1 .. #rkl-1]];
      n := #aaa`ProductLocations;
      m := Maximum(aaa`ChainDegrees);
      imlst := aaa`ProductLocations cat 
            [<&+[rkl[j]:j in [2..i-1]],0>:i in [n+2 .. #rkl]];
      image := HorizontalJoin(aaa`ProductRecord, 
            KMatrixSpace(fld,Nrows(aaa`ProductRecord),
	    &+[rkl[j]:j in [n+1 .. #rkl]])!0);
      aaa := <aaa`ChainMapRecord,aaa`ChainSizes,aaa`ChainDegrees,
            aaa`Cocycles,image,imlst>;
      for i := n-m+1 to #rkl-2 do 
         aaa := ChainMapExtension(aaa,pror,resin,Dimension(A),fld,rkl,sts,i);
      end for;
   end if;
else
   A := Algebra(M);
   fld := CoefficientRing(resin`PCgenMats[1]);
   sts := [0] cat [&+[rkl[i]*rkl[i+1]:i in [1 .. j]]: j in [1 .. #rkl-1]];
   genlst := [<1,i>:i in [1 .. rkl[2]]];
   chmapsize := [rkl[2] : i in [1..rkl[2]]];
   chmapdeg := [1 : i in [1..rkl[2]]];
   imlst := [<0,rkl[2]>] cat [<&+[rkl[j]:j in [2..i-1]],0>:i in [3.. #rkl]];
   image := KMatrixSpace(fld,rkl[2], &+rkl-1)!0;
   InsertBlock(~image,BasisMatrix(VectorSpace(fld,rkl[2])),1,1);
   chmat := FirstChainMaps(Dimension(A),fld,rkl);
   aaa := <chmat,chmapsize,chmapdeg,genlst,image,imlst>;
   for i := 1 to #rkl-2 do 
      aaa := ChainMapExtension(aaa,pror,resin,Dimension(A),fld,rkl,sts,i);
   end for;
end if;
rrff := recformat<ChainMapRecord:Parent(aaa[1]), ChainSizes:SeqEnum,
	ChainDegrees:SeqEnum, Cocycles:SeqEnum,
	ProductRecord:Parent(aaa[5]), ProductLocations:SeqEnum>;
bbb := rec<rrff|ChainMapRecord:= aaa[1],ChainSizes:= aaa[2],
        ChainDegrees:= aaa[3], Cocycles:=aaa[4], 
        ProductRecord:=aaa[5],ProductLocations:=aaa[6]>;
M`AllCompactChainMaps := bbb;

            return bbb;

end intrinsic;

