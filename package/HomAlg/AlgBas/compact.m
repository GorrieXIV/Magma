freeze;

import "algebras.m": ListSummandIndices;

CreateBoundaryMap := function(CM,A);

MA := CM[1];
DL := CM[2];
RL := CM[3];
dimlst := [Dimension(ProjectiveModule(A,i)):i in [1 .. #DL]];
doml := &cat[[dimlst[j]:t in [1 ..DL[j]]]:j in [1 .. #DL]];
ranl := &cat[[dimlst[j]:t in [1 ..RL[j]]]:j in [1 .. #DL]];
ff := BaseRing(A);
omap := KMatrixSpace(ff,&+doml,&+ranl)!0;
dloc := [0] cat [&+[doml[i]:i in [1..j]]:j in [1.. #doml]];
rloc := [0] cat [&+[ranl[i]:i in [1..j]]:j in [1..#ranl]];
dl := ListSummandIndices(DL);
rl := ListSummandIndices(RL);
W,ilst,plst := DirectSum([VectorSpace(ff,ranl[j]):j in [1..#ranl]]);
for i := 1 to #dloc-1 do
   for j := 1 to #rloc-1 do
      m := plst[j](MA[i]);
      if m ne plst[j](W!0) then
         mmat := LiftHomomorphism(ProjectiveModule(A,rl[j])!m,dl[i]);
         InsertBlock(~omap,mmat,dloc[i]+1,rloc[j]+1);
      end if;
   end for;
end for;

   return omap;

end function;

//*******************************************************************

FirstBoundaryMat := function(M);
 
alg := Algebra(M);
n1 := NumberOfProjectives(alg);
g1 := Ngens(alg);
ff := BaseRing(alg);
prj, phi, xxu,xxv, p1l := ProjectiveCover(M);
K,mu := sub<prj|Kernel(phi)>;
if Dimension(K) eq 0 then 
   return <0,[0:i in [1 .. n1]],p1l>,phi;
end if;
J := JacobsonRadical(K);
Q, theta := quo<K|J>;
mmat := KMatrixSpace(ff,Dimension(Q),Dimension(prj))!0;
if n1 gt 1 then
   nn := 0;
   ppl :=  [0:i in [1 .. n1]];
   for i := 1 to n1 do
      Bi := [x@@theta:x in Basis(RowSpace(Action(Q).i))];
      for j := 1 to #Bi do
         mmat[nn+j] := 
                VectorSpace(ff,Dimension(prj))!mu(Bi[j]*Generators(alg)[i]);
      end for;
      nn := nn+#Bi;
      ppl[i] := #Bi;
   end for;
else
   BB := [x@@theta:x in Basis(Q)];
   for j := 1 to #BB do
      mmat[j] := VectorSpace(ff,Dimension(prj))!mu(BB[j]);
   end for;
   ppl := [Dimension(Q)];
end if;

       return <mmat,ppl,p1l>,phi;

end function;

//*********************************************************************

FirstBoundaryMatD := function(M,dplst);
// this function is for the deleted resolution. The dplst is the list
// projectives that are NOT deleted.  

alg := Algebra(M);
n1 := NumberOfProjectives(alg);
g1 := Ngens(alg);
ff := BaseRing(alg);
prj, phi, xxu,xxv, p1l := ProjectiveCover(M);
KK, gamma := Kernel(phi);
K,mu := sub<KK|&+[RowSpace(Action(KK).i):i in dplst]>; 
if Dimension(K) eq 0 then 
   return <0,[0:i in [1 .. n1]],p1l>,phi;
end if;
J := JacobsonRadical(K);
Q, theta := quo<K|J>;
mmat := KMatrixSpace(ff,Dimension(Q),Dimension(prj))!0;
if n1 gt 1 then
   nn := 0;
   ppl :=  [0:i in [1 .. n1]];
   for i in dplst do
      Bi := [x@@theta:x in Basis(RowSpace(Action(Q).i))];
      for j := 1 to #Bi do
         mmat[nn+j] := 
           VectorSpace(ff,Dimension(prj))!gamma(mu(Bi[j]*Generators(alg)[i]));
      end for;
      nn := nn+#Bi;
      ppl[i] := #Bi;
   end for;
else
   BB := [x@@theta:x in Basis(Q)];
   for j := 1 to #BB do
      mmat[j] := VectorSpace(ff,Dimension(prj))!mu(BB[j]);
   end for;
   ppl := [Dimension(Q)];
end if;

       return <mmat,ppl,p1l>,phi;

end function;

//***********************************************************************

ResolutionStep := function(CM,A,mg);

if &+CM[2] eq 0 then 
     return <0,CM[2],CM[2]>;
end if;
ff := BaseRing(A);
nn := NumberOfProjectives(A);
nng := Ngens(A) - #CM[2];//the number of nonidempotent generators 
pjl := CM[2];
mm := &+[pjl[i]*Dimension(ProjectiveModule(A,i)):i in [1 .. #pjl]];
                              // the dimesnion of the projective module
lll := ListSummandIndices(pjl);
prl := [Dimension(ProjectiveModule(A,lll[i])):i in [1 .. #lll]];
prln := [0] cat [&+[prl[j]: j in [1 .. i]]:i in [1 .. #prl]];
prj := VectorSpace(ff,mm);
delta := CreateBoundaryMap(CM,A);
nul := NullSpace(delta);
if Dimension(nul) eq 0 then
   return <0,[0:i in [1 .. nn]],CM[2]>;
end if;
dnull := Dimension(nul); 

TOS := func<X | SparseMatrix(X)>;
www := SparseMatrix(ff,dnull*nng,mm);

mker := TOS(BasisMatrix(nul));

for i := 1 to #prl do
   subk := Submatrix(mker,1,prln[i]+1,dnull,prl[i]);
   for j := 1 to #mg do
      a := Action(ProjectiveModule(A,lll[i])).mg[j];
      InsertBlock(~www,subk*TOS(a), (j-1)*dnull+1,prln[i]+1);
   end for;
end for;
nrad := RowSpace(www);
if nn eq 1 then
   ext := ExtendBasis(nrad,nul); 
   top := KSpaceWithBasis([ext[i]:i in [Dimension(nrad)+1 .. #ext]]);
   nmap := BasisMatrix(top);
   nlst := [Dimension(top)];      
else
   nlst := [];
   nmap := KMatrixSpace(ff,dnull-Dimension(nrad),mm)!0;
   rind := 0;
   for t := 1 to nn do
      www := SparseMatrix(ff,dnull,mm);
      for i := 1 to #prl do
         subk := Submatrix(mker,1,prln[i]+1,dnull,prl[i]);
         InsertBlock(~www,subk*TOS(Action(ProjectiveModule(A,lll[i])).t),
		     1,prln[i]+1);
      end for;
      nrs := RowSpace(www);
      if nrs subset nrad then
         nlst[t] := 0;
      else 
         int := nrs meet nrad;
         ext := ExtendBasis(int,nrs);
         top := KSpaceWithBasis([ext[i]:i in [Dimension(int)+1 .. #ext]]);
         pmap := BasisMatrix(top);
         InsertBlock(~nmap,pmap,rind+1,1);
         rind := rind+Dimension(top);
         nlst[t] := Dimension(top);
      end if;
   end for;
end if;

                  return <nmap,nlst,CM[2]>;

end function;

//***********************************************************************

ResolutionStepD := function(CM,A,dplst);
// This function computes a step in a deleted resolution. Here, dplst
// is the list of projectives that are not deleted. 

if &+CM[2] eq 0 then 
     return <0,CM[2],CM[2]>;
end if;
ff := BaseRing(A);
nn := NumberOfProjectives(A);
nng := Ngens(A) - #CM[2];//the number of nonidempotent generators 
pjl := CM[2];  // the number of projective modules;
mm := &+[pjl[i]*Dimension(ProjectiveModule(A,i)):i in [1 .. #pjl]];
                              // the dimesnion of the projective module
lll := ListSummandIndices(pjl);
prl := [Dimension(ProjectiveModule(A,lll[i])):i in [1 .. #lll]];
prln := [0] cat [&+[prl[j]: j in [1 .. i]]:i in [1 .. #prl]];
prj := VectorSpace(ff,mm);
delta := CreateBoundaryMap(CM,A);
nul := NullSpace(delta);
if Dimension(nul) eq 0 then
   return <0,[0:i in [1 .. nn]],CM[2]>;
end if;
dnull := Dimension(nul); 
mker := BasisMatrix(nul);

      //make list of terminal indices of nonidempotent generators
tinx := [[j: j in [1 .. nn]|
	   NonIdempotentGenerators(A)[i]*IdempotentGenerators(A)[j] ne 0][1]
	   : i in [1 .. nng]];			
ntinx := [i: i in [1 .. nng]| tinx[i] notin dplst];

www := KMatrixSpace(ff,dnull*#dplst,mm)!0;

for i := 1 to #prl do
   subk := Submatrix(mker,1,prln[i]+1,dnull,prl[i]);
   for j := 1 to #dplst do
      InsertBlock(~www,subk*Action(ProjectiveModule(A,lll[i])).dplst[j],
		(j-1)*dnull+1,prln[i]+1);
   end for;
end for;
        // this is the image of the idempotents on the kernel
        // now we must get the radical generators

nmod1 := RowSpace(www);
mker1 := BasisMatrix(nmod1);

// PPP := DirectSum([ProjectiveModule(A,x): x in lll]);    //QQQQQQQQQQQQQQQQQ
// mmmm := sub<PPP|[PPP!mker1[i]: i in [1 .. Nrows(mker1)]]>;
// print Dimension(mmmm), Dimension(JacobsonRadical(mmmm));
//     print [Rank(Action(mmmm).i): i in [1 .. nn]];
// qqqq := quo<mmmm|JacobsonRadical(mmmm)>;
// print [Rank(Action(qqqq).i): i in [1 .. nn]];
// uuuu := sub<PPP|[PPP!BasisMatrix(nul)[i]: i in [1 .. Dimension(nul)]]>;
// print mmmm subset uuuu;
// if Dimension(mmmm) lt Dimension(uuuu) then 
// qqqq1 := quo<uuuu|mmmm>;
// print [Rank(Action(qqqq1).i): i in [1 .. nn]];
// else 
// print "dimensions are equal";
//  end if;

flag := true;
while flag do 
   nmod := nmod1;
   www1 := KMatrixSpace(ff,Nrows(mker1)*#ntinx,mm)!0;
   for i := 1 to #prl do
      subk := Submatrix(mker1,1,prln[i]+1,Nrows(mker1),prl[i]);
      for j := 1 to #ntinx do
         InsertBlock(~www1,
		     subk*Action(ProjectiveModule(A,lll[i])).(nn+ntinx[j]),
                     (j-1)*Nrows(mker1)+1,prln[i]+1);
      end for;
   end for;
   www2 := VerticalJoin(mker1,www1);
   nmod1 := RowSpace(www2);
   mker1 := BasisMatrix(nmod1);
   if Dimension(nmod1) eq Dimension(nmod) then
      flag := false;
      nmod :=  nmod1;
   end if;
end while;



                         // now we have the module. we must get the radical

www := KMatrixSpace(ff,Nrows(mker1)*nng,mm)!0;
for i := 1 to #prl do
   subk := Submatrix(mker1,1,prln[i]+1,Nrows(mker1),prl[i]);
   for j := 1 to nng do
      InsertBlock(~www,subk*Action(ProjectiveModule(A,lll[i])).(nn+j),
                (j-1)*Nrows(mker1)+1,prln[i]+1);
   end for;
end for;
nrad := RowSpace(www);

if nn eq 1 then
   ext := ExtendBasis(nrad,nmod); 
   top := KSpaceWithBasis([ext[i]:i in [Dimension(nrad)+1 .. #ext]]);
   nmap := BasisMatrix(top);
   nlst := [Dimension(top)];      
else
   nlst := [0: i in [1 .. nn]];
   nmap := KMatrixSpace(ff,Dimension(nmod)-Dimension(nrad),mm)!0;
   rind := 0;
   for t in dplst do
      www := KMatrixSpace(ff,Dimension(nmod),mm)!0;
      for i := 1 to #prl do
         subk := Submatrix(mker1,1,prln[i]+1,Dimension(nmod),prl[i]);
         InsertBlock(~www,subk*Action(ProjectiveModule(A,lll[i])).t,
		     1,prln[i]+1);
      end for;
      nrs := RowSpace(www);
      if nrs subset nrad then
         nlst[t] := 0;
      else 
         int := nrs meet nrad;
//  print(Dimension(int)) , Dimension(nrs);


         ext := ExtendBasis(int,nrs);
         top := KSpaceWithBasis([ext[i]:i in [Dimension(int)+1 .. #ext]]);
         pmap := BasisMatrix(top);
         InsertBlock(~nmap,pmap,rind+1,1);
         rind := rind+Dimension(top);
         nlst[t] := Dimension(top);
      end if;
   end for;
end if;
// print nlst, CM[2];

                  return <nmap,nlst,CM[2]>;

end function;

//*********************************************************************

MNIG := function(A)

rr := RightRegularModule(A);
ss := JacobsonRadical(rr);
tt := JacobsonRadical(ss);
ee := ExtendBasis(ss,rr);
nig := [NumberOfProjectives(A)+1 .. Ngens(A)];
if Dimension(ss) eq 0 then
mnig := nig;
else						//Dim(ss) = 0
mnig := [];
for x in nig do
   for j := Dimension(ss)+1 to Dimension(rr) do
      if ee[j]*Action(rr).x notin tt then
        Append(~mnig,x);
        break j;
      end if;					//ee[j] ...
   end for;					//j
end for;					//x
end if;					//Dim(ss) = 0
return mnig;
end function;

//********************************************************************

CompactPR := function(M,n);

alg := Algebra(M);
prj, epsilon := FirstBoundaryMat(M);
precord := [* prj[1] *];
betti := [prj[2], prj[3]];
//  pll := [* <prj[1],prj[2],prj[3]> *];
if n gt 1 then 				// stop here if n =1
    // we should also stop here if the boundary map is injective.  *****
   nig := [NumberOfProjectives(alg)+1 .. Ngens(alg)];
			//nig is the indices of the nonidempotent generators
   if &+betti[1] eq 0 then 
      ming := nig;
   else						//&+betti[1] = 0
      ming := MNIG(alg);
   end if;					//&+betti[1] = 0
   lprj := <precord[1], betti[1], betti[2]>;
   for i := 1 to n-1 do				
      npr := ResolutionStep(lprj,alg,ming);
      betti := [npr[2]] cat betti;
      precord := [* npr[1] *] cat precord;
                     //      pll := [* <npr[1],npr[2],npr[3]> *] cat pll;
      lprj := <precord[1], betti[1], betti[2]>;
   end for;					// i
end if;
    
return betti, precord, epsilon;

end function;

//********************************************************************

CompactDeletedPR := function(M,n,dlst);

alg := Algebra(M);
prj, epsilon := FirstBoundaryMatD(M,dlst);
precord := [* prj[1] *];
betti := [prj[2], prj[3]];
//  pll := [* <prj[1],prj[2],prj[3]> *];
if n gt 1 then 				// stop here if n =1
    // we should also stop here if the boundary map is injective.  *****
   nig := [NumberOfProjectives(alg)+1 .. Ngens(alg)];
			//nig is the indices of the nonidempotent generators
   if &+betti[1] eq 0 then 
      ming := nig;
   else						//&+betti[1] = 0
      ming := MNIG(alg);
   end if;					//&+betti[1] = 0
   lprj := <precord[1], betti[1], betti[2]>;
   for i := 1 to n-1 do				
      npr := ResolutionStepD(lprj,alg,dlst);
      betti := [npr[2]] cat betti;
      precord := [* npr[1] *] cat precord;
                     //      pll := [* <npr[1],npr[2],npr[3]> *] cat pll;
      lprj := <precord[1], betti[1], betti[2]>;
   end for;					// i
end if;
    
return betti, precord, epsilon;

end function;

//*********************************************************************

intrinsic SimpleHomologyDimensions(M::ModAlgBas) -> SeqEnum
{The sequence of sequences of dimensions of the homology groups 
been computed.}

   if assigned M`CompactProjectiveResolution then
   P :=  M`CompactProjectiveResolution;
   aa := P`BettiNumbers;
   if NumberOfProjectives(Algebra(M)) eq 1 and Type(aa[1]) eq SeqEnum then
   aa := &cat aa;
   end if;
   else
   print "  No projective resolution for M has been computed";
   a,b := IsProjective(M);
   aa := b;
   end if;
   return aa;

end intrinsic;

intrinsic SimpleCohomologyDimensions(M::ModAlgBas) -> SeqEnum
{The sequence of sequences of dimensions of the cohomology groups 
Ext^j(Si,M) for simple modules Si, to the extent that they have
been computed.}

   if assigned M`CompactInjectiveResolution then
      P :=  M`CompactInjectiveResolution;
      aa := P`BettiNumbers;
      if NumberOfProjectives(Algebra(M)) eq 1 and Type(aa[1]) eq SeqEnum then
         aa := &cat aa;
      end if;
      if Type(aa) eq RngIntElt then 
         aa := [aa];
      end if;      
      bb := Reverse(aa);
      return bb;
   else 
      print "  No injective resolution for M has been computed";
      bb,b := IsInjective(M);
      return b;
   end if;

      bb := Reverse(aa);

end intrinsic;

//**********************************************************************

ExtendCompactPR := function(P,n);

if P`Typ eq "ProjectiveResolution" then 
alg := Algebra(P`Module);
end if;
if P`Typ eq "InjectiveResolution" then 
alg := OppositeAlgebra(Algebra(P`Module));
end if;
              //nprj := P[1];
betti := P`BettiNumbers;
precord := P`ResolutionRecord;
nprj := <precord[1], betti[1], betti[2]>;
ming := MNIG(alg);
for i := 1 to n do
ns := ResolutionStep(nprj,alg,ming);
betti := [ns[2]] cat betti;
precord := [* ns[1] *] cat precord;
nprj := ns;
           // nprj := [* ns *] cat nprj;
end for;
rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:List,
            Module:ModAlgBas,AugmentationMap:ModMatFldElt,
            Typ:MonStgElt>;
cpr := rec<rf|BettiNumbers := betti,ResolutionRecord := precord,
            Module := P`Module, AugmentationMap := P`AugmentationMap,
            Typ := P`Typ>;

     return cpr;

end function;

//*********************************************************************

intrinsic CompactProjectiveResolution(M::ModAlgBas, n::RngIntElt) -> Rec

{Given a module M over a basic algebra and a natural number n the 
function computes a projective resolution for M out to n steps. The 
function returns the resolution in compact form together with the 
augmentation map (P_0 -> M). The compact form of the resolution is a
list of the the minimal pieces of information needed to reconstruct
the boundary maps in the resolution. That is, the boundary map
(P_\{i+1\} -> P_i) is recorded as a tuple consisting of a matrix whose 
entries are the images of the generators for indecomposable projective
modules making up P_\{i+1\} in the indecomposable projective modules
making up P_i and two lists of integers givin the number of indecomposable
projective modules of each isomorphism class in P_\{i+1\} and in P_i.}


   if Type(Algebra(M)) eq AlgBasGrpP then 
      return CompactProjectiveResolutionPGroup(M,n);
   end if;
   if assigned M`CompactProjectiveResolution then
      cpr := M`CompactProjectiveResolution;
      ww := #cpr`BettiNumbers-1;
      if ww ge n then 
              return cpr;
      else 
         cpr2 := ExtendCompactPR(cpr,n-ww);
         M`CompactProjectiveResolution := cpr2;
             return cpr2;
      end if;
   else
      betti, precord, epsilon := CompactPR(M,n);
      rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:
            List,Module:ModAlgBas,AugmentationMap:ModMatFldElt,
            Typ:MonStgElt>;
      cpr := rec<rf|BettiNumbers := betti,ResolutionRecord := precord,
            Module := M, AugmentationMap := epsilon, Typ:= 
            "ProjectiveResolution">;   
      M`CompactProjectiveResolution := cpr;
   end if;
   
            return cpr;

end intrinsic;

//*********************************************************************

intrinsic CompactDeletedProjectiveResolution
         (M::ModAlgBas, n::RngIntElt, dellst) -> Rec

{Given a module M over a basic algebra and a natural number n the function 
computes a deleted projective resolution for M out to n steps. The list 
"dellst" is the list of indices of projective modules which are not deleted. 
The function returns the resolution in compact form together with the 
augmentation map (P_0 -> M). The compact form of the resolution is a
list of the the minimal pieces of information needed to reconstruct
the boundary maps in the resolution. That is, the boundary map
(P_\{i+1\} -> P_i) is recorded as a tuple consisting of a matrix whose 
entries are the images of the generators for indecomposable projective
modules making up P_\{i+1\} in the indecomposable projective modules
making up P_i and two lists of integers givin the number of indecomposable
projective modules of each isomorphism class in P_\{i+1\} and in P_i.}

   betti, precord, epsilon := CompactDeletedPR(M,n,dellst);
      rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:
            List,Module:ModAlgBas,AugmentationMap:ModMatFldElt,
            Typ:MonStgElt>;
      cpr := rec<rf|BettiNumbers := betti,ResolutionRecord := precord,
            Module := M, AugmentationMap := epsilon, Typ:= 
            "ProjectiveResolution">;   
   
   
            return cpr;

end intrinsic;



//**********************************************************************

intrinsic CompactInjectiveResolution(M::ModAlgBas ,n::RngIntElt) -> Rec

{Given a module M over a basic algebra and a natural number n the 
function computes an injective resolution for M out to n steps. The 
function returns the resolution in compact form together with the 
coaugmentation map (M -> I_0). The compact form of the resolution is a
list of the the minimal pieces of information needed to reconstruct
the boundary maps in the resolution. That is the boundary map
(I_i -> I_\{i-1\}) is recorded as a tuple consisting of a matrix whose 
entries are the images of the generators for indecomposable injective
modules making up I_i in the indecomposable injective modules making 
up I_\{i-1\} and two lists of integers givin the number of indecomposable
projective modules of each isomorphism class in I_i and in I_\{i-1\}.
The actual return of the function is the 
compact projective resolution of the dual module of M over the opposite 
algebra of the algebra of M.}

// need to include possibility that we are done

  if assigned M`CompactInjectiveResolution then
   cpr := M`CompactInjectiveResolution;
   ww := #cpr`BettiNumbers-1;
   if ww ge n then 
      return cpr;
   else 
      cpr2 := ExtendCompactPR(cpr,n-ww);
      M`CompactInjectiveResolution := cpr2;
      rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:
            List,Module:ModAlgBas,CoaugmentationMap:ModMatFldElt,
            Typ:MonStgElt>;
      cpr := rec<rf|BettiNumbers := cpr2`BettiNumbers,
            ResolutionRecord := cpr2`ResolutionRecord,
            Module := M, 
            CoaugmentationMap := cpr2`CoaugmentationMap, 
            Typ:= "InjectiveResolution">;   
      M`CompactInjectiveResolution := cpr;
      return cpr;
   end if;
  else
   A := Algebra(M);
   OA := OppositeAlgebra(A);
   DM := Dual(M);
   M`Dual := DM;
   cpr1 := CompactProjectiveResolution(DM,n);
   rf := recformat<BettiNumbers:SeqEnum, ResolutionRecord:
            List,Module:ModAlgBas,CoaugmentationMap:ModMatFldElt,
            Typ:MonStgElt>;
   cpr := rec<rf|BettiNumbers := cpr1`BettiNumbers,
            ResolutionRecord := cpr1`ResolutionRecord,
            Module := M, 
            CoaugmentationMap := cpr1`AugmentationMap, 
            Typ:= "InjectiveResolution">;   
   M`CompactInjectiveResolution := cpr;
   end if;

return cpr;

end intrinsic;

//********************************************************************

CompactToPR := function(A,Q,R);
// A is the algebra, Q is the Betti Numbers and R is the resolution
// record

n := 1;
for j := 1 to #Q-1 do
   if &+Q[j] eq 0 then 
      n := n+1;
   end if;
end for;
PJ := [*  *];
if n eq #Q then 
   Pj1 := ProjectiveModule(A,Q[n]);
   z := ZeroModule(A);
   H := Hom(z,Pj1); 
   PJ := [* H!0 *];
else 
   pj1 := ProjectiveModule(A,Q[n]);
   for i := n to #Q-1 do
      pj2 := ProjectiveModule(A,Q[i+1]);
      delta := CreateBoundaryMap(<R[i],Q[i],Q[i+1]>,A);
      delta1 := hom<pj1 -> pj2|delta>;
      delta2 := MapToMatrix(delta1);
      pj1 := pj2;
      PJ[i-n+1] := delta2;
   end for;
end if;
n := Minimum(n,#Q-1);
PJ1 := Complex(PJ,0);
if n gt 1 then
   for j := 2 to n do
      PJ1 := LeftZeroExtension(PJ1);
   end for;
end if;

return PJ1;

end function;

//********************************************************************

CompactToPR2 := function(A,Q,R,lim);
// A is the algebra, Q is the Betti Numbers and R is the resolution
// record. This is the same function as CompactToPR except that we stop
// the computation at lim. 

n := 1;
for j := 1 to lim do
   if &+Q[j] eq 0 then
      n := n+1;
   end if;
end for;
PJ := [*  *];
if n eq #Q then
   Pj1 := ProjectiveModule(A,Q[n]);
   z := ZeroModule(A);
   H := Hom(z,Pj1);
   PJ := [* H!0 *];
else
   pj1 := ProjectiveModule(A,Q[n]);
   for i := n to #Q-1 do
      pj2 := ProjectiveModule(A,Q[i+1]);
      delta := CreateBoundaryMap(<R[i],Q[i],Q[i+1]>,A);
      delta1 := hom<pj1 -> pj2|delta>;
      delta2 := MapToMatrix(delta1);
      pj1 := pj2;
      PJ[i-n+1] := delta2;
   end for;
end if;
n := Minimum(n,#Q-1);
PJ1 := Complex(PJ,0);
if n gt 1 then
   for j := 2 to n do
      PJ1 := LeftZeroExtension(PJ1);
   end for;
end if;

return PJ1;

end function;

//**********************************************************************

intrinsic ProjectiveResolution(M::ModAlgBas, n::RngIntElt) -> ModCpx, 
                   ModMatFldElt
{The complex giving the minimal projective resolution of M
together with the augmentation homomorphism from the 
projective cover of M into M. Note that homomorphisms go from left to
right so that the cokernel of the last homomorphism in the complex is M.}

if Type(Algebra(M)) eq AlgBasGrpP then
   return ProjectiveResolutionPGroup(CompactProjectiveResolutionPGroup(M,n));
end if;
cpr := CompactProjectiveResolution(M,n);
Q := cpr`BettiNumbers;
k := #Q;
R := cpr`ResolutionRecord;
au := cpr`AugmentationMap;
if #Q eq n+1 then
   CP := CompactToPR(Algebra(M),Q,R);
else //  #cpr[1] gt n 
   Q := [Q[j]: j in [k-n .. k]];
   R := [* R[i]: i in [k-n .. k-1] *];
   CP := CompactToPR(Algebra(M),Q,R);
end if;

return CP,au;

end intrinsic;

//**********************************************************************

intrinsic ProjectiveResolution(PR::Rec) -> ModCpx, 
                   ModMatFldElt
{The complex giving the minimal projective resolution of M
together with the augmentation homomorphism from the 
projective cover of M into M. Note that homomorphisms go from left to
right so that the cokernel of the last homomorphism in the complex is M.}

if Type(Algebra(PR`Module)) eq AlgBasGrpP then
   return ProjectiveResolutionPGroup(PR);
end if;
Q := PR`BettiNumbers;
R := PR`ResolutionRecord;
au := PR`AugmentationMap;
CP := CompactToPR(Algebra(PR`Module),Q,R);

          return CP,au;

end intrinsic;

//***********************************************************************

intrinsic DeletedProjectiveResolution(PR::Rec) -> ModCpx, 
                   ModMatFldElt
{The complex giving the minimal deleted projective resolution of M
together with the augmentation homomorphism from the 
projective cover of M into M. Note that homomorphisms go from left to
right so that the cokernel of the last homomorphism in the complex is M.
The input is the Compact deleted projective resolution.}

Q := PR`BettiNumbers;
R := PR`ResolutionRecord;
au := PR`AugmentationMap;
CP := CompactToPR(Algebra(PR`Module),Q,R);

          return CP,au;

end intrinsic;

//***********************************************************************

intrinsic InjectiveResolution(M::ModAlgBas, n::RngIntElt) -> ModCpx, 
                      ModMatFldElt
{The complex giving the minimal injective resolution of M
together with the inclusion homomorphism from M into its 
injective hull. Note that homomorphisms go from left to
right so that the kernel of the first homomorphism in the complex is M.}

   cpr := CompactInjectiveResolution(M,n);
   Q := cpr`BettiNumbers;
   k := #Q;
   R := cpr`ResolutionRecord;
   au := cpr`CoaugmentationMap;
   if #Q eq n+1 then
      CP := CompactToPR(OppositeAlgebra(Algebra(M)),Q,R);
   else //  #cpr[1] gt n 
      Q := [Q[j]: j in [k-n .. k]];
      R := [* R[i]: i in [k-n .. k-1] *];
      CP := CompactToPR(OppositeAlgebra(Algebra(M)),Q,R);
   end if;
   a,b := Degrees(CP);
   CP1 := Dual(CP,-a);
   au1 := MapToMatrix(hom<M -> Term(CP1,0)|Dual(au)>);

         return CP1,au1;

end intrinsic;

//************************************************************************

intrinsic BoundaryMap(PR::Rec,n::RngIntElt) -> ModMatFldElt
{Returns the boundary map in degree n for the compact projective
resolution PR}

   R := PR`ResolutionRecord;
   B := PR`BettiNumbers;
   A := Algebra(PR`Module);
   if Type(A) eq AlgBasGrpP then
      return BoundaryMapGrpP(PR,n);
   end if;
   k := #R-n+1;
   if &+B[k] eq 0 then
      if &+B[k+1] eq 0 then
         return AHom(ZeroModule(A), ZeroModule(A))!0;
      else 
         return AHom(ZeroModule(A), ProjectiveModule(A,B[k+1]))!0;
      end if;
   else
      pj1 := ProjectiveModule(A,B[k]);
      pj2 := ProjectiveModule(A,B[k+1]);
      delta := CreateBoundaryMap(<PR`ResolutionRecord[k],B[k],B[k+1]>,A);
      delta1 := hom<pj1 -> pj2|delta>;
      delta2 := MapToMatrix(delta1);
   end if;

            return delta2;

end intrinsic;

intrinsic SyzygyModule(M::ModAlgBas, n::RngIntElt) -> ModAlgBas
{The nth syzygy module of M. The kernel of the nth boundary map in
a minimal projective resolution of M.}

   cpr :=  CompactProjectiveResolution(M,n-1);
   B := cpr`BettiNumbers;
   A := Algebra(M);
   k := #B-n+1;
   if n eq 1 then 
      omM := Kernel(cpr`AugmentationMap);
   else
      if Type(B[k]) eq SeqEnum and &+B[k] eq 0 then
          omM := ZeroModule(A);
      else
          delta2 := BoundaryMap(cpr,n-1);
          omM := Kernel(delta2);
      end if;
   end if;

           return omM;

end intrinsic;


intrinsic InjectiveSyzygyModule(M::ModAlgBas, n::RngIntElt) -> ModAlgBas
{The nth injective-syzygy module of M. The cokernel of the nth boundary
map in a minimal injective resolution of M.}

   cpr :=  CompactInjectiveResolution(M,n-1);
   R := cpr`ResolutionRecord;
   B := cpr`BettiNumbers;
   A := OppositeAlgebra(Algebra(M));
   k := #R-n+2;
   if n eq 1 then 
      omM := Kernel(cpr`CoaugmentationMap);
   else
      Q := R[k];
      if &+B[k] eq 0 then
      omM := ZeroModule(A);
   else
      pj1 := ProjectiveModule(A,B[k]);
      pj2 := ProjectiveModule(A,B[k+1]);
      delta := CreateBoundaryMap(<Q,B[k],B[k+1]>,A);
      delta1 := hom<pj1 -> pj2|delta>;
      delta2 := MapToMatrix(delta1);
   omM := Dual(Kernel(delta2));
   end if;
   end if;

return omM;

end intrinsic;
