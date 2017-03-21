freeze;

//  Jon F. Carlson, June 2012


declare verbose Automorphisms, 1;

import "autofunc.m": GradedAutosModuloRadicalSquared;
import "autofunc.m": AutoMatsOnSocle;
import "autofunc.m": TruncationMatrix;
import "autofunc.m": RadicalDimensions;
import "autofunc.m": ExtendHomomorphism;
import "autofunc.m": LeftInverseMatrix;
import "autofunc.m": Least;


//  checks := true;
checks := false;

/////////////////////////////////////////////////////////////////

InducedGradedHomomorphism := function(phi, A, B);
// This function assumes that the idempotents on A and B match up.

radA := MinimalGeneratorForm(A)`RadicalDimensions;
radB := MinimalGeneratorForm(B)`RadicalDimensions;
dimA := DimensionsOfProjectiveModules(A);
dimB := DimensionsOfProjectiveModules(B);
rA := [x cat [0]:x in radA];
rB := [x cat [0]:x in radB];
bsA1 := [[x[i]-x[i+1]: i in [1 .. #x-1]]:x in rA];
bsB1 := [[x[i]-x[i+1]: i in [1 .. #x-1]]:x in rB];
for i := 1 to #bsA1 do
   if #bsA1[i] gt #bsB1[i] then
      bsB1[i] cat:= [0: j in [1 .. #bsA1[i]-#bsB1[i]]];
   end if;
end for;
bsA := &cat bsA1;
bsB := &cat bsB1;
zeta := KMatrixSpace(BaseRing(A), Dimension(A), Dimension(B))!0;
rndx := 1;
cndx := 1;
for i := 1 to #bsA do
   if bsB[i] ne 0 then
      InsertBlock(~zeta, Submatrix(phi,rndx,cndx,bsA[i],bsB[i]),rndx,cndx);
   end if;
   rndx +:= bsA[i];
   cndx +:= bsB[i];
end for;

        return zeta;

end function;

/////////////////////////////////////////////////////////////////


BuildHomomorphismFromGenerators := function(A,B,lst);
// lst is a list of vectors of elements of B, that are the images of the
// generators of A, under the homomorphism to be built. The
// constructs the matrix of that homomorphism.

np := NumberOfProjectives(A);
dimp := DimensionsOfProjectiveModules(A);
rct := 0;
mat := KMatrixSpace(BaseRing(A), Dimension(A), Dimension(B))!0;
for i := 1 to np do
   pt := PathTree(A,i);
   for j := 1 to dimp[i] do
      if pt[j][1] eq 1 then
         mat[rct+j] := lst[pt[j][2]];
      else
         mat[rct+j] := Vector( (B!mat[rct+pt[j][1]]) * (B!lst[pt[j][2]]) );
      end if;
   end for;
   rct +:= dimp[i];
end for;

        return mat;

end function;

/////////////////////////////////////////////////////////////////////////

intrinsic BuildHomomorphismFromGradedCap(A::AlgBas, 
               B::AlgBas, phi:ModMatFldElt) -> ModMatFldElt
{Returns the graded homomorphism from the associated graded algebra X of
A to the associated graded algebra Y of B, whose cap is phi. That is 
phi is the matrix of the induced homomorphism of X/Rad^2(X) to Y/Rad^2(Y).}

k := BaseRing(A);
X := AssociatedGradedAlgebra(A);
Y := AssociatedGradedAlgebra(B);

MFGa := MinimalGeneratorForm(A);
rdimsa := MFGa`RadicalDimensions;
dpma := DimensionsOfProjectiveModules(A);
npa := NumberOfProjectives(A);
dpma := DimensionsOfProjectiveModules(A);

MFGb := MinimalGeneratorForm(B);
rdimsb := MFGb`RadicalDimensions;
dpmb := DimensionsOfProjectiveModules(B);
npb := NumberOfProjectives(B);
dpmb := DimensionsOfProjectiveModules(B);

tdimsa := [];
sdims1a := [1];
sdims2a := [1];
for i := 1 to #dpma do
   tdimsa[i] := dpma[i] - rdimsa[i][3];
   sdims1a[i+1] := sdims1a[i] + dpma[i];
   sdims2a[i+1] := sdims2a[i] + tdimsa[i];
end for;

tdimsb := [];
sdims1b := [1];
sdims2b := [1];
for i := 1 to #dpmb do
   tdimsb[i] := dpmb[i] - rdimsb[i][3];
   sdims1b[i+1] := sdims1b[i] + dpmb[i];
   sdims2b[i+1] := sdims2b[i] + tdimsb[i];
end for;

genlst := [];
W, inj1, prj1 := DirectSum([VectorSpace(k,x):x in tdimsb]);
udims := &cat[[tdimsb[i], dpmb[i]-tdimsb[i]]: i in [1 .. #tdimsb]];
V, inj2, prj2 := DirectSum([VectorSpace(k,x):x in udims]);
for i := 1 to npa do
   v := &+[inj2[2*j-1](prj1[j](phi[sdims2a[i]])):j in [1 .. #tdimsb]];
   Append(~genlst, v);
end for;
for i := 1 to npa do
   if tdimsa[i] gt 1 then 
      for t := 1 to tdimsa[i]-1  do
	 v := &+[inj2[2*j-1](prj1[j](phi[sdims2a[i]+t])):j in [1 .. #tdimsb]];
         Append(~genlst, v);
      end for;
   end if;
end for;
MM := BuildHomomorphismFromGenerators(X,Y,genlst);

	return MM;

end intrinsic;


////////////////////////////////////////////////////////////////

intrinsic GradedCoverAlgebra(A::AlgBas) -> AlgBas, ModMatFldElt
{This a assumes that we are given the truncated algebra
of a graded algebra. It creates the basic algebra of the natural
cover of A and also returns the matrix of the cover onto A.}

CA, gamma:= CoverAlgebra(A);
AS := AssociatedGradedAlgebra(CA);
zzz := InducedGradedHomomorphism(gamma, AS, A);
W := Kernel(zzz);
rad := MinimalGeneratorForm(AS)`RadicalDimensions;
dp := DimensionsOfProjectiveModules(AS);
D, inj, prj := DirectSum([VectorSpace(BaseRing(A),x): x in dp]);
xxx := [];
for i := 1 to #dp do
Wi := prj[i](W);
xxx cat:= [inj[i](Basis(Wi)[t]): t in [1 .. Dimension(Wi)-rad[i][#rad[i]]]];
end for;
Q := quo<AS|sub<VectorSpace(AS)|xxx>>;
lss := [Vector(x)*gamma: x in Generators(CA)];
mat := BuildHomomorphismFromGenerators(Q,A,lss);

        return Q, mat;

end intrinsic;

/////////////////////////////////////////////////////////////////////

GradedAutoStepTwo := function(C);

MGF := MinimalGeneratorForm(C);
A := MGF`Algebra;
sdd := MGF`FilterDimensions;
B := TruncatedAlgebra(A,2);
vprint Automorphisms: "getting automorphisms at level 2";
vtime Automorphisms: gmats, nmats  := GradedAutosModuloRadicalSquared(A,sdd);
if checks then    /////////////////////////////////////////////////
   print "checking first automorphisms: ";                    /////
   print [IsAlgebraHomomorphism(B,B,x):x in gmats];           /////
   print [IsAlgebraHomomorphism(B,B,x):x in nmats];           /////
end if;     ///////////////////////////////////////////////////////

tail := GeneratorAssociatedIdempotents(A);
rdd := MGF`RadicalDimensions;
lp := [#x:x in rdd];

        return A, B, tail, lp, gmats, nmats;

end function;

//////////////////////////////////////////////////////////////////////

GradedAutoNextStep := function(A, TA, E, ends, projl, theta, gmats, nmats, n);
// A is the original algebra
// TA is the previous truncation
// E is the standard algebra
// ends is the idempotent ends of generators
// projl is the lengths of the projectives of A
// theta is the isomorphism form E to TA
// gplst is stabilizer group of E generated by then nonunipotent elements
// uplst is the unipotent subgroup of the stabilizer
// n is the level of the truncation

k := BaseRing(A);
B, sigma := TruncatedAlgebra(A,n);
sigma := TruncationMatrix(B,TA);
ends := GeneratorAssociatedIdempotents(E);
vprint Automorphisms: "Getting cover algebra";
vtime Automorphisms: C, rho := GradedCoverAlgebra(E);
rrc := RadicalDimensions(C);
dimC := Dimension(C);

if checks then   /////////////////////////////////////////////////
   print  "DimensionTest for cover algebra", IsDimensionCompatible(C); ///
   print  "PathTreeTest for cover algebra", IsPathTree(C);  ////
   print  "HomomorphismTest for cover algerba",             //////
              IsAlgebraHomomorphism(C,E,rho);                    //////
end if;  /////////////////////////////////////////////////////////

beta := ExtendHomomorphism(E,C,TA,B,rho,LeftInverseMatrix(sigma), theta);
vprint Automorphisms:  "Extended homomorphism to truncation has ",
       Nrows(beta), "rows and ", Ncols(beta), "columns.";

if checks then   /////////////////////////////////////////////////
   print "Homomorphism test for extension",                 //////
                 IsAlgebraHomomorphism(C,B, beta);               //////
end if;  /////////////////////////////////////////////////////////

rhi := LeftInverseMatrix(rho);
vprint Automorphisms: "Extending Automorphisms from previous step";
vtime Automorphisms:
           Gmats := [ExtendHomomorphism(E,C,E,C, rho,rhi,x):x in gmats];
vtime Automorphisms:
        Nmats := [ExtendHomomorphism(E,C,E,C, rho,rhi,x):x in nmats];

if checks then    /////////////////////////////////////////////////
   print "checking extended automorphisms: ";                 /////
   print [IsAlgebraHomomorphism(C,C,x):x in Gmats];           /////
   print [IsAlgebraHomomorphism(C,C,x):x in Nmats];           /////
end if;     ///////////////////////////////////////////////////////

AlgGL := GL(dimC,k);
xi := BasisMatrix(Kernel(rho));
ix := RightInverseMatrix(xi);
vprint Automorphisms : "Getting action on Socle ";
vtime Automorphisms : ggmats := AutoMatsOnSocle(Gmats,xi,ix);
vtime Automorphisms : numats := AutoMatsOnSocle(Nmats,xi,ix);

if checks then     //////////////////////////////////////////////////
   print "checking upper triangular of unipotent group on socle"; ///
   print [IsUpperTriangular(x):x in numats];                      ///
end if;       ///////////////////////////////////////////////////////

SocGL := GL(Dimension(Kernel(rho)), k);
KK := Kernel(xi*beta);
Ugrp := sub<SocGL|numats>;

      if checks then    ////////////////////////////////////////////////
         print "Checking upper triangular of group",               /////
            [IsUpperTriangular(y): y in Generators(Ugrp)];         /////
      end if;    ///////////////////////////////////////////////////////

UUgrp := UnipotentMatrixGroup(Ugrp);
Hgrp := sub<AlgGL|Gmats cat Nmats>;
vtime Automorphisms : 
      gggmats := AutoMatsOnSocle([Hgrp.i: i in [1 .. Ngens(Hgrp)]],xi,ix);
Ggrp := sub<SocGL|gggmats>;
ftheta := hom<Hgrp -> Ggrp|gggmats>;

      if checks then //////////////////////////////////////////////////
         print "Size of nonunipotent group", #Ggrp;               /////
      end if; /////////////////////////////////////////////////////////

Sy := Ugrp;
vprint Automorphisms: "Getting first stabilizer";
vtime Automorphisms: ST := Stabilizer(Ggrp, KK);
a,b,c := CosetAction(Ggrp,Sy);
dcr := DoubleCosetRepresentatives(b,a(ST),a(Sy));
DCR := [x@@a:x in dcr];
Ob := [];


vprint Automorphisms: "Unipotent stabilizers: ";
vtime Automorphisms: for x in DCR do
   aa,bb,uu, vv := UnipotentStabiliser(UUgrp,KK*x);
   Append(~Ob,<x,aa,bb,uu>);
end for;
vprint Automorphisms: "Getting least conjugate of kernel :";
vtime Automorphisms: ll := Least([x[3]:x in Ob]);
gam := Ob[ll][4];
addlst := [];
if #Ob gt 1 then
   for i := 1 to #Ob do
      if not  i eq ll then
         if Ob[i][3] eq Ob[ll][3] then
            vprint Automorphisms: "Adding generators";
              Append(~addlst, <Ob[i][1],Ob[i][4]*gam^-1>);

	if checks then    //////////////////////////////////////////////////
	print "checking additional stabilizer element";   //////////////////
	print KK*Ob[i][1]*Ob[i][4] eq KK*Ob[ll][1]*Ob[ll][4];   ////////////
	print KK*Ob[i][1]*Ob[i][4] eq Ob[ll][3];     ///////////////////////
	end if;  ///////////////////////////////////////////////////////////

         end if;
      end if;
   end for;
end if;
vprint Automorphisms : "Lifting general automorphisms";
omega := Ob[ll][1]@@ftheta;
vtime Automorphisms :
    NGmats := Setseq(Generators((ST@@ftheta)^omega));

if Ngens(UUgrp) eq 0 then
   gamma := AlgGL!1;
   NNmats := [gamma];
else
   muu := WordMap(UUgrp);
   vprint Automorphisms : "Lifting unipotent automorphisms";
   gamma := Evaluate(muu(gam),sub<AlgGL|Nmats>);
   NNmats := [Evaluate(muu(x),sub<AlgGL|Nmats>):
       x in Generators(Ob[ll][2])];
end if;

if #addlst ne 0 then
   for x in addlst do
      Append(~NGmats, omega^-1*(x[1]@@ftheta)*
                   Evaluate(muu(x[2]),sub<AlgGL|Nmats>));
   end for;
end if;
SS := Ob[ll][3]*gam^-1*xi;

	if checks then ////////////////////////////////////////////////////
	   print "checking kernel:   ", SS*omega^-1 eq Kernel(beta); //////
	end if;    ////////////////////////////////////////////////////////

	if checks then    /////////////////////////////////////////////////
	   print "elements in stabilizer";   //////////////////////////////
	   print [SS*x eq SS: x in NGmats];  //////////////////////////////
	   print [SS*x eq SS: x in NNmats];  //////////////////////////////
	end if;   /////////////////////////////////////////////////////////

alph := AlgGL!gamma^-1*omega^-1;
vprint Automorphisms: "Getting quotient algebra ";
vtime Automorphisms:  EE, zeta := quo<C|SS>;
zeta1 := Matrix(zeta);

	if checks then    /////////////////////////////////////////////////
	   print "Dimension test for quotient algebra: ",              ////
              IsDimensionCompatible(EE);                               ////
	   print "PathTree test for quotient algebra: ",               ////
              IsPathTree(EE);                                          ////
	   print "Homomorphism test for quotient map: ",               ////
              IsAlgebraHomomorphism(C,EE, zeta1);                      ////
	end if;   /////////////////////////////////////////////////////////

vprint Automorphisms: "The dimension of the quotient algebra is   ",
                                 Dimension(EE);
vprint Automorphisms: "Obtaining induced homomorphisms on quotient";
vtime Automorphisms: psi := InducedHomomorphism(omega^-1*beta, zeta1,
   KIdentityMatrix(k,Dimension(B)));

	if checks then   //////////////////////////////////////////////////
	   print "Checking induced map is homomorphism: ",             ////
                     IsAlgebraHomomorphism(EE,B, psi);                 ////
	end if;   /////////////////////////////////////////////////////////

vtime Automorphisms : ngplst :=
       [InducedHomomorphism(KMatrixSpace(k,dimC,dimC)!x,
                zeta1, zeta1): x in NGmats];
vtime Automorphisms : nuplst1 :=
       [InducedHomomorphism(KMatrixSpace(k,dimC,dimC)!x,
                zeta1, zeta1): x in NNmats];
	
GU := sub<GL(Dimension(EE),k)|nuplst1>;
UU := UnipotentMatrixGroup(GU);
nuplst := InternalUnipPCGensCleaned(UU,1,false);

	if checks then /////////////////////////////////////////////////////
	   print "Checking the conjugacy of subspace with minimum: ",   ////
	          SS*omega^-1 eq Kernel(beta);                          ////
	   print "Transformation is automorphism",                      ////
				IsAlgebraHomomorphism(C,C,alph);        ////
	   print "Kernel is an ideal: ", IsIdeal(C,SS);                 ////
	end if;   //////////////////////////////////////////////////////////

	if checks then   //////////////////////////////////////////////////
	   print "Checking automorphisms on quotient: ";               ////
	   print [IsAlgebraHomomorphism(EE,EE,x):x in ngplst];          ////
	   print [IsAlgebraHomomorphism(EE,EE,x):x in nuplst];          ////
	end if;   /////////////////////////////////////////////////////////

vprint Automorphisms : "Number of general automorphisms:   ", #ngplst;
vprint Automorphisms : "Number of unipotent automorphisms:   ", #nuplst;

         return B, EE, psi, ngplst, nuplst, SS, C;

end function;

////////////////////////////////////////////////////////////////////////

SmallAutoGroup := function(A,B,ggrp);
// this function assumes that A is an associated graded algebra. ggrp
// is  matrix group of automorphisms of some truncation of A. Here loc
// is the location of the generators.

k := BaseRing(A);
cycs := Reverse(CyclicSubgroups(ggrp));
locA := PositionsOfGenerators(A);
locB := PositionsOfGenerators(B);
sigma := RightInverseMatrix(TruncationMatrix(A,B));
XGL := GL(Dimension(A),k);
ngrp := sub<XGL|>;
ugrp := sub<ggrp|>;
for x in cycs do
   if x`order gt 1 then
      ss := x`subgroup;
      nn := Normalizer(ggrp, ss);
      gplst := [ss.1^y: y in Transversal(ggrp,nn)];
      for t in gplst do
         if not t in ugrp then
            lst := [t[locB[i]]*sigma:i in [1 .. #locA]];
            mat := BuildHomomorphismFromGenerators(A,A,lst);
            a := IsAlgebraHomomorphism(A,A,mat);
            if a then
               ngrp := sub<XGL|ngrp, mat>;
               ugrp := sub<ggrp|ugrp, t>;
               if #ugrp eq #ggrp then 
                  break x;
               end if;
            end if;
         end if;
      end for;
   end if;
end for;

        return ngrp;

end function;

////////////////////////////////////////////////////////////////

StabilizerOfList := function(lst)
// Returns the subgroup of all permutations on n letters, where n is 
// the length of the sequence lst, that fix lst when permuting the 
// order of the elements. 


// first get classes
n := #lst;
cls := [];
for j := 1 to n do
   if not j in &cat cls then
      Append(~cls, [i: i in [j .. n]|lst[i] eq lst[j]]);
   end if;
end for;
// now make permutation group
S := sub<Sym(n)|>;
for x in cls do
   if #x eq 2 then 
       S := sub<Sym(n)|S, Sym(n)!(x[1],x[2])>;
   elif #x gt 2 then
       a := Sym(n)!(x[1],x[2]); b := &*[Sym(n)!(x[1],x[j]): j in [2 .. #x]]; 
       S := sub<Sym(n)|Setseq(Generators(S)) cat  [a,b]>;
   end if;
end for;

	return S;

end function;

////////////////////////////////////////////////////////////////

intrinsic  GradedAutomorphismGroupMatchingIdempotents(A::AlgBas) -> 
		GrpMat, SeqEnum, SeqEnum
{Returns the group of graded automorphisms of the basic algebra A
that preserve the idempotents of A. Returns also the graded caps 
(matrices of homomorphisms from X/Rad^2(X) to itself, where X is 
the Associated Graded algebra of A) of the generators of the automorphism
group in two sequenced, nonunipotent generators and unipotent generators.}

k := BaseRing(A);
if Dimension(A) eq 1 then 
   return SL(1,k), [IdentityMatrix(k,1)], [];
end if;
X := AssociatedGradedAlgebra(A);
XX, B, ends, leng, g2mats, n2mats:= GradedAutoStepTwo(X);
E := B;
LGL := GL(Dimension(A),k);
if Dimension(A) eq Dimension(B) then
   return sub<LGL|g2mats cat n2mats>, g2mats, n2mats;
end if;
theta := Matrix(IdentityMatrix(BaseRing(A), Dimension(B)));
gplst := g2mats;
uplst := n2mats;

for i := 3 to Maximum(leng) do
   BGL := GL(Dimension(B),k);
   if #gplst eq 0 then 
      rlst := [BGL!x:x in uplst];
   elif #uplst eq 0 then 
      rlst := [BGL!x:x in gplst];
   else 
      rlst := [BGL!x:x in gplst] cat [BGL!x: x in uplst];
   end if;
   NGL := sub<BGL|rlst>;
   if #NGL le 1000 then
      if i ge 3 then
         thetain  := theta^-1;
         rlst := [thetain*x*theta: x in rlst];
         NGL := sub<BGL|rlst>;
      end if;
      GG := SmallAutoGroup(X, E, NGL);
      gplst := Setseq(Generators(GG));
      uplst := [];
      break;
   else 
      vprint Automorphisms: "";
      vprint Automorphisms: "                      =========     ";
      vprint Automorphisms: "Step",i;
      vtime Automorphisms: B, E, theta, gplst, uplst, V, CC:=
          GradedAutoNextStep(XX, B, E, ends, leng, theta, gplst, uplst, i);
   end if;
end for;
if Nrows(theta) eq Dimension(XX) then
   thetain := theta^-1;
   gplst := [thetain*x*theta: x in gplst];
   uplst := [thetain*x*theta: x in uplst];
end if;
if #gplst eq 0 then
   rlst := [LGL!x: x in uplst];
elif #uplst eq 0 then
   rlst := [LGL!x: x in gplst];
else
   rlst := [LGL!x: x in gplst] cat [LGL!x: x in uplst];
end if;
gautogrp := sub< LGL | rlst >;

raddims := MinimalGeneratorForm(X)`RadicalDimensions;
ddims := DimensionsOfProjectiveModules(A);
tdims := [];
sdims1 := [1];
sdims2 := [1];
for i := 1 to #ddims do
   tdims[i] := ddims[i] - raddims[i][3];
   sdims1[i+1] := sdims1[i] + ddims[i];
   sdims2[i+1] := sdims2[i] + tdims[i];
end for;
MMM := KMatrixSpace(k, &+tdims, &+tdims)!0;
ngplst := [];
for j := 1 to #gplst do
   ngp := MMM;
   for i := 1 to #ddims do
      InsertBlock(~ngp,
             Submatrix(gplst[j],sdims1[i],sdims1[i],tdims[i],tdims[i]),
             sdims2[i], sdims2[i]);
   end for;
   Append(~ngplst,ngp);                          //tt2^-1*ngp*tt2);
end for;
nuplst := [];
for j := 1 to #uplst do
   ugp := MMM;
   for i := 1 to #ddims do
      InsertBlock(~ugp,
             Submatrix(uplst[j],sdims1[i],sdims1[i],tdims[i],tdims[i]),
             sdims2[i], sdims2[i]);
   end for;
   Append(~nuplst, ugp); 
end for;

	return      gautogrp, ngplst, nuplst, theta;

end intrinsic;

///////////////////////////////////////////////////////////////

GradedIsoStepTwo := function(C);

MGF := MinimalGeneratorForm(C);
A := MGF`Algebra;
sdd := MGF`FilterDimensions;
B := TruncatedAlgebra(A,2);
vprint Automorphisms: "getting automorphisms at level 2";
vtime Automorphisms: gmats, nmats :=
           GradedAutosModuloRadicalSquared(A,sdd);

       if checks then    /////////////////////////////////////////////////
          print "checking first automorphisms: ";                    /////
          print [IsAlgebraHomomorphism(B,B,x):x in gmats];           /////
          print [IsAlgebraHomomorphism(B,B,x):x in nmats];            /////
       end if;     ///////////////////////////////////////////////////////

// nmats := [];
tail := GeneratorAssociatedIdempotents(A);
rdd := MGF`RadicalDimensions;
lp := [#x:x in rdd];

        return A, B, tail, lp, gmats, nmats;

end function;

///////////////////////////////////////////////////////////////////

GradedIsoNextStep := function(A1, TA1, A2, TA2, E,
        ends, projl, theta1, theta2, gmats, nmats, n);
// A1, A2 are the original algebra
// TA1, TA2 are the previous truncation
// E is the standard algebra
// ends is the idempotent ends of generators
// projl is the lengths of the projectives of A
// theta1, theta2 are the isomorphism from E to TA1, TA2
// gplst is stabilizer group of E generated by then nonunipotent elements
// uplst is the unipotent subgroup of the stabilizer
// n is the level of the truncation

k := BaseRing(A1);
B1 := TruncatedAlgebra(A1,n);
sigma1 := TruncationMatrix(B1,TA1);
B2 := TruncatedAlgebra(A2,n);
sigma2 := TruncationMatrix(B2,TA2);
ends := GeneratorAssociatedIdempotents(E);
vprint Automorphisms: "Getting graded cover algebra";
vtime Automorphisms: C, rho := GradedCoverAlgebra(E);
rrc := RadicalDimensions(C);

       if checks then   /////////////////////////////////////////////////
          print  "DimensionTest for cover algebra",                 /////
                    IsDimensionCompatible(C);                       /////
          print  "PathTreeTest for cover algebra", IsPathTree(C);   /////
          print  "HomomorphismTest for cover algerba",              /////
                    IsAlgebraHomomorphism(C,E,rho);                 /////
       end if;  /////////////////////////////////////////////////////////

beta1 := ExtendHomomorphism(E,C,TA1,B1,rho,LeftInverseMatrix(sigma1), theta1);
beta2 := ExtendHomomorphism(E,C,TA2,B2,rho,LeftInverseMatrix(sigma2), theta2);
vprint Automorphisms:  "Extended homomorphism to truncation has ",
       Nrows(beta1), "rows and ", Ncols(beta1), "columns.";

       if checks then   /////////////////////////////////////////////////
          print "Homomorphism tests for extensions",               //////
                        IsAlgebraHomomorphism(C,B1, beta1);        //////
                        IsAlgebraHomomorphism(C,B2, beta2);        //////
       end if;  /////////////////////////////////////////////////////////

rhi := LeftInverseMatrix(rho);
vprint Automorphisms: "Extending Automorphisms from previous step";
vtime Automorphisms:
           Gmats := [ExtendHomomorphism(E,C,E,C, rho,rhi,x):x in gmats];
vtime Automorphisms:
        Nmats := [ExtendHomomorphism(E,C,E,C, rho,rhi,x):x in nmats];

       if checks then    /////////////////////////////////////////////////
          print "checking extended automorphisms: ";                 /////
          print [IsAlgebraHomomorphism(C,C,x):x in Gmats];           /////
          print [IsAlgebraHomomorphism(C,C,x):x in Nmats];           /////
       end if;     ///////////////////////////////////////////////////////

AlgGL := GL(Dimension(C),k);
xi := BasisMatrix(Kernel(rho));
ix := RightInverseMatrix(xi);
vprint Automorphisms : "Getting action and kernel on Socle ";
vtime Automorphisms : ggmats := AutoMatsOnSocle(Gmats,xi,ix);
vtime Automorphisms : numats := AutoMatsOnSocle(Nmats,xi,ix);

       if checks then     //////////////////////////////////////////////////
          print "checking upper triangular of unipotent group on socle"; ///
          print [IsUpperTriangular(x):x in numats];                      ///
       end if;       ///////////////////////////////////////////////////////

SocGL := GL(Dimension(Kernel(rho)), k);
Hgrp := sub<AlgGL|Gmats cat Nmats>;
vtime Automorphisms :
      gggmats := AutoMatsOnSocle([Hgrp.i: i in [1 .. Ngens(Hgrp)]],xi,ix);
Ggrp := sub<SocGL|gggmats>;
ftheta := hom<Hgrp -> Ggrp|gggmats>;

      if checks then //////////////////////////////////////////////////
          print "Size of nonunipotent group", #Ggrp;               /////
      end if; /////////////////////////////////////////////////////////

Ugrp := sub<SocGL|numats>;
UUgrp := UnipotentMatrixGroup(Ugrp);
muu := WordMap(UUgrp);
Sy := UUgrp;

        //   first kernel stabilizer

KK1 := Kernel(xi*beta1);
vprint Automorphisms: "Getting first stabilizer of first kernel";
vtime Automorphisms: ST := Stabilizer(Ggrp, KK1);
vprint Automorphisms: "Getting coset action";
vtime Automorphisms : a,b,c := CosetAction(Ggrp,Ugrp);
vprint Automorphisms: "Getting double cosets";
vtime Automorphisms: dcr := DoubleCosetRepresentatives(b,a(ST),a(Ugrp));
DCR := [x@@a:x in dcr];

Ob := [];
vprint Automorphisms: "Unipotent stabilizers of first: ";
vtime Automorphisms: for x in DCR do
   aa,bb,uu, vv := UnipotentStabiliser(UUgrp,KK1*x);
   Append(~Ob,<x,aa,bb,uu>);
end for;
vprint Automorphisms: "Getting least conjugate of kernel :";
vtime Automorphisms: ll1 := Least([x[3]:x in Ob]);
Ob1 := Ob[ll1];

	//      Getting second kernel stabilizer

KK2 := Kernel(xi*beta2);
vprint Automorphisms: "Getting first stabilizer of second kernel";
vtime Automorphisms: ST := Stabilizer(Ggrp, KK2);
vprint Automorphisms: "Getting coset action";
vtime Automorphisms : a,b,c := CosetAction(Ggrp,Ugrp);
vprint Automorphisms: "Getting double cosets";
vtime Automorphisms: dcr := DoubleCosetRepresentatives(b,a(ST),a(Ugrp));
DCR := [x@@a:x in dcr];
Ob := [];
vprint Automorphisms: "Unipotent stabilizers: ";
vtime Automorphisms: for x in DCR do
   aa,bb,uu, vv := UnipotentStabiliser(UUgrp,KK2*x);
   Append(~Ob,<x,aa,bb,uu>);
end for;
vprint Automorphisms: "Getting least conjugate of kernel :";
vtime Automorphisms: ll2 := Least([x[3]:x in Ob]);
Ob2 := Ob[ll2];

if Ob1[3] ne Ob2[3] then
        return false, n, 0,0,0,0,0,0,0;
end if;

gam := Ob2[4];
addlst := [];
if #Ob gt 1 then
   for i := 1 to #Ob do
      if not  i eq ll2 then
         if Ob[i][3] eq Ob2[3] then
            vprint Automorphisms: "Adding generators";
              Append(~addlst, <Ob[i][1],Ob[i][4]*gam^-1>);

       if checks then    ///////////////////////////////////////////////////
       print "checking additional stabilizer element";   ///////////////////
       print KK2*Ob[i][1]*Ob[i][4] eq KK2*Ob[ll2][1]*Ob[ll2][4];   /////////
       print KK2*Ob[i][1]*Ob[i][4] eq Ob[ll2][3];     //////////////////////
       end if;    //////////////////////////////////////////////////////////

         end if;
      end if;
   end for;
end if;

vprint Automorphisms : "Lifting general automorphisms";
omega1 := (Ob1[1]*Ob1[4]*Ob2[4]^-1)@@ftheta;
omega2 := Ob2[1]@@ftheta;
vtime Automorphisms :
    NGmats := Setseq(Generators((ST@@ftheta)^omega2));
if Ngens(UUgrp) eq 0 then
   gamma := AlgGL!1;
   NNmats := [gamma];
else
   vprint Automorphisms : "Lifting unipotent automorphisms";
   gamma := Evaluate(muu(gam),sub<AlgGL|Nmats>);
   NNmats := [Evaluate(muu(x),sub<AlgGL|Nmats>):
       x in Generators(Ob2[2])];
end if;
if #addlst ne 0 then
   for x in addlst do
      Append(~NGmats, omega2^-1*(x[1]@@ftheta)*
                   Evaluate(muu(x[2]),sub<AlgGL|Nmats>));
   end for;
end if;

SS := Ob2[3]*gam^-1*xi;

       if checks then ////////////////////////////////////////////////////
          print "checking kernel:   ", SS*omega2^-1 eq Kernel(beta2); ////
       end if;    ////////////////////////////////////////////////////////

       if checks then    /////////////////////////////////////////////////
          print "elements in stabilizer";   //////////////////////////////
          print [SS*x eq SS: x in NGmats];  //////////////////////////////
          print [SS*x eq SS: x in NNmats];  //////////////////////////////
       end if;   /////////////////////////////////////////////////////////

alph := AlgGL!gamma^-1*omega2^-1;
vprint Automorphisms: "Getting quotient algebra ";
vtime Automorphisms:  EE, zeta := quo<C|SS>;
zeta1 := Matrix(zeta);

       if checks then    /////////////////////////////////////////////////
          print "Dimension test for quotient algebra: ",              ////
                     IsDimensionCompatible(EE);                       ////
          print "PathTree test for quotient algebra: ",               ////
                     IsPathTree(EE);                                  ////
          print "Homomorphism test for quotient map: ",               ////
                     IsAlgebraHomomorphism(C,EE, zeta1);               ////
       end if;   /////////////////////////////////////////////////////////

vprint Automorphisms: "The dimension of the quotient algebra is   ",
                                 Dimension(EE);
vprint Automorphisms: "Obtaining induced homomorphisms on quotient";
vtime Automorphisms: psi1 := InducedHomomorphism(omega1^-1*beta1, zeta1,
   KIdentityMatrix(k,Dimension(B1)));
vtime Automorphisms: psi2 := InducedHomomorphism(omega2^-1*beta2, zeta1,
   KIdentityMatrix(k,Dimension(B2)));

       if checks then   //////////////////////////////////////////////////
          print "Checking induced map is homomorphism: ",             ////
                          IsAlgebraHomomorphism(EE,B1, psi1);         ////
                          IsAlgebraHomomorphism(EE,B2, psi2);         ////
          print Dimension(B1), Dimension(B2);                         ////
          print IsAlgebraHomomorphism(B1,B2, psi1^-1*psi2);           ////
       end if;   /////////////////////////////////////////////////////////

vtime Automorphisms : ngplst :=
       [InducedHomomorphism(KMatrixSpace(k,Nrows(x),Ncols(x))!x,
                  zeta1, zeta1): x in NGmats];
vtime Automorphisms : nuplst1 :=
       [InducedHomomorphism(KMatrixSpace(k,Nrows(x),Ncols(x))!x,
                  zeta1, zeta1): x in NNmats];
GU := sub<GL(Dimension(EE),k)|nuplst1>;
UU := UnipotentMatrixGroup(GU);
nuplst := InternalUnipPCGensCleaned(UU,1,false);

       if checks then //////////////////////////////////////////////////////
          print "Checking the conjugacy of subspaces with minimum: ",   ////
                 SS*omega1^-1 eq Kernel(beta1);                         ////
          print "Checking the conjugacy of subspace with minimum: ",    ////
                SS*omega2^-1 eq Kernel(beta2);                          ////
          print "Transformation is automorphism",                       ////
                IsAlgebraHomomorphism(C,C,alph);                        ////
          print "Kernel is an ideal: ", IsIdeal(C,SS);                  ////
       end if;   ///////////////////////////////////////////////////////////

       if checks then   //////////////////////////////////////////////////
          print "Checking automorphisms on quotient: ";               ////
          print [IsAlgebraHomomorphism(EE,EE,x):x in ngplst];         ////
          print [IsAlgebraHomomorphism(EE,EE,x):x in nuplst];         ////
       end if;   /////////////////////////////////////////////////////////

vprint Automorphisms : "Number of general automorphisms:   ", #ngplst;
vprint Automorphisms : "Number of unipotent automorphisms:   ", #nuplst;

         return B1, B2, EE, psi1, psi2, ngplst, nuplst, SS, C;

end function;

///////////////////////////////////////////////////////////////////////

function IsGradedIsomorphicMI(U, V)  // assumes match of idempotents

//{Returns true if U and V are isomorphic algebras and returns also the
//isomorphism from U to V.}

k := BaseRing(U);
if Dimension(U) ne Dimension(V) then 
   return false, KMatrixSpace(k,1,1)!0, [0], [0], KMatrixSpace(k,1,1)!0;
end if;
if Dimension(U) eq NumberOfProjectives(U) then 
   if Dimension(V) eq NumberOfProjectives(V) then 
      return true, KIdentityMatrix(k,Dimension(U)),
           [KIdentityMatrix(k,Dimension(U))], [], 
           KIdentityMatrix(k,Dimension(U));
   else 
      return false, KMatrixSpace(k,1,1)!0, [0], [0], KMatrixSpace(k,1,1)!0;
   end if;
end if;
if Dimension(V) eq NumberOfProjectives(V) then
   return false, KMatrixSpace(k,1,1)!0, [0], [0], KMatrixSpace(k,1,1)!0;
end if;
X := AssociatedGradedAlgebra(U);
sigma := GradedFactorIsomorphism(U);
Y := AssociatedGradedAlgebra(V);
tau := GradedFactorIsomorphism(V);
taui := tau^(-1);
A1, B1, tail1, lp1, g2mats, n2mats := GradedIsoStepTwo(X);
A2, B2, tail2, lp2, g2mats, n2mats := GradedIsoStepTwo(Y);
if tail1 ne tail2 or lp1 ne lp2 then
        return false, KMatrixSpace(k,1,1)!0, [0], [0], KMatrixSpace(k,1,1)!0;
end if;
E := B2;
if Dimension(A1) eq Dimension(B1) then 
   return true, KIdentityMatrix(k,Dimension(U)), 
      [tau*x*taui: x in g2mats], [tau*x*taui: x in n2mats],
           sigma*taui;
end if; 
theta1 := Matrix(IdentityMatrix(k, Dimension(B1)));
theta2 := Matrix(IdentityMatrix(k, Dimension(B2)));
gplst := g2mats;
uplst := n2mats;

vprint Automorphisms:  "checking initial homomorphism ",
        IsAlgebraHomomorphism(B2,B1,KMatrixSpace(k,
		Nrows(theta1),Ncols(theta1))!theta1);
ww := Maximum(lp2);
for i := 3 to ww do
   vprint Automorphisms: "";
   vprint Automorphisms: "                    ==========  ";
   vprint Automorphisms: "Step ", i;
   vtime Automorphisms: B1, B2, E, theta1, theta2, gplst, uplst, V, CC :=
          GradedIsoNextStep(A1, B1, A2, B2, E, tail2, lp2,
              theta1, theta2, gplst, uplst, i);
   if Type(B1) eq BoolElt then
        return false, KMatrixSpace(k,1,1)![B2], [0], [0], KMatrixSpace(k,1,1)!0;
   end if;
end for;
raddims := MinimalGeneratorForm(X)`RadicalDimensions;
ddims := DimensionsOfProjectiveModules(X);
tdims := [];
sdims1 := [1];
sdims2 := [1];
for i := 1 to #ddims do
   tdims[i] := ddims[i] - raddims[i][3];
   sdims1[i+1] := sdims1[i] + ddims[i];
   sdims2[i+1] := sdims2[i] + tdims[i];
end for;
MMM := KMatrixSpace(k, &+tdims, &+tdims)!0;
tt2 := MMM;
for i := 1 to #ddims do
   InsertBlock(~tt2,
             Submatrix(theta2,sdims1[i],sdims1[i],tdims[i],tdims[i]),
             sdims2[i], sdims2[i]);
end for;
ngplst := [];
ngplst := [];
for j := 1 to #gplst do
   ngp := MMM;
   for i := 1 to #ddims do
      InsertBlock(~ngp,
             Submatrix(gplst[j],sdims1[i],sdims1[i],tdims[i],tdims[i]),
             sdims2[i], sdims2[i]);
   end for;
   Append(~ngplst, tt2^-1*ngp*tt2);
end for;
nuplst := [];
for j := 1 to #uplst do
   ugp := MMM;
   for i := 1 to #ddims do
      InsertBlock(~ugp,
             Submatrix(uplst[j],sdims1[i],sdims1[i],tdims[i],tdims[i]),
             sdims2[i], sdims2[i]);
   end for;
   Append(~nuplst, tt2^-1*ugp*tt2);
end for;
mu := GradedCapHomomorphism(X,Y,theta1^(-1)*theta2);
ngplst1 := [tau*x*taui: x in ngplst];
nuplst1 := [tau*x*taui: x in nuplst];
//checks := true;

	/////////////////////////////////////////////////////////////////
	if checks then /////////////////////////////////////////////////
	print IsAlgebraHomomorphism(X, Y, theta1^(-1)*theta2); //////////
	end if;  ////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////

        return true, theta1^(-1)*theta2, ngplst1, nuplst1, sigma*mu*taui;

end function;

////////////////////////////////////////////////////////////////////////

intrinsic GradedAutomorphismGroup(A::AlgBas) -> GrpMat, SeqEnum[ModMatFldElt],
	SeqEnum[ModMatFldElt], SeqEnum[ModMatFldElt], GrpPerm
{Returns the group of graded automorphisms of the associated graded 
algebra X of the basic algebra A. returns also the graded caps
of the generators of the graded automorhism group. These are the induced
automorphisms of X/Rad^2(X) to itself, and they are returned as two
lists of nonunipotent and unipotent generators that preserve the idempotents
of X and a list of generators that permute the idempotents.}

k := BaseRing(A);
autgp, glmats, nilmats := GradedAutomorphismGroupMatchingIdempotents(A);

np := NumberOfProjectives(A);
dpm := DimensionsOfProjectiveModules(A);
XGL := GL(Dimension(A),k);
ngrp := [];
ulst := [];
ugrp := sub<Sym(#dpm)|>;
if np gt 1 and #Seqset(dpm) ne #dpm then 
   X := AssociatedGradedAlgebra(A);
   PG := StabilizerOfList(DimensionsOfProjectiveModules(A));
   ugrp := sub<PG|>;
   cycs := Reverse(CyclicSubgroups(PG));
   for x in cycs do
      if x`order gt 1 then
         ss := x`subgroup;
         nn := Normalizer(PG, sub<PG|ugrp,ss>);
         gplst := [ss.1^y: y in Transversal(PG,nn)];
         for t in gplst do
            if not t in ugrp then
//               B, theta1 := ChangeIdempotents(X,t);
//               mmf := MinimalGeneratorForm(B);
//               muu := mmf`Homomorphism;
//               Y := AssociatedGradedAlgebra(mmf`Algebra);
               Y, theta1 := ChangeIdempotents(X,t);
               boo, gamma := IsGradedIsomorphicMI(X,Y);
               if boo then
                  ugrp := sub<PG|ugrp, t>;
                  Append(~ulst,t);
//                  Append(~ngrp, gamma*Matrix(muu)*Matrix(theta1)^-1);
                  Append(~ngrp, gamma*Matrix(theta1)^-1);
                  if #ugrp eq #PG then
                     break;
                  end if;
               end if;
            end if;            
         end for;
      end if;
   end for;
end if;
if np eq 1 then
   ugrp := Sym(1);
end if;
if #ulst ne 0 then
   gdautogp := sub<XGL| Setseq(Generators(autgp)) cat [XGL!x:x in ngrp]>;
else 
   gdautogp := autgp;
end if;

pmats := [];
if #ulst ne 0 then 
   raddims := MinimalGeneratorForm(A)`RadicalDimensions;
   tdims := [];
   sdims1 := [1];
   sdims2 := [1];
   for i := 1 to #dpm do
      tdims[i] := dpm[i] - raddims[i][3];
      sdims1[i+1] := sdims1[i] + dpm[i];
      sdims2[i+1] := sdims2[i] + tdims[i];
   end for;
   MMM := KMatrixSpace(k, &+tdims, &+tdims)!0;
   for j := 1 to #ulst do
      tt := MMM;
      for i := 1 to #dpm do
         InsertBlock(~tt,
              Submatrix(ngrp[j], sdims1[i], sdims1[i^ulst[j]],
                     tdims[i], tdims[i^ulst[j]]),
                sdims2[i], sdims2[i^ulst[j]]);
      end for;
      Append(~pmats, tt);
   end for;
end if;

	return gdautogp, glmats, nilmats, pmats, ugrp;

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic IsGradedIsomorphic(A::AlgBas,B::AlgBas) -> Bool, ModMatFldElt
{True if the associated graded algebras of A and B are isomorphic, in 
which case the isomorphism is returned.} 

np := NumberOfProjectives(A);
if np ne NumberOfProjectives(B) then
	return false, KMatrixSpace(BaseRing(A), 1, 1)!0;
end if;
X := AssociatedGradedAlgebra(A);
Z := AssociatedGradedAlgebra(B);
if np eq 1 then 
   boo, mat := IsGradedIsomorphicMI(A,B);
   if boo then 
	return boo, GradedCapHomomorphism(X,Z,mat);
   else
	return boo, mat;
   end if;
end if;
dpa := DimensionsOfProjectiveModules(A);
dpb := DimensionsOfProjectiveModules(B);
if Sort(dpa) ne Sort(dpb) then 
        return false, KMatrixSpace(BaseRing(A), 1, 1)!0;
end if;
for x in Sym(np) do
   if &and[dpa[i] eq dpb[i^x]: i in [1 .. #dpa]] then
      C,theta1 := ChangeIdempotents(Z,x);

        /////////////////////////////////////////////////////////////
        checks := false;  ///////////////////////////////////////////
        // checks := true;  /////////////////////////////////////////
        if checks then  ////////////////////////////////////////////
        IsAlgebraHomomorphism(C, Z, theta1);  ///////////////////////
        end if;   ///////////////////////////////////////////////////
        /////////////////////////////////////////////////////////////

      mmf := MinimalGeneratorForm(C);
      muu := mmf`Homomorphism;
      Y := AssociatedGradedAlgebra(mmf`Algebra);

        //////////////////////////////////////////////////////////////
        if checks then   /////////////////////////////////////////////
        IsAlgebraHomomorphism(C,Y, muu);  ////////////////////////////
        end if;  /////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////

      boo, gamma := IsGradedIsomorphicMI(X,Y);

        //////////////////////////////////////////////////////////////
        if checks then   ////////////////////////////////////////////
        IsAlgebraHomomorphism(X, Y, gamma); //////////////////////////
        end if;  /////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////


      if boo then
         return boo, GradedCapHomomorphism(X,Z,
                       gamma*Matrix(muu)*Matrix(theta1)^-1);
      end if;
   end if;
end for;

	return false, KMatrixSpace(BaseRing(A), 1, 1)!0;

end intrinsic;

