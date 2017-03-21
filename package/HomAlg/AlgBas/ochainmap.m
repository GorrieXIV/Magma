freeze;

import "algebras.m": ListSummandIndices;
import "compact.m": CreateBoundaryMap, CompactToPR, CompactToPR2;

// We have the following diagram
//
//			mu
//		P ------------------>	B
//		
//		|			|
//	(gamma)	|			|   theta
//		V			V
//			phi
//		B  -----------------> 	C
//
//   where we assume 
// 		1.)  P is projective (it may be a projective module
//			together with the list of the multiplicities
//			of the indecomposable projectives in it. 
//		2.) the Image of mu*theta should be in the image of phi.
//			Return an error message otherwise.
// 		3.) mu may be given in compact form (if for example it
//			is a term in a projective resolution). 
//		4.) If both mu and phi are in compcact form then
// 			theta may be give in compact form or may be
//			given only as a matric or maybe a map of 
// 			projective modules.
// The function returns gamma.


// Note that when we install complexes then the types given below will
// change.

ChainStep := function(mu,theta,phi,alg);

ff := BaseRing(alg);
npp := NumberOfProjectives(alg);
pflag := true;
if Type(mu) eq ModMatFldElt then
   pflag := false;
end if;
bflag := true;
if Type(phi) eq ModMatFldElt then
   bflag := false;
end if;
if pflag then
   Pll := mu[2];
   if bflag then
				// phi and mu both in compact form
      if Type(theta) eq Tup then		// theta compact
         thet := CreateBoundaryMap(theta,alg);
      else					// theta is matrix
         thet := theta;
      end if;					// type theta
      IMA := mu[1]*thet;
      phi1 := CreateBoundaryMap(phi,alg);
      bool, INV := IsConsistent(phi1, IMA);
      if npp gt 1 then
         bbb := [0] cat [&+[Pll[i]:i in [1 .. j]]:j in [1 .. #Pll]];
         ccc := ListSummandIndices(phi[2]);
         Qll := [Dimension(ProjectiveModule(alg,ccc[i])): i in [1 .. #ccc]];
         aaa := [0] cat [&+[Qll[i]:i in [1 .. j]]:j in [1 .. #Qll]];
         INA := KMatrixSpace(ff,Nrows(INV),Ncols(INV))!0;
         for i := 1 to #Pll do
            if Pll[i] ne 0 then
               for j := 1 to #aaa-1 do
                  if Qll[j] ne 0 then
                     InsertBlock(~INA,Submatrix(INV,bbb[i]+1,
                                 aaa[j]+1,Pll[i],Qll[j])*
	                         Action(ProjectiveModule(alg,ccc[j])).i,
                                     bbb[i]+1,aaa[j]+1);
                  end if;		       		// Qll[j] > 0
               end for;					//j
            end if;					// Pll[i] > 0
         end for;					//i
         INV := INA;
      end if;
      CHM := <INV,mu[2],phi[2]>;

//                                *** 1 ***   done

   else 				//mu compact, phi not (bflag)
      IMA := mu[1]*theta;
      bool, INV := IsConsistent(phi, IMA);
      if npp gt 1 then 
         aaa := ListSummandIndices(Pll);
         INA := KMatrixSpace(ff,Nrows(INV),Ncols(INV))!
	      [INV[j]*Action(Domain(phi)).aaa[j]: j in [1 .. Nrows(INV)]];
         INV := INA;
      end if;						// npp > 1
      CHM := <INV,mu[2],phi[2]>;
//                                *** 2 ***   done

   end if;						// bflag
else 						// pflag = false
   P := Domain(mu);
   rad := JacobsonRadical(P);
   if npp gt 1 then 
      qq, xi := quo<P|rad>;
      BC := [];
      Pll := [];
      for i := 1 to npp do
         bb := [x@@xi:x in Basis(sub<qq|[y*Action(qq).i:y in Basis(qq)]>)];
         Pll[i] := #bb;
         BC := BC cat bb;
      end for;  					// i 
      BB := KMatrixSpace(ff, #BC, Dimension(Domain(mu)))!BC;
   else 						//npp = 1
      ext := ExtendBasis(P,rad);
      top := KSpaceWithBasis([ext[i]:i in [Dimension(rad)+1 .. #ext]]);
      BB := BasisMatrix(top);
      Pll := [Nrows(BB)];
   end if;						// npp > 1
   IMA := BB*mu*theta;
   if bflag then			// phi compact, mu not
      phi1 := CreateBoundaryMap(phi,alg);
      bool, INV := IsConsistent(phi1, IMA);
      if npp gt 1 then
         bbb := [0] cat [&+[Pll[i]:i in [1 .. j]]:j in [1 .. #Pll]];
         ccc := ListSummandIndices(phi[2]);
         Qll := [Dimension(ProjectiveModule(alg,ccc[i])): i in [1 .. #ccc]];
         aaa := [0] cat [&+[Qll[i]:i in [1 .. j]]:j in [1 .. #Qll]];
         INA := KMatrixSpace(ff,Nrows(INV),Ncols(INV))!0;
         for i := 1 to #Pll do
            if Pll[i] ne 0 then
               for j := 1 to #aaa-1 do
                  if Qll[j] ne 0 then
                     InsertBlock(~INA,Submatrix(INV,bbb[i]+1,aaa[j]+1,
                              Pll[i],Qll[j])*
	                      Action(ProjectiveModule(alg,ccc[j])).i,
                              bbb[i]+1,aaa[j]+1);
                  end if;				  	// Qll[j] > 0
               end for;					//j
            end if;						// Pll[i] > 0
         end for;					//i
         INV := INA;
      end if;						//npp > 1
      IMM := ProjectiveModule(alg,phi[2]);
      CHM := LiftHomomorphism([IMM!INV[j]: j in [1 .. Nrows(INV)]],Pll);

//                                *** 3 ***   done


   else				// neither phi nor mu compact
      bool, INV := IsConsistent(phi, IMA);
      if npp gt 1 then
         aaa := ListSummandIndices(Pll);
         INA := KMatrixSpace(ff,Nrows(INV),Ncols(INV))!
	     [INV[j]*Action(Domain(phi)).aaa[j]: j in [1 .. Nrows(INV)]];
         INV := INA;
      end if;
   IMM := Domain(phi);
   CHM := LiftHomomorphism([IMM!INV[j]: j in [1 .. Nrows(INV)]],Pll);

//                                *** 4 ***

   end if;					//bflag
end if;					//pflag

          return CHM;

end function;

//********************************************************************

CompactCocycle := function(L,n,A);

if NumberOfProjectives(A) eq 1 then 
   nn := Dimension(ProjectiveModule(A,1));
   nL := [1];
else 
   nl := ListSummandIndices(L);
   nn := Dimension(ProjectiveModule(A,nl[n]));
   nL := [0:i in [1 .. #L]];
   nL[nl[n]] := 1;
end if;
cmat := KMatrixSpace(BaseRing(A),&+L,nn)!0;
cmat[n] := Basis(VectorSpace(BaseRing(A),nn))[1];

      return <cmat,L,nL>;

end function;

//*********************************************************************

nChainMap := function(prj1,prj2,t,d,n,alg);

// prj1 and prj2 are the projective resolutions that the domain and
// codomain of the chain map. The map phi is a map from the term in 
// degree d of prj1 to the module M. The complex prj2 is the projective
// resolution of the module M. The natural number n is the limit of
// the computation. This version depends on the second projective
// resolution being compact, but only because of the augmentation
// map.

ff := BaseRing(alg);
a1 := #prj1`BettiNumbers -1;
a2 := #prj2`BettiNumbers -1;
CMM := [* <CompactCocycle(prj1`BettiNumbers[a1-d+1],t,alg),d,0> *];
			  //(prj1[1][a1-d+1][2],t,alg),d,0> *];
if n gt 0 then
   nn := Minimum([n-1,a2,a1-d]);
   for i := 1 to nn do
      map1 := <prj1`ResolutionRecord[a1-d-i+1],prj1`BettiNumbers[a1-d-i+1],
		   prj1`BettiNumbers[a1-d-i+2]>;
      map2 := <prj2`ResolutionRecord[a1-i+1],prj2`BettiNumbers[a1-i+1],
		   prj2`BettiNumbers[a1-i+2]>;
      xx := ChainStep(map1,CMM[1][1],map2,alg);
      CMM := [* <xx,d+i,i> *] cat CMM;
   end for;
end if;

           return CMM;

end function;

//***********************************************************************

Cocycle := function(L,n,A);

if NumberOfProjectives(A) eq 1 then 
   nn := (n-1)*Dimension(ProjectiveModule(A,1))+1;
else 
   nl := DimensionsOfProjectiveModules(A);
   nll := ListSummandIndices(L);
   nlll := [0] cat [&+[nl[nll[j]]:j in [1 .. i]]:i in [1 .. #nll]];
   nn := nlll[n]+1;
end if;
cmat := KMatrixSpace(BaseRing(A),nlll[#nlll],1)!0;
cmat[nn] := Basis(VectorSpace(BaseRing(A),1))[1];

            return cmat;

end function;

//*********************************************************************

TopOfChainMap := function(C,alg,b1,b2,d);
// C is the compact chain map, alg is the algebra, b1 and b2 are the
// Betti numbers for the projective resolutions and d is the degree.

T := [*  *];
for k := 1 to #C do
   i := #C-k+1;
   M1 := Transpose(C[i][1][1]);
   M2 := KMatrixSpace(BaseRing(alg),&+C[i][1][3],&+C[i][1][2])!0;
   if NumberOfProjectives(alg) eq 1 then
      rlst := [1] cat 
        [Dimension(ProjectiveModule(alg,1))*k+1:k in [1 .. &+C[i][1][3]]];
   else
      aa := ListSummandIndices(C[i][1][3]);
      bb := [Dimension(ProjectiveModule(alg,aa[i])):i in [1 .. #aa]];
      rlst := [1] cat [&+[bb[j]:j in [1 .. i]]+1:i in [1 .. #bb]];
   end if;
   for j := 1 to #rlst-1 do
      M2[j] := M1[rlst[j]];
      M3 := Transpose(M2);
      T[k] := M3;
   end for;
end for;
TT := [* T[#T+1-i]: i in [ 1 .. #T] *];
//blst := 
SS := SimpleModule(BasicAlgebra(BaseRing(alg)),1);
Plst := [DirectSum([SS:i in [1 .. &+b1[j]]]):j in [1 .. #b1]];
Qlst := [DirectSum([SS:i in [1 .. &+b2[j]]]):j in [1 .. #b2]];
PMlst := [* AHom(Plst[i], Plst[i+1])!0: i in [1 .. #Plst-1] *];
QMlst := [* AHom(Qlst[i], Qlst[i+1])!0: i in [1 .. #Qlst-1] *];
CC := Complex(PMlst,0);
DD := Complex(QMlst,0);
ch := ChainMap(TT,CC,DD,-d);

                return T, ch;

end function;

//********************************************************************

intrinsic CohomologyRingGenerators(Prj::Rec) -> Rec
{Given a projective resolutions P for a simple module S over a basic
algebra A, the function returns the chain maps in compact form of the 
minimal generators for the cohomology Ext*(S,S).}

AC := [* *];
TP1 := [* *];                               //tops of generators
TP2 := [* *];                               //tops of composites
                                   // the tops will be triples consisting
                                   // the actual list of matrices of the tops,
                                   // the ordered list of product of generators
                                   // and the total degree.
alg := Algebra(Prj`Module);    //Algebra(Domain(Prj[2]));
pp := #Prj`BettiNumbers -1;
ff := BaseRing(alg);
aa := CompactToPR(alg,Prj`BettiNumbers, Prj`ResolutionRecord);
nn := &+[i:i in [1 .. NumberOfProjectives(alg)]|
                    Determinant(Action(Prj`Module).i) ne 0];
xx := Prj`BettiNumbers;
xxx := [xx[pp-i+1]: i in [ 1 .. pp]];
                                                     // this is the type of
                                                     // of the projectives
                                                     // in the resolution.
ddd := [];
for i := 1 to #xxx do
   if xxx[i][nn] gt 0 then
      ddd[i] := 1;
   else 
      ddd[i] := 0;
   end if;
end for;                                            //the degrees of interest
nn1 := Minimum([i:i in [1 .. #ddd]| ddd[i] ne 0]);
                                                     //first nonzero degree
                                                     //of cohomology
for i := 1 to #ddd do
   if ddd[i] ne 0 then
      if i lt 2*nn1 then
         lss := ListSummandIndices(xxx[i]);
         aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
         for t in aaa do
            chm := nChainMap(Prj,Prj,t,i,pp,alg);   
            Append(~AC,chm);
            ch, tp := TopOfChainMap(chm,alg,xx,xx,i);
            Append(~TP1,<tp,[#TP1+1],i>);
         end for;                                         // t
      end if;                                          // i < 2*nn1
      if i ge 2*nn1 then
                          // get all of the tops
         rho := KMatrixSpace(ff, &+xxx[i],xxx[i][nn])!0;
         lss := ListSummandIndices(xxx[i]);
         aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
         for l := 1 to #aaa do
            rho[aaa[l]][l] := ff!1; 
         end for;                                     // l
         V := VectorSpace(ff,xxx[i][nn]);
         VV := VectorSpace(ff, &+xxx[i]);
         W := sub<V|>;
         if &+[ddd[s] + ddd[i-s]:s in [1 .. i-1]] ge 2 then
            TP := TP1 cat TP2;
            for c := 1 to #TP1 do
               for d := 1 to #TP do
         	  if TP1[c][3] + TP[d][3] eq i then 
                     ww := Vector(Transpose(ModuleMap(TP1[c][1],
                       TP1[c][3]+TP[d][3])*ModuleMap(TP[d][1],TP[d][3]))*rho);
                     if ww notin W then
                        W := sub<V|W,ww>;
                        top :=  TP1[c][1]*TP[d][1];
                        Append(~TP2,<top,TP1[c][2] cat TP[d][2],i>);
                     end if;                         // ww notin W
                  end if;                            // degrees wrong
                  if W eq V then 
                     break c;
                  end if;                                         // W = V
               end for;                                        // d
            end for;                                        // c
         end if;                           // ddd -- composite degrees
         if W ne V then
            trho := Transpose(rho);
            ext := ExtendBasis(W,V);
            nelts := [Index(Basis(VV),x):x in 
                    [trho(ext[i]):i in [Dimension(W)+1 .. Dimension(V)]]];
            for t in nelts do 
               chm := nChainMap(Prj,Prj,t,i,#Prj`BettiNumbers-1,alg);
               Append(~AC,chm);
               ch, tp := TopOfChainMap(chm,alg,xx,xx,i);
               Append(~TP1,<tp,[#TP1+1],i>);
            end for;                                         // t
         end if;                                          // W ne V
      end if;                                       // i > 2*nn1-1            
   end if;                                           // ddd[i] > 0
end for;                                          //i

                 return <AC,TP1,TP2>;

end intrinsic;

//********************************************************************

intrinsic DegreesOfGenerators(ACM::Tup) -> SeqEnum
{Given the generators for cohomolgy, the function returns the list 
of degrees of the minimal generators.}

ss := [ACM[2][i][3]: i in [1 .. #ACM[2]]];
return ss;

end intrinsic;

//*********************************************************************


intrinsic CohomologyRightModuleGenerators(P::Rec , Q::Rec, CQ::Tup) -> Tup
{Given projective resolutions P and Q for simple module S and T over a basic
algebra A and the cohomology generators for T associated to the resolution
Q, the function returns the chain maps in compact form of the minimal 
generators for the cohomology Ext*(S,T) as a right module over the 
cohomology ring Ext*(T,T).}

AC := [* *];
TP1 := [* *];                               //tops of generators
TP := CQ[2] cat CQ[3];                     //tops of cohomology for T
                                   // the tops will be triples consisting
                                   // the actual list of matrices of the tops,
                                   // the ordered list of product of generators
                                   // and the total degree.
alg := Algebra(P`Module);   //alg := Algebra(Domain(P[1]));
p1 := #P`BettiNumbers -1;
pp := Minimum(#P`BettiNumbers,#Q`BettiNumbers) -1;
ff := BaseRing(alg);
                                  // need to allow for noncompact resolutions
aa := CompactToPR2(alg,Q`BettiNumbers, Q`ResolutionRecord,pp);
nn := &+[i:i in [1 .. NumberOfProjectives(alg)]|
                    Determinant(Action(Q`Module).i) ne 0];
                                  // this the number of the simple module T
xx := P`BettiNumbers;
xxx := [xx[#xx-i]: i in [ 1 .. pp]];
                                                      // this is the type of
                                                     // of the projectives
                                                     // in the resolution.
ddd := [];
for i := 1 to pp do
   if xxx[i][nn] gt 0 then
      ddd[i] := 1;
   else 
      ddd[i] := 0;
   end if;
end for;                                            //the degrees of interest
if &+ddd eq 0 then
   return <0>;
end if;
nn1 := Minimum([i:i in [1 .. #ddd]| ddd[i] ne 0]);
                                                     //first nonzero degree
                                                     //of cohomology
nn2 := Minimum(DegreesOfGenerators(CQ));
dde := [TP[i][3]:i in [1 .. #TP]];                // degrees of elements
                                                    // in the cohomology of T
for i := 1 to #ddd do
   if ddd[i] ne 0 then
      if i lt nn1 + nn2 then
         lss := ListSummandIndices(xxx[i]);
         aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
         for t in aaa do
            chm := nChainMap(P,Q,t,i,#P`BettiNumbers-1,alg);
            Append(~AC,chm);
            tp := TopOfChainMap(chm,alg,xx,Q`BettiNumbers,i);
            Append(~TP1,<tp,[#TP1+1],i>);
         end for;                                         // t
      else
                          // get all of the tops
      VV := VectorSpace(ff,&+xxx[i]);
      V := VectorSpace(ff,xxx[i][nn]);
      rho := Hom(VV,V)!0;
      lss := ListSummandIndices(xxx[i]);
      aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
      for l := 1 to #aaa do
         rho[aaa[l]] := Basis(V)[l]; 
      end for;                                         // l
      W := sub<V|>;
      if &+[ddd[s] + #[x:x in dde|x eq i-s]:s in [1 .. i-1]] ge 2 then
         for c := 1 to #TP1 do
            for d := 1 to #TP do
               if TP1[c][3]+TP[d][3] eq i then
                  ww := rho(Transpose(TP1[c][1][TP[d][3]+1]*TP[d][1][1])[1]);
                  if ww notin W then
                     W := sub<V|W,ww>;
                        top := [* *];
                        for l := 1 to pp-i+1 do
                           top[l] :=  TP1[c][1][TP[d][3]+l]*TP[d][1][l];
                        end for;
                     end if;                                     // ww notin W
                  end if;                                     // degrees wrong
                  if W eq V then 
                     break c;
                  end if;                                         // W = V
               end for;                                        // d
            end for;                                        // c
         end if;                                // ddd -- composite degrees
         if W ne V then
            trho := Transpose(rho);
            ext := ExtendBasis(W,V);
            nelts := [Index(Basis(VV),x):x in 
                    [trho(ext[i]):i in [Dimension(W)+1 .. Dimension(V)]]];
            for t in nelts do 
               chm := nChainMap(P,Q,t,i,#P`BettiNumbers-1,alg);
               Append(~AC,chm);
               tp := TopOfChainMap(chm,alg,xx,Q`BettiNumbers,i);
               Append(~TP1,<tp,[#TP1+1],i>);
            end for;                                         // t
         end if;                          // W ne V

      end if;                                 // i > 2*nn1-1            
   end if;                                           // ddd[i] > 0
end for;                                          //i

            return <AC,TP1>;

end intrinsic;

//************************************************************************

intrinsic CohomologyLeftModuleGenerators(P::Rec ,CP::Tup, Q::Rec) -> Tup
{Given projective resolutions P and Q for simple module S and T over a basic
algebra A and the cohomology generators for T associated to the resolution
Q, the function returns the chain maps in compact form of the minimal 
generators for the cohomology Ext*(S,T) as a left module over the cohomology 
ring Ext*(S,S).}

AC := [* *];
TP1 := [* *];                               //tops of generators
TP := CP[2] cat CP[3];                     //tops of cohomology for S
                                   // the tops will be triples consisting
                                   // the actual list of matrices of the tops,
                                   // the ordered list of product of generators
                                   // and the total degree.
alg := Algebra(P`Module);
p1 := #P`BettiNumbers -1;
pp := Minimum(#P`BettiNumbers,#Q`BettiNumbers) -1;
ff := BaseRing(alg);
                                  // need to allow for noncompact resolutions
aa := CompactToPR2(alg,Q`BettiNumbers, Q`ResolutionRecord,pp);
nn := &+[i:i in [1 .. NumberOfProjectives(alg)]|
                    Determinant(Action(Q`Module).i) ne 0];
                                  // this the number of the simple module T
xx := P`BettiNumbers;
xxx := [xx[#xx-i]: i in [ 1 .. pp]];
                                                     // this is the type of
                                                     // of the projectives
                                                     // in the resolution.
ddd := [];
for i := 1 to pp do
   if xxx[i][nn] gt 0 then
      ddd[i] := 1;
   else 
      ddd[i] := 0;
   end if;
end for;                                            //the degrees of interest
if &+ddd eq 0 then 
   return <0>;
end if;
nn1 := Minimum([i:i in [1 .. #ddd]| ddd[i] ne 0]);
                                                     //first nonzero degree
                                                     //of cohomology
nn2 := Minimum(DegreesOfGenerators(CP));
dde := [TP[i][3]:i in [1 .. #TP]];                // degrees of elements
                                                    // in the cohomology of S
for i := 1 to #ddd do
   if ddd[i] ne 0 then
      if i lt nn1 + nn2 then
         lss := ListSummandIndices(xxx[i]);
         aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
         for t in aaa do
            chm := nChainMap(P,Q,t,i,#P`BettiNumbers-1,alg);
            Append(~AC,chm);
            tp := TopOfChainMap(chm,alg,xx,Q`BettiNumbers,i);
            Append(~TP1,<tp,[#TP1+1],i>);
         end for;                                         // t
      else
                          // get all of the tops
         VV := VectorSpace(ff,&+xxx[i]);
         V := VectorSpace(ff,xxx[i][nn]);
         rho := Hom(VV,V)!0;
         lss := ListSummandIndices(xxx[i]);
         aaa := [j: j in [1 .. #lss]|lss[j] eq nn];
         for l := 1 to #aaa do
            rho[aaa[l]] := Basis(V)[l]; 
         end for;                                         // l
         W := sub<V|>;
         if &+[ddd[s] + #[x:x in dde|x eq i-s]:s in [1 .. i-1]] ge 2 then
            for c := 1 to #TP1 do
               for d := 1 to #TP do
                  if TP1[c][3]+TP[d][3] eq i then
                     ww := rho(Transpose(TP[d][1][TP1[c][3]+1]*
					 TP1[c][1][1])[1]);
                     if ww notin W then
                        W := sub<V|W,ww>;
                        top := [* *];
                        for l := 1 to pp-i+1 do
                           top[l] :=  TP[d][1][TP1[c][3]+l]*TP1[c][1][l];
                        end for;
                     end if;                            // ww notin W
                  end if;                              // degrees wrong
                  if W eq V then 
                     break c;
                  end if;                                 // W = V
               end for;                                        // d
            end for;                                        // c
         end if;                       // ddd -- composite degrees
         if W ne V then
            trho := Transpose(rho);
            ext := ExtendBasis(W,V);
            nelts := [Index(Basis(VV),x):x in 
                    [trho(ext[i]):i in [Dimension(W)+1 .. Dimension(V)]]];
            for t in nelts do 
               chm := nChainMap(P,Q,t,i,#P`BettiNumbers-1,alg);
               Append(~AC,chm);
               tp := TopOfChainMap(chm,alg,xx,Q`BettiNumbers,i);
               Append(~TP1,<tp,[#TP1+1],i>);
            end for;                                         // t
         end if;                                          // W ne V

      end if;                                           // i > 2*nn1-1            
   end if;                                           // ddd[i] > 0
end for;                                          //i

              return <AC,TP1>;

end intrinsic;

//********************************************************************


intrinsic DegreesOfCohomologyGenerators(AC::Tup) -> SeqEnum
{Returns the degrees of the chain maps of the generators of the 
   cohomology}

   deg := [AC[1][i][#AC[1][i]][2]:i in [1 .. #AC[1]]];
   return deg;

end intrinsic;

/***************************************************************************
			  Cohomology Generators
***************************************************************************/

intrinsic CohomologyGeneratorToChainMap(P::ModCpx,Q::ModCpx,C::Tup,
		  n::RngIntElt) -> MapChn
{Given the projective resolutions P and Q of two modules M and N and 
the cohomology generators in compact form C of the cohomology module, 
Ext_B^*(M,N), the function returns the chain map from P to Q that lifts 
the nth generator of the of the cohomology ring and has degree equal to 
the degree of that generator.}

   cmm := [* *];
   cll := C[1][n];
   m := cll[#cll][2];
   A := Algebra(Term(P,0));
   for j := 1 to #cll do
   cmm[j] := Hom(Term(P,#cll+m-j),Term(Q,#cll-j))!
               CreateBoundaryMap(cll[j][1],A);
   end for;
   CM := ChainMap(cmm,P,Q,-m);
   return CM;

end intrinsic;

//***********************************************************************

intrinsic CohomologyGeneratorToChainMap(P::ModCpx,C::Tup,n::RngIntElt) ->
     MapChn
{Given the projective resolution P of a module and the cohomology generators
in compact form C of the cohomology ring of that module, the function returns 
the chain map from P to P that lifts the nth generator of the of the cohomology
ring and has degree equal to the degree of that generator.}

   cmm := [* *];
   cll := C[1][n];
   m := cll[#cll][2];
   A := Algebra(Term(P,0));
   for j := 1 to #cll do
   cmm[j] := Hom(Term(P,#cll+m-j),Term(P,#cll-j))!
           CreateBoundaryMap(cll[j][1],A);
   end for;
   CM := ChainMap(cmm,P,P,-m);

   return CM;

end intrinsic;



