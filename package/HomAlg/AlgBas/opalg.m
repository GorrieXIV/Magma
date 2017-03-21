freeze;

NonIdempotentAGenerators := function(alg);
n := NumberOfProjectives(alg);
pt := &cat[PathTree(alg,i):i in [1 .. n]];
bl := [];
for i := 1 to #pt do
if pt[i][1] eq 1 and pt[i][2] gt n then
bl[pt[i][2]-n] :=  alg!Basis(VectorSpace(alg))[i];
end if;
end for;
return bl;
end function;


AlgebraGenerators := function(alg);
blst := IdempotentGenerators(alg) cat NonIdempotentGenerators(alg);
return blst;
end function;


GeneratorWords := function(alg);
revtr := [];
for i := 1 to NumberOfProjectives(alg) do
trr := PathTree(alg,i);
for t := 1 to #trr do
aa := [Index(IdempotentGenerators(alg),e):e in IdempotentGenerators(alg)|
		(alg!Injection(alg,i,ProjectiveModule(alg,i).t))*alg!e ne 0];
nn := t;
for j := 1 to #trr do
if nn ne 1 then 
aa := aa cat [trr[nn][2]];
nn := trr[nn][1];
end if;
end for;
revtr := revtr cat  [aa];
end for;
end for;
return revtr;
end function;

intrinsic PathTreeCyclicModule(mmd::ModRng,ig::RngIntElt,nig::RngIntElt) -> ModAlgBas
{}

   wwd := mmd;
   rq := [mmd];
   n:=2;
   while Dimension(wwd) ne  0 do
   rm := JacobsonRadical(wwd);
   rq[n] := rm;
   wwd := rm;
   n := n+1;
   end while;
   q1, theta := quo<mmd|rq[2]>;
   if Dimension(q1) ne 1 then
   print "Module is not cyclic";
   return 0;
   end if;
   num := &+[n: n in [1 .. ig]|q1.1*Action(q1).n eq q1.1];
   tlst := [(q1.1@@theta)*Action(mmd).num];
   trr := [<1,num>];
   baselst := tlst;
   nu := 0;
   for j := 3 to #rq do
   qq,phi := quo<mmd|rq[n-1]>;
   BB := [];
   BBQ := [qq!0];
   for k := 1 to #baselst do
   for l := ig+1 to ig+nig do
   xx := baselst[k]*Action(mmd).l;
   if phi(xx) notin sub<qq|BBQ> then
   Append(~BB,xx);
   Append(~BBQ,phi(xx));
   Append (~trr, <nu+k,l>);
   end if;
   end for;
   end for;
   nu := nu + #baselst;
   baselst := BB;
   tlst := tlst cat BB;
   end for;
   MM := MatrixAlgebra(CoefficientRing(mmd),Dimension(mmd));
   mat := MM!tlst;
   inv := mat^-1;
   rmmm := sub<MM |[mat*(Action(mmd).i)*inv: i in [1 .. ig+nig]]>;
   return <rmmm, trr>;

end intrinsic;

intrinsic OppositeAlgebra(A::AlgBas) -> AlgBas
{Given a basic algebra A, creates the opposite algebra. This is the algebra
with the same set of elements but with multiplication * given by x*y = yx.}

// Note that the we are changing the basis for the basis for the opposite
// algebra. So an element v in A will not be represented by the same vector
// in the opposite algebra of A. A function for the change of basis is 
// given below.
   if assigned A`OppositeAlgebra then
	return A`OppositeAlgebra;
   end if;

   ff := BaseRing(A);
   N := NumberOfProjectives(A);
   pt := &cat[PathTree(A,i): i in [1 .. N]];
   gen := AlgebraGenerators(A);					//Generators(A);
			flag := true;
   if N eq 1 then
   rid := [1: i in [1 .. Ngens(A)]];
   lid := rid;
   relst := [1 : i in [1 .. #pt]];
   else
   rid := &cat[[j:j in [1 .. N]|
			gen[i]*gen[j] eq gen[i]]: i in [1 .. Ngens(A)]];
   lid := &cat[[j:j in [1 .. N]|
			gen[j]*gen[i] eq gen[i]]: i in [1 .. Ngens(A)]];
   relst := [rid[pt[j][2]]:j in [1 .. #pt]];  
                  // list of right idempotents
   end if;
   tll := [];
   diml := [];
   cdml := [0];
   lelst := [];
   for i := 1 to N do
   ll := [1];
   pi := PathTree(A,i);
   diml[i]:= #pi;
   cdml[i+1] := &+diml;
   lelst := lelst cat [i: j in [1 .. #pi]];
   if #pi gt 1 then 
   for j := 2 to #pi do
   ll[j] := ll[pi[j][1]]+1;
   end for;
   end if;
   tll := tll cat ll;
   end for;
                 // Now we have the total length list.
   maxl := Maximum(tll);
   V := RSpace(Integers(),maxl+8);
   zz := [0:i in [1 .. maxl]];
   ccdm := &cat[[cdml[j]: i in [1 .. diml[j]]]:j in [1 .. N]];
   vlst := [V!([j, ccdm[j]+pt[j][1], pt[j][2], tll[j],0,0, lelst[j], relst[j]] 
	cat zz):j in [1 .. #pt]];
   BB := Basis(V);
   for j := 1 to #pt do
   if vlst[j][4] gt 1 then     //vlst[j][4] is the length of the word.
   x := vlst[j];
   ww := vlst[x[2]];
   x := x + x[3]*BB[9] + &+[ww[8+i]*BB[9+i]:i in [1 .. x[4]-1]];
   vlst[j] := x;
   end if;
   end for;
   newlst := &cat[&cat[[x:x in vlst|x[4] eq i and x[8] eq k]:
         i in [1 .. maxl]]:k in [1..N]];
   ndims := [#[x:x in newlst|x[8] eq k]:k in [1 .. N]];
   cndims := [0] cat [&+[ndims[i]: i in [1 .. j]]:j in [1 .. N]];
			// now check to see if we have a tree
   I := Integers();
   RS := RSpace;
   VV,In,In2,Pr,Pr2 := DirectSum(RS(I,7),RS(I,maxl+1));
   CC := Basis(RS(I,maxl+1));
   for i := 1 to N do
   newlst[cndims[i]+1] := newlst[cndims[i]+1]+(cndims[i]+1)*BB[5]+i*BB[6]; 
   vecl := [Pr2(newlst[t]):t in [cndims[i]+1 .. cndims[i+1]]];
   for k := 2 to ndims[i] do
   tt := cndims[i]+k;
   xx :=  vecl[k]-vecl[k][newlst[tt][4]]*CC[newlst[tt][4]];
   if xx in vecl then 
   newlst[tt] := newlst[tt] + (cndims[i]+Index(vecl,xx))*BB[5] + 
		vecl[k][newlst[tt][4]]*BB[6];
   else 
			flag := false;	
			break i;
   end if;
   end for;
   end for;
			if flag then
				/*print "reverse trees"*/;
   npt := [];
   for i := 1 to N do
   npi := [<newlst[cndims[i]+k][5]-cndims[i],newlst[cndims[i]+k][6]>:
	k in [1 .. ndims[i]]];
   npt[i] := npi;
   end for;
   MM := MatrixAlgebra(ff,#pt);
   M0 := MM!0;
   VV := VectorSpace(ff,#pt);
   for i := 1 to #pt do
   M0[i] := Basis(VV)[newlst[i][1]];
   end for;
   M1 := M0^-1;
   MAS := [* *];
   act := Action(DirectSum([ProjectiveModule(A,i):i in [1 .. N]]));
   uu,ii,pp := DirectSum([VectorSpace(ff,ndims[k]):k in [1 .. N]]);
   for i := 1 to N do
   pi := npt[i];
   Mi := MatrixAlgebra(ff,ndims[i]);
   Milst  := [Mi!0: t in [1 .. Ngens(A)]];
   for t := 1 to Ngens(A) do
   for s := 1 to #pi do
   if newlst[cndims[i]+s][7] eq t then
   Milst[t][s][s] := ff!1;
   end if;
   end for;
   end for;
   MAS[i] := Milst;
   end for;
   nml := [MM!0:i in [N+1 .. Ngens(A)]];
   actt := [Transpose(act.i): i in [1 .. Ngens(A)]];
/*
vlst;
"VV:",VV;
#vlst;
*/
   for t := N+1 to Ngens(A) do
   for j := 1 to #pt do
       if vlst[j][4] eq 1 then 
/*
t-N,j;
"gent:", gen[t];
"pgent:", Parent(gen[t]);
*/
	   nml[t-N][j] := VV!gen[t]*act.(vlst[j][3]);
       end if;
   end for;
   for j := 2 to maxl do
   for s := 2 to #pt do
   if vlst[s][4] eq j then 
   nml[t-N][s] := nml[t-N][vlst[s][2]]*act.(vlst[s][3]);
   end if;
   end for;
   end for;
   end for;
   Nml := [M0*nml[i]*M1: i in [1 .. #nml]];
   for j := 1 to N do
   for k := 1 to #Nml do
   MAS[j][k+N] := Submatrix(Nml[k],cndims[j]+1,cndims[j]+1,ndims[j],ndims[j]);
   end for;
   end for;
   algl := [<sub<MatrixAlgebra(ff,ndims[j])|MAS[j]>,npt[j]>:j in [1 .. N]];
   nalg := BasicAlgebra(algl);
				else
   print "must create paths";
   gw := GeneratorWords(A);
   n := Maximum([#x:x in gw]); 
   tr := [];
   for i := 1 to NumberOfProjectives(A) do
   pb := [];
   for j := 1 to n do
   for w in gw do
   if #w eq j and w[1] eq i then
   Append(~pb,Index(gw,w));
   end if;
   end for;
   end for;
   tr[i] := pb;
   end for;
   pjm := [];
   V := VectorSpace(A);
   BB := Basis(A);
   for i := 1 to #pt do
   st := tr[i];
   matlst := [];
   vi :=VectorSpace(ff,#st);
   mat := Hom(V, vi)!0;
   for j := 1 to #st do
   mat[st[j]] := vi.j;
   end for;					
   mtt := hom<V ->vi|mat>;
   MM := MatrixAlgebra(ff,Dimension(vi));
   M0 := MM!0;
   for j := 1 to NumberOfGenerators(A) do
   gm := M0;
   for k := 1 to Dimension(vi) do
   gm[k] := mtt(V!(gen[j]*BB[st[k]]));
   end for;
   matlst[j] := gm;
   end for;
   Mi := sub< MM | matlst >;
   mm := RModule(VectorSpace(ff,Nrows(matlst[1])),matlst);
   pjm[i] := PathTreeCyclicModule(mm,
	#IdempotentGenerators(A),
	#NonIdempotentGenerators(A));
   end for;
   nalg := BasicAlgebra(pjm);
					end if;
   A`OppositeAlgebra := nalg;
   nalg`OppositeAlgebra := A;
   return nalg;

end intrinsic;

intrinsic BaseChangeMatrix(A::AlgBas) -> ModMatFldElt
{Given a basic algebra A and its opposite algebra O, creates the change of
basis matrix B from the vector space of A to the vector space of O, so
that if x, y are in A then (xy)B is the same as (yB)(xB) in O.}

   O := OppositeAlgebra(A);
   V := VectorSpace(A);
   BCM := Hom(V,V)!0;
   gens := AlgebraGenerators(O);  			//just Generators
   nn := 1;
   ids := #IdempotentGenerators(O);
   for i := 1 to ids do
   x := gens[i];
   BCM[nn] := V!x;
   pt := PathTree(A,i);
   if #pt gt 1 then
   for j := 1 to #pt-1 do
   BCM[nn+j] := V!(gens[pt[j+1][2]]*O!BCM[nn+pt[j+1][1]-1]);
   end for;
   end if;
   nn := nn+#pt;
   end for;
   return BCM;
   
end intrinsic;

intrinsic Dual(M::ModAlgBas)->ModAlgBas
{Returns the dual of a module M over a basic algebra A as a module
over the algebra O which is the opposite algebra of A.}

   O := OppositeAlgebra(Algebra(M));
   if Dimension(M) eq 0 then 
   C:= ZeroComplex(O,1,0);
   dmod := Term(C,0);
   else
   dmod := AModule(O,[Transpose(Action(M).i):
	i in [1 .. Ngens(Algebra(M))]]);
   end if;
   M`Dual := dmod;
   dmod`Dual := M;

   return dmod;

end intrinsic;

intrinsic Dual(T::ModMatFldElt) -> ModMatFldElt
{Given a homomorphism between two modules over a basic algebra A, returns the
dual homomorphism between the dual modules over the opposite algebra O of A.}

    O := OppositeAlgebra(Algebra(Domain(T)));
    if Dimension(Codomain(T)) gt 0 and Dimension(Domain(T)) gt 0 then
    gamma := hom<Dual(Codomain(T)) -> Dual(Domain(T))|Transpose(T)>;
    gamma1 := MapToMatrix(gamma);
    else
    gamma1 := ZeroMap(Dual(Codomain(T)),Dual(Domain(T)));
    end if;
    return gamma1;
    
end intrinsic;

intrinsic InjectiveModule(A::AlgBas,n::RngIntElt) -> ModAlgBas
{The injective hull of the nth simple A-module}

   O := OppositeAlgebra(A);
   D := ProjectiveModule(O,n);
   DD := AModule(A,[Transpose(Action(D).i): 
	i in [1 .. Ngens(A)]]);
   return DD;

end intrinsic;

intrinsic InjectiveModule(A::AlgBas,S::SeqEnum) -> ModAlgBas
{The injective module that is the injective hull of direct sum of 
S[1] copies of the first simple module for the algebra, S[2] copies
of the second simple module, etc.}

   O := OppositeAlgebra(A);
   D := ProjectiveModule(O,S);
   DD := AModule(A,[Transpose(Action(D).i): 
	i in [1 .. Ngens(A)]]);
   return DD;

end intrinsic;



intrinsic InjectiveHull(M::ModAlgBas) -> ModAlgBas, 
         ModMatFldElt,SeqEnum,ModMatFldElt,ModMatFldElt
{Given a module M over a basic algebra A, returns the injective 
hull I of M as an A-module and the inclusion homomorphism
theta: M --> I.}

   O := OppositeAlgebra(Algebra(M));
   dmod := AModule(O,[Transpose(Action(M).i): 
	i in [1 .. Ngens(Algebra(M))]]);
   dinj, dtheta, ij, proj,seq := ProjectiveCover(dmod);
   inj := AModule(Algebra(M),[Transpose(Action(dinj).i): 
	i in [1 .. Ngens(Algebra(M))]]);
   theta := Hom(M, inj)!Transpose(dtheta);
   pj1 := [Dual(MapToMatrix(ij[j])):j in [1 .. #ij]];
   inj1 := [Dual(MapToMatrix(proj[j])):j in [1 .. #proj]];
   return inj, theta, inj1,pj1, seq;

end intrinsic;





