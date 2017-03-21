freeze;

declare attributes AlgBasGrpP: Group, PCGroup, PCMap;

intrinsic BasicAlgebra(G::GrpPC, k::FldFin) -> AlgBasGrpP
{Given a finite p-group G and a field k of characteristic p and 
returns the group algebra kG in the form of a basic algebra.}

   require #G ne 1: "Group cannot be the trivial group";
   require #FactoredOrder(G) eq 1: "Group is not a p-group";

   p := Characteristic(k);
   fac := FactoredOrder(G);
   if #fac gt 1 then
	print "Error! -- Group is not a p-group";
	return 0;
   end if;
   if fac[1][1] ne p then 
	print "ERROR!  -- Field is of wrong characteristic";
	return 0;
   end if;
   exp := fac[1][2];
   fld := GF(p);

   pcg, phi := StandardPresentation(G);
   gens1 := [pcg.i @@ phi: i in [1 .. #PCGenerators(pcg)]];
   //gens := [gens1[i] @@ phi1: i in [1 .. #gens1]];
   gens := gens1;

   MM := PermutationModule(G, sub<G|Id(G)>, fld);
   m1 := MM.1;
   BB := Hom(VectorSpace(fld,1),VectorSpace(fld,#G))!m1;
   ident := Representation(MM)(Id(G));
   for i := 1 to exp do
	x := Representation(MM)(gens[i]);
	CC := BB;
	nn := Dimension(Domain(CC));
	BB := Hom(VectorSpace(fld,p*nn),VectorSpace(fld,#G))!0;
	InsertBlock(~BB,CC,1,1);
	for k := 1 to p-1 do
	InsertBlock(~BB,Submatrix(BB,nn*(k-1)+1,1,nn,#G)*(x-ident),nn*k+1,1);
	end for;
   end for;
   uuu := MatrixAlgebra(fld, #G)!BB;
   FG := GModule(G, [uuu*Representation(MM)(G.i)*uuu^-1 : \
      i in [1 .. NPCgens(G)]]);
   fg := ExtendField(FG,k);
   matrng := MatrixAlgebra(k,#G);
   minlst := [matrng!(Representation(fg)(G.i)-Representation(fg)(Id(G))):
	i in [1 .. Ngens(G)]];
   pclst := [matrng!1] cat 
	[matrng!(Representation(fg)(gens[i])-Representation(fg)(Id(G))):
	i in [1 .. #gens]];
   mrr := sub<matrng|pclst>;
   trr := [<1,1>];
   for i := 2 to #G do
	xx := Maximum([j:j in [0] cat [1 .. exp]|p^j lt i]);
	trr[i] := <i-p^xx,xx+2>;
   end for;
   AA := BasicAlgebraPGroup([<mrr,trr>]);
   AA`Group := G;
   AA`PCGroup := pcg;
   AA`PCMap := phi;
   return AA;

end intrinsic;

intrinsic BasicAlgebra(G::GrpPerm, k::FldFin) -> AlgBasGrpP
{Given a finite p-group G and a field k of characteristic p and 
returns the group algebra kG in the form of a basic algebra.}

   require #FactoredOrder(G) eq 1: "Group is not a p-group";
   G1, phi1 := PCGroup(G);
   B := BasicAlgebra(G1, k);
   B`Group := G;
   B`PCMap := phi1 * B`PCMap;
   return B;

end intrinsic;

intrinsic BasicAlgebra(G::GrpAb, k::FldFin) -> AlgBasGrpP
{Given a finite p-group G and a field k of characteristic p and 
returns the group algebra kG in the form of a basic algebra.}

   require #FactoredOrder(G) eq 1: "Group is not a p-group";
   G1, phi1 := PCGroup(G);
   B := BasicAlgebra(G1, k);
   B`Group := G;
   B`PCMap := phi1 * B`PCMap;
   return B;

end intrinsic;


intrinsic Group(A::AlgBasGrpP) -> Grp
{The group which defines A}
    return A`Group;
end intrinsic;

intrinsic PCGroup(A::AlgBasGrpP) -> Grp
{The internal PC group of A}
    return A`PCGroup;
end intrinsic;

intrinsic PCMap(A::AlgBasGrpP) -> Grp
{The map from Group(A) to PCGroup(A)}
    return A`PCMap;
end intrinsic;


//intrinsic BasicAlgebra(F::AlgFPOld,s::RngIntElt,L::SeqEnum,
intrinsic BasicAlgebra(F::AlgFPOld,s::RngIntElt,L::SeqEnum,
	R::SeqEnum)-> AlgBas
{Creates a basic algebra from a minimal set of relations. The input is 
a free algebra, the number of idempotents, a list of the right and left
idempotents corresponding to the nonidempotent generators of the algebra
and a list of relations. The function creates the extra relations that
are natural to the idempotents and the multiplications of the idempotents
on the nonidempotent generators. Thus the user needs only supply the 
relations among the nonidempotent generators.}
// F := FA;N :== s; LR:= L; 
   ff := BaseRing(F);
   il := [&+[F.i: i in [1 .. s]]-F!1] cat 
	[F.i*F.j:i in [1 .. s],j in [1 .. s]|i ne j] cat
	[F.i^2 -F.i:i in [1 .. s]];
   jl := &cat[[F.L[j][1]*F.(j+s)-F.(j+s),
	F.(j+s)*F.L[j][2]-F.(j+s)]: j in [1 .. #L]]
	cat [F.t*F.(j+s):j in [1 .. #L], t in [1 .. s]|
		t ne L[j][1]]
	cat [F.(j+s)*F.t:j in [1 .. #L], t in [1 .. s]|
		t ne L[j][2]];
   rels := il cat jl cat R;
   MM := quo<F|rels>;
   I := ideal<MM|MM!0>;
   qqq := QuotientModule(MM,I:MaxWt := 200000);
   MAT := MatrixAlgebra<ff,Nrows(qqq[1])|qqq>;
   RM := RModule(VectorSpace(ff,Nrows(qqq[1])),qqq);
   act := Action(RM);
   mmlst := [sub<RM|RM.1*act.i>: i in [1 .. s]];
   BA  := BasicAlgebra([PathTreeCyclicModule(x,s,#L):x in mmlst]);
   return BA;

end intrinsic;

intrinsic TensorProduct(A::AlgBas,B::AlgBas) -> AlgBas
{Creates the tensor product of two basic algebras}

ff :=  BaseRing(A);
if ff ne BaseRing(B) then
print "algebras have incompatable coefficient fields";
return 0;
end if;
mdlst := [];
n1 := NumberOfProjectives(A);
g1 := Ngens(A);
n2 := NumberOfProjectives(B);
g2 := Ngens(B);
prjlst := [];
for i := 1 to n1 do
Pi := ProjectiveModule(A,i);
ggg := Generators(A);
for j := 1 to n2 do
Qj := ProjectiveModule(B,j);
matlst1 := [TensorProduct(Action(Pi).l,Action(Qj).m):m in [1..n2],l in [1..n1]];
matlst2 := [TensorProduct(Action(Pi).l,Action(Qj).m):l in [n1+1 .. g1], 
	m in [1 .. n2]];
matlst3 := [TensorProduct(Action(Pi).l,Action(Qj).m):m in [n2+1 .. g2],
	l in [1 .. n1]];
matlst := matlst1 cat matlst2 cat matlst3;
mal:= MatrixAlgebra(ff,Dimension(Pi)*Dimension(Qj));
mta := sub<mal|matlst>;
pt1 := PathTree(A,i);
pt2 := PathTree(B,j);
tree := [<1,(i-1)*n2+j>] cat [<pt2[t][1],g1*n2+(i-1)*(g2-n2)+pt2[t][2]-n2>:
	t in [2 .. #pt2]];
if #pt1 gt 1 then 
for w := 2 to #pt1 do
a := <(pt1[w][1]-1)*#pt2+1,n1*n2+(j-1)*(g1-n1)+pt1[w][2]-n1>;
u := &+[k:k in [1 .. n1]|ggg[pt1[w][2]]*ggg[k] eq ggg[pt1[w][2]]];
//print u;
tree := tree cat [a] cat 
	[<(w-1)*#pt2+pt2[t][1], g1*n2+(u-1)*(g2-n2)+pt2[t][2]-n2>:
	t in [2..#pt2]];
end for;
end if;
Append(~prjlst,<mta,tree>);
end for;
end for;
AA := BasicAlgebra(prjlst);
return AA;
end intrinsic;


intrinsic ZeroModule(A::AlgBas) -> ModAlgBas
{The zero A-module}

   if assigned A`ZeroModule then
       return A`ZeroModule;
   end if;
   C := ZeroComplex(A,1,0);
   zz := Term(C,0);
   A`ZeroModule := zz;
   return zz;

end intrinsic;

intrinsic ZeroMap(M::ModAlgBas,N::ModAlgBas) -> ModMatFldElt
{The zero map from M to N}

   A := Algebra(M);
   zz := ZeroModule(A);
   a := Hom(M,zz)!0;
   b := Hom(zz,N)!0;
   c := a*b;
   return c;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////

declare attributes Grp: BasicAlgebra;

intrinsic GModule(A::AlgBasGrpP) -> ModGrp, ModGrp
{The standard module of A as a module over Group(A) and as a module
over PCgroup(A)}
  
    GG := Group(A);
    G := PCGroup(A);
    f := FactoredOrder(G)[1];
    P := ProjectiveModule(A,1);
    M := GModule(G, [Action(P).(i+1) + Action(P).1: i in [1 .. f[2]]]);
    if Type(GG) eq GrpPC then
       pcg, phi := StandardPresentation(GG);
    else
       pg, mu := PCGroup(GG);
       pcg, nu := StandardPresentation(pg);
       phi := mu*nu;
    end if;
      
    NN := GModule(pcg, [Action(P).(i+1) + Action(P).1: i in [1 .. f[2]]]);
    if Type(GG) eq  GrpPC then
       N := GModule(GG, [Representation(NN)(phi(GG.i)): i in [1 .. f[2]]]);
    else
       N := GModule(GG,[Representation(NN)(phi(GG.i)): i in [1 .. Ngens(GG)]]);
    end if;
  
return N, M;
  
end intrinsic;


intrinsic AModule(M::ModGrp) -> ModAlg
{Converts a GModule over a p-group to a module over the basic
   algbra of that group.}
  
    G := Group(M);
    if assigned  G`BasicAlgebra then
       A := G`BasicAlgebra;
    else
       A := BasicAlgebra(G);
    end if;
    phi := PCMap(A);
    H := PCGroup(A);
    gens := [H.i @@ phi:i in [1 .. NPCgens(H)]];
    id := Representation(M)(Id(G));
    Mats := [id] cat [Representation(M)(x) - id: x in gens];
    U := AModule(A,Mats);
  
       return U;
  
end intrinsic;

intrinsic GModule(M::ModAlgBas) -> ModGrp
{Converts a module for the basic algebra of a p-group into
a module over the p-group.}
  
    A := Algebra(M);
    G := Group(A);
    phi := PCMap(A);
    H := PCGroup(A);
    N := GModule(H,[Action(M).(i+1)+Action(M).1: i in [1 .. NPCgens(H)]]);
    if Type(G) eq GrpPC then
       W := GModule(G,[Representation(N)(phi(G.i)): i in [ 1 .. NPCgens(G)]]);
    else
       W := GModule(G,[Representation(N)(phi(G.i)): i in [ 1 .. Ngens(G)]]);
    end if;
  
    return W;
  
end intrinsic;

  
////////////////////////////////////////////////////////////////////////

intrinsic BasicAlgebra(G::Grp) -> AlgBasGrpP
{The basic algebra of the p-group G over the prime field of characteristic p}
  
    if assigned G`BasicAlgebra then
	return G`BasicAlgebra;
    end if;

    require #G ne 1: "Group cannot be the trivial group";

    p := FactoredOrder(G)[1][1];
    A := BasicAlgebra(G, GF(p));
    G`BasicAlgebra := A;
    return A;
  
end intrinsic;

//////////////////////////////////////////////////////////////////////////

intrinsic BasicAlgebraGrpPToBasicAlgebra(A::AlgBasGrpP) -> AlgBas
{Converts the a basic algebra of a p-group to the type AlgBas.}

     return BasicAlgebra([<Action(ProjectiveModule(A,1)), PathTree(A,1)>]);

end intrinsic;
