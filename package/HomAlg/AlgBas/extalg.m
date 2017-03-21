freeze;

ComputedProjectiveDimension := function(Prj);
// Tne input Prj is the projective resolution of the module M. The
// function returns the projective dimension of M as computed in Prj.

bet := Prj`BettiNumbers;
W := [&+bet[#bet-i+1]: i in [1 .. #bet]];
if W[#W] ne 0 then
   return W[#W]-1;
else
   n := 0;
   for i := 1 to #W do
      if W[i] eq 0 then
         n := i-1;
         break i;
      end if;
   end for;
end if;

       return n-1;

end function;


SetUpAlgebra := function(B, n);
// creates the basic structures for the extalgebra of B.

Proj := [CompactProjectiveResolution(SimpleModule(B,i),n): 
	      i in [1 .. NumberOfProjectives(B)]];
crg := [CohomologyRingGenerators(Proj[i]): i in [1 .. #Proj]];
crmg := [* [* CohomologyRightModuleGenerators(Proj[i],Proj[j],crg[j]): 
              i in [1 .. #Proj] *] : j in [1 .. #Proj] *];
tcg :=  [* [* crmg[i][j]`TopsOfCohomologyGenerators: 
            i in [1 .. #Proj] *] : j in [1 .. #Proj] *];
tcg2 := [];
chdeg := [[crmg[i][j]`ChainDegrees: i in [1 .. #Proj]]: j in [1 .. #Proj]];
pathends := [<i,i>:i in [1 .. #Proj]];
for i := 1 to #Proj do
  for j := 1 to #Proj do
    if #chdeg[i][j] ne 0 then 
       pathends cat:= [<i,j>: x in [1 .. #chdeg[i][j]]];
       for k := 1 to #chdeg[i][j] do
          Append(~tcg2,tcg[i][j][k][1]);
       end for;
    end if;
  end for;
end for;
cd := [ComputedProjectiveDimension(Proj[i]):i in [1 .. #Proj]];
P := FreeAlgebra(BaseRing(B), #pathends);


    return  tcg2, chdeg, pathends, cd, P;

end function;

//****************************************************************

SillyRelations := function(P,pte);

// P is a free algebra, pte is the sequence of pathends.

e := Maximum([x[1]: x in pte]);
rels1 := [P.i^2-P.i: i in [1 .. e]];
rels2 := [P.i*P.j:i in [1..e], j in [1 .. e]|i ne j];
rels3 := [P.pte[k][1]*P.k-P.k:k in [e+1 .. #pte]];
rels4 := [P.k*P.pte[k][2]-P.k:k in [e+1 .. #pte]];
rels5 := [P.i*P.j:i in [e+1 .. #pte], j in [e+1 .. #pte]|
                 pte[i][2] ne pte[j][1]];
rels6 := [&+[P.i: i in [1 .. e]] - P!1];
rels7 := [P.i*P.j: i in [1 .. e], j in [e+1 .. #pte]|i ne pte[j][1]];
rels8 := [P.j*P.i: i in [1 .. e], j in [e+1 .. #pte]|i ne pte[j][2]];

return rels1 cat rels2 cat rels3 cat rels4 cat rels5 cat rels6
       cat rels7 cat rels8;

end function;


FirstMonomials := function(ptends, cdeg, P);
// Sets up the generators of the free algebra arranged by degree and
// the pathends.

n := Maximum([x[1]: x in ptends]);
deglst := &cat &cat cdeg;
mcdeg := Maximum(deglst);
genlst := [<ptends[n+i][1],ptends[n+i][2], deglst[i]>: 
                     i in [1 .. #deglst]];
GEN := [[[[]:i in [1..n]]:j in [1..n]]: k in [1..mcdeg]];
for i := 1 to #deglst do
   x := genlst[i];
   Append(~GEN[x[3]][x[1]][x[2]],P.(n+i));
end for;

         return genlst, GEN;

end function;


MonomialIdealOfShortRelations := function(R);
// gets the monomial ideal of the short relations in preparation for
// getting the next step of the radical. R should be a sequence of 
// elements in a free algebra, called P below.

P := Parent(R[1]);
I := ideal<P|[x:x in R|#Terms(x) lt 2]>;
J := LeadingMonomialIdeal(I);

     return J;

end function;



NextAdmissibleMonomials := function(GEN, MONS, pte, chdeg, P, I, ddd)
// Here GEN is the file locating the generators for the radical, MONS
// is the monimials already computed. GEN and MONS are arranged first 
// by degree, then location (left and right idempotent multipliers). 
// chdeg is the degrees of the chain mape, pte is the pathends, P is
// the free algebra, I is the monomial ideal of the short relations 
//that have been computed so far,  and ddd is the degree that we are 
//currently computing the relations for. 

n := Maximum([x[1]: x in pte]);
mchd := Maximum(&cat &cat chdeg);
top := Minimum(ddd-1, mchd);
MONS1 := MONS;
if ddd gt mchd then
   MONS1 := MONS1 cat [[[[]:i in [1..n]]:j in [1..n]]];
end if;
                     // MONS1 will be the new list of monomials
for d := 1 to top do
   for i := 1 to n do
      for j := 1 to n do
         for k := 1 to n do
	    if #MONS[ddd-d][i][k] ne 0 and #GEN[d][k][j] ne 0 then
               MONS1[ddd][i][j] cat:= [x*y: x in MONS[ddd-d][i][k], 
                      y in GEN[d][k][j]  |  x*y notin I];
            end if;
	 end for;
      end for;
   end for;
end for;

     return MONS1;

end function;

//*********************************************************************

ListIndicesWithCorrection := function(vlst, alist, cor);

      return [[Index(vlst,a[i])-cor: i in [1 .. Length(a)]]:a in alist];

end function;

//*********************************************************************

MatrixOfMonomial := function(indlst, chmlst, genlst);

if #indlst eq 1 then 
   return ModuleMap(chmlst[indlst[1]],genlst[indlst[1]][3]);
end if;
dgt := [genlst[indlst[i]][3]: i in [1 .. #indlst]];
deglst := [&+[dgt[j]:j in [i .. #dgt]]:i in [1 .. #dgt]];
coc := ModuleMap(chmlst[indlst[1]],deglst[1]);
for i := 2 to #indlst do
   coc := coc* ModuleMap(chmlst[indlst[i]],deglst[i]);
end for;

       return coc;

end function;

//*********************************************************************

RelationsCreation := function(PP, mooo, nnn, chmmm, gennn);

moo := Reverse(Sort(mooo));
NE := [];
Inds := ListIndicesWithCorrection([PP.i: i in [1 .. Rank(PP)]], moo,nnn);
mats := [MatrixOfMonomial(Inds[j], chmmm, gennn): j in [1 .. #Inds]];
Mat := Matrix([Transpose(x)[1]:x in mats]);
Null := Basis(NullSpace(Mat));
for v in Null do
	Append(~NE, &+[v[i]*moo[i]: i in [1 .. #moo]]);
end for;
LM := [LeadingMonomial(x):x in NE];
moo2 := [x:x in moo|x notin LM];

         return NE, Reverse(moo2);

end function;


//************************************************************************


NextStepInRelations:= function(chms, cdeg, pathe, genlst, maxd, 
       GN, MN, REL, ddd); 
// cdeg is the chainmap degrees, sorted by location as in SetUP
// chm is the chainmaps as in SetUp.
// pathe is the pathends
// genlst is the location of the polynomial generators with their
//            degrees as in FirstMonomials.
// maxd is the list of projective dimensions as in SetUp.
// GN is the list of generators as in FirstMonomial.
// MN is the  computed monomials as in NextAdmiss... 
// REL is the complete list of relations.
// ddd is the degree we are computing. 
//   We are renewing MN and REL


I := MonomialIdealOfShortRelations(REL);
P := Parent(REL[1]);
MNS := NextAdmissibleMonomials(GN, MN, pathe, cdeg, P, I, ddd);
n := Maximum([x[1]:x in pathe]);
NREL := REL;
chms1 := chms;
cdeg1 := cdeg;
pathe1 := pathe;
genlst1 := genlst;
GN1 := GN;
for i := 1 to n do
   for j := 1 to n do
      mons := MNS[ddd][i][j];
      if ddd gt maxd[i] then 
         Nrel := mons;
         MNS[ddd][i][j] := [];
      else
         Nrel := [];
         if #mons ne 0 then 
             Nrel, mons2 := RelationsCreation(P, mons, n, chms1, genlst1);
             MNS[ddd][i][j] := mons2;
             if ddd le Maximum(&cat &cat cdeg1) then
               flag := true;
               while flag do
                if #GN1[ddd][i][j] ne 0 then 
                   wll := [x:x in Nrel|1 in {Length(y): y in Monomials(x)}];
                   if #wll ne 0 then 
                      w1 := wll[1]; 
                      w2 := [x:x in Monomials(w1)|Length(x) eq 1][1];
                      nmm := Index([P.i:i in [1 .. Rank(P)]], w2);
                      Q := FreeAlgebra(BaseRing(P),Rank(P)-1);
                      if nmm eq Rank(P) then 
                         phi := hom<P -> Q|[Q.i: i in [1 .. nmm-1]] cat [Q!0]>;
                      else 
                         phi := hom<P -> Q|[Q.i: i in [1 .. nmm-1]] 
                                 cat [Q!0] cat [Q.i: i in [nmm .. Rank(P)-1]]>;
                      end if;
                      NREL := [phi(x):x in NREL| phi(x) ne 0];
                      P := Q;
                      GN2:= [[[[]:r in [1 .. n]]:x in [1 .. n]]:
                                       t in [1 .. #GN1]];
                      MNS1 := [[[[]:r in [1 .. n]]:x in [1 .. n]]:
                                       t in [1 .. #MNS]];
                      Remove(~chms1,nmm-n);
                      Remove(~pathe, nmm);
                      aa := Index(GN1[ddd][i][j], w2);
                      Remove(~GN1[ddd][i][j], aa);
                      Remove(~cdeg1[i][j], aa);
                      for r := 1 to #GN1 do
			for s := 1 to n do
			  for t := 1 to n do
			    if #GN1[r][s][t] ne 0 then
                              GN2[r][s][t] := [phi(x):x in GN1[r][s][t]];
                            end if;
                          end for;
                        end for;
                      end for;
                      for r := 1 to #MNS do 
			for s := 1 to n do
			  for t := 1 to n do
                            if #MNS[r][s][t] ne 0 then 
                              MNS1[r][s][t] := [phi(x):x in MNS[r][s][t]];
                            end if;
                          end for;
                        end for;
                      end for;
                      GN1 := GN2;
                      MNS := MNS1;
                      Remove(~genlst1, nmm-n);
                      mons := [phi(x):x in mons|phi(x) ne 0];
                      Nrel, mons2 := RelationsCreation(P, mons, n, 
                                 chms1, genlst1);
                      MNS[ddd][i][j] := mons2;;
		   else
		      flag := false;
                   end if;               
		else
		   flag := false;
                end if;
               end while;
             end if;
         end if;
      end if;
      NREL := NREL cat Nrel;
   end for;
end for;

return NREL, MNS, chms1, cdeg1, pathe1, genlst1, GN1;

end function;

//************************************************************************

intrinsic ExtAlgebra(A::AlgBas , n::RngIntElt) -> Rec
{Returns the ext algebra B of the basic algebra A where the projecive
resolutions and cohomology have been computed to degree n. The ext
algebra is the algebra Ext_B^*(S,S) where S is the directs sum of 
the simple A modules. }


if assigned A`ExtAlgebra then
   if n eq A`ExtAlgebra`NumberOfComputedSteps then
      return A`ExtAlgebra;
   end if;
end if;
s1, s2, s3, s4, s5 := SetUpAlgebra(A,n);
srels := SillyRelations(s5,s3);
fmon1, fmon2 := FirstMonomials(s3,s2,s5);
nr1 := srels;
nm1 := fmon2;
for j := 2 to n do
   nr2, nm2, s1, s2, s3, fmon1, fmon2 := 
             NextStepInRelations(s1,s2,s3,fmon1,s4,fmon2,nm1,nr1,j);
   nm1 := nm2;
   nr1 := nr2;
end for;
rrr := recformat<FreeAlgebra:AlgFr,Relations:SeqEnum, 
            ChainMapsOfGenerators:SeqEnum, DegreesOfGenerators:SeqEnum, 
	    MonomialBasisByLocation:SeqEnum, MonomialBasis:SeqEnum,
            NumberOfComputedSteps:RngIntElt,ComputedGlobalDimension:RngIntElt>;
bbb := rec<rrr|FreeAlgebra := Parent(nr2[1]), Relations := nr2,
        ChainMapsOfGenerators := s1, DegreesOfGenerators := fmon1, 
        MonomialBasisByLocation := nm2, MonomialBasis := 
	   [Parent(nr2[1]).i: i in [1 .. NumberOfProjectives(A)]] cat 
             &cat &cat &cat nm2,
        NumberOfComputedSteps := n, ComputedGlobalDimension := Maximum(s4)>;
A`ExtAlgebra := bbb;

     return bbb;

end intrinsic;

//************************************************************************

intrinsic ExtAlgebra(A::AlgBasGrpP,n::RngIntElt) -> Rec
{Returns the ext algebra B of the basic algebra A where the projecive
resolutions and cohomology have been computed to degree n. The ext
algebra is the algebra Ext_B^*(S,S) where S is the directs sum of
the simple A modules. }

   return ExtAlgebra(BasicAlgebraGrpPToBasicAlgebra(A),n);

end intrinsic;

//************************************************************************

intrinsic CompactProjectiveResolutionsOfSimpleModules(A::AlgBas,
     n::RngIntElt)   -> SeqEnum
{Returns a sequence of the compact projective resolutions of the simple
A-modules computed to degree n.}

pj := [CompactProjectiveResolution(SimpleModule(A,i),n):
                                    i in [1 .. NumberOfProjectives(A)]];

     return pj;

end intrinsic;

intrinsic CompactProjectiveResolutionsOfAllSimpleModules(A::AlgBas,
     n::RngIntElt)   -> SeqEnum
{Returns a sequence of the compact projective resolutions of the simple
A-modules computed to degree n.}

pj := [CompactProjectiveResolution(SimpleModule(A,i),n):
                                    i in [1 .. NumberOfProjectives(A)]];

     return pj;

end intrinsic;

//********************************************************************

intrinsic SumOfBettiNumbersOfSimpleModules(A::AlgBas , 
    n::RngIntElt) -> RngIntElt
{Returns the sum of the Betti Numbers of all simple module of the 
algebra A. The projective resolutions of the simple modules are computed
to degree n. This is the dimension of the ext algebra of A computed to
degree n.}

aa := [CompactProjectiveResolution(SimpleModule(A,i),n)`BettiNumbers:
				    i in [1 .. NumberOfProjectives(A)]];
return &+ &cat &cat aa;

end intrinsic;

//**********************************************************************

intrinsic BasicAlgebraOfExtAlgebra(ext::Rec) -> AlgBas
{The function forms the basic algebra from a computed extalgebra. The 
 input for  is the output of the ExtAlgebra function.  If the exalgebra 
is not verified to be finite dimensional by the computation, then an 
error is returned.}

require ext`NumberOfComputedSteps gt ext`ComputedGlobalDimension: 
       "ExtAlgebra has not been computed to have finite dimension";
a := ext`DegreesOfGenerators;
b := [<a[i][1],a[i][2]> : i in [1 .. #a]];
F := ext`FreeAlgebra;
C := BasicAlgebra(F, ext`Relations, Rank(F)-#b,b);

  return C;

end intrinsic;

//**********************************************************************

intrinsic BasicAlgebraOfExtAlgebra(A::AlgBas) -> AlgBas
{The function forms the basic algebra from a computed extalgebra of the
basic algebra A. If no extalgebra  for.A has been computed or if the 
exalgebra is not verified to be finite dimensional then an error is
returned.}

require assigned A`ExtAlgebra: "No ExtAlgebra for the input has been
computed.";
B := A`ExtAlgebra;
require B`NumberOfComputedSteps gt B`ComputedGlobalDimension: 
       "ExtAlgebra has not been computed to have finite dimension";
C := BasicAlgebraOfExtAlgebra(B);

     return C;

end intrinsic;

//**********************************************************************

intrinsic BasicAlgebraOfExtAlgebra(A::AlgBas, n::RngIntElt) -> AlgBas
{The function forms the basic algebra for the extalgebra of A computed
to n steps. If no extalgebra  for.A to n steps has been computed then 
it computes one. If the exalgebra is not verified to be finite 
dimensional by the computation, then an error is returned.}

B := ExtAlgebra(A,n);
require B`NumberOfComputedSteps gt B`ComputedGlobalDimension: 
       "ExtAlgebra has not been computed to have finite dimension";
C := BasicAlgebraOfExtAlgebra(B);

     return C;

end intrinsic;
