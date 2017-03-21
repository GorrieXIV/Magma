freeze;

intrinsic GradedCommutativeRing(F::Fld,L::SeqEnum) -> AlgFr, AlgFr
{Returns the graded commutative algebra with coefficient ring
F and variables in degrees of the sequence L.}

P := FreeAlgebra(F,L);
R := [P.i*P.j - (-1)^(L[i]*L[j])*P.j*P.i: i in [1 .. #L], j in [1 .. #L]
	|i le j];
I := ideal<P|R>;

     return P,I;

end intrinsic;

//********************************************************************

CohomologyRelationsEven := function(PR,ACM);
// Computes the cohomology relations but without the Groebner basis
// in the case that the characteristic of the base field is 2.

M := PR`Module;
rrr := Reverse(PR`BettiNumbers);
chmap := ACM`ChainMapRecord;
chmapsz := ACM`ChainSizes;
chdeg := ACM`ChainDegrees;
numb := #rrr-1;
fff := CoefficientRing(Parent(chmap));
recor := Transpose(chmap)[1];
recmat := KMatrixSpace(fff,1,Ncols(recor))!recor;

F := PolynomialRing(fff,chdeg);

Gdata := [];  // This is the data for the generators.

rowind := [0] cat [&+[rrr[chdeg[i]+j]: j in [1 .. #rrr-chdeg[i]]]:
		i in [1 .. #chdeg]];
SS := SimpleModule(BasicAlgebra(fff),1);
Plst := [DirectSum([SS:i in [1 .. rrr[#rrr-j+1]]]):j in [1 .. #rrr]];
Ulst := [* AHom(Plst[i], Plst[i+1])!0: i in [1 .. #rrr -1] *];
CC := Complex(Ulst,0);

for i := 1 to #chdeg do
   matlsti := [* *];
   for j := 1 to #rrr-chdeg[i] do
      temat := KMatrixSpace(fff,rrr[j],rrr[chdeg[i]+j])!0;
      if i eq 1 then 
	 n1 := 0;
      else 
	 n1 := &+[chmapsz[t]: t in [1 .. i-1]];
      end if;
      if j eq 1 then
	 n2 := 0;
      else
	 n2 := &+[rrr[chdeg[i]+t]*rrr[t]:t in [1 .. j-1]];
      end if;
      for k := 1 to rrr[j] do
         InsertBlock(~temat, Submatrix(recmat,1,
	       n1+n2+(k-1)*rrr[chdeg[i]+j]+1, 1,rrr[chdeg[i]+j]),k,1);
      end for;
      Append(~matlsti,Transpose(temat));
      matlstj := [* matlsti[#matlsti-j+1]: j in [1 .. #matlsti] *];
   end for;
   ch := ChainMap(matlstj,CC,CC,-chdeg[i]);
   Append(~Gdata,<chdeg[i], F.i, ch>);
end for;
                   // Now we have the generators set up. Products will be by 
                   // compostions of chain maps. 
MMON := [x:x in Gdata|x[1] eq 1];  // the monomials that are left
I := ideal<F|>;      // the ideal of leading monomials
S := [];             // the list of relations
LM := [];            // the leading monomials of the relations

UU := [];           // the monomials that go to zero

for tt := 2 to numb do  // get relation one degree at a time
//   MMn := [x: x in Gdata| x[1] eq tt];
   MMn := [];
   mmsi := [];               // this is the list of monomials that we have
                          // constructed in degree tt.
   for x in MMON do
      for y in Gdata do
         z := x[2]*y[2];
         if x[1] + y[1] eq tt      // checks that we have right degree
                       and z notin mmsi 
                         // checks that we have not already considered it
                       then 
            Append(~mmsi,z);
            if z notin I then
               w := ModuleMap(x[3],x[1]+y[1])* ModuleMap(y[3],y[1]);
               if w eq Parent(w)!0 then   // we have a new relation
	          Append(~LM, z);
                  Append(~S, z);
               else
		  Append(~MMn, <z,Transpose(w)[1],x,y>);
               end if;
            end if;
         end if;
      end for;
   end for;
           // Now we need to sort MMn so that we get a GB in this degree.
   ss1 := [x[1]:x in MMn]; 
   Sort(~ss1); 
   Reverse(~ss1); 
   MMm := [[x: x in MMn|  x[1] eq ss1[i]][1]: i in [1 .. #ss1]];
            // Now we have sorted by decreasing order of the monomials.
   MAT := KMatrixSpace(fff,#MMm,rrr[tt+1])![x[2]:x in MMm];
   NS := NullSpace(MAT);
   if Dimension(NS) ne 0 then
      B := Basis(NS);
      RM := [];
      for x in B do
         h := &+[x[j]*MMm[j][1]: j in [1 .. #MMm]];
         k := LeadingMonomial(h);
         c := [i: i in [1 .. #MMn]|MMm[i][1] eq k][1];
         Append(~RM,c);
         Append(~S,h);
         Append(~LM,k);
      end for;
      Sort(~RM);
      for i := #RM to 1 by -1 do
         Remove(~MMn,RM[i]);
      end for;
   end if;
   NMM := [<tt,x[1],x[3][3]*x[4][3]>: x in MMm];
   I := ideal<F|LM>;
   MMON := NMM cat MMON cat [x: x in Gdata|x[1] eq tt];
end for;

rff := recformat<PolRing:RngMPol,RelationsIdeal:RngMPol,
		ComputedRelations: SeqEnum, MonomialData:SeqEnum,
		NumberOfSteps:RngIntElt>;

rels := rec<rff|PolRing:= F, RelationsIdeal := ideal<F|S>,
             ComputedRelations := S, MonomialData := MMON,
             NumberOfSteps := numb>;
M`CohomologyRelations := rels;

return rels;

end function;



//********************************************************************

CohomologyRelationsOdd := function(PR,ACM);
// Computes the cohomology relations but without the Groebner basis
// in the case that the characteristic of the base field is odd.

M := PR`Module;
rrr := Reverse(PR`BettiNumbers);
chmap := ACM`ChainMapRecord;
chmapsz := ACM`ChainSizes;
chdeg := ACM`ChainDegrees;
numb := #rrr-1;
fff := CoefficientRing(Parent(chmap));
recor := Transpose(chmap)[1];
recmat := KMatrixSpace(fff,1,Ncols(recor))!recor;

F,J  := GradedCommutativeRing(fff,chdeg);
LJ := LeadingMonomialIdeal(J);

Gdata := [];  // This is the data for the generators.

rowind := [0] cat [&+[rrr[chdeg[i]+j]: j in [1 .. #rrr-chdeg[i]]]:
		i in [1 .. #chdeg]];
SS := SimpleModule(BasicAlgebra(fff),1);
Plst := [DirectSum([SS:i in [1 .. rrr[#rrr-j+1]]]):j in [1 .. #rrr]];
Ulst := [* AHom(Plst[i], Plst[i+1])!0: i in [1 .. #rrr -1] *];
CC := Complex(Ulst,0);

for i := 1 to #chdeg do
   matlsti := [* *];
   for j := 1 to #rrr-chdeg[i] do
      temat := KMatrixSpace(fff,rrr[j],rrr[chdeg[i]+j])!0;
      if i eq 1 then 
	 n1 := 0;
      else 
	 n1 := &+[chmapsz[t]: t in [1 .. i-1]];
      end if;
      if j eq 1 then
	 n2 := 0;
      else
	 n2 := &+[rrr[chdeg[i]+t]*rrr[t]:t in [1 .. j-1]];
      end if;
      for k := 1 to rrr[j] do
         InsertBlock(~temat, Submatrix(recmat,1,
	       n1+n2+(k-1)*rrr[chdeg[i]+j]+1, 1,rrr[chdeg[i]+j]),k,1);
      end for;
      Append(~matlsti,Transpose(temat));
      matlstj := [* matlsti[#matlsti-j+1]: j in [1 .. #matlsti] *];
   end for;
   ch := ChainMap(matlstj,CC,CC,-chdeg[i]);
   Append(~Gdata,<chdeg[i], F.i, ch>);
end for;
                   // Now we have the generators set up. Products will be by 
                   // compostions of chain maps. 
MMON := [x:x in Gdata|x[1] eq 1];  // the monomials that are left
I := LJ;      // the ideal of leading monomials
S := [F!x: x in Basis(J)];             // the list of relations
LM := [F!x: x in Basis(LJ)];         // the leading monomials of the relations
UU := [];           // the monomials that go to zero

for tt := 2 to numb do  // get relation one degree at a time
   MMn := [];
   mmsi := [];               // this is the list of monomials that we have
                          // constructed in degree tt.
   for x in MMON do
      for y in Gdata do
         z := x[2]*y[2];
         if x[1] + y[1] eq tt      // checks that we have right degree
                       and z notin mmsi 
                         // checks that we have not already considered it
                       then 
            Append(~mmsi,z);
            if z notin I then
               w := ModuleMap(x[3],x[1]+y[1])* ModuleMap(y[3],y[1]);
               if w eq Parent(w)!0 then   // we have a new relation
	          Append(~LM, z);
                  Append(~S, z);
               else
		  Append(~MMn, <z,Transpose(w)[1],x,y>);
               end if;
            end if;
         end if;
      end for;
   end for;
           // Now we need to sort MMn so that we get a GB in this degree.
   ss1 := [x[1]:x in MMn]; 
   Sort(~ss1); 
   Reverse(~ss1); 
   MMm := [[x: x in MMn|  x[1] eq ss1[i]][1]: i in [1 .. #ss1]];
            // Now we have sorted by decreasing order of the monomials.
   MAT := KMatrixSpace(fff,#MMm,rrr[tt+1])![x[2]:x in MMm];
   NS := NullSpace(MAT);
   if Dimension(NS) ne 0 then
      B := Basis(NS);
      RM := [];
      for x in B do
         h := &+[x[j]*MMm[j][1]: j in [1 .. #MMm]];
         k := LeadingMonomial(h);
         c := [i: i in [1 .. #MMn]|MMm[i][1] eq k][1];
         Append(~RM,c);
         Append(~S,h);
         Append(~LM,k);
      end for;
      Sort(~RM);
      for i := #RM to 1 by -1 do
         Remove(~MMn,RM[i]);
      end for;
   end if;
   NMM := [<tt,x[1],x[3][3]*x[4][3]>: x in MMm];
   I := ideal<F|LM>;
   MMON := NMM cat MMON cat [x: x in Gdata|x[1] eq tt];
end for;

rff := recformat<PolRing:AlgFr,RelationsIdeal:AlgFr,
		ComputedRelations: SeqEnum, MonomialData:SeqEnum,
		NumberOfSteps:RngIntElt>;

rels := rec<rff|PolRing:= F, RelationsIdeal := ideal<F|S>,
             ComputedRelations := S, MonomialData := MMON,
             NumberOfSteps := numb>;
M`CohomologyRelations := rels;

return rels;

end function;





//******************************************************************

intrinsic MinimalRelations(R::Rec) -> SeqEnum
{Gets the minimal relation for the cohomology ring whose relation 
				     structure is contained in R}

P := R`PolRing;
I := R`RelationsIdeal;

min := [];

II := ideal<P|>;
B := Basis(I);
for x in Basis(I) do
   if x notin II then 
      Append(~min, NormalForm(x, II));
      II := ideal<P|Basis(II) cat [x]>;
   end if;
end for;

       return min;

end intrinsic;

//******************************************************************

intrinsic CohomologyRing(k::ModAlgBas,n::RngIntElt) -> Rec
{Computes the mod-p cohomology ring of the trivial module over 
p-Group G. The module must be given as a module over the basic
algebra of G. }

if assigned k`CohomologyRelations then 
   rels := k`CohomologyRelations;
   if rels`NumberOfSteps gt n then 
      return rels;
   end if;
end if;

if assigned k`AllCompactChainMaps then 
   acc := k`AllCompactChainMaps;
   prj := k`CompactProjectiveResolutionPGroup;
   if #acc`ProductLocations le n+1 then 
      prj := CompactProjectiveResolutionPGroup(k,n);
      acc := AllCompactChainMaps(prj);
   end if;
else
   prj := CompactProjectiveResolutionPGroup(k,n);
   acc := AllCompactChainMaps(prj);
end if;
rels := CohomologyRelations(prj,acc);
k`CohomologyRing := rels;

              return rels;

end intrinsic;

//********************************************************************

intrinsic CohomologyRelations(PR::Rec,ACM::Rec) -> Rec
{Computes the cohomology relations but without the Groebner basis.}

p := Characteristic(CoefficientRing(PR`ResolutionRecord));
if p eq 2 then 
relations := CohomologyRelationsEven(PR,ACM);
else 
relations := CohomologyRelationsOdd(PR,ACM);
end if;

return relations;

end intrinsic;
