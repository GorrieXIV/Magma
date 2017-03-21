freeze;

MatrixToVector := function(M);

ZM := KMatrixSpace(BaseRing(M),1, Nrows(M)*Ncols(M))!0;
for i := 1 to Nrows(M) do
InsertBlock(~ZM,M[i], 1, (i-1)*Ncols(M)+1);
end for;

return ZM[1];

end function;

//*****************************************************************

Generators_Relations := function(L);

// L is a list of matrices or elements which can be added and 
// multiplied. The elements in L must be nilpotent. Indeed, the 
// monoid they generate must be nilpotent. 

ff := BaseRing(L[1]);
ll := Nrows(L[1])^2;
F := FreeAlgebra(ff, #L);
phi := hom<F -> Parent(L[1])| L>;
I := ideal<F|>;      // the ideal of leading monomials
S := [];             // the list of relations
LM := [];            // the leading monomials of the relations
GG := [F.i: i in [1 .. Rank(F)]];
MM := [];           // the monomials and matrices that don't go to zero
UU := [];           // the monomials that go to zero
n := 0;
flag := true;
KM := KMatrixSpace(BaseRing(L[1]), Nrows(L[1]), Nrows(L[1]));
NMM := [];          // the list of monomials that will be modified and 
                    // altered for each step
while flag do 
   n := n+1;
   if n eq 1 then 
      NMM := [<GG[i],L[i],MatrixToVector(L[i])>: i in [1 .. #L]]; 
                                        // the degree 1 list of mons and mats
      MM1 := NMM;
      MATminus := KMatrixSpace(ff,#MM1,ll)!0;
      for i := 1 to #MM1 do
	 MATminus[i] := MM1[i][3];
      end for;
      MM := MM1;
      NMM := MM1;
      NGG := GG;
   else 
      flag := false;
      MMn := [];  // degree n mons and mats to be weeded out
      for x in NMM do
         for y in MM1 do
            z := x[1]*y[1];
            if z notin I then 
               w := x[2]*y[2];
               if w ne 0 then 
                  Append(~MMn, <z,w, MatrixToVector(w)>);
               else 
                  Append(~LM,z);
                  Append(~S,z);
               end if;
            end if;
         end for;
      end for;
      if #MMn ne 0 then
         NGG := [x[1]: x in MMn] cat NGG;
         MATn := KMatrixSpace(ff,#MMn,ll)!0;
         for i := 1 to #MMn do
	    MATn[i] := MMn[i][3];
         end for;
         MAT := VerticalJoin(MATn, MATminus);
         NS := NullSpace(MAT);
         if Dimension(NS) ne 0 then
            B := Basis(NS);
            RM := [];
            for x in B do
               h := &+[x[j]*NGG[j]: j in [1 .. #NGG]];
               k := LeadingMonomial(h);
               c := Index(NGG,k);
               Append(~RM,c);
               Append(~S,h);
               Append(~LM,k);
            end for;
            Sort(~RM);
            for i := #RM to 1 by -1 do
               Remove(~NGG,RM[i]);
               Remove(~MMn,RM[i]);
            end for;
         end if;
         NMM := MMn;
         MATn := KMatrixSpace(ff,#MMn,ll)!0;
         for i := 1 to #MMn do
            MATn[i] := MMn[i][3];
         end for;
         MATminus := VerticalJoin(MATn,MATminus);
         I := ideal<F|LM>;
         MM := NMM cat MM;
      end if;
      if #MMn ne 0 then 
         flag := true;
      end if;
   end if;
end while;
J := ideal<F|S>;

         return F, J, phi, MM;

end function;

//*******************************************************************

simplify1 := function(rel)
// makes an easy simplification

P := Parent(rel);
mons := Monomials(rel);
nrel := rel;
ind := 0;
flag := false;
leads := [0];
if #mons gt 1 then 
   min, ind := Minimum([Degree(x): x in mons]);
   if #[x : x in mons| Degree(x) eq min] eq 1 then 
      leads := [x[1]: x in mons];
      tails := [x[Length(x)]: x in mons];
      if #Seqset(leads) eq 1 and #Seqset(tails) eq 1 then 
         cof := Coefficients(rel);
         newmons := [];
         for i := 1 to #mons do
            x := mons[i];
            if Length(x) eq 2 then 
               newmons[i] := P!1;
            else
               newmons[i] := &*[x[j]: j in [2 .. Length(x)-1]];
            end if;
         end for;
         p := Characteristic(BaseRing(P));
         nrel := leads[1]*
                (&+[cof[ind]^(-1)*cof[j]*newmons[j]: j in [1 .. #mons]])^(p-1);
         flag := true;
      end if;
   end if;
end if;

	return nrel, Index([P.i: i in [1 .. Rank(P)]],leads[1]), flag;

end function;

//*******************************************************************

simplify2 := function(relations);

P := Parent(relations[1]);
imagelst := [P.i : i in [1 .. Rank(P)]];
theta := hom<P -> P| imagelst>;
cflg := false;
for rr in relations do
   nrr, ind, flg := simplify1(rr);
   if flg then 
      newimlst := imagelst;
      newimlst[ind] := nrr;
      phi := hom<P -> P | newimlst>;
      theta := theta*phi;
      cflg := true;
   end if;
end for;

if cflg then
   nrels := [x@theta : x in relations];
else 
   nrels := relations;
end if;

       return nrels;

end function;
 
//******************************************************************

minrels := function(lst);

P := Parent(lst[1]);
nlst := lst;
flag := false;
d := Minimum([Degree(x): x in lst]);
for i := #nlst to 1 by -1 do
   if Degree(nlst[i]) gt d then    
      nnls := Remove(nlst, i);
      I := ideal<P|nnls>;
      if nlst[i] in I then 
         nlst := nnls;
      end if;
   end if;
end for;
 
	return nlst;

end function;
 
//*******************************************************************

quiver := function(B)
// presents the quiver of a basic algebra B. Each arrow is given as a pair
// consisting of the index of the source and the target of the arrow. 

n := NumberOfProjectives(B);
qu1 := GeneratorAssociatedIdempotents(B);
if #qu1 eq n then 
	return [];
end if;

return [qu1[i]: i in [n+1 .. #qu1]];

end function;

//*******************************************************************

quiver_relations := function(B)
// gives the relations on the quiver. excluded are obvious rlations 
// involving the product of two elements such that the target of the 
// first arrow is not equal to the source of the second.

M := RightRegularModule(B);
Act := Action(M);
n := NumberOfProjectives(B);
m := Ngens(B);
if n eq m then 
	return [];
end if;
LL := [Act.i: i in [n+1 .. m]];
P, J, uuu, vvv := Generators_Relations(LL);
I := ideal<P | simplify2(Basis(J))>;
quiv := quiver(B);
unwanted := [P.i*P.j: i in [1 .. m-n], j in [1 .. m-n]|
			quiv[i][2] ne quiv[j][1]];
Groebner(I);
W := minrels(Basis(I));
if BaseRing(P) ne PrimeField(BaseRing(P)) then 
   baseflag := true;
   k := PrimeField(BaseRing(P));
else baseflag := false;
end if;
J := ideal<P|unwanted>;
B := [x: x in W| not x in J];
for i := 1 to #B do
   if #Monomials(B[i]) eq 1 then
      B[i] := Monomials(B[i])[1];
   else
      B[i] := Coefficients(B[i])[#Monomials(B[i])]^(-1)* &+(Terms(B[i]));
   end if;
end for;

	return B, unwanted;

end function;

///////////////////////////////////////////////////////////////////////

intrinsic Quiver(A::AlgBas) -> SeqEnum 
{Returns the quiver of the basic algebra A}

return quiver(A);

end intrinsic;

///////////////////////////////////////////////////////////////////////

intrinsic QuiverAndRelations(A::AlgBas) -> SeqEnum, SeqEnum, SeqEnum 
{For a basic algebra A, returns the quiver of A, the sequence relations
of on the nonidempotent generators and a condensed sequence of relations
that does not contain the obvious relations of degree two where the head 
of the first arrow does not match the tail of the second} 

X, Y := quiver_relations(A);

	return quiver(A), X cat Y, X;

end intrinsic;
