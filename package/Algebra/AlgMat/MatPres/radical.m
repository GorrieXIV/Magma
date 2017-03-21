freeze;

ChangeOfBasisMatrixA := function(M, G, T, n);
// Puts the algebra in normal form. We are given a list of primitive 
// idempotents G and a list of permutation matrices T. n is the list
// of dimensions over the central field of the algebra -- the list of 
// orders of the permutation matrices.

BAS := [];
f := CoefficientRing(M);
dim := Nrows(M.1);
V := VectorSpace(f, dim);
RS := [RowSpace(x): x in G];
for i := 1 to #G do
   B := [V!x: x in Basis(RS[i])];
   BAS := BAS cat B;
   if n[i] gt 1 then 
      ni := Rank(T[i]) div Dimension(RS[i]);
      for k := 1 to ni-1 do
         B := [v*T[i]: v in B];
         BAS := BAS cat B;
      end for;
   end if;
end for;

mat := KMatrixSpace(f, dim, dim)!BAS;

return mat, mat^-1;

end function;

ChangeOfBasisMatrixB := function(M, g, t);
// Puts the algebra in normal form. This an algebra which is simple
// and has a primitive idempotent g and permutation matrix t.

BAS := [];
MM := Codomain(M);
f := CoefficientRing(MM);
dim := Nrows(MM.1);
V := VectorSpace(f, dim);
RS := RowSpace(g);
B := [V!x: x in Basis(RS)];
BAS := BAS cat B;
n := dim div Rank(g);
if n gt 1 then 
   for k := 1 to n-1 do
      B := [v*t: v in B];
      BAS := BAS cat B;
   end for;
end if;

mat := KMatrixSpace(f, dim, dim)!BAS;

return mat, mat^-1;

end function;

//******************************************************************

NeededIndices := function(G,n);
// G is the list of primitive idempotents in A, and n is the list
// of dimensions of the simple modules. 

gind := [Rank(G[i]): i in [1 .. #G]];
rowind := [0] cat [&+[gind[i]*n[i]: i in [1 ..j]]:j in [1 .. #n]];

   return gind, rowind;

end function; 


//*******************************************************************

NormalFormA := function(A,G,T,B, mat, mati);
// Puts the algebra in normal form using the matrix output of change
// of basis matrices

    AA := [mat*A.i*mati: i in [1 .. #Generators(A)]];

    if false and assigned A`DiagonalBlockStructure then
	B := A`DiagonalBlockStructure;
//"B:", B; "Here mat:", mat;
	t, bmat := HasBlockDiagMat(mat, B);
	ti, bmati := HasBlockDiagMat(mati, B);
	assert t;
	assert ti;
	mat := bmat;
	bmati := mati;

	GG := [mat*x*mati: x in G];
	TT := [mat*x*mati: x in T];
	BB := [mat*x*mati: x in B];
    else
	GG := [mat*Matrix(x)*mati: x in G];
	TT := [mat*Matrix(x)*mati: x in T];
	BB := [mat*Matrix(x)*mati: x in B];

	B := [];

	/*
	B := DiagonalBlockStructure([Matrix(x): x in GG cat TT cat BB]);
	"*** combined seq DiagonalBlockStructure:", B;
	if assigned A`DiagonalBlockStructure then
	    "A`DiagonalBlockStructure:", A`DiagonalBlockStructure;
	end if;
	*/

	if false and #B gt 1 then
	    GG := [BlockDiagMat(X, B): X in GG];
	    TT := [BlockDiagMat(X, B): X in TT];
	    BB := [BlockDiagMat(X, B): X in BB];
	end if;
    end if;

    return AA, GG,TT,BB;

end function;

//******************************************************************

BasisForRadical_i_ne_j := function(AL, gind, rowind, bi, bj, n, i, j);
// We are assuming that the generators of A (AL) are already in 
// standard form. Here gind and rowind are the needed indices,
// n is the list of dimensions of the simple modules and i,j are 
// indexes of simple modules.

GL := [];
ff := CoefficientRing(AL[1]);
nn := Nrows(AL[1]);
for t := 1 to #AL do
   for u := 1 to n[i] do
      for v := 1 to n[j] do
         Append(~GL, Submatrix(AL[t], rowind[i] + (u-1)*gind[i] +1 , 
		rowind[j] + (v-1)*gind[j] +1, gind[i], gind[j]));
      end for;
   end for;
end for;
if #bi ne 0 then 
   GL := GL cat [y*x: x in GL, y in bi];
end if;
if #bj ne 0 then 
   GL := GL cat [x*y: x in GL, y in bj];
end if;
gens1 := Basis(sub<KMatrixSpace(ff,gind[i],gind[j])| GL>);
zer := KMatrixSpace(ff,nn,nn)!0;
gens2 := [InsertBlock(zer,x,rowind[i]+1, rowind[j]+1): x in gens1];

return gens2,   gens1;

end function;

//******************************************************************

PowersOfBetaBar := function(B);

ff := CoefficientRing(B);
r := Rank(B);
hh := KMatrixSpace(ff,r,r)!Submatrix(B,1,1,r,r);
// n := Characteristic(ff)^r;
n := (#ff)^r;
// PL := [hh^i: i in [1 .. n-1]] cat [KMatrixSpace(ff,r,r)!0];
PL := [hh];
for i := 2 to n - 1 do
    PL[i] := PL[i - 1]*hh;
end for;
Append(~PL, KMatrixSpace(ff,r,r)!0);

return PL, r;

end function;

//**********************************************************************

PowersOfBeta := function(B,i,rowind,r);

b := B[i];
s := Rank(b);
ff := CoefficientRing(b);
hh := KMatrixSpace(ff,s,s)!Submatrix(b,rowind[i]+ 1,rowind[i]+ 1,s,s);
// n := Characteristic(ff)^r;
n := (#ff)^r;
//PL := [hh^i: i in [1 .. n-1]] cat [KMatrixSpace(ff,s,s)!0];
PL := [hh];
for i := 2 to n - 1 do
    PL[i] := PL[i - 1]*hh;
end for;
Append(~PL, KMatrixSpace(ff,s,s)!0);

return PL;

end function;

//******************************************************************

BasisForRadical_i_i := function(AL, ALi, glst, rowind, PowB, PowBar, BB, n, i);
// We are assuming that the generators of A (AL) are already in 
// standard form. Here gind and rowind are the needed indices,
// n is the list of dimensions of the simple modules and i is  
// indexes of simple modules. PowB and PowBbar are the powers of 
// of beta and beta-bar. 

ff := CoefficientRing(AL[1]);
g1 := glst[i];
g2 := Rank(PowBar[1]);
nn := Nrows(AL[1]);
GL := [];
for t := 1 to #AL do
   for u := 1 to n[i] do
      for v := 1 to n[i] do
         aa := Submatrix(AL[t],rowind[i]+(u-1)*g1 +1, 
                        rowind[i]+(v-1)*g1+1,g1,g1);
         bb := Submatrix(ALi[t],(u-1)*g2 +1,(v-1)*g2+1,g2,g2);
         if bb eq KMatrixSpace(ff,g2,g2)!0 then 
            Append(~GL,aa);
         else 
            r := Index(PowBar,bb);
            Append(~GL,aa - PowB[r]);
         end if;
      end for;
   end for;
end for;
if #BB ne 0 then 
   GL := GL cat [z*y*x: z in BB, x in GL, y in BB];
end if;
gens1 := Basis(sub<KMatrixSpace(ff,g1,g1)| GL>);
zer := KMatrixSpace(ff,nn,nn)!0;
gens2 := [InsertBlock(zer,x,rowind[i]+1, rowind[i]+1): x in gens1];

          return gens2,  gens1;

end function;

//******************************************************************

function RadicalSquared(L, glst, ff);
// L ia the list of possible generators of the radical. We create a 
// list of bases of the squares of the bases 

W := L;
WW := L;
r := #L;
flag := true;
n := 0;
while flag do
flag := false;
n := n+1;
   for i := 1 to r  do
      for j := 1 to r do
         if n eq 1 then 
            U := [];
         else 
            U := W[i][j];
         end if;
         for k := 1 to r do
            if #W[i][k] ne 0 and #L[k][j] ne 0 then
               U := U cat [xy : x in W[i][k], y in L[k][j]|
			       not IsZero(xy) where xy := x*y];
            end if;
         end for;

/*
"#U:", #U;
if #U gt 0 then
Universe(U);
#Set(U);
if Nrows(U[1]) eq Ncols(U[1]) then
time "DiagonalBlockStructure(U):", DiagonalBlockStructure([Matrix(x): x in U]);
end if;
end if;
*/

         UU := sub<KMatrixSpace(ff,glst[i],glst[j])| Set(U)>;
         N := Basis(UU);
         if N eq W[i][j] then continue;
         else 
            if #N ne #W[i][j] then 
               WW[i][j] := N;
               flag := true;
            else 
               if #N ne Dimension(sub<KMatrixSpace(ff,glst[i],glst[j])|
				  Set(U) join Set(W[i][j])>) then 
	          WW[i][j] := N;
                  flag := false;
               end if;
            end if;
         end if;
      end for;
   end for;   
W := WW;
end while;

return W;

end function;

//********************************************************************


function nprune(S, A, glst, rowind, mt, mi)

   ff := CoefficientRing(A);
   r := #S;
   T := Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]);
   TT := Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]);
   ST := [];
   V_0 := KMatrixSpace(CoefficientRing(A), Degree(A), Degree(A))!0;
   W := RadicalSquared(S,glst,ff);
   for i := 1 to r do
      for j := 1 to r do
         vprint Presentation: "<i,j> =", i, j;
         V := KMatrixSpace(ff, glst[i],glst[j]);
         U := sub< V | W[i][j] >;
         X := sub< V | W[i][j] cat S[i][j] >; 
         R := Basis(Complement(X, U meet X));
	 T[i][j] := [mi*InsertBlock(V_0,x,rowind[i]+1, rowind[j]+1)*mt: 
                x in R];
         TT[i][j] := R;
	 ST cat:=  T[i][j];
      end for;
   end for;

	return T, ST, TT;
		
end function;

//*********************************************************************

radical_generators := function(AL, ALi, G, T, B, n, k);

mtt, mti := ChangeOfBasisMatrixA(AL, G, T, n);
AA, GG, TT, BB := NormalFormA(AL,G,T,B,mtt,mti);
gss, row := NeededIndices(GG,n);

/*
"mtt DiagonalBlockStructure:", DiagonalBlockStructure(mtt);
"mti DiagonalBlockStructure:", DiagonalBlockStructure(mti);
*/

GEN := [];
OGEN := [];
lGEN := [* *];
np := #gss;
ddd := SimpleQuotientAlgebras(AL)`DegreesOfCenters;
Pb := [* *];
for i := 1 to #ddd do
  if ddd[i] eq 1 then 
    Pb[i] := [];
   else
    bb := Submatrix(BB[i], row[i]+1, row[i]+1, gss[i], gss[i]);
    Pb[i] := [bb^(j): j in [1 .. ddd[i]-1]];
  end if;
end for;
for i := 1 to np do
   OGENi := [];
   lGENi := [* *];
   for j := 1 to np do
      if i ne j then 
         gen,gen2 := BasisForRadical_i_ne_j(AA, gss, row, 
                    Pb[i], Pb[j], n, i, j);
         Append(~GEN,gen);
         Append(~lGENi, gen2);
         ogen := [mti*x*mtt:x in gen];
         Append(~OGENi,ogen);
      else 
         gb := k[i]`PrimitiveIdempotentOnQuotient;
         tb := k[i]`PermutationOnQuotient;
         bb := k[i]`FieldGeneratorOnQuotient;
         mm,mi :=  ChangeOfBasisMatrixB(ALi[i],gb,tb);
         X := Domain(ALi[i]);
	 AAi := [mm*(ALi[i](X.j))*mi:j in [1 .. Ngens(AL)]];
         bb := mm*bb*mi;
         PBs,s := PowersOfBetaBar(bb);
         PBb := PowersOfBeta(BB,i,row,s);
         gen, gen2 := BasisForRadical_i_i(AA, AAi, gss, row, 
                       PBb, PBs,Pb[i],n,i);
         Append(~GEN,gen);
         Append(~lGENi, gen2);
         ogen := [mti*x*mtt:x in gen];
         Append(~OGENi,ogen);
      end if;
   end for;
   Append(~OGEN,OGENi);
   Append(~lGEN,lGENi);
end for;

aaa, bbb, ccc  := nprune(lGEN, AL, gss, row,mtt,mti);

              return aaa, bbb, ccc, <mtt,mti>;

end function;


