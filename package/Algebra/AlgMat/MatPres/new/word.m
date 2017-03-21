freeze;

filtered_basis_radical := function(n, L, mu);
// n is the list of ranks of the primitive idempotents
// L is the sequence of basis elements for the radical -- condensed.
// mu is the back map associating each element of L with a monomial.

   r := #n;
   nn := [0] cat [&+[n[i]: i in [1 ..j]]: j in [1 .. r]];
   T := Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]);
   for x in L do
      for i := 1 to r do
         if not &and[IsZero(x[t]): t in [nn[i]+1 .. nn[i+1]]] then 
            y := Transpose(x);
            for j := 1 to r do 
               if not &and[IsZero(y[t]): t in [nn[j]+1 .. nn[j+1]]] then 
                  Append(~T[i][j], <Submatrix(x,nn[i]+1, nn[j]+1, n[i], n[j]),                             mu(x)>);
               end if;
            end for;
         end if;
      end for;
   end for;

           return T;

end function; 

//***********************************************************************

filtered_basis_field_generators := function(n, L);
// n is the list of ranks of the primitive idempotents
// L is the sequence of basis elements for the field generators -- condensed.

   r := #n;
   nn := [0] cat [&+[n[i]: i in [1 ..j]]: j in [1 .. r]];
   T := [* *];
   for i := 1 to r do
      Append(~T, Submatrix(L[i],nn[i]+1, nn[i]+1, n[i], n[i]));
   end for;

           return T;

end function; 

//************************************************************************

word_solution_matrices := function(A, rand, lim1, lim2);

ff := CoefficientRing(A);
als := AlgebraStructure(A : Rand := rand, limprod := lim1, limsum := lim2);
P := als`FreeAlgebra;
d := SimpleQuotientAlgebras(A)`DegreesOfCenters;
q := SimpleQuotientAlgebras(A)`OrdersOfCenters;
als := AlgebraStructure(A);
radmats := als`CondensedRadicalBasis;
fldmats := als`CondensedFieldGenerators;
s := RanksOfPrimitiveIdempotents(A);
SS := radmats;
r := #SS;
for i := 1 to r do
   for j := 1 to r do
      rowlst := [];
      monlst := [];
      if i eq j then 
         if d[i] gt 1 then 
            rowlst := [Vector(fldmats[i]^j): j in [1 .. d[i]-1]] cat 
                    [Vector(IdentityMatrix(ff, s[i]))];
            monlst := [P.i^j:j in [1 .. d[i]-1]] cat [P.i^(q[i]-1)];
         else 
            rowlst := [Vector(IdentityMatrix(ff, s[i]))];
            monlst := [P.i^(q[i]-1)];
	 end if;
      end if;
      if #radmats[i][j] ne 0  then 
	 rowlst cat:= [Vector(radmats[i][j][k][1]): k in 
	       		      [1 .. #radmats[i][j]]];
	 monlst cat:= [radmats[i][j][k][2]: k in 
			      [1 .. #radmats[i][j]]];
      end if;
      if #rowlst ne 0 then
      	 SS[i][j] := <Matrix(rowlst),monlst>;
      else 
       	 SS[i][j] := [];
      end if;
   end for ;
end for;

		 return SS;

end function;

//********************************************************************

intrinsic WordProblemData(A::AlgMat : Rand := "PartSpin", limprod := 7, limsum := 8) -> List
{The data needed for the solution to the word problem.

The user has two choices of randomization. The default is "PartSpin", which
begins a spin and takes random linear combinations as the rendom elements.
This should work for all algebra. The second is "Meataxe", which evaluated
small polynomials on the generators. The user can choose the maximum degree
of the monomals in the polynomial ("limprod") and the maximum number of 
terms in the polynomial ("limsum"). The defaults are 7 and 8 respectively.
The "Meataxe" method is faster for many algebras such as actions of groups
on modules, but it may fail completely in other cases. 
}

if assigned A`WordProblemData then 
return A`WordProblemData;
end if;
mats := word_solution_matrices(A, Rand, limprod, limsum);
A`WordProblemData := mats;

        return mats;

end intrinsic;

//*******************************************************************


intrinsic WordProblem(A::AlgMat, x::AlgMatElt : 
	Rand := "PartSpin", limprod := 7, limsum := 8) -> BoolElt, AlgFrElt
{Expresses the element x as a word in the presentation of A. 

The user has two choices of randomization. The default is "PartSpin", which
begins a spin and takes random linear combinations as the rendom elements.
This should work for all algebra. The second is "Meataxe", which evaluated
small polynomials on the generators. The user can choose the maximum degree
of the monomals in the polynomial ("limprod") and the maximum number of 
terms in the polynomial ("limsum"). The defaults are 7 and 8 respectively.
The "Meataxe" method is faster for many algebras such as actions of groups
on modules, but it may fail completely in other cases. 
}

rand := Rand;
lim1 := limprod;
lim2 := limsum;
matlst := WordProblemData( A : Rand := rand, limprod := lim1, limsum := lim2);
s := RanksOfPrimitiveIdempotents(A);
n := SimpleQuotientAlgebras(A)`DegreesOverCenters;
r := #n;
ww := [s[i]*n[i]: i in [1 .. r]];
rowind := [0] cat [&+[ww[j]:j in [ 1 .. i]]: i in [ 1 .. r]];
P, I := Presentation(A);
bool := true;
pol := P!0;
uu := AlgebraStructure(A)`StandardFormConjugationMatrices;
y := uu[1]*x*uu[2];
for i := 1 to r do
   for j := 1 to r do

    if #n eq &+n then 

      if #matlst[i][j] ne 0 then  
         plst := matlst[i][j][2];
         vlst := Vector(Submatrix(y,rowind[i]+1, rowind[j]+1, s[i], s[j]));
         a, sol := IsConsistent(matlst[i][j][1],vlst);
         if a then
	 pp := &+[sol[t]*plst[t]: t in [1 .. #plst]];
            pol +:= pp;
         else
            return a;
         end if;
      else 
         if not IsZero(Submatrix(y,rowind[i]+1, rowind[j]+1, ww[i], ww[j])) then
            return false;
         end if;
      end if;

    else

      if #matlst[i][j] ne 0 then  
         plst := matlst[i][j][2];
         vlst := [Vector(Submatrix(y,
                  rowind[i]+1+(k-1)*s[i], rowind[j]+1+(l-1)*s[j], s[i], s[j])):
                  k in [1 .. n[i]], l in [1 .. n[j]]];
         a, sol := IsConsistent(matlst[i][j][1],vlst);
         if a then
            pp := &+[P.(r+i)^(n[i]+1-k)*
		      &+[sol[n[i]*(l-1)+k][t]*plst[t]: t in [1 .. #plst]]*
                      P.(r+j)^(l-1):
	          k in [1 .. n[i]], l in [1 .. n[j]]];
            pol +:= pp;
         else
            return a;
         end if;
      else 
         if not IsZero(Submatrix(y,rowind[i]+1, rowind[j]+1, ww[i], ww[j])) then
            return false;
         end if;
      end if;

    end if;

   end for;
end for;

return bool, pol;

end intrinsic;

//********************************************************************


locate_generators := function(T);
// T is the list of lists of the radical generators. 

r := #T;
loc := [];
for i := 1 to r do
   for j := 1 to r do
      loc cat:= [<i,j> : k in [1 .. #T[i][j]]];
   end for;
end for;

   return loc;

end function;

