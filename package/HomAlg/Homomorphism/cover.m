freeze;

//    Jon F. Carlson, June 2012

intrinsic ReversePath(PT:: SeqEnum, j:: RngIntElt) -> SeqEnum
{Returns the path from a basis element of a projective module of a
basic algebra to the idemptent.  The input is the path tree and the
index of the basis element in the standard basis. If the return for
an element is [i1, i2, .. ij] then the element is the product of
the generators indexed by the elements of the sequence in the given
order.}

aa := [];
k := j;
flag := true;
while flag do
   Append(~aa,PT[k][2]);
   k := PT[k][1];
   if k eq 1 then
      flag := false;
   end if;
end while;
bb := Reverse(aa);

        return bb;

end intrinsic;

//////////////////////////////////////////////////////////////////////

RadicalLength:= function(M);
N := JacobsonRadical(M);
S := [1];
while Dimension(N) gt 0 do
   L := JacobsonRadical(N);
   Append(~S, Dimension(N)-Dimension(L));
   N := L;
end while;

return S;

end function;

//////////////////////////////////////////////////////////////////////

intrinsic CoverAlgebra(A:: AlgBas) -> AlgBas, ModMatFldElt
{constructs the maximal extension AA as in [0 -> K -> AA -> A -> 0]
such that AA acts trivially on K and AA is an algebra with exactly
the same minimal number of generators as A. Returns AA and the
algebra homomorphism of AA onto A.}

k := BaseRing(A);
nproj := NumberOfProjectives(A);
NIGs := NonIdempotentGenerators(A);
nigs := #NIGs;
ngens := nproj+nigs;
radlengths := [#RadicalLength(ProjectiveModule(A,i)): i in [ 1 .. nproj]];
mmm := Maximum(radlengths);
NNN := [];
cmatlst := [* *];
cflag := true;
tails := GeneratorAssociatedIdempotents(A);
for j := 1 to nproj do
        P := ProjectiveModule(A,j);
   np := Dimension(P);
     // we extend each projective. note that if the radical length of
     // P is smaller than max, then there is no point in extending.
   pt := PathTree(A,j);
   revpts := [ReversePath(pt, i): i in [1 .. np]];
   AG := ActionGenerator(A,j);
   elimlst := [];
   elimlst := [];
   for i := 1 to #NIGs do
      for l := 1 to #pt do
         if pt[l][2] eq nproj+i then
            Append(~elimlst,i*np+pt[l][1]);
         end if;
         if tails[pt[l][2]][2] ne tails[i+nproj][1] then
            Append(~elimlst,i*np+l);
         end if;
      end for;
   end for;
   keeplst := [<i*np+l,i,l>:l in [1 .. np],
                i in [1 .. #NIGs]| i*np+l notin elimlst];
   indlst1 := [np] cat [#[x:x in keeplst|x[2] eq i]:i in [1 .. #NIGs]];
   indlst2 := [&+[indlst1[l]:l in [1 .. i]]:
                        i in  [1 .. #NIGs +1]];
   clst := [];
   Ksp := KMatrixSpace(k, np+#keeplst, np+#keeplst);
   NAG:= [InsertBlock(Ksp!0, AG[i], 1, 1): i in [1 .. ngens]];
        for i := 1 to #NAG do
                mat := NAG[i];
                if i le nproj then
                   for t := 1 to #indlst2 -1 do
                                if tails[t+nproj][2] eq i then
                                   for s := indlst2[t]+1 to indlst2[t+1] do
                                      mat[s][s] := 1;
                                   end for;
                               end if;
                        end for;
                end if;
      if i gt nproj then
         if indlst1[i+1-nproj] gt 0 then
            for t := indlst2[i-nproj]+1 to indlst2[i+1-nproj] do
               if not mat[keeplst[t-np][3]] eq VectorSpace(k,Ncols(mat))!0 then
                  Append(~clst,[i,t,keeplst[t-np][3]]);
                end if;
                mat[keeplst[t-np][3]][t] := 1;
             end for;
         end if;
      end if;
      NAG[i] := mat;
      end for;
      if #clst eq 0 then
         NNN[j] := < MatrixAlgebra< k, Nrows(NAG[1]) | NAG>,
                pt cat [<x[3],x[2]+nproj>:x in keeplst]>;
         Append(~cmatlst, IdentityMatrix(k, Nrows(NAG[1])));
      else
         cmat := IdentityMatrix(k,Nrows(NAG[1]));
         for x in clst do
            cmat[x[2]] := NAG[x[1]][x[3]];
         end for;
         icmat := cmat^-1;
         NAG2 := [cmat*x*icmat: x in NAG];
         NNN[j] := < MatrixAlgebra<k, Nrows(NAG[1]) | NAG2>,
                pt cat [<x[3],x[2]+nproj>:x in keeplst]>;
         Append(~cmatlst, cmat);
         cflag := false;
      end if;
end for;
C := BasicAlgebra(NNN);
dp1 := DimensionsOfProjectiveModules(A);
dp2 := DimensionsOfProjectiveModules(C);
rho := KMatrixSpace(k,Dimension(C),Dimension(A))!0;
rcount := 1;
ccount := 1;
for r := 1 to nproj do
   if cflag then
      InsertBlock(~rho,IdentityMatrix(k,dp1[r]),rcount,ccount);
   else
      InsertBlock(~rho,Submatrix(cmatlst[r],1,1,dp2[r],dp1[r]),rcount,ccount);
   end if;
   rcount +:= dp2[r];
   ccount +:= dp1[r];
end for;
zeta := rho;                                 //  zeta := ma*rho;
S := Kernel(zeta);
VV  := sub<VectorSpace(BaseRing(C),Dimension(C))|
   [Vector(y*C!x): x in Basis(S), y in NonIdempotentGenerators(C)]> ;
B, mu := quo<C| VV>;           // C, mu := QuotientAlgebra(B,VV);
psi := InducedHomomorphism(zeta, 
          KMatrixSpace(k,Dimension(C),Dimension(B))!Matrix(mu), 
          KIdentityMatrix(k,Dimension(A)));

	return B, psi;       // return B, ma*psi, rdim, socdim;

end intrinsic;


