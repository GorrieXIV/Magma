freeze;

//  Jon F. Carlson, June 2012

intrinsic IsDimensionCompatible(B:: AlgBas) -> Bool
{True if the dimension of a basic algebra is the same as the 
dimension of the matrix algebra of its action on itself. If 
false then the algebra is not a basic algebra}

nn := Dimension(Action(RightRegularModule(B)));

	return nn eq Dimension(B);

end intrinsic;



//////////////////////////////////////////////////////////////////////

LocationOfGenerators := function(A);
// finds the location of the generators as elements of the standard basis
// of the underlying vector space of the algebra.

np := NumberOfProjectives(A);
PT := &cat[PathTree(A,i): i in [1 .. np]];
loc := [[j : j in [1 .. #PT]|PT[j][2] eq i and PT[j][1] eq 1][1]:
        i in [1 .. #Generators(A)]];

return loc;

end function;

////////////////////////////////////////////////////////////////////

intrinsic IsPathTree(B::AlgBas) -> Bool
{true if the basis elements of the projective modules in the basic
algebra are determined by the path tree.} 

loc := LocationOfGenerators(B);
nproj := NumberOfProjectives(B);
dp := DimensionsOfProjectiveModules(B);
dsum := [0] cat [&+[dp[i]: i in [1 .. j]]:j in [1 .. nproj]];
nn := 0;
flag := true;
V := Basis(VectorSpace(BaseRing(B),Dimension(B)));
for i := 1 to nproj do
   a := loc[i];
   pt := PathTree(B,i);
   for j := 2 to #pt do
      if not Vector(B.(dsum[i]+pt[j][1])*B.(loc[pt[j][2]])) 
                         eq V[dsum[i]+j] then
         flag := false;
print i, pt[j];
         break;
         break;
      end if;
   end for;
end for;

	return flag;

end intrinsic;

////////////////////////////////////////////////////////////////////

HomIm := function(A, psi, x);
// returns the image of x under the homomorphism of basic algebras
// given by the matrix psi whose target is the algebra A.

        return A!(Vector(x)*psi);

end function;

//////////////////////////////////////////////////////////////////

IsAlgHom := function(A, B, psi)
// True if the matrix psi represents a homomorphism from basic algebra
// A to basic algebra B.

for x in Generators(A) do
   for i := 1 to Dimension(A) do
      if not HomIm(B, psi, A.i)*HomIm(B, psi, x) eq HomIm(B, psi, A.i*x) then
         return false;
      end if;
   end for;
end for;

        return true;

end function;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBas, B::AlgBas, psi::ModMatFldElt) -> Bool
{True if the matrix psi represents a homomorphism from basic algebra
A to basic algebra B.}

	return IsAlgHom(A,B,psi);

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBas, B::AlgBas, psi::AlgMatElt) -> Bool
{True if the matrix psi represents a homomorphism from basic algebra
A to basic algebra B.}

        return IsAlgHom(A,B,psi);

end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBas, B::AlgBas, psi::GrpMatElt) -> Bool
{True if the matrix psi represents a homomorphism from basic algebra
A to basic algebra B.}

        return IsAlgHom(A,B,Matrix(psi));

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(psi::Map) -> Bool
{True if the map psi is a homomorphism of basic algebras.}

        return IsAlgHom(Domain(psi), Codomain(psi), Matrix(psi));

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBas, B::AlgBas, psi::Map) -> Bool
{True if the map psi is a homomorphism of basic algebras A to B.}

        return IsAlgHom(A, B, Matrix(psi));

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBasGrpP, B::AlgBasGrpP, psi::Map) -> Bool
{True if the map psi is a homomorphism of basic algebras A to B.}

        return IsAlgHom(A, B, Matrix(psi));

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBasGrpP, B::AlgBas, psi::Map) -> Bool
{True if the map psi is a homomorphism of basic algebras A to B.}

        return IsAlgHom(A, B, Matrix(psi));

end intrinsic;

/////////////////////////////////////////////////////////////////////////

intrinsic IsAlgebraHomomorphism(A::AlgBas, B::AlgBasGrpP, psi::Map) -> Bool
{True if the map psi is a homomorphism of basic algebras A to B.}

        return IsAlgHom(A, B, Matrix(psi));

end intrinsic;








//////////////////////////////////////////////////////////////////

intrinsic IsIdeal(A::AlgBas, S::ModTupFld) -> Bool
{True if the subspace spanned by the elements of S is a two-sided 
ideal of the basic algebra A.}

flag := true;
for x in Generators(A) do 
for y in Basis(S) do 
if not Vector(x*A!y) in S then
   flag := false; 
   break;
end if;
if not Vector(A!y*x) in S then
      flag := false;
      break;
   end if;
end for;
end for;

	return flag;

end intrinsic;

////////////////////////////////////////////////////////////////////

intrinsic IsLeftIdeal(A::AlgBas, S::ModTupFld) -> Bool
{True if the subspace spanned by the elements of S is a left
ideal of the basic algebra A.}

flag := true;
for x in Generators(A) do 
for y in Basis(S) do
if not Vector(x*A!y) in S then
   flag := false;
   break;
end if;
end for;
end for;

        return flag;

end intrinsic;

//////////////////////////////////////////////////////////////////

intrinsic IsRightIdeal(A::AlgBas, S::ModTupFld) -> Bool
{True if the subspace spanned by the elements of S is a two-sided
ideal of the basic algebra A.}

flag := true;
for x in Generators(A) do 
for y in Basis(S) do
if not Vector(x*A!y) in S then
   flag := false;
   break;
end if;
if not Vector(A!y*x) in S then
      flag := false;
      break;
   end if;
end for;
end for;

        return flag;

end intrinsic;

