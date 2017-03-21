freeze;

/***************************************************************************
			       Creation
****************************************************************************/

intrinsic ZeroChainMap(C::ModCpx, D::ModCpx) -> MapChn
{Create the chain map from C to D all of whose module maps are zero}
    // check algebras compatible
    max, min := Degrees(C);
    L := [* *];
    for i := max to min by -1 do
	f := Hom(Term(C, i), Term(D, i)) ! 0;
	Append(~L, f);
    end for;
    return ChainMap(L, C, D, 0);
end intrinsic;

/***************************************************************************
			       Check
****************************************************************************/

intrinsic IsProperChainMap(f::MapChn) -> BoolElt
{Checks to see if we can take kernel and cokernel without truncating the 
complexes.}

   C := Domain(f);
   D := Codomain(f);   
   a,b := Degrees(C);
   c,d := Degrees(D);
   n := Degree(f);
   flag :=  true;
   if a+n gt c then 
      if BoundaryMap(C, c-n+1)*ModuleMap(f,c-n) ne 
                                   Hom(Term(C,c-n-1), Term(D,c))!0 
           then flag := false;
      end if;
   end if;
   if b+n gt d then 
      if ModuleMap(f,b)*BoundaryMap(D, b+n) ne Hom(Term(C,b),Term(D,b+n-1))!0
           then flag := false;
      end if;
   end if;

   return flag;

end intrinsic;

intrinsic IsChainMap(L::List,C::ModCpx,D::ModCpx,n::RngIntElt) -> BoolElt
{True if the list of maps L from the terms of complex C to the terms of D
is a chain complex of degree n, i. e. it has the right length and the
diagram commutes}
  
   a,b := Degrees(C);
   c,d := Degrees(D);
   max := Minimum(a,c+n);
   min := Maximum(b,d+n);
   if max - min +1 ne #L then
   return false;
   end if;
   return forall{i:i in [min+1 .. max]|
    Rank(BoundaryMap(C,i-n)*L[max+2-i] - L[max+1-i]*BoundaryMap(D,i)) eq 0};
  
end intrinsic;
  
intrinsic IsChainMap(f::MapChn) -> BoolElt
{True if the chain map f really is a chain map}

return IsChainMap(ModuleMaps(f),Domain(f),Codomain(f),Degree(f));

end intrinsic;

/***************************************************************************
			       Access
****************************************************************************/

intrinsic DefinedInDegrees(f::MapChn) -> RngIntElt, RngIntElt
{The first and last degree of the domain of f on which the chain map f 
   is defined.}

   a,b := Degrees(Domain(f));
   c,d := Degrees(Codomain(f));
   n := Degree(f);
   u := Minimum([a,c-n]);
   v := Maximum([b,d-n]);

   return u,v;
end intrinsic;

intrinsic ModuleMaps(f::MapChn) -> List
{The module maps of f}
    max, min := DefinedInDegrees(f);
    L := [* *];
    for i := max to min by -1 do
	Append(~L, ModuleMap(f, i));
    end for;
    return L;
end intrinsic;

intrinsic Kernel(f::MapChn) -> ModCpx, MapChn
{The kernel complex of f and the chain map of the inclusion. In the event 
that the chain map is not defined on a particular term of the Domain then 
the entire term is assumed to be in the kernel.}
    require IsProperChainMap(f): "Argument is not a proper chain map";
    C := Domain(f);
    a,b := DefinedInDegrees(f);
    max, min := Degrees(C);
    S := [* *];
    for i := max to min by -1 do
      if i ge b then 
	Append(~S, Kernel(ModuleMap(f, i)));
      else 
        Append(~S, Term(C,i));
      end if;
    end for;
    return Subcomplex(C, S);
end intrinsic;

intrinsic Cokernel(f::MapChn) -> ModCpx, MapChn
{The cokernel complex of f and the chain map of the projection onto the
quotient}
    require IsProperChainMap(f): "Argument is not a proper chain map";
    return quo<Codomain(f) | Image(f)>;
end intrinsic;

ImageF := function(MAT);

im := Image(MAT);
im2,mu := sub<Codomain(MAT)|im>;
mu2 := MapToMatrix(mu);
nu := Hom(Domain(MAT),im2)!Solution(mu2,MAT);
return im2, mu2, nu;

end function;

intrinsic Image(f::MapChn) -> ModCpx, MapChn, MapChn
{The image complex I of f and the inclusion of I into the codomain and
the projection of the domain onto I. If the chain map has no defined image 
into a particular term of the codomain then the image is assumed to be zero}
    require IsProperChainMap(f): "Argument is not a proper chain map";
    C := Domain(f);
    D := Codomain(f);
    max, min := Degrees(D);
    a,b := DefinedInDegrees(f);
    n := Degree(f);
    S := [* *];
    MM := [* *];
    for i := max to min by -1 do
      if i gt a+n then 
        Append(~S, sub<Term(D,i)|>);
      else
        ss,ll,mm := ImageF(ModuleMap(f, i-n));
        Append(~S, ss);
        Append(~MM,mm);
      end if;
    end for;
    I, L := Subcomplex(D, S);
    P := ChainMap(MM,C,I,n);

    return I, L, P;

end intrinsic;

/***************************************************************************
			       Basic operations
****************************************************************************/

intrinsic '+'(f::MapChn, g:: MapChn) -> MapChn
{The sum of the two chain maps f and g}
    // Check dom, codom compat
    C := Codomain(f);
    D := Codomain(f);
    d := Degree(f);
    a,b := DefinedInDegrees(f);
    max, min := DefinedInDegrees(g);
require a eq max:"Chain maps are not defined in the same degrees";
require b eq min:"Chain maps are not defined in the same degrees";
    require Degree(g) eq d:
	"Degree of argument 2 does not equal that of argument 1";
    L := [* *];
    for i := max to min by -1 do
	a := ModuleMap(f, i);
	b := ModuleMap(g, i);
	c := a + b;
	Append(~L, c);
    end for;
    return ChainMap(L, C, D, d);
end intrinsic;

intrinsic 'eq'(f::MapChn,g::MapChn) -> Bool
{Checks to see if two chain maps are equal}

a,b := DefinedInDegrees(f);
c,d := DefinedInDegrees(g);
if a ne c then return false;
end if;
if b ne d then return false;
end if;
for j := a to b by -1 do
   if ModuleMap(f,j) ne ModuleMap(g,j) then
      return false;
   end if;
end for;

      return true;

end intrinsic;

intrinsic '*'(s::RngIntElt, f::MapChn) -> MapChn
{The product of the scalar s and the chain map f}
    C := Domain(f);
    D := Codomain(f);
    d := Degree(f);
    max, min := DefinedInDegrees(f);
    L := [* *];
    for i := max to min by -1 do
	a := s * ModuleMap(f, i);
	Append(~L, a);
    end for;
    return ChainMap(L, C, D, d);
end intrinsic;

intrinsic '*'(f::MapChn, g:: MapChn) -> MapChn
{The composition of the two chain maps f and g}
//function Composition(f,g);

    C := Domain(f);
    X := Codomain(f);
//       require X eq Domain(g): "Composition not defined for these maps" ;
    D := Codomain(g);
    m := Degree(f);
    n := Degree(g);
    a, b := Degrees(X);
    u, v := Degrees(C);
    x, y := Degrees(D);
L := [* *];
for i := u to v by -1 do
   if i+m+n le x and i+m+n ge y then 
      if i+m le a and i+m ge b then 
         Append(~L, ModuleMap(f,i)*ModuleMap(g,i+m));
      else 
         Append(~L, AHom(Term(C,i),Term(D,i+m+n))!0);
      end if;
   end if;
end for;
h := ChainMap(L, C, D, m+n);
// checks
c, d := DefinedInDegrees(h);
if c+m gt a then 
     require  
     BoundaryMap(C,a-m-1)*ModuleMap(h,a-m) eq 
                    AHom(Term(C,a-m-1),Term(D,a+n))!0:
                 "The composition is not a chain map";
end if;
if d+m lt b then require
     ModuleMap(h,b-m)*BoundaryMap(C,b+n) eq AHom(Term(C,b-m),Term(D,b+n-1))!0:
                 "The composition is not a chain map";
end if;

       return h;

end intrinsic;

/***************************************************************************
			       Boolians
****************************************************************************/

intrinsic IsZero(f::MapChn) -> BoolElt
{True if and only if the chain map f is zero in every degree}
    return forall{x: x in ModuleMaps(f) | IsZero(x)};
end intrinsic;

intrinsic IsInjective(f::MapChn) -> BoolElt
{True if and only if the chain map f is an injection in every degree}
    return forall{x: x in ModuleMaps(f) | IsInjective(x)};
end intrinsic;

intrinsic IsSurjective(f::MapChn) -> BoolElt
{True if and only if the chain map f is a surjection in every degree}
    return forall{x: x in ModuleMaps(f) | IsSurjective(x)};
end intrinsic;

intrinsic IsIsomorphism(f::MapChn) -> BoolElt
{True if and only if the chain map f is an isomorphism in every degree}
    return forall{x: x in ModuleMaps(f) | IsInjective(x) and IsSurjective(x)};
end intrinsic;

intrinsic IsShortExactSequence(f::MapChn,g::MapChn) -> BoolElt
{True if the sequence of chain complexes, 
0 -> Domain(f) -> Domain(g) -> Codomain(g) -> 0, 
where the internal maps are f and g, is exact.}

   require Degree(f) eq 0: "First argument does not have degree 0";
   require Degree(g) eq 0: "second argument does not have degree 0";
   flag := true;
   SS := EqualizeDegrees([Domain(f),Domain(g),Codomain(g)]);
   a,b := Degrees(SS[1]);
   for i := a to b by -1 do
   W := [* *];
   if Dimension(Term(SS[1],i)) ne 0 and Dimension(Term(SS[2],i)) ne 0
   then
   W[1] := ModuleMap(f,i);
   else
   W[1] := ZeroMap(Term(SS[1],i),Term(SS[2],i));
   end if;
   if Dimension(Term(SS[2],i)) ne 0 and Dimension(Term(SS[3],i)) ne 0
   then
   W[2] := ModuleMap(g,i);
   else
   W[2] := ZeroMap(Term(SS[2],i),Term(SS[3],i));
   end if;
   if IsExact(ZeroExtension(Complex(W,0))) eq false then
   flag := false;
   return flag;
   end if;
   end for;

   return flag;

end intrinsic;

/*****************************************************************************
			      Homology
*****************************************************************************/

intrinsic InducedMapOnHomology(f::MapChn,n::RngIntElt) -> ModTupFldElt
{The homomorphism induced on homology by the chain map f in degree n.}
   C := Domain(f);
   D := Codomain(f);
   HC,mu := Homology(C,n);
   KC,sigma := Kernel(BoundaryMap(C,n));
   HD,nu := Homology(D,n+Degree(f));
   KD,tau := Kernel(BoundaryMap(D,n+Degree(f)));
   B := Basis(HC);
   ff := ModuleMap(f,n);
   B1 := [nu(ff(sigma(B[j]@@mu))@@tau):j in [1 .. #B]];
   theta := Hom(HC, HD)!B1;
   return theta;

end intrinsic;

intrinsic ConnectingHomomorphism(f::MapChn,g::MapChn,n::RngIntElt) -> 
             ModMatFldElt
{The connecting homomorphism in degree n of the short exact sequence of
chain complexes given by the chain maps f and g.}

   C := Domain(f);
   D := Codomain(g);
   H1, phi1 := Homology(C,n-1);
   H2, phi2 := Homology(D,n);
   gn := ModuleMap(g,n);
   fn := ModuleMap(f,n-1);
   require IsSurjective(gn):"Second arguement is not surjective in degree n";
   V3 := Solution(MapToMatrix(phi2), EndomorphismRing(H2)!1);
   U, theta  := Kernel(BoundaryMap(D,n));
   V3 := V3*MapToMatrix(theta);
   V5 := Solution(gn,V3);
   V5 := V5*BoundaryMap(Codomain(f),n);
   V7 := Solution(fn,V5);
   kk, mu  :=  Kernel(BoundaryMap(C,n-1));
   V8 := Solution(MapToMatrix(mu), V7);
   V8 := V8*MapToMatrix(phi1);

   return Hom(H2,H1)!V8;

end intrinsic;

intrinsic LongExactSequenceOnHomology(f::MapChn,g::MapChn) -> ModCpx
{The long exact sequence on homology for the exact sequence of complexes
given by the chain maps f and g as a chain complex with the homolgy group
in degree i for the Cokernel of C appearing in degree 3i.}

   D := Domain(f);
   E := Codomain(f);
   F := Codomain(g);
   a,b := Degrees(D);
   c,d := Degrees(E);
   u,v := Degrees(F);
   require a eq c and c eq u and b eq d and d eq v:"Complexes do not all 
		have the same degrees";
   hd := Homology(D);
   he := Homology(E);
   hf := Homology(F);
   C := [* *];
   C[1] := Hom(hd[1],he[1])!InducedMapOnHomology(f,a-1);
   C[2] := Hom(he[1],hf[1])!InducedMapOnHomology(g,a-1);
   if a-b gt 2 then 
   for i := a-2 to b+1 by -1 do
   j := a-1-i;
   C[3*j] := Hom(hf[j],hd[j+1])!ConnectingHomomorphism(f,g,i+1);
   C[3*j+1] := Hom(hd[j+1],he[j+1])!InducedMapOnHomology(f,i);
   C[3*j+2] := Hom(he[j+1],hf[j+1])!InducedMapOnHomology(g,i);
   end for;
   end if;

   return Complex(C,3*(b+1));

end intrinsic;









