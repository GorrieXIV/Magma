freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: elt.m
   DESC: Basic ModAbVarElt functionality.

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Elements of Modular Abelian Varieties

BEGIN_HANDBOOK_INTRO
We represent torsion points on modular abelian varieties as follows.
Suppose $A$ is an abelian variety defined over the complex numbers
$\C$.  Then $A(\C)$ is canonically isomorphic to
$H_1(A,\R)/H_1(A,\Z)$, and the torsion subgroup of $A(\C)$ is
isomorphic to $H_1(A,\Q)/H_1(A,\Z)$.  We represent a torsion element
of $A(\C)$ by giving a representative element of $H_1(A,\Q)$.  The
functions below provide basic arithmetic operations with such
elements, application of homomorphisms, and 
conversion functions.   

Sometimes it is useful to consider elements of $H_1(A,\R)$, given
by floating point vectors (i.e., over {\tt RealField()}). These
represent certain points of infinite order, but without further
information we do not know exactly what point they represent,
or even whether such a point is $0$.    
END_HANDBOOK_INTRO
*/

import "homology.m":
   BasisChange_Rational_to_Lattice,
   BasisChange_Real_to_Lattice;

import "rings.m": 
   ApproximateRational,
   CommonFieldOfDefinition,
   IsDefnField,
   QQ, RR;

forward
   Create_ModAbVarElt,
   Create_ModAbVarElt_Zero,
   IsOverQ,
   PutInCommonParent;

declare type ModAbVarElt;

declare attributes ModAbVarElt:
   element,                    // element of either the rational or 
                               // real homology of ambient variety.
   lattice_element,            // element in terms of basis of integral lattice
   parent,                     // the variety that contains this torsion element.
   field_of_definition,        // minimal field of definition of this element.
   order;

function IsOverQ(x)
   return Type(BaseRing(Parent(x`element))) eq FldRat;
end function;


/***************************************************************************

  << Arithmetic >>

The following commands support basic arithmetic operations on
elements of modular abelian varieties.   Operations include
addition, subtraction, and multiplication by an integer, rational
number, or real number.

EXAMPLES


In this example, we construct $J_0(23)$, and consider the finite
subgroup $\ker(T_3-5)$, which has order $400$.  We then do
various arithmetic operations with some of its elements.
\begincode
> A := JZero(23);
> t3 := HeckeOperator(A,3);
> Factorization(CharacteristicPolynomial(t3));
[
    <x^2 - 5, 2>
]
> G := Kernel(t3-5);
> #G;
400
> Generators(G);
[
    Element of abelian variety defined by [1/10 0 1/10 1/5] modulo homology,
    Element of abelian variety defined by [0 0 0 -5/2] modulo homology,
    Element of abelian variety defined by [1/10 -1/10 0 -1/5] modulo homology,
    Element of abelian variety defined by [1 -3/2 2 1] modulo homology
]
> x := G.1;
> 1.5*x;
Element of abelian variety defined by [0.149999999999999999999999999998 0.E-28 
0.149999999999999999999999999998 
0.299999999999999999999999999996] modulo homology
> (3/2)*x;
Element of abelian variety defined by [3/20 0 3/20 3/10] modulo homology
> 10*x;
0
> x*1.5;
Element of abelian variety defined by [0.149999999999999999999999999998 0.E-28 
0.149999999999999999999999999998 
0.299999999999999999999999999996] modulo homology
> 1.5*x eq x*1.5;
true
> x*(3/2);
Element of abelian variety defined by [3/20 0 3/20 3/10] modulo homology
> x*5;
Element of abelian variety defined by [1/2 0 1/2 1] modulo homology
> G.1 + G.2;
Element of abelian variety defined by [1/10 0 1/10 -23/10] modulo homology
> G.1 - G.2;
Element of abelian variety defined by [1/10 0 1/10 27/10] modulo homology
\endcode


 ***************************************************************************/

intrinsic '+'(x::ModAbVarElt, y::ModAbVarElt) -> ModAbVarElt
{The sum of x and y.}
   if Parent(x) ne Parent(y) then
      X := PutInCommonParent([*x,y*]);
      return X[1] + X[2];
   end if;
   return Create_ModAbVarElt(Element(x)+Element(y), Parent(x), CommonFieldOfDefinition([* x,y *]));
end intrinsic;

intrinsic '-'(x::ModAbVarElt, y::ModAbVarElt) -> ModAbVarElt
{The difference x minus y.}
   if Parent(x) ne Parent(y) then
      X := PutInCommonParent([* x,y *]);
      return X[1] + X[2];
   end if;
   return Create_ModAbVarElt(Element(x)-Element(y), Parent(x), CommonFieldOfDefinition([* x,y *]));
end intrinsic;

intrinsic '*'(a::RngIntElt, x::ModAbVarElt) -> ModAbVarElt
{Product of the integer a by the element x.}
   return Create_ModAbVarElt(a*Element(x), Parent(x), FieldOfDefinition(x));
end intrinsic;

intrinsic '*'(a::FldRatElt, x::ModAbVarElt) -> ModAbVarElt
{Product of the rational number a by the element x.}
   return Create_ModAbVarElt(a*Element(x), Parent(x), FieldOfDefinition(x));
end intrinsic;


intrinsic '*'(a::FldReElt, x::ModAbVarElt) -> ModAbVarElt
{Product of the real number a by the element x.}
   e := Element(x);
   if IsOverQ(x) then
      e := VectorSpace(RR,Degree(x))!e;
   end if;
   return Create_ModAbVarElt(a*e, Parent(x), FieldOfDefinition(x));
end intrinsic;

intrinsic '*'(x::ModAbVarElt, a::RngIntElt) -> ModAbVarElt
{Product of the integer a by the element x.}
   return a*x;
end intrinsic;

intrinsic '*'(x::ModAbVarElt, a::FldRatElt) -> ModAbVarElt
{Product of the rational number a by the element x.}
   return a*x;
end intrinsic;

intrinsic '*'(x::ModAbVarElt, a::FldReElt) -> ModAbVarElt
{Product of the real number a by the element x.}
   require IsReal(a) : "Argument 2 must be real.";
   return a*x;
end intrinsic;


/***************************************************************************

  << Invariants >>

 ***************************************************************************/

intrinsic Degree(x::ModAbVarElt) -> RngIntElt
{The dimension of the homology of the parent of x.}
   return Degree(x`element);
end intrinsic;

intrinsic FieldOfDefinition(x::ModAbVarElt) -> ModTupFldElt
{A field that x is defined over, which need not be minimal.}
   return x`field_of_definition;
end intrinsic;


intrinsic Order(x::ModAbVarElt) -> RngIntElt
{The order of x, if x is known exactly.  Otherwise an
error occurs.}
   if IsOverQ(x) then
      return #Subgroup([x]);
   end if;
   require false : "Order not well-defined for elements defined by real"*
                   " homology; try ApproximateOrder instead.";
end intrinsic;

intrinsic ApproximateOrder(x::ModAbVarElt) -> RngIntElt
{Given a point x on a modular abelian variety return the exact order of x}
   if IsOverQ(x) then
      return Order(x);
   end if;
   return Order(ApproximateByTorsionPoint(x));
end intrinsic;


/***************************************************************************

  << Predicates >>

 ***************************************************************************/

intrinsic 'in'(x::ModAbVarElt, X::List) -> BoolElt
{True if x in an element of the list X.}
   return &or [x eq y : y in X];
end intrinsic; 

intrinsic IsExact(x::ModAbVarElt) -> BoolElt
{True if x is known exactly, i.e., x is defined by an element
of the rational homology.}
   return IsOverQ(x);
end intrinsic;

intrinsic IsZero(x::ModAbVarElt) -> BoolElt
/*ALT_DOC
True if x is known exactly and is equal to 0.  If x is
not known exactly, true if a real homology vector that
represents x is "very close" to an element of the integral
homology, where very close means that the distance is
within $1/10^n$, where {\tt n=M`point\_precision} and M is the 
parent of x.
END_ALT_DOC*/
{True if x is known exactly and is equal to 0.  If x is
not known exactly, true if a real homology vector that
represents x is "very close" to an element of the integral
homology.}
   L := IntegralHomology(Parent(x));
   if IsOverQ(x) then
      return Element(x) in L;
   end if;
   _, d := ClosestVectors(L, Element(x));
   return Abs(d) lt 10^(-Parent(x)`point_precision);
end intrinsic;

intrinsic 'eq'(x::ModAbVarElt, y::ModAbVarElt) -> BoolElt
{True if x equals y.}
   return (Parent(x) eq Parent(y)) and IsZero(x-y);
end intrinsic;



/***************************************************************************

  << Homomorphisms >>

 ***************************************************************************/


/* Homomorphisms */
intrinsic '@'(x::ModAbVarElt, phi::MapModAbVar) -> ModAbVarElt
{The image of x under the homomorphism phi.}
   if Domain(phi) eq Parent(x) then
      M := IsOverQ(x) select Matrix(phi) else RealMatrix(phi);
      y := Element(x)*M;
      return Create_ModAbVarElt(y, Codomain(phi), CommonFieldOfDefinition([* x,phi *]));
   end if;
   A := Parent(x);
   e := ModularEmbedding(A);
   if Codomain(e) eq Domain(phi) then
      return x*(e*phi);
   end if;
   require false: "The domain of phi must be the parent of argument 1.";
end intrinsic;

intrinsic '@@'(x::ModAbVarElt, phi::MapModAbVar) -> ModAbVarElt
{An inverse image of x under the homomorphism phi.}
   require Codomain(phi) eq Parent(x) : 
         "The codomain of phi must be the parent of argument 1.";
   M := IsOverQ(x) select Matrix(phi) else RealMatrix(phi);
   t, y := IsConsistent(M,Element(x));
   require t : "Argument 1 is not in the image of argument 2.";
   return Create_ModAbVarElt(y, Domain(phi), CommonFieldOfDefinition([* x,phi *]));
end intrinsic;


/***************************************************************************

  << Representation of Torsion Points >>

 ***************************************************************************/

intrinsic Eltseq(x::ModAbVarElt) -> SeqEnum
{A sequence of rational or real numbers that defines x.}
   return Eltseq(x`lattice_element);
end intrinsic;

intrinsic Element(x::ModAbVarElt) -> ModTupFldElt
{The vector in homology that represents x.}
   return x`element;
end intrinsic;

intrinsic LatticeCoordinates(x::ModAbVarElt) -> ModTupFldElt
{A vector over the rational or real field that represents x
with respect to the homology of the parent abelian variety of x.}
   if not assigned x`lattice_element then
      H := Homology(Parent(x));
      if IsOverQ(x) then
         x`lattice_element := x`element*BasisChange_Rational_to_Lattice(H);
      else
         x`lattice_element := x`element*BasisChange_Real_to_Lattice(H); 
      end if;
   end if;
   return x`lattice_element;
end intrinsic;

intrinsic ApproximateByTorsionPoint(x::ModAbVarElt : Cutoff:=10^3) -> ModAbVarElt
{If x is defined by an element z in the real homology H_1(A,R), use
continued fractions to find an element of H_1(A,Q) that approximates
z, and return  corresponding point.}
   if IsOverQ(x) then
      return x;
   end if;
   e := Eltseq(x);
   v := [ApproximateRational(a,Cutoff) : a in e];
   return Parent(x)!v;
end intrinsic;


function Create_ModAbVarElt(element, parent, field_of_definition)
   assert Type(element) eq ModTupFldElt;
   assert Type(parent) eq ModAbVar;
   assert IsDefnField(field_of_definition);
   assert Dimension(Homology(parent)) eq Degree(element);

   x := New(ModAbVarElt);
   x`element := element;
   if Type(BaseRing(Parent(element))) eq FldRat then
      C := BasisChange_Rational_to_Lattice(Homology(parent));
   else 
      C := BasisChange_Real_to_Lattice(Homology(parent));
   end if;
   x`lattice_element := element*C;
   x`parent := parent;
   x`field_of_definition := field_of_definition;
   if x`element eq 0 and Characteristic(field_of_definition) eq 0 then
      x`field_of_definition := QQ;
   end if;
   return x;
end function;

function Create_ModAbVarElt_Zero(A)
   assert Type(A) eq ModAbVar;
   H := Homology(A);
   return Create_ModAbVarElt(VectorSpace(H)!0, A, QQ);
end function;

intrinsic Parent(x::ModAbVarElt) -> ModAbVar
{The abelian variety that x is an element of.}
   return x`parent;
end intrinsic;

intrinsic Print(x::ModAbVarElt, level::MonStgElt)
{}
   if IsZero(x) then
      printf "0";
   else
      c := LatticeCoordinates(x);
      s := "[";
      for i in [1..Degree(c)] do
         s *:= Sprintf("%o%o",c[i],(i lt Degree(c) select " " else "]"));
      end for;
      printf "Element of abelian variety defined by %o modulo homology", s;
   end if;
end intrinsic;


function PutInCommonParent(X)
   // Put the elements of X in the direct product of their parents.
   // In the future, we may replace "direct product" by something more refined.
   // For example, if two parents are sub-abelian varieties of a common Jacobian,
   // put the two points in the common Jacobian. 
   if #X eq 0 then
      return X;
   end if;
   
   // 1. Find distinct ambient spaces of elements of X.
   D := [* Parent(X[1]) *];    // We use lists here, because we can only 
                       // define 'in' for lists (not sequences), as of June 2003.
   for i in [2..#X] do 
      B := Parent(X[i]);
      if not (B in D) then
         Append(~D, B);
      end if;
   end for;
   if #D eq 1 then
      return X;
   end if;
   S, embed, proj := DirectSum([x : x in D]);
   X2 := [*  *];   // doesn't work below to append if I use a sequence
   for x in X do
      for i in [1..#D] do
         if D[i] eq Parent(x) then
            Append(~X2,embed[i](x));
         end if;
      end for;
   end for;
   return [x : x in X2];  // I don't know why i have to do this.
end function;

intrinsic 'in'(x::ModAbVarElt, A::ModAbVar) -> BoolElt
{}
   return Parent(x) eq A;
end intrinsic;

