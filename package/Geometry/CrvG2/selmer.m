freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/**************************
 * Hyperelliptic/selmer.m *
 *                        *
 * Compute 2-Selmer group *
 *                        *
 * Michael Stoll          *
 *                        *
 * started 18-Oct-1998    *
 **************************/

/*----------------------------------------------------------------
  TO DO
  
    Use better way of finding local images
     - higher degree divisors
    
    Replace m2 by applying the projection V1 -> V2 after the computation
    
    Use tuples instead of lists
   


  CHANGES

  M. Stoll, 2000-08-12
  
    Removed obsolete code
    
    Corrected MakeIsSquare(RngOrdIdl) -- in residue characteristic 2,
      the element was not normalized.
    
    Added some comments
    
    Small correction in CasselsKernel (d ne 0 --> not IsSquare(d))
    
    New deterministic algorithm for determining part of the local image
      in the odd degree case (image of degree 1 divisors).
    
    TwoSelmerGroupData now transforms the curve if necessary to ontain
      the required form.
 
    Corrected problems with real precision (must get correct sign under
      real embeddings)
    
    Some corrections in TwoSelmer... regarding Points
  
  M. Stoll, 2000-08-16:
  
    Moved BadPrimes to curve.m and jacobian.m
  
  2000-08-18:
  
    Now using infinite precision p-adic rings to avoid factorisation
      errors.
  
  2000-08-25:
  
    Using better way for local images also in the even degree case
      (for degree 1 divisors).
  
  2000-09-28:
  
    Fixed some bugs in ImageOfDelta2. (Thanks to Nils Bruin)
    
    Fixed a bug in TwoSelmerGroupData -- Points were not moved to new
      Jacobian when model is changed. (Thanks to Nils Bruin)
    
    Added a fourth return value to TwoSelmerGroupData -- the list of
      the fields used.
    
    Added BachBound and MinkowskiBound for the rational field.
  
  2000-09-29:
  
    Modified the 2-Selmer group algorithm, following a suggestion of
      Nils Bruin. It is now possible to pass a set/sequence of number
      fields to it for use in the computation. If none of the fields
      matches, the OptimalRepresentation given by Magma is used.
      The fourth return value is now a set, to be compatible with
      the format for the Fields parameter.
  
  2000-10-01:
  
    Fixed some bugs introduced two days ago:
      (1) A field could be chosen that was a strict superfield of the
          field we want.
      (2) The mapping from the fields back to polynomials was not
          updated to take account of the fact that theta is not
          necessarily the generator of the field.
  
    Changed depth-first search in ImageOfDelta2 into breadth-first search.
      This should be faster in most cases where the image of the points
      on the curve is already everything.
  
  2001-05-14:
  
    Fixed a bug with ImageOfDelta in the even degree case -- when f
      was not monic, f/lcf(f) was used instead of f.
      Thanks to Nils Bruin.
  
    Changed UnitGroup() into pFundamentalUnits( ,2); this is faster.
  
  2001-05-25:
  
    Introduced signatures for TorsionUnitGroup and pFundamentalUnits
      to deal with rational field. Thanks to Nils Bruin.
  
    Fixed a couple of bugs in the auxiliray functions used in IsDeficient.
      Thanks to Nils Bruin.

  David Kohel, 2001-06-28:

  Included the change of model (ModelForTSG) from models.m as a
  local function, and updated the few instances of isomorphism
  creation.


  2001-07: scheme merge. PL.
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
                 Curve fix
  
  Michael Stoll, 2001-09-18
  
    Fixed a few bugs introduced with the new version, e.g.
    + MinimalInteger --> Minimum  (MinimalInteger has become obsolete)
    + Transformation in ModelForTSG
    + Workaround for EVIL BUG (two HC's are always considered equal)
  
  2001-09-18: David Kohel

    + Moved Minimum out to FldRat directory.
    + Slight renormalization in ModelForTSG
    + Evil bug and workaround removed

  2002-11-19: Nils Bruin
  
    + Trying to move rep. back to input curve for SelmerGroupData if
    input curve is of form y^2=f(x).

  2002-12-16: Nils Bruin

    + In IsDef1, changed StollsNewtonPolygon(...) to
    DefiningPoints(StollsNewtonPolygon(...)). Apparently, a separate type for newton
    polygons has been introduced in the mean time.
    + Happy change: in MakeTry, 2-adic case, ripped out HasRoots and put in
    calls to my code SquareFreePart and SquareFreeRoots. Cut exec time by
    A LOT.
    + And made the ring finite precision in order to let SquarefreeRoots
    work properly. Once a proper HasRoots is implemented, changeback
    recommended.
  
  2002-02-24: Nils Bruin
  
    + NewtonPolygon in this package renamed to StollsNewtonPolygon
    due to incompatibility with newly introduced NewtonPolygon intrinsics
    + Changed StollsNewtonPolygon to a function, calling the intrinsic
    NewtonPolygon, provided by the system.

  2002-02-27: Nils Bruin
    + LocalImageOdd: Precision on pAdicRing increased. This seems to be
    necessary to get good results with the new local package:
    (example curve that failed: y^2 = x^5 - 1766*x^3 - 1764*x^2 - 440*x)
    Once factorisation has been redone this can perhaps be reconsidered

  2002-04-11: Nils Bruin
    + dseq:=[1..Minimum(2,g)] in order to avoid producing divisor classes
    of degree larger than 2. 
    The curve
    y^2=4455516*x^9 + 4626882*x^8 + 3031860*x^7 + 1183845*x^6 - 356616*x^5 -
           721188*x^4 - 435240*x^3 - 149175*x^2 - 31590*x - 3159
    (strongly believe the returned bounds should be 5,7)
    was returning inconsistent answers. It seems to be stable now. However, it
    still seems rather slow. Awaiting other strategies, we just restrict to
    degree 1,2 divisor classes and hope for the best ...
    
    + turned off "new" searching (systematic searching) for degree 1 divisors
    for degree(f) gt 6 because that seems to be rather slow then (much slower
    than the random approach)

  2005-03-04: Nicole Sutherland
    Update for changes due to use of mpfr real fields instead of the pari reals.

  2005-11, Steve:

    Quick patch in MakeTry to fix a bug: in some examples
    (such as y^2 = (x^2+31)*(x^4+31^2) ), the program
    could not find enough p-adic points on the Jacobian
  
  2006-1, Steve:
     
    Provided HasSquareSha is an alternative name for IsEven.

    Provided simpler optional parameters in TwoSelmerGroupData for
    controlling the class group computation. 
    The old options still work, but are no longer documented.
    The new options are 
       Bound := RngIntElt, or
       BachBound := BoolElt, or
       BachBoundFrac := FldRatElt
    (specify only one of them).
    See the handbook for details.

    Change to the old optional parameters in TwoSelmerGroupData 
    for nonrigorous class groups:
    The option BoundType := "Relative" (in the old system) 
    has been "corrected" so that the Bound in ClassGroup is set to be
       constant*Log(Disc(K))^2 
    instead of 
       constant*Log(Disc(K))
    (so that it is a constant multiple of the Bach bound). 


  2006-5, Steve

    In V2.13, TwoSelmerGroupData is no longer a publicized intrinsic
    (although it will remain available). The official way to use it
    will be to call TwoSelmerGroup (a new intrinsic as an interface)
    with Al:="TwoSelmerGroupData" (which is the default, although that may change).

  *****  CHANGES NOT COMPLETELY INTERNAL TO TwoSelmerGroupData  *****
         SHOULD IN FUTURE BE LOGGED IN CrvHyp/selmer_main.m

    Also, I have finally started using pSelmerGroup for the class/unit stuff.
    One consequence is that the vararg UseUnits has been removed.
    At the moment, the computation is done the old way too, as a check
    on correctness and on timings.
    (The old stuff will be taken out in a patch release fairly soon 
    after release of V2.13.)
    If, for the moment, you want to only do things the old way, set 
    compare_new_vs_old := false;
    in the first line of TwoSelmerGroupData, below.


  2007-1, Steve 

    In HasPoint(f,p): fixed infinite recursion bug in Brumer's example
    > HasPoint(-3*x^6+4*x^5-4*x^4-14*x^3+8*x^2+8*x-3,2);

    Added a case in (the function created in) MakeTry() to deal with
    the possibility that a random pair of conjugate quadratic x-values
    have the same y-value. This came up in Brumer's example
    > TwoSelmerGroup(Jacobian(HyperellipticCurve(x^6+4*x^5-10*x^3+4*x^2+8*x-7)));

  2007-11, MS
   Fixed a bug in IsDef1h (could lead to rank bound too low or too high by 1, 
   since Jacobian was reported wrongly to be odd or even).  Example: 
   > HasSquareSha(Jacobian(HyperellipticCurve(-x^6-2*x^5+2*x^4+2*x^3-x^2-3*x+2)));

  2007-11, Steve
   Now sorted the 2-Selmer data correctly (independent elements first).
   The map returned by TwoSelmerGroup should now send the group generators
   to independent elements in A* / Q*A^2

  2008-07, Steve
   Fix MyResidueClassField for rel exts (use Valuation instead of RamificationDegree)

  2008-12 Nicole Sutherland
   Replace FldPr by FldRe

  2012-01 Brendan
   Fixed IsDeficient() and added more functionality for higher genus

 ----------------------------------------------------------------*/

// Nicely formatted output of sequences

procedure PrintBasis(B, indent)
  for b in B do
    printf " "^indent*"%o\n", b;
  end for;
end procedure;

// Some preliminary stuff on classes mod squares in p-adic fields

// Find smallest positive integer d such that d*x is integral.
function Denom(x)
  // x::FldNumElt
  // f := AbsoluteMinimalPolynomial(x);
  // return LCM([Denominator(c) : c in Coefficients(f)]);
  den1 := LCM([Denominator(c) : c in Eltseq(x)]);
  O := Integers(Parent(x));
  x1 := O!(den1*x);
  num := GCD(den1, GCD(ChangeUniverse(Eltseq(x1), Integers())));
  return ExactQuotient(den1, num), O!(x1/num);
end function;

function MyResidueClassField(pid)
  // Given a prime ideal, returns the residue field Order(pid)/pid
  // together with the reduction map from the ring of pid-integral
  // elements in the corresponding number field to the residue field. 
  // This map has an inverse.

// Type checking on two possible argument types:

if ISA(Type(pid), RngOrdIdl) then
  // return ResidueClassField(Order(pid), pid);
  O := Order(pid);
  K := FieldOfFractions(O);
  F, m := ResidueClassField(O, pid);
  p := Minimum(pid);
  e := ChineseRemainderTheorem(pid, ideal<O|O!p>/pid^Valuation(p,Place(pid)),
                               O!1, O!0);
  f := function(x)
         if x eq 0 then return F!0; end if;
         v := Valuation(x, pid);
         error if v lt 0, 
               "Error in reduction modulo a prime ideal:",
                x, "is not integral with respect to", pid;
         if v gt 0 then return F!0; end if;
         den := Denom(x);
         v := Valuation(den, p);
         y := x * e^v; // y is now p-integral and = x mod pid
         den := Denom(y);
         error if den mod p eq 0,
               "Something´s wrong in MyResidueClassField in selmer.m!";
         return m(O!(den*y))/F!den;
       end function;
  return F, map< K -> F | x :-> f(x), y :-> y @@ m >;
elif Type(pid) eq RngInt then
  O := Integers();
  K := FieldOfFractions(O);
  p := Generator(pid);
  // require IsPrime(p): "The ideal must be a prime ideal.";
  F, m := ResidueClassField(O, pid);
  f := function(x)
         if x eq 0 then return F!0; end if;
         v := Valuation(x, p);
         error if v lt 0, 
               "Error in reduction modulo a prime ideal:",
                x, "is not integral with respect to", pid;
         if v gt 0 then return F!0; end if;
         return (F!Numerator(x))/F!Denominator(x);
       end function;
  return F, map< K -> F | x :-> f(x), y :-> y @@ m >;
end if;
  error if false, "Unrecognized argument in MyResidueClassField";
end function;


// We represent a p-adic field by the following data:
// + a number field K;
// + a prime ideal in O, the integers of K, lying above p.
// From these, we deduce
// + a uniformizer;
// + a homomorphism K^* -->> finite elementary abelian 2-group with
//   kernel the elements that are squares in the completion.

// Return the map  K^* -> a GF(2)-vector space 
function MakeModSquares(K, pid)
  // (K::FldNum, pid::prime ideal in K) -> ModTupFld, Map
  O := Integers(K);
  p := Minimum(pid);
  e := RamificationIndex(pid, p);
  f := Degree(pid);
  _, pi := TwoElementNormal(pid);
  F, m := MyResidueClassField(pid);
  if IsOdd(p) then
    V := KSpace(GF(2), 2); // the codomain of our homomorphism
    h := map< K -> V | x :-> V![GF(2) | v, IsSquare(m(y)) select 0 else 1]
                             where y := x/(pi^v)
                             where v := Valuation(x, pid)>;
  else
    // p = 2
    
    // c is a pid-adic square and a pid-unit, but lies in all other
    // prime ideals above 2 in O. 
    c := ChineseRemainderTheorem(pid^(2*e+1), ideal<O | O!2>/pid^e, O!1, O!0);
    // Our elementary abelian 2-group K_pid^*/(K_pid^*)^2 has rank 2 + e*f.
    V := KSpace(GF(2), 2 + e*f);
    // A pid-unit is a square in K_pid iff it is a square in R.
    R := quo<O | pid^(2*e+1)>;
    // reps is a lift to O of an F_2-basis of F.
    reps := [ R!((F![ i eq j select 1 else 0 : i in [1..f] ]) @@ m)
               : j in [1..f] ];
    // A basis of pid-units modulo squares is given by
    //  [ 1 + r*pi^(2*i-1) : r in reps, i in [1..e] ] cat [ unr ] ,
    // where unr = 1 + 4*u such that the absolute trace of the image
    // of u in the residue field is non-zero. Together with pi itself,
    // we get a basis of pid-adics modulo squares.
    sc := function(y) // y in K is a pid-unit
            r := [GF(2) | ];
            // Make y integral without changing its class mod squares
            dy := Denom(y);
            if IsEven(dy) then
              y *:= c^Valuation(dy, 2);
              dy := Denom(y);
              error if IsEven(dy),
                    "Something is wrong in MakeModSquares in selmer.m!";
            end if;
            y := (dy mod 8)*O!(dy*y);
            z := (R!y)^(2^f-1); // put it into 1 + pid
            for i := 1 to e do
              // Determine contribution of (1 + ?*pi^(2*i-1))
              seq := Eltseq(m((K!O!(z - 1))/pi^(2*i-1)));
              r cat:= seq;
              for j := 1 to f do
                if seq[j] ne 0 then
                  z *:= 1 + reps[j]*(R!pi)^(2*i-1);
                end if;
              end for;
              if i lt e then
                // Determine contribution of (1 + ?*pi^i)^2
                z2 := Sqrt(m((K!O!(z - 1))/pi^(2*i)));
                z *:= (1 + (R!(z2 @@ m))*(R!pi)^i)^2;
              else
                // Determine unramified contribution
                r cat:= [AbsoluteTrace(m((K!O!(z - 1))/K!4))];
              end if;
            end for;
            return r;
          end function; 
    h := map< K -> V | x :-> V!([GF(2) | v] cat sc(x/pi^v))
                             where v := Valuation(x, pid)>;
  end if;
  return V, h;
end function;    


// This function returns a function that, given an element x of O, returns
// as a first value true or false, depending on whether x is a square in
// the completion of O at pid or not. A second value is returned when the
// first vakue is false; it indicates modulo which power of the uniformizer
// it can be recognized that x is a non-square.
intrinsic MakeIsSquare(pid::RngOrdIdl) -> UserProgram
{ Given a prime ideal in some order O, return a function that decides
  whether its argument (an element of O) is a square in the completion
  of O at pid. }
  O := Order(pid);
  p := Minimum(pid);
  e := RamificationIndex(pid, p);
  f := Degree(pid);
  _, pi := TwoElementNormal(pid);
  F, m := ResidueClassField(pid); // works OK for RngOrdIdl's
  if IsOdd(p) then
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, pid);
             if IsEven(v) then return IsSquare(m(x/pi^v)), v+1;
             else return false, v+1;
             end if;
           end function;
  else
    // p = 2
    R := quo<O | pid^(2*e+1)>;
    K := FieldOfFractions(O);
    // c is a pid-adic square and a pid-unit, but lies in all other
    // prime ideals above 2 in O. 
    c := ChineseRemainderTheorem(pid^(2*e+1), ideal<O | O!2>/pid^e, O!1, O!0);
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, pid);
             if IsOdd(v) then return false, v+1; end if;
             // Normalize
             y := (K!x)/pi^v;
             // Make y integral without changing its class mod squares
             dy := Denom(y);
             if IsEven(dy) then
               y *:= c^Valuation(dy, 2);
               dy := Denom(y);
               error if IsEven(dy),
                     "Something is wrong in MakeIsSquare in selmer.m!";
             end if;
             y := (dy mod 8)*O!(dy*y);
             z := (R!y)^(2^f-1); // put it into 1 + pid            
             for i := 1 to e do
               if Valuation(O!(z-1), pid) lt 2*i then
                 // There is some contribution of (1 + ?*pi^(2*i-1))
                 return false, v + 2*i;
               end if;
               z1 := (K!O!(z - 1))/pi^(2*i);
               if i lt e then
                 // Eliminate contribution of (1 + ?*pi^i)^2
                 z *:= (1 + (R!(Sqrt(m(z1)) @@ m))*(R!pi)^i)^2;
               elif AbsoluteTrace(m(z1)) ne 0 then
                 // We have an unramified non-square
                 return false, v + 2*e + 1;
               end if;
             end for;
             return true, _;
           end function;
  end if;
end intrinsic;    

intrinsic MakeIsSquare(p::RngIntElt) -> UserProgram
{ Given a prime number p, return a function that decides
  whether its argument (an integer) is a square in Z_p. }
  require IsPrime(p): "p must be a prime number";
  if p eq 2 then
    return function(x)
             if x eq 0 then return true, _; end if;
             v := Valuation(x, 2);
             if IsOdd(v) then return false, v+1; end if;
             x /:= 2^v;
             x := Numerator(x)*Denominator(x);
             if x mod 4 eq 3 then return false, v+2; end if;
             if x mod 8 eq 5 then return false, v+3; end if;
             return true, _;
           end function;
 else
   return function(x)
            if x eq 0 then return true, _; end if;
            v := Valuation(x, p);
            if IsOdd(v) then return false, v+1; end if;
            x /:= p^v;
            x := Numerator(x)*Denominator(x);
            return IsSquare(GF(p)!x), v+1;
          end function;
  end if;
end intrinsic;

intrinsic MakeIsSquare(I::RngInt) -> UserProgram
{ Given a prime ideal pZ in the integers, return a function that decides
  whether its argument (an integer) is a square in Z_p. }
  return MakeIsSquare(Generator(I));
end intrinsic;

// Compute the Newton polygon of a polynomial

function StollsNewtonPolygon(f, p)                                              
   N := NewtonPolygon(f, p);                                                    
   return [<Integers()!a[1],Integers()!a[2]>: a  in LowerVertices(N)];
end function;                                                                   

// We first need a procedure to find the deficient places for a curve
// (of genus 2 over Q). Recall that a place v is called deficient for
// the curve C if there are no points in C(K) for all odd degree extensions
// K of Q_v.

intrinsic HasPoint(f::RngUPolElt, pid::RngOrdIdl) -> BoolElt
{ Tests whether the curve y^2 = f(x), where f has coefficients
  coercible into O = Order(pid), has a point with x-coordinate
  in the p-adic ring given by completing O at pid. }
    require IsPrime(pid): "pid must be a prime ideal.";
    O := Order(pid);
    issq := MakeIsSquare(pid);
    _, pi := TwoElementNormal(pid);
    pi := O!pi;
    F, m := ResidueClassField(O, pid);
    R := [ a @@ m : a in F ];
    P := PolynomialRing(O);
    x := P.1;
    f := P!f;
    function HasPointRec(fx)
      test, v := issq(O!Coefficient(fx, 0));
      if test then return true; end if;
        // A general non-local exit construct would be nice here...
      vf := Min([Valuation(c, pid) : j in [1..Degree(fx)]
                  | c ne 0 where c := O!Coefficient(fx, j)]);
      if vf ge v then return false; end if;
      // TO DO: may need to randomise R ... see comment below in HasPoint(f,p)
      return exists{ r : r in R | HasPointRec(Evaluate(fx, pi*x + r)) };
    end function;
    return HasPointRec(f);
end intrinsic;

intrinsic HasPoint(f::RngUPolElt, p::RngIntElt) -> BoolElt
{ Tests whether the curve y^2 = f(x), where f has integral coefficients,
  has a point with x-coordinate in the p-adic integers. }
    require IsPrime(p): "p must be a prime number.";
    issq := MakeIsSquare(p);
    Z := Integers();
    x := Parent(f).1;
    function HasPointRec(fx)
      test, v := issq(Z!Coefficient(fx, 0));
      if test then return true; end if;
        // A general non-local exit construct would be nice here...
      vf := Min([Valuation(c, p) : j in [1..Degree(fx)]
                  | c ne 0 where c := Z!Coefficient(fx, j)]);
      if vf ge v then return false; end if;
      // Steve's fix: randomize this to avoid infinite recursion that can occur 
      // when the substitutions happen to zoom in on a (rational or p-adic) zero. 
      //return exists{ r : r in [0..p-1] | HasPointRec(Evaluate(fx, p*x + r)) };
      residueclasses := [k] cat [0..k-1] cat [k+1..p-1] where k := Random(p-1);
      return exists{ r : r in residueclasses | HasPointRec(Evaluate(fx, p*x + r)) };
    end function;
    return HasPointRec(f);
end intrinsic;

// The ramified extensions of degree 3 of Q_2

P := PolynomialRing(Rationals());
X := P.1;

K21 := NumberField(X^3 + X + 1);
O21 := Integers(K21);
p21 := Decomposition(O21, 2)[1,1];

K22 := NumberField(X^3 - 2);
O22 := Integers(K22);
p22 := Decomposition(O22, 2)[1,1];

// The ramified extensions of degree 3 of Q_3

ramifiedExtensions3 :=
 [ f(pol) : pol in [ X^3 + 3*X - 3, X^3 - 3*X - 3, X^3 - 3*X^2 - 3,
                     X^3 + 3*X^2 - 3, X^3 + 3*X^2 + 6, X^3 + 3*X^2 - 12,
                     X^3 - 3, X^3 + 6, X^3 - 12 ] ]
 where f := func< pol | [* pid, pr *]
                        where _, pr := TwoElementNormal(pid)
                        where pid := Decomposition(O, 3)[1,1]
                        where O := Integers(NumberField(pol)) >;

forward IsDef2;
forward IsDef1h;
forward IsDef2h;

function IsDef1(f, p)
  // Determine whether there is some x in the maximal ideal of an odd degree
  // extension of Q_p such that f(x) is a square. f has integral coefficients,
  // p is odd. 
  vprintf Selmer, 3: " IsDef1(%o, %o)\n", f, p;
  f := PolynomialRing(Integers())!f; // to be safe
  // a function that tests whether an integer x is a p-adic square
  issq := function(x)
            x := Integers()!x;
            if x eq 0 then return true; end if;
            v := Valuation(x, p);
            if IsOdd(v) then return false; end if;
            return IsSquare(GF(p)!(x div p^v));
          end function;
  // if trailing coefficient is a square --> OK (x = 0)
  if issq(Coefficient(f, 0)) then return true; end if;
  np := StollsNewtonPolygon(f, p);
  vprintf Selmer, 3: "  Newton Polygon = %o\n", np;
  for i := 1 to #np-1 do
    // slope non-negative --> zeroes have non-positive valuation
    if np[i+1,2] ge np[i,2] then break; end if;
    // segment of odd length or square coefficient at vertex --> OK
    if IsOdd(np[i+1,1] - np[i,1]) or issq(Coefficient(f, np[i+1,1])) then
      return true;
    end if;
  end for;
  // Now look at the segments (all of even length) in turn
  for i := 1 to #np-1 do
    // stop when slope becomes non-negative
    if np[i+1,2] ge np[i,2] then break; end if;
    slope := (np[i,2]-np[i+1,2])/(np[i+1,1]-np[i,1]);
    den := Denominator(slope);
    num := Numerator(slope);
    // solution only possible when denominator is odd
    if IsOdd(den) then
      case den:
        when 1:
          // zoom in on segment
          if IsDef2(Evaluate(f, p^num*Parent(f).1), p) then return true;
          end if; 
        when 3:
          // zoom in on segment; need to look at ramified degree 3 extensions
          case p mod 3:
            when 0:
              // p = 3: check all ramified extensions directly
              for rext in ramifiedExtensions3 do
                P := PolynomialRing(Order(rext[1]));
                if HasPoint(Evaluate(f, rext[2]^num*P.1), rext[1])
                  then return true;
                end if;
              end for;
            when 1:
              // p = 1 mod 3: three possible ramified extensions, but we
              // can decide which one to take
              v := np[2,2];
              a := Coefficient(f, 6) div p^v;
              b := Coefficient(f, 3) div p^(v+num);
              c := Coefficient(f, 0) div p^(v+2*num);
              u := Integers()!(GF(p)!(a*(b^2-4*a*c)))^(2*num);
              K := NumberField(X^3 - u*p);
              O := Integers(K);
              P := PolynomialRing(O);
              pid := Decomposition(O, p)[1,1];
              if IsDef2h(Evaluate(f, (O!K.1)^Numerator(slope)*P.1), pid)
                then return true;
              end if;
            when 2:
              // P = 2 mod 3: only one ramified degree 3 extension
              K := NumberField(X^3 - p);
              O := Integers(K);
              P := PolynomialRing(O);
              pid := Decomposition(O, p)[1,1];
              if IsDef2h(Evaluate(f, (O!K.1)^Numerator(slope)*P.1), pid)
                then return true;
              end if;
            end case;
        else error "Something is wrong in IsDef1 in CrvG2/selmer.m!";
      end case;
    end if;
  end for;
  return false;
end function;

function IsDef2(f, p)
  // Determine whether there is some x in the units of an odd degree
  // extension of Q_p such that f(x) is a square. f has integral coefficients,
  // p is odd. 
  vprintf Selmer, 3: " IsDef2(%o, %o)\n", f, p;
  f := PolynomialRing(Integers())!f; // to be safe
  k := Min([ Valuation(c, p) : c in Eltseq(f) | c ne 0 ]);
  fred := PolynomialRing(GF(p))![ c/p^k : c in Eltseq(f) ];
  u := LeadingCoefficient(fred);
  fred := (1/u)*fred;
  // find irreducible factors with non-zero roots
  fact := [ x : x in Factorization(fred) | x[1] ne Parent(fred).1 ];
  if GetVerbose("Selmer") ge 3 then
    printf "  Factorization mod %o:\n   ", p;
    for pair in fact do
      printf " (%o)", pair[1];
      if pair[2] gt 1 then printf "^%o", pair[2]; end if;
    end for;
    printf "\n";
  end if;
  // valuation(f) even and lcf a square or irreducible factor
  // of odd multiplicity --> OK  [compare Poonen-Stoll]
  if IsEven(k) and (IsSquare(u) or exists{ x : x in fact | IsOdd(x[2]) }) then
    return true;
  end if;
  // odd degree factor over Q_p --> OK  [compare Poonen-Stoll]
  if exists{ x : x  in fact | IsOdd(Degree(x[1])*x[2]) } then return true;
  end if;
  // otherwise look at the factors in turn
  for fe in fact do
    if IsOdd(Degree(fe[1])) then
      case Degree(fe[1]):
        when 1:
          // zoom in on factor
          if IsDef1(Evaluate(f, Parent(f).1-Integers()!Coefficient(fe[1],0)), p)
          then return true;
          end if;
        when 3:
          // zoom in on factor. have to take unramified degree 3 extension
//          K := NumberField(PolynomialRing(Rationals())!Eltseq(fe[1]));
          K := NumberField(PolynomialRing(Rationals())!
                              ChangeUniverse(Eltseq(fe[1]), Integers()));
          O := Integers(K);
          P := PolynomialRing(O);
          f := Evaluate(f, P.1 + (O!K.1));
          vprintf Selmer, 3: "  New f = %o\n", f;
          pid := ideal< O | O!p >;
          if IsDef1h(f, pid) then return true; end if;
        else error "Something is wrong in IsDef2 in CrvG2/selmer.m!";
      end case;
    end if;
  end for;
  return false;
end function;

function IsDef1h(f, pid)
  // Determine whether there is some x in pid such that
  // f(x) is a square in the completion at pid of its number field. 
  // f has pid-integral coefficients, pid is odd.
  vprintf Selmer, 3: " IsDef1h(%o, %o)\n", f, pid;
  O := Order(pid);
  _, pr := TwoElementNormal(pid);
  issq := MakeIsSquare(pid);
  if issq(Coefficient(f, 0)) then return true; end if;
  np := StollsNewtonPolygon(f, pid);
  vprintf Selmer, 3: "  Newton Polygon = %o\n", np;
  for i := 1 to #np-1 do
    // stop when slope becomes non-negative
    if np[i+1,2] ge np[i,2] then break; end if;
    // segment of odd length or square coefficient at vertex --> OK
    if IsOdd(np[i+1,1] - np[i,1]) or issq(Coefficient(f, np[i+1,1])) then
      return true;
    end if;
  end for;
  for i := 1 to #np-1 do
    // stop when slope becomes non-negative
    if np[i+1,2] ge np[i,2] then break; end if;
    slope := (np[i,2]-np[i+1,2])/(np[i+1,1]-np[i,1]);
    den := Denominator(slope);
    num := Numerator(slope);
    if IsOdd(den) then
      // solution only possible when denominator is odd
      case den:
        when 1:
          // zoom in on segment
          // corrected (MS, 2007-11-06) - was IsDef1h
          if IsDef2h(Evaluate(f, pr^num*Parent(f).1), pid) then
            return true;
          end if; 
        else error 
            "Something is wrong in IsDef1h in CrvG2/selmer.m!";
      end case;
    end if;
  end for;
  return false;  
end function;

function IsDef2h(f, pid)
  // Determine whether there is some x in O_pid^* such that
  // f(x) is a square in the completion at pid of its number field. 
  // f has pid-integral coefficients, pid is odd. 
  vprintf Selmer, 3: " IsDef2h(%o, %o)\n", f, pid;
  k := Min([ Valuation(c, pid) : c in Eltseq(f) | c ne 0 ]);
  _, pi := TwoElementNormal(pid);
  O := Order(pid);
  F, m := ResidueClassField(O, pid);
  mm := func< x | m(O!(den*x))/m(O!den) where den := Denominator(x) >;
  fred := PolynomialRing(F)![ mm(c/pi^k) : c in Eltseq(f) ];
  u := LeadingCoefficient(fred);
  fred := (1/u)*fred;
  // look at irreducible factors with non-zero roots
  fact := [ x : x in Factorization(fred) | x[1] ne Parent(fred).1 ];
  if GetVerbose("Selmer") ge 3 then
    printf "  Factorization mod pid:\n   ";
    for pair in fact do
      printf " (%o)", pair[1];
      if pair[2] gt 1 then printf "^%o", pair[2]; end if;
    end for;
    printf "\n";
  end if;
  // compare IsDef2
  if IsEven(k) and (IsSquare(u) or exists{ x : x in fact | IsOdd(x[2]) }) then
    return true;
  end if;
  if exists{ x : x in fact | IsOdd(Degree(x[1])*x[2]) } then return true;
  end if;
  for fe in fact do
    if Degree(fe[1]) eq 1 and IsDef1h(fnew, pid)
         where fnew := Evaluate(f, Parent(f).1 - (Coefficient(fe[1],0) @@ m))
      then return true;
    end if;
  end for;
  return false;
end function;

intrinsic IsDeficient(C::CrvHyp, p::RngIntElt) -> BoolElt
{ Tests whether C (a curve of genus 2 over the rationals) is deficient
  at p (p = 0 stands for the infinite place). This means that there
  is no point of odd degree over Q_p on C. }
  // Compare my talk in Nunspeet, March 1998
  require BaseField(C) cmpeq Rationals():
          "IsDeficient is currently only implemented for curves over",
          "the rationals.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0 and forall{ c : c in Eltseq(f) | IsIntegral(c) }:
          "IsDeficient is currently only implemented for curves of the form",
          "y^2 = f(x) where f has integral coefficients.";
  if IsOdd(Degree(f)) then return false; end if;
  if p ne 0 and Valuation(Integers()!Discriminant(C), p) le Genus(C)
    then return false;
  end if;
  if p eq 0 then
    // infinity
    fr := PolynomialRing(RealField())!f;
    return Coefficient(f, 0) lt 0 and LeadingCoefficient(f) lt 0
            and forall{ r[1] : r in Roots(fr) | not IsReal(r[1]) };
      // This should really be tested using a function like gp's polsturm
  end if;
  
  if Genus(C) gt 2 then
    //BMC added cases 3 le g le 6
    require Genus(C) le 6: 
    "IsDeficient is currently only fully implemented for curves",
    "of genus le 6.";
    return not HasIndexOne(f,2,p);
  end if;

// Now Degree(f) = 6;  

if p eq 2 then
  //BMC: Bug fix
  //fr := Evaluate(Parent(f)!Reverse(Eltseq(f)), 2*Parent(f).1);
  fr := Evaluate(Parent(f)!Reverse(Eltseq(f)), Parent(f).1);
  // it is true that one only needs to consider points
  // with x integral or with z in pi*O_K. I assume this was the
  // thought behind the change of variables z <- 2*z. 
  // But over the ramified degree 3 extension this means we are
  // looking for points in pi^3*O_K!
  //
  // An example where this fails: y^2 = -8*x^6 + 8*x^5 + 9*x^4 + 6*x^2 - 5
  // which has a point with x = (1/2)^(1/3)
  return not(HasPoint(f, 2) or HasPoint(fr, 2)
                or HasPoint(f, p21) or HasPoint(fr, p21)
                or HasPoint(f, p22) or HasPoint(fr, p22));
  end if;


 // now p is odd
  fr := Parent(f)!Reverse(Eltseq(f));
  return not(IsDef1(f, p) or IsDef2(f, p) or IsDef1(fr, p));
end intrinsic;

intrinsic HasSquareSha(J::JacHyp) -> BoolElt
{ Determines if J, the Jacobian of a curve (over the rationals),
  is even in the sense of Poonen-Stoll, i.e. if its Shafarevich-Tate group
  (supposed to be finite) has square order, or not. }
  return IsEven(J);
end intrinsic;

intrinsic IsEven(J::JacHyp) -> BoolElt
{ Determines if J, the Jacobian of a curve (over the rationals),
  is even in the sense of Poonen-Stoll, i.e. if its Shafarevich-Tate group
  (supposed to be finite) has square order, or not. }
  C := Curve(J);
  K := BaseField(C);
  require K cmpeq Rationals() or Category(K) eq FldNum :
          "IsEven is only implemented for Jacobians of curves over",
          "number fields.";
  // Jacobians of odd genus hyperelliptic cuvres are always even.
  if IsOdd(Genus(C)) then return true; end if;
  // If the curve has a rational point, then the Jacobian is even.
  if #PointsAtInfinity(C) gt 0 then return true; end if;
  require K cmpeq Rationals() :
          "IsEven is only fully implemented for Jacobians of curves over the",
          "rationals.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0 and forall{ c : c in Eltseq(f) | IsIntegral(c) }:
          "IsEven is only implemented for Jacobians of curves of the form",
          " y^2 = f(x)  where f has integral coefficients.";
  bad_primes := BadPrimes(C : Badness := Genus(C)+1);
  vprintf Selmer, 2:
          "IsEven(Jac(y^2 = %o)):\n  Bad primes = %o\n", f, bad_primes;
  def_primes := [ p : p in [0] cat bad_primes | IsDeficient(C, p) ];
  vprintf Selmer, 2 :
          "  Deficient places = %o\n", def_primes;
  return IsEven(#def_primes);
end intrinsic;

// Here are the resolvent polynomials we need to decide whether the kernel
// of the Cassels map may be larger than 2*J(Q).
// Resolvents[1] is used for irreducible f,
// Resolvents[2] is used for f = (deg 4)*(deg 2),
// Resolvents[3] is used for f = (deg 2)*(deg 2)*(deg 2).

R6 := PolynomialRing(Rationals(), 6);
PR6 := PolynomialRing(R6);

Resolvents :=
 [ // Case f irreducible with
   //  f = x^6 - a[6]*x^5 + a[5]*x^4 - a[4]*x^3 + a[3]*x^2 - a[2]*x + a[1]
   X^10 - a[4]*X^9 + (-9*a[1] - a[2]*a[6] + a[3]*a[5])*X^8 + (6*a[1]*a[4] +
    a[1]*a[5]*a[6] + a[2]*a[3] + 2*a[2]*a[4]*a[6] - a[2]*a[5]^2 -
    a[3]^2*a[6])*X^7 + (27*a[1]^2 + 9*a[1]*a[2]*a[6] - 9*a[1]*a[3]*a[5] +
    a[1]*a[3]*a[6]^2 + 3*a[1]*a[4]^2 - 3*a[1]*a[4]*a[5]*a[6] + a[1]*a[5]^3 +
    a[2]^2*a[5] - a[2]^2*a[6]^2 - 3*a[2]*a[3]*a[4] + a[2]*a[3]*a[5]*a[6] +
    a[3]^3)*X^6 + (-9*a[1]^2*a[4] - 3*a[1]^2*a[5]*a[6] - 2*a[1]^2*a[6]^3 -
    3*a[1]*a[2]*a[3] - 16*a[1]*a[2]*a[4]*a[6] + 4*a[1]*a[2]*a[5]^2 +
    2*a[1]*a[2]*a[5]*a[6]^2 + 4*a[1]*a[3]^2*a[6] + a[1]*a[3]*a[4]*a[5] +
    2*a[1]*a[3]*a[4]*a[6]^2 - a[1]*a[3]*a[5]^2*a[6] - 2*a[2]^3 +
    2*a[2]^2*a[3]*a[6] + 2*a[2]^2*a[4]*a[5] - a[2]^2*a[4]*a[6]^2 -
    a[2]*a[3]^2*a[5])*X^5 + (-27*a[1]^3 - 30*a[1]^2*a[2]*a[6] +
    18*a[1]^2*a[3]*a[5] - 2*a[1]^2*a[3]*a[6]^2 - 15*a[1]^2*a[4]^2 +
    16*a[1]^2*a[4]*a[5]*a[6] + a[1]^2*a[4]*a[6]^3 - 4*a[1]^2*a[5]^3 -
    a[1]^2*a[5]^2*a[6]^2 - 2*a[1]*a[2]^2*a[5] + 6*a[1]*a[2]^2*a[6]^2 +
    16*a[1]*a[2]*a[3]*a[4] - 3*a[1]*a[2]*a[3]*a[6]^3 - a[1]*a[2]*a[4]^2*a[6] -
    2*a[1]*a[2]*a[4]*a[5]^2 + a[1]*a[2]*a[4]*a[5]*a[6]^2 - 4*a[1]*a[3]^3 -
    2*a[1]*a[3]^2*a[4]*a[6] + a[1]*a[3]^2*a[5]^2 + a[2]^3*a[4] -
    3*a[2]^3*a[5]*a[6] + a[2]^3*a[6]^3 - a[2]^2*a[3]^2 +
    a[2]^2*a[3]*a[4]*a[6])*X^4 + (9*a[1]^3*a[6]^3 + 39*a[1]^2*a[2]*a[4]*a[6] -
    14*a[1]^2*a[2]*a[5]*a[6]^2 + a[1]^2*a[2]*a[6]^4 - 11*a[1]^2*a[3]*a[4]*a[6]^2
    + 2*a[1]^2*a[3]*a[5]*a[6]^3 - 3*a[1]^2*a[4]^3 + 3*a[1]^2*a[4]^2*a[5]*a[6] -
    a[1]^2*a[4]^2*a[6]^3 + 9*a[1]*a[2]^3 - 14*a[1]*a[2]^2*a[3]*a[6] -
    11*a[1]*a[2]^2*a[4]*a[5] + 6*a[1]*a[2]^2*a[4]*a[6]^2 +
    3*a[1]*a[2]^2*a[5]^2*a[6] - a[1]*a[2]^2*a[5]*a[6]^3 +
    3*a[1]*a[2]*a[3]^2*a[6]^2 + 3*a[1]*a[2]*a[3]*a[4]^2 -
    a[1]*a[2]*a[3]*a[4]*a[5]*a[6] + a[2]^4*a[6] + 2*a[2]^3*a[3]*a[5] -
    a[2]^3*a[3]*a[6]^2 - a[2]^3*a[4]^2)*X^3 + (36*a[1]^3*a[2]*a[6] -
    6*a[1]^3*a[3]*a[6]^2 + 18*a[1]^3*a[4]^2 - 24*a[1]^3*a[4]*a[5]*a[6] -
    4*a[1]^3*a[4]*a[6]^3 + 8*a[1]^3*a[5]^2*a[6]^2 - a[1]^3*a[5]*a[6]^4 -
    6*a[1]^2*a[2]^2*a[5] - 7*a[1]^2*a[2]^2*a[6]^2 - 24*a[1]^2*a[2]*a[3]*a[4] -
    4*a[1]^2*a[2]*a[3]*a[5]*a[6] + 10*a[1]^2*a[2]*a[3]*a[6]^3 +
    8*a[1]^2*a[2]*a[4]^2*a[6] + 8*a[1]^2*a[2]*a[4]*a[5]^2 -
    8*a[1]^2*a[2]*a[4]*a[5]*a[6]^2 + a[1]^2*a[2]*a[4]*a[6]^4 +
    8*a[1]^2*a[3]^2*a[4]*a[6] - 2*a[1]^2*a[3]^2*a[5]*a[6]^2 -
    2*a[1]^2*a[3]*a[4]^2*a[5] + a[1]^2*a[3]*a[4]^2*a[6]^2 - 4*a[1]*a[2]^3*a[4] +
    10*a[1]*a[2]^3*a[5]*a[6] - 4*a[1]*a[2]^3*a[6]^3 + 8*a[1]*a[2]^2*a[3]^2 -
    8*a[1]*a[2]^2*a[3]*a[4]*a[6] - 2*a[1]*a[2]^2*a[3]*a[5]^2 +
    a[1]*a[2]^2*a[3]*a[5]*a[6]^2 + a[1]*a[2]^2*a[4]^2*a[5] - a[2]^4*a[3] +
    a[2]^4*a[4]*a[6])*X^2 + (-8*a[1]^4*a[6]^3 - 24*a[1]^3*a[2]*a[4]*a[6] +
    16*a[1]^3*a[2]*a[5]*a[6]^2 - 2*a[1]^3*a[2]*a[6]^4 +
    8*a[1]^3*a[3]*a[4]*a[6]^2 - a[1]^3*a[3]*a[6]^5 + 8*a[1]^3*a[4]^3 -
    8*a[1]^3*a[4]^2*a[5]*a[6] + 3*a[1]^3*a[4]^2*a[6]^3 - 8*a[1]^2*a[2]^3 +
    16*a[1]^2*a[2]^2*a[3]*a[6] + 8*a[1]^2*a[2]^2*a[4]*a[5] -
    6*a[1]^2*a[2]^2*a[4]*a[6]^2 - 8*a[1]^2*a[2]^2*a[5]^2*a[6] +
    3*a[1]^2*a[2]^2*a[5]*a[6]^3 - 8*a[1]^2*a[2]*a[3]^2*a[6]^2 -
    8*a[1]^2*a[2]*a[3]*a[4]^2 + 8*a[1]^2*a[2]*a[3]*a[4]*a[5]*a[6] -
    a[1]^2*a[2]*a[3]*a[4]*a[6]^3 - a[1]^2*a[2]*a[4]^3*a[6] - 2*a[1]*a[2]^4*a[6]
    + 3*a[1]*a[2]^3*a[3]*a[6]^2 + 3*a[1]*a[2]^3*a[4]^2 -
    a[1]*a[2]^3*a[4]*a[5]*a[6] - a[2]^5*a[5])*X + 8*a[1]^4*a[4]*a[6]^3 -
    4*a[1]^4*a[5]*a[6]^4 + a[1]^4*a[6]^6 - 4*a[1]^3*a[2]*a[3]*a[6]^3 -
    12*a[1]^3*a[2]*a[4]^2*a[6] + 8*a[1]^3*a[2]*a[4]*a[5]*a[6]^2 -
    2*a[1]^3*a[2]*a[4]*a[6]^4 + a[1]^3*a[3]^2*a[6]^4 -
    2*a[1]^3*a[3]*a[4]^2*a[6]^2 + a[1]^3*a[4]^4 + 8*a[1]^2*a[2]^3*a[4] -
    4*a[1]^2*a[2]^3*a[5]*a[6] + 2*a[1]^2*a[2]^3*a[6]^3 +
    8*a[1]^2*a[2]^2*a[3]*a[4]*a[6] - 2*a[1]^2*a[2]^2*a[3]*a[5]*a[6]^2 -
    2*a[1]^2*a[2]^2*a[4]^2*a[5] + a[1]^2*a[2]^2*a[4]^2*a[6]^2 -
    4*a[1]*a[2]^4*a[3] - 2*a[1]*a[2]^4*a[4]*a[6] + a[1]*a[2]^4*a[5]^2 + a[2]^6,
   // Case f = g*h with
   //  g = x^4 - a[4]*x^3 + a[3]*x^2 - a[2]*x + a[1]  and
   //  h = x^2 - a[6]*x + a[5].
   X^6 - a[3]*a[6]*X^5 + (-4*a[1]*a[5] - a[1]*a[6]^2 - 2*a[2]*a[4]*a[5] +
    a[2]*a[4]*a[6]^2 + a[3]^2*a[5])*X^4 + (2*a[1]*a[3]*a[6]^3 +
    3*a[1]*a[4]^2*a[5]*a[6] - a[1]*a[4]^2*a[6]^3 + 3*a[2]^2*a[5]*a[6] -
    a[2]^2*a[6]^3 - a[2]*a[3]*a[4]*a[5]*a[6])*X^3 + (8*a[1]^2*a[5]*a[6]^2 -
    a[1]^2*a[6]^4 + 8*a[1]*a[2]*a[4]*a[5]^2 - 8*a[1]*a[2]*a[4]*a[5]*a[6]^2 +
    a[1]*a[2]*a[4]*a[6]^4 - 2*a[1]*a[3]^2*a[5]*a[6]^2 -
    2*a[1]*a[3]*a[4]^2*a[5]^2 + a[1]*a[3]*a[4]^2*a[5]*a[6]^2 -
    2*a[2]^2*a[3]*a[5]^2 + a[2]^2*a[3]*a[5]*a[6]^2 + a[2]^2*a[4]^2*a[5]^2)*X^2 +
    (-a[1]^2*a[3]*a[6]^5 - 8*a[1]^2*a[4]^2*a[5]^2*a[6] +
    3*a[1]^2*a[4]^2*a[5]*a[6]^3 - 8*a[1]*a[2]^2*a[5]^2*a[6] +
    3*a[1]*a[2]^2*a[5]*a[6]^3 + 8*a[1]*a[2]*a[3]*a[4]*a[5]^2*a[6] -
    a[1]*a[2]*a[3]*a[4]*a[5]*a[6]^3 - a[1]*a[2]*a[4]^3*a[5]^2*a[6] -
    a[2]^3*a[4]*a[5]^2*a[6])*X - 4*a[1]^3*a[5]*a[6]^4 + a[1]^3*a[6]^6 +
    8*a[1]^2*a[2]*a[4]*a[5]^2*a[6]^2 - 2*a[1]^2*a[2]*a[4]*a[5]*a[6]^4 +
    a[1]^2*a[3]^2*a[5]*a[6]^4 - 2*a[1]^2*a[3]*a[4]^2*a[5]^2*a[6]^2 +
    a[1]^2*a[4]^4*a[5]^3 - 2*a[1]*a[2]^2*a[3]*a[5]^2*a[6]^2 -
    2*a[1]*a[2]^2*a[4]^2*a[5]^3 + a[1]*a[2]^2*a[4]^2*a[5]^2*a[6]^2 +
    a[2]^4*a[5]^3,
   // Case f = g1*g2*g3 with
   //  g1 = x^2 - a[2]*x + a[1],
   //  g2 = x^2 - a[4]*x + a[3],
   //  g3 = x^2 - a[6]*x + a[5].
   X^4 - a[2]*a[4]*a[6]*X^3 + (-2*a[1]*a[3]*a[6]^2 - 2*a[1]*a[4]^2*a[5] +
    a[1]*a[4]^2*a[6]^2 - 2*a[2]^2*a[3]*a[5] + a[2]^2*a[3]*a[6]^2 +
    a[2]^2*a[4]^2*a[5])*X^2 + (8*a[1]*a[2]*a[3]*a[4]*a[5]*a[6] -
    a[1]*a[2]*a[3]*a[4]*a[6]^3 - a[1]*a[2]*a[4]^3*a[5]*a[6] -
    a[2]^3*a[3]*a[4]*a[5]*a[6])*X + a[1]^2*a[3]^2*a[6]^4 -
    2*a[1]^2*a[3]*a[4]^2*a[5]*a[6]^2 + a[1]^2*a[4]^4*a[5]^2 -
    2*a[1]*a[2]^2*a[3]^2*a[5]*a[6]^2 - 2*a[1]*a[2]^2*a[3]*a[4]^2*a[5]^2 +
    a[1]*a[2]^2*a[3]*a[4]^2*a[5]*a[6]^2 + a[2]^4*a[3]^2*a[5]^2 ]
  where a := [-(-1)^i*R6.i : i in [1..6]]
  where X := PR6.1;

// The following function takes the factorization of f (without 
// multiplicities -- they are known to be one) and returns
// three values. The first value if true if the Cassels kernel is guaranteed
// to equal 2*J(Q) and false otherwise. In this second case, the second
// value is the factorization of the resolvent (which is adjusted so as
// to be square-free) into factors in Z[x]. The third value gives a
// square-free integer d such that the quadratic subextension of L
// is Q(sqrt(d)), if such a subextension exists.
function CasselsKernel(fact)
  vprintf Selmer, 2: " CasselsKernel:\n";
  degrees := [ Degree(a) : a in fact ];
  P := Universe(fact);
  if exists{ d : d in degrees | IsOdd(d) } then
    vprint Selmer, 2 :
           "  Polynomial has factor of odd degree, hence kernel is 2*J(Q).";
    return true, [ PolynomialRing(Integers()) | ], _;
  end if;
  case degrees:
    when [6]:
      res := func< f | hom< PR6 -> P |
                            hom<R6 -> P | Eltseq(f[1])[1..6]>, P.1 >
                        (Resolvents[1]) >;
    when [4, 2]:
      res := func< f | hom< PR6 -> P |
                            hom<R6 -> P | Eltseq(f[1])[1..4]
                                           cat Eltseq(f[2])[1..2]>, 
                            P.1 >
                        (Resolvents[2]) >;
    when [2, 4]:
      res := func< f | hom< PR6 -> P |
                            hom<R6 -> P | Eltseq(f[2])[1..4] 
                                           cat Eltseq(f[1])[1..2]>, 
                            P.1 >
                        (Resolvents[2]) >;
    when [2, 2, 2]:
      res := func< f | hom< PR6 -> P |
                            hom<R6 -> P | Eltseq(f[1])[1..2]
                                           cat Eltseq(f[2])[1..2]
                                           cat Eltseq(f[3])[1..2]>, 
                            P.1 >
                        (Resolvents[3]) >;
  end case;
  while true do
    rfact := Factorization(res(fact));
    if exists{ r : r in rfact | Degree(r[1]) eq 1 and r[2] eq 1 } then
      vprint Selmer, 2:
             "  Resolvent has a simple rational root, hence kernel is 2*J(Q).";
      f0 := &*[ Coefficient(a, 0) : a in fact ];
      d := 0;
      while d eq 0 do
        for r in [ -Coefficient(a[1], 0) : a in rfact
                              | Degree(a[1]) eq 1 and a[2] eq 1 ] do
          d := Integers()!(r^2 - 4*f0);
          if not IsSquare(d) then break; end if;
        end for;
        if not IsSquare(d) then
          return true, [ PolynomialRing(Integers()) | ], SquarefreeFactorization(d);
        else
          vprint Selmer, 2:
                 "  Can't determine quadratic subfield. Compute new resolvent.";
          fact := [ Evaluate(f, P.1 + 1) : f in fact ];
          rfact := Factorization(res(fact));
        end if;
      end while; // d eq 0
    elif forall{ r : r in rfact | r[2] eq 1 } then
      vprint Selmer, 2:
             "  Resolvent is square-free and has no rational root,";
      vprint Selmer, 2:
             "   hence the kernel of the Cassels map may be larger than 2*J(Q).";
      return false, [ PolynomialRing(Integers()) | r[1] : r in rfact ], _;
    else
      vprint Selmer, 2:
             "  Resolvent is not square-free. Compute new resolvent.";
      fact := [ Evaluate(f, P.1 + 1) : f in fact ];
    end if;
  end while;
end function;


// 2-descent in the odd degree case

// This function generates a function that generates random p-adic
// points on the Jacobian. Let try_func be the result of MakeTry. Then
// try_func() returns a polynomial that is the first component of a p-adic
// point on the (interesting part of the) Jacobian.
function MakeTry(f, p, nu, deg)
  lcf := LeadingCoefficient(f);
  d := Degree(f);
  g := (d - 1) div 2;
  PZ := PolynomialRing(Rationals());   // was Integers()
  P := Parent(f);
  PP := PolynomialRing(P);
  PPZ := PolynomialRing(PZ);
  PtoPP := hom<P -> PP | PP.1>;
  PZtoPPZ := hom<PZ -> PPZ | PPZ.1>;
  dseq := IsOdd(Degree(f)) or lcf eq 1 
          select [deg..Minimum(2,g)] else [2*Ceiling(deg/2)..g by 2];
  numin := Min([ Valuation(c, p)/(d - j) : j in [0..d-1] | c ne 0
                  where c := Coefficient(f, j)/lcf ]);
  numin := Ceiling(numin);
  vprintf Selmer, 3: "     MakeTry(p = %o, nu = %o):\n", p, nu;
  nu -:= numin;
  vprintf Selmer, 3: "       numin = %o, new nu = %o.\n", numin, nu;
  if p eq 2 then
    issq := MakeIsSquare(2);
    try_func := function(d)
        // Michael's method searches in particular congruence classes,
        // and in occasional examples it is too restrictive.
        // Steve's method searches blindly.
        method := Random([1..5]) eq 1 select "Steve" else "Michael";
        if method eq "Steve" then
           rand := 1;   // random positive integer (according to a log distribution)
           while Random(1) eq 1 do rand +:= 1; end while;
        else
           rand := 1;
        end if;
             case d:
               when 1:
                 if method eq "Michael" then
                   x := 2^numin*Random(1, 2^nu);
                 else
                   x := 2^Random(-2*rand,2*rand)*Random(1, 2^nu);
                 end if;
                 if Random(1,4) eq 1 then x /:= 4; end if;
                 fx := Evaluate(f, x);
                 if fx eq 0 then return false, _; end if;
                 if issq(fx) then return true, P.1 - x;
                 else return false, _;
                 end if;
               when 2:
                 if method eq "Michael" then
                    if Random(1,4) eq 1 then
                       poly := P![ 4^(numin-2)*Random(1, 4^nu), 
                                   2^(numin-2)*Random(1, 2^nu), 1 ];
                    else
                       poly := P![ 4^numin*Random(1, 4^nu),
                                   2^numin*Random(1, 2^nu), 1 ];
                    end if;
                 else
                       poly := P![ 2^Random(-4*rand,4*rand)*Random(1, 4^nu),
                                   2^Random(-2*rand,2*rand)*Random(1, 2^nu), 1 ];
                 end if;
                 if Discriminant(poly) eq 0 then return false, _; end if;
                 ff := Resultant(PtoPP(f) - (PP!P.1), PtoPP(poly));
                 A := Coefficient(ff, 1); B := Coefficient(ff, 0);
                 if B eq 0 then return false, _; end if;
                 // The following 'if' is added by Steve.
                 if A^2-4*B eq 0 then 
                   // The two y-values, which are the roots of ff, are equal.
                   if IsSquare(pAdicField(p:Precision:=100)! -A/2) then return true, poly;
                   else return false, _; end if;
                   // Actually the 'false' case could possibly still be useful but
                   // the current code doesn't work for it (even after manually setting 'precn' below).
                 end if;
                 if A eq 0 then
                   w := Valuation(B, 2) div 4;
                 else
                   w := Min(Valuation(A, 2) div 2, Valuation(B, 2) div 4);
                 end if;
                 A := Integers()!(A/4^w); B := Integers()!(B/16^w);
                 fg := ((PZ.1)^2 + A)^2 - 4*B;
                 precn := 100 + 2*Valuation(Discriminant(fg), p);
                 if #SquarefreeRoots(SquarefreePart(
                             Polynomial(pAdicField(2,precn),fg))) gt 0 then
                 
                 //  if HasRoot(SquarefreePart(fg),pAdicField(2,50)) then
                    return true, poly;
                 else                  // put Steve's method in here too?  
                   return false, _;
                 end if;
               else
                 if Random(1,4) eq 1 then
                   poly := P![ 2^((numin-2)*(d-i))*Random(1,2^(nu*(d-i)))
                                : i in [0..d] ];
                 else
                   poly := P![ 2^(numin*(d-i))*Random(1, 2^(nu*(d-i)))
                                : i in [0..d] ];
                 end if;
                 //it seems to be a wise thing to make the polynomials monic
                 if Discriminant(poly) eq 0 then return false, _; end if;
                 // Now compute resultant
                 ff := Resultant(PtoPP(f) - (PP!P.1)^2, PtoPP(poly));
                 if Coefficient(ff, 0) eq 0 then return false, _; end if;
                 // rescale
                 d := Degree(ff);
                 w := Min([ Valuation(c, 2) div (2*k) : k in [1..d] | c ne 0
                             where c := Coefficient(ff, d-k) ]);
                 ff := PZ!(4^(-d*w)*Evaluate(ff, Parent(ff).1*4^w));
                 vD := Valuation(Discriminant(ff), 2);
	         R := pAdicRing(2 : Precision := vD + 8);
	         PR := PolynomialRing(R);
                 // factor
                 ffact := [ a[1] : a in Factorization(PR!ff) ];
                 // This criterion is only sufficient but not necessary.
                 // But it is almost necessary, so it hopefully won't make
                 // much of a difference in practice.
                 // In principle, it is possible that we miss a generator;
                 // this would result in an infinite loop.
                 if forall{ a : a in ffact
                              | IsOdd(Degree(a)) or
			        exists{i : i in [1..Degree(a)-1 by 2]
                            | not(IsWeaklyZero(Coefficient(a, i)))} }
                   then return true, poly;
                 else
                   return false, _;
                 end if;
             end case;
           end function;
  else
    issq := MakeIsSquare(p);
    try_func := function(d)
        // Michael's method searches in particular congruence classes,
        // and in occasional examples it is too restrictive.
        // Steve's method searches blindly.
        method := Random([1..5]) eq 1 select "Steve" else "Michael";
        if method eq "Steve" then
           rand := 0;   // random positive integer (according to a log distribution)
           keepadding := true;
           while keepadding do
                 rand +:= 1;
                 keepadding := Random([true,false]);
           end while;
        else
           rand := 1;
        end if;
             case d:
               when 1:
                 if method eq "Michael" then
                    x := p^numin*Random(1, p^nu);
                 else
                    x := p^Random([-2*rand..2*rand])*Random(1, p^nu);
                 end if;
                 fx := Evaluate(f, x);
                 if fx eq 0 then return false, _; end if;
                 if issq(fx) then return true, P.1 - x;
                 else return false, _;
                 end if;
               when 2:
                 if method eq "Michael" then
                    poly := PZ![ p^(2*numin)*Random(1, p^(2*nu)),
                                 p^numin*Random(1, p^nu), 1];
                 else
                    poly := PZ![ p^(Random(-6*rand,6*rand))*Random(1, p^(2*nu)),
                                 p^Random(-3*rand,3*rand)*Random(1, p^nu), 1];
                 end if;
                 if Discriminant(poly) eq 0 then return false, _; end if;
                 ff := Resultant(PZtoPPZ(PZ!f) - (PPZ!PZ.1), PZtoPPZ(poly));
                 A := Coefficient(ff, 1); B := Coefficient(ff, 0);
                 if B eq 0 then return false, _; end if;
                 // The following 'if' is added by Steve.
                 if A^2-4*B eq 0 then 
                   // The two y-values, which are the roots of ff, are equal.
                   if IsSquare(pAdicField(p:Precision:=100)! -A/2) then return true, poly;
                   else return false, _; end if;
                   // Actually the 'false' case could possibly still be useful but
                   // the current code doesn't work for it (even after manually setting 'precn' below).
                 end if;
                 if A eq 0 then
                   w := Valuation(B, p) div 4;
                 else
                   w := Min(Valuation(A, p) div 2, Valuation(B, p) div 4);
                 end if;
                 A := Integers()!(A/p^(2*w)); B := Integers()!(B/p^(4*w));
                 fg := ((PZ.1)^2 + A)^2 - 4*B;
                 precn := 100 + 2*Valuation(Discriminant(fg), p);
                 if HasRoot(fg, pAdicRing(p:Precision:=precn)) then return true, poly;
                 else return false, _;
                 end if;
               else                  // put Steve's method in here too?
                 poly := PZ![ p^(numin*(d-i))*Random(1,p^(nu*(d-i)))
                               : i in [0..d] ];
                 if Discriminant(poly) eq 0 then return false, _; end if;
                 ff := Resultant(PZtoPPZ(PZ!f) - (PPZ!PZ.1)^2, PZtoPPZ(poly));
                 if Coefficient(ff, 0) eq 0 then return false, _; end if;
                 vD := Valuation(Discriminant(ff), p);
	         R := pAdicRing(p : Precision := vD + 8);
	         PR := PolynomialRing(R);
                 // factor
                 ffact := [ a[1] : a in  Factorization(PR!ff) ];
                 // This criterion is only sufficient but not necessary.
                 // But it is almost necessary, so it hopefully won't make
                 // much of a difference in practice.
                 // In principle, it is possible that we miss a generator;
                 // this would result in an infinite loop.
                 if forall{ a : a in ffact
                              | IsOdd(Degree(a)) or
			        exists{i : i in [1..Degree(a)-1 by 2]
                                   | not(IsWeaklyZero(Coefficient(a, i)))} }
                   then return true, poly;
                 else
                   return false, _;
                 end if;
           end case;
         end function;
  end if;
  return function()
           repeat flag, poly := try_func(Random(dseq)); until flag;
           return poly;
         end function;
end function;

// Alternative method for obtaining the local image (at least the image
// of degree 1 points)

function ImageOfDelta2(f, W1, m1, W2, m2, check)
  // f: polynomial in Q[x] with integral coefficients
  // V1: an F_2 vector space
  // W1: a subspace of V1
  // m1: a map from Q[x] into V1
  // V2: an F_2 vector space
  // W2: a subspace of V2
  // m2: a map from Q[x] into V2
  // check: a predicate on F_2 vector spaces
  // 
  // returns W1 + image of delta_2 (via m1) and same for W2, m2;
  //   it is known that the first component satisfeis check.
  // (cf. `Implementing 2-descent for Jacobians of hyperelliptic curves',
  //  section 6)
  vprintf Selmer, 3: "    ImageOfDelta:\n";
  vprintf Selmer, 3: "      f = %o\n", f;
  vprintf Selmer, 3: "      p = %o\n", 2;
  V1 := Codomain(m1); V2 := Codomain(m2);
  PZ := PolynomialRing(Integers());
  x := Parent(f).1;
  X := PZ.1;
  f := PZ!f;
  function NewImage(W1, W2, xi)
    W1new := sub< V1 | W1, m1(xi - x) >;
    if IsVerbose("Selmer", 2) and Dimension(W1new) gt Dimension(W1) then
      printf "     x = %o --> new generator %o\n", xi, m1(xi-x);
    end if;
    W2new := sub< V2 | W2, m2(xi - x) >;
    return W1new, W2new;
  end function;
  // breadth-first search -- agenda contains the list of data that
  // still have to be dealt with in the form of quadruples
  // < f, xi0, a, depth >
  agenda := [ <PZ!(4^Degree(f)*Evaluate(f, x/4)), 0, 1/4, 0>];
  while not IsEmpty(agenda) do
    last := agenda[#agenda]; Prune(~agenda);
    f, xi0, a, depth := Explode(last);
    vprintf Selmer, 3: " "^depth*"      DeltaRec(%o, %o)\n", xi0, a;
    df := Derivative(f);
    for xi in GF(2) do
      fx := Evaluate(f, xi);
      xi1 := Integers()!xi;
      if fx eq 0 then
        fx1 := Evaluate(df, xi);
        if fx1 eq 0 then
          // f(xi1 + 2*X) = f(xi1) + 2*df(xi1)*X + O(2^2) = f(xi1) + O(2^2)
          if Evaluate(f, Integers(4)!xi1) eq 0 then
            // all coefficients of f(xi1 + 2*X) divisible by 4 ==> recurse
            agenda := [ <ExactQuotient(Evaluate(f, xi1 + 2*X), 4), 
                         xi0 + a*xi1, 2*a, depth+1> ] cat agenda;
          // else valuation is always one ==> no square
          end if;
        else // fx1 ne 0
          // exactly one of f(xi1), f(xi1+2) is divisible by 4
          xi1 +:= Integers()!Evaluate(f, Integers(4)!xi1);
          // now exactly one of f(xi1), f(xi1+4) is divisible by 8;
          // this value of xi1 is redundant, leading to a zero of f.
          // Continue with the other possibility.
          xi1 +:= Integers()!(4 + Evaluate(f, Integers(8)!xi1));
          // now recurse
          agenda := [ <ExactQuotient(Evaluate(f, xi1 + 8*X), 4), 
                       xi0 + a*xi1, 8*a, depth+1> ] cat agenda;
        end if; //fx1 eq 0
      else // fx ne 0
        // f(xi1 + 2*X) is always odd. Find values of xi1 mod 8 that give
        // f(xi1) = 1 mod 8.
        for xi2 in [Integers(8) | xi1 + i : i in [0,2,4,6]] do
          if Evaluate(f, xi2) eq 1 then
            W1, W2 := NewImage(W1, W2, xi0 + a*Integers()!xi2);
            if check(W1) then return W1, W2; end if;
          end if;
        end for;
      end if; // fx eq 0
    end for; // xi in GF(2)
  end while;
  return W1, W2;
end function;

function ImageOfDelta(f, p, W1, m1, W2, m2, check)
  // f: polynomial in Q[x] with integral coefficients
  // p: a prime
  // V1: an F_2 vector space
  // W1: a subspace of V1
  // m1: a map from Q[x] into V1
  // V2: an F_2 vector space
  // W2: a subspace of V2
  // m2: a map from Q[x] into V2
  // check: a predicate on F_2 vector spaces
  // 
  // returns W1 + image of delta_p (via m1), W2 + corresponding image via m2;
  //   it is known that the first component satisfies check.
  // (cf. `Implementing 2-descent for Jacobians of hyperelliptic curves',
  //  section 6)
  if p eq 2 then return ImageOfDelta2(f, W1, m1, W2, m2, check); end if;
  vprintf Selmer, 3: "    ImageOfDelta:\n";
  vprintf Selmer, 3: "      f = %o\n", f;
  vprintf Selmer, 3: "      p = %o\n", p;
  x := Parent(f).1;
  V1 := Codomain(m1); V2 := Codomain(m2);
  PZ := PolynomialRing(Integers());
  X := PZ.1;
  f := PZ!f;
  function NewImage(W1, W2, xi)
    W1new := sub< V1 | W1, m1(xi - x) >;
    if IsVerbose("Selmer", 2) and Dimension(W1new) gt Dimension(W1) then
      printf "     x = %o --> new generator %o\n", xi, m1(xi-x);
    end if;
    W2new := sub< V2 | W2, m2(xi - x) >;
    return W1new, W2new;
  end function;
  function DeltaRec(W1, W2, f, xi0, a, depth)
    vprintf Selmer, 3: " "^depth*"      DeltaRec(%o, %o)\n", xi0, a;
    df := Derivative(f);
    for xi in GF(p) do
      fx := Evaluate(f, xi);
      if fx eq 0 then
        fx1 := Evaluate(df, xi);
        if fx1 eq 0 then
          // f(xi1 + p*X) = f(xi1) mod p^2
          xi1 := Integers()!xi;
          if Evaluate(f, Integers(p^2)!xi1) eq 0 then
            // all coefficients of f(xi1 + p*X) divisble by p^2 ==> recurse
            W1, W2 := DeltaRec(W1, W2, 
                               ExactQuotient(Evaluate(f, xi1 + p*X), p^2), 
                               xi0 + a*xi1, p*a, depth+1);
            if check(W1) then return W1, W2; end if;
          end if;
          // else fx1 ne 0, and xi1 lifts to a unique zero of f ==> abort
        end if; //fx1 eq 0
      else // fx ne 0
        if IsSquare(fx) then
          xi1 := Integers()!xi;
          W1, W2 := NewImage(W1, W2, xi0 + a*xi1);
          if check(W1) then return W1, W2; end if;
        end if; // IsSquare(fx)
      end if; // fx eq 0
    end for; // xi in GF(p)
    return W1, W2;
  end function;
  return DeltaRec(W1, W2, f, 0, 1, 0);
end function;

// LocalImageOdd computes the image of the p-adic coboundary morphism.
// The curve is  y^2 = f(x),  v is the p-adic valuation of the discriminant
// of the curve. Let L be the etale algebra Q[x]/(f). Then m1 and m2 are the
// maps from L^* to L_p^*/(L_p^*)^2 and to I_p/I_p^2 (where the codomains
// are represented as GF(2)-vector spaces).
// LocalImageOdd returns two values -- the images in L_p^*/(L_p^*)^2 and 
// in I_p/I_p^2.

function LocalImageOdd(f, p, m1, m2, v, Points, debug)
  // vprintf Selmer, 3:
  //         "   LocalImageOdd(%o, %o, map<>, map<>, %o)\n", f, p, v;
  g := (Degree(f) - 1) div 2;       // the genus
  if p eq 2 then v -:= 4*g; end if; // valuation of Discriminant(f)
  nu := 1 + (v div 2);              // the p-adic precision we need
  if p eq 2 then nu +:= 6; v +:= 2; end if;
  // Determine size and image of 2-torsion over Q_p.
  //Precision bound below is changed due to new locals being lossier.
  R := pAdicRing(p : Precision := v+8);
  PR := PolynomialRing(R);
  PZ := PolynomialRing(Integers());
  fact := [ a[1] : a in Factorization(PR!PZ!f) ];
  vprintf Selmer, 3:
          "    2-torsion subgroup has dimension %o.\n", #fact - 1;
  tfact := [ Parent(f) |
             (-1)^Degree(fact[j])*(fact[j] - &*[ fact[i] : i in [1..#fact]
                                                         | i ne j])
              : j in [1..#fact-1] ];
  // determine image of 2-torsion
  W1 := sub< Codomain(m1) | [ m1(tf) : tf in tfact ] >;
  W2 := sub< Codomain(m2) | [ m2(tf) : tf in tfact ] >;
  if GetVerbose("Selmer") ge 3 and #fact gt 1 then
    printf "    Image of 2-torsion:\n";
    PrintBasis(Basis(W1), 6);
  end if;
  // dim is the dimension W1 should have
  dim := #fact - 1;
  if p eq 2 then dim +:= g; end if;
  vprintf Selmer, 3:
          "    Dimension of local image = %o.\n", dim;
  if Dimension(W1) eq dim then
    vprintf Selmer, 3:
            "    Local image is image of 2-torsion.\n";
    return W1, W2;
  end if;
  for pt in Points do
    poly := pt[1];
    W1n := sub< Codomain(m1) | W1, m1((-1)^Degree(poly)*poly) >;
    if Dimension(W1n) gt Dimension(W1) then
      vprintf Selmer, 2:
              "     point %o gives new generator: %o\n", pt, m1(poly);
      W1 := W1n;
      W2 := sub< Codomain(m2) | W2, m2(poly) >;
    end if;
    if Dimension(W1) eq dim then return W1, W2; end if;
  end for;   /*** This is where search strategy goes ***/
  // change this into `if false then' to revert to old behaviour
  if p lt 6 and Degree(f) le 6 then
    W1, W2 := ImageOfDelta(f, p, W1, m1, W2, m2, func<W|Dimension(W) eq dim>);
    if Dimension(W1) eq dim then return W1, W2; end if;
    deg := 2;
  else
    deg := 1;
  end if;
  try_func := MakeTry(f, p, nu, deg);
  NumExtraPoints := 0;   // As a check, find some extra points 
                         // and check that the dimension remains right
  repeat
    if Dimension(W1) ge dim then 
       NumExtraPoints +:= 1; 
    end if;
    // find more generators
    poly := try_func();
    vprintf Selmer, 3: "     try_func() -> %o\n", poly;
    poly := (-1)^Degree(poly)*poly;
    W1n := sub< Codomain(m1) | W1, m1(poly) >;
    if Dimension(W1n) gt Dimension(W1) then
      vprintf Selmer, 2:
              "     %o --> new generator: %o\n", poly, m1(poly);
      W1 := W1n;
      W2 := sub< Codomain(m2) | W2, m2(poly) >;
    end if;
    error if Dimension(W1) gt dim,
          "Finding spurious local points at ",p,
          " ... try increasing p-adic precision \n";
  until Dimension(W1) ge dim and NumExtraPoints ge (debug select 10 else 2);
  return W1, W2;
end function;


// LocalImageEven computes the image of the p-adic coboundary morphism.
// The curve is  y^2 = f(x),  v is the p-adic valuation of the discriminant
// of the curve. Let L be the etale algebra Q[x]/(f). Then m1 and m2 are the
// maps from L^* to L_p^*/(L_p^*)^2 and to I_p/I_p^2 (where the codomains
// are represented as GF(2)-vector spaces).
// LocalImageEven returns three values -- the images in L_p^*/(L_p^*)^2 and 
// in I_p/I_p^2 (joined with the image of Q_p^*) and a flag indicating
// whether the local Cassels kernel is 2 J.

function LocalImageEven(lcf, f, p, m1, m2, v, Q1, Q2, resfact, proj, Points, debug)
  g := (Degree(f) - 1) div 2;       // the genus (= 2)
  if p eq 2 then v -:= 4*g; end if; // valuation of Discriminant(f)
  nu := 1 + (v div 2);              // the p-adic precision we need
  if p eq 2 then nu +:= 6; v +:= 2; end if;
  // Determine size and image of 2-torsion over Q_p.
  P := Parent(f);
  R := pAdicRing(p : Precision := v+8);
  PR := PolynomialRing(R);
  PZ := PolynomialRing(Integers());
  fact := [ a[1] : a in Factorization(PR!PZ!f) ];
  rank2t := #fact - 1;
  Odd := exists(oddf){ a : a in fact | IsOdd(Degree(a)) };
  if Odd then rank2t -:= 1; end if;
  vprintf Selmer, 3:
          "    2-torsion subgroup has dimension %o.\n", rank2t;
  if Odd then
    // some factors have odd degree, oddf is one of them
    tfact := [ P | fact[j] - (R!lcf)*&*[ PR | fact[i] : i in [1..#fact]
                                                      | i ne j ]
                    : j in [1..#fact] | IsEven(Degree(fact[j])) ]
         cat [ P | oddf*f1 - (R!lcf)*&*[ PR | f2 : f2 in fact
                                                 | f2 ne oddf and f2 ne f1 ]
                    : f1 in fact | IsOdd(Degree(f1)) and f1 ne oddf ];
    Prune(~tfact);
  else
    // all factors have even degree
    tfact := [ P | fact[j] - (R!lcf)*&*[ PR | fact[i] : i in [1..#fact]
                                                      | i ne j ]
                   : j in [1..#fact-1] ];
  end if;
  if GetVerbose("Selmer") ge 3 then
    // printf "     Basis of 2-torsion:\n";
    // PrintBasis(tfact, 7);
    printf "     Basis of image of Q_%o^*:\n", p;
    PrintBasis(Basis(Q1), 7);
    printf "     Image of basis of 2-torsion:\n";
    PrintBasis([ m1(tf) : tf in tfact ], 7);
  end if;
  // Find out about Cassels kernel
  Cas := Odd or #resfact eq 0
       or exists{ r : r in resfact | HasRoot(r, pAdicRing(p:Precision:=100)) };
  // dim is the dimension W1 should have
  dim := rank2t;
  if p eq 2 then dim +:= g; end if;
  vprintf Selmer, 3:
          "    J(Q_%o)/2J(Q_%o) has dimension %o.\n", p, p, dim;
  if not Cas then dim -:= 1; end if;
  vprintf Selmer, 3:
          "    Its image has dimension %o.\n", dim;
  dim +:= Dimension(Q1); // dim of inverse image in V1
  // determine image of 2-torsion
  W1 := sub< Codomain(m1) | Q1, [ m1(tf) : tf in tfact ] >;
  W2 := sub< Codomain(m2) | Q2, [ m2(tf) : tf in tfact ] >;
  if GetVerbose("Selmer") ge 3 and rank2t ge 1 then
    printf "    Image of 2-torsion (lifted back):\n";
    PrintBasis(Basis(W1), 6);
  end if;
  vprintf Selmer, 3:
          "    Dimension of local image (lifted back) = %o.\n", dim;
  if Dimension(W1) eq dim then
    vprintf Selmer, 3:
            "    Local image is image of 2-torsion.\n";
  else
    for pt in Points do
      poly := pt[1];
      W1n := sub< Codomain(m1) | W1, m1(poly) >;
      if Dimension(W1n) gt Dimension(W1) then
        vprintf Selmer, 2:
                "     point %o gives new generator: %o\n", pt, m1(poly);
        W1 := W1n;
        W2 := sub< Codomain(m2) | W2, m2(poly) >;
      end if;
      if Dimension(W1) eq dim then break; end if;
    end for;
    if p lt 6 then /*** this is where search strategy goes ***/
      VV1 := KSpace(GF(2), Dimension(Codomain(m1))+1);
      VV2 := KSpace(GF(2), Dimension(Codomain(m2))+1);
      WW1 := sub< VV1 | [ Eltseq(w) cat [GF(2)|0] : w in Basis(W1) ] >;
      WW2 := sub< VV2 | [ Eltseq(w) cat [GF(2)|0] : w in Basis(W2) ] >;
      mm1 := map< Domain(m1) -> VV1 |
                  x :-> VV1!(Eltseq(m1(x)) cat [GF(2)|Degree(x)]) >;
      mm2 := map< Domain(m2) -> VV2 |
                  x :-> VV2!(Eltseq(m2(x)) cat [GF(2)|Degree(x)]) >;
      U := sub< VV1 | [ VV1.i : i in [1..Dimension(VV1)-1] ] >;
      check := func< W | Dimension(W meet U) eq dim >;
      WW1, WW2 := ImageOfDelta(lcf*f, p, WW1, mm1, WW2, mm2, check);
      W1 := sub< Codomain(m1) | [ Prune(Eltseq(w)) : w in Basis(WW1 meet U) ] >;
      W2 := sub< Codomain(m2) | [ Prune(Eltseq(w)) : w in Basis(WW2 meet U2) ] >
        where U2 := sub< VV2 | [ VV2.i : i in [1..Dimension(VV2)-1] ] >;
      deg := 2;
    else
      deg := 1;
    end if;
    try_func := MakeTry(lcf*f, p, nu, deg);
    NumExtraPoints := 0;
    repeat
      if Dimension(W1) ge dim then 
          NumExtraPoints +:= 1; 
      end if;
      // find more generators
      poly := try_func();
      vprintf Selmer, 3: "     try_func() -> %o\n", poly;
      W1n := sub< Codomain(m1) | W1, m1(poly) >;
      if Dimension(W1n) gt Dimension(W1) then
        vprintf Selmer, 2:
                "     %o --> new generator: %o\n", poly, m1(poly);
        W1 := W1n;
        W2 := sub< Codomain(m2) | W2, m2(poly) >;
      end if;
      error if Dimension(W1) gt dim,
            "Finding spurious local points at ",p,
            " ... try increasing p-adic precision \n";
    until Dimension(W1) ge dim and NumExtraPoints ge (debug select 10 else 2);
  end if;
  if W2 eq Q2 then
    W2 := sub< Codomain(m2) | >;
    W1 := W1 meet Kernel(proj);
  end if;
  return W1, W2, Cas;
end function;


function TwoSelmerWork(C, BoundType, Bound, UseUnits, Points, Fields, debug)
  // C : y^2 = f(x),
  // f is a square-free integral polynomial either monic of odd degree
  // or of (even) degree 6 and of the form lcf*f1(x) with f1 integral.

compare_new_vs_old := debug;

  f := HyperellipticPolynomials(C);
  degree := Degree(f);
  Odd := IsOdd(degree);
  if not Odd then
    lcf := LeadingCoefficient(f);
    f := (1/lcf)*f;
    lcf := Integers()!lcf;
  end if;
  bad_primes := BadPrimes(C); // contains 2 (and the divisors of lcf)
  vprintf Selmer, 2: " Bad primes = %o\n", bad_primes;
  disc := Integers()!Discriminant(C);
  not_so_bad_primes := [ p : p in bad_primes | Valuation(disc, p) eq 1 ];
  if not IsEmpty(not_so_bad_primes) then
    vprintf Selmer, 2: 
            "  The following primes divide the discriminant exactly: %o\n",
            not_so_bad_primes;
    bad_primes := [ p : p in bad_primes | p notin not_so_bad_primes ];
    vprintf Selmer, 2: "  Bad primes now = %o\n", bad_primes;
  end if;
  fact := [ a[1] : a in Factorization(f) ];
  if GetVerbose("Selmer") ge 2 then
    if #fact eq 1 then
      print "  f is irreducible.";
    else
      printf "  f factors as";
      if not Odd then
        if lcf ne 1 then
          if lcf eq -1 then printf " -"; else printf " %o", lcf; end if;
        end if;
      end if;
      for h in fact do printf " (%o)", h; end for;
      printf ".\n";
    end if;
  end if;
  if not Odd then
    // Determine global Cassels kernel
    CasGlob, resfact, subext_disc := CasselsKernel(fact);
    if not IsEmpty(resfact) and GetVerbose("Selmer") ge 2 then
      if #resfact eq 1 then
        printf "   Resolvent = %o.\n", resfact[1];
      else
        printf "   Resolvent =";
        for r in resfact do printf " (%o)", r; end for;
        printf ".\n";
      end if;
    end if;
    HaveQuadraticSubextension
      := CasGlob and forall{ a : a in fact | IsEven(Degree(a)) };
  end if;
  // A sequence of number fields (of which some are the rationals) 
  // is not possible...
  fields := [* *];  // list of fields K corresponding to factors h of f
  thetas := [* *];  // list of zeros of h in K
  invhoms := [* *]; // list of maps K --> Q[x] inverse to evaluation at theta
  for h in fact do
    deg := Degree(h);
    if deg eq 1 then
      K := Rationals();
    elif not exists(K){ K : K in Fields | Degree(K) eq deg and HasRoot(h, K) } 
    then
      K := OptimisedRepresentation(NumberField(h));
    end if;
    _, theta := HasRoot(h, K);
    if IsVerbose("Selmer", 2) then
      printf "  For factor %o, use field defined by\n    %o\n", 
             h, DefiningPolynomial(K);
      printf "    and theta = %o\n", theta;
    end if;
    // Determine section to evaluation at theta Q[x] --> K
    mat := Matrix(deg, &cat[ Eltseq(theta^i) : i in [0..Degree(h)-1] ])^-1;
    invhom := map< K -> Parent(f)
                   | z :-> Parent(f)!Eltseq(Matrix(deg, Eltseq(z))*mat) >;
    Append(~fields, K);
    Append(~thetas, theta);
    Append(~invhoms, invhom);
  end for;
  // for later use as fourth return value: construct set of 
  // number fields used
  nfields := {K : i in [1..#fields] | Category(K) eq FldNum
                                       where K := fields[i]};
  rank2t := #fact - 1;
  if not Odd then
    if exists{ a : a in fact | IsOdd(Degree(a)) } then rank2t -:= 1; end if;
  end if;
  vprintf Selmer, 2:
          "  The 2-torsion group has dimension %o.\n", rank2t;
  vprint Selmer, 2: "  Determining local images...";
  t0 := Cputime();
  local_info := [ ];
  // this sequence will contain lists 
  //  [* p, <V1, m1, W1>, <V2, m2, W2>, dec *]  (if the degree is odd)
  //  [* p, <V1, m1, W1, Q1>, <V2, m2, W2, Q2>, dec *]  (if the degree is even)
  // with:
  // + p a prime (or 0, standing for infinity)
  // + m1 : L^* --> V1 the local map (V1 a GF(2)-vector space)
  // + W1 subset V1 the image of the local points in V1
  // + Q1 subset V1 the image of Q_p^* (if deg is even)
  // + <V2, m2, W2[, Q2]> the same, but with the valuation map,
  //       meaning that m2 : L^* --> V2 = (Z/2)^r is just
  //                         l :--> [val_P(l) mod 2 : P above p]
  // + dec the decomposition of p in the various number fields
  if not Odd then
    added_gens := [ ]; // Generators of the image of Q^* in the 
                       // Big Fake Selmer group (see below)
  end if;
  for p in bad_primes do
    vprint Selmer, 2: "   p =", p;
    // A sequence like this is not possible...
    // decomps := [ Decomposition(Integers(fields[i]), p) : i in [1..#fields] ];
    decomps := [* *];
    for i := 1 to #fields do
      Append(~decomps, Decomposition(Integers(fields[i]), p));
    end for;
    mms := &cat[ [ [* V, m, gen *] 
                   where gen := thetas[i]
                   where V, m := MakeModSquares(K, pid)
                   where K := fields[i]
                   where pid := decomps[i,j,1]
                    : j in [1..#decomps[i]] ]
                   : i in [1..#fields] ];
    if GetVerbose("Selmer") ge 3 then
      printf "    L_%o decomposes into %o local fields with invariants\n     ",
             p, #mms;
      for i := 1 to #fields do
        for pair in decomps[i] do
          printf " (e = %o, f = %o)", RamificationIndex(pid), Degree(pid)
                 where pid := pair[1];
        end for;
      end for;
      printf "\n";
    end if;
    V1 := KSpace(GF(2), &+[ Dimension(vmk[1]) : vmk in mms ]);
    V2 := KSpace(GF(2), #mms);
    m1 := map< Parent(f) -> V1 |
               z :-> V1!&cat[ Eltseq(vmk[2](Evaluate(z, vmk[3])))
                               : vmk in mms ] >;
    m2 := map< Parent(f) -> V2 |
               z :-> V2![ GF(2) | Eltseq(vmk[2](Evaluate(z, vmk[3])))[1]
                                   : vmk in mms ] >;
    if Odd then
      W1, W2 := LocalImageOdd(f, p, m1, m2, Valuation(disc, p), Points, debug);
      Cas := true;
    else
      QBasis := p eq 2 select [ Parent(f) | 2, 3, 5 ]
                       else [ Parent(f) | p, d() ]
                            where d := function()
                                         for j := 2 to p-1 do
                                           if not IsSquare(GF(p)!j)
                                             then return j;
                                           end if;
                                         end for;
                                       end function;
      Q1 := sub< V1 | [ m1(b) : b in QBasis ] >;
      Q2 := sub< V2 | m2(Parent(f)!p) >;
      iseq := [ 1 + &+dseq[1..i-1] : i in [1..#dseq] ]
              where dseq := [ Dimension(vmk[1]) : vmk in mms ];
      proj := hom< V1 -> V2 | [ V2!Eltseq(b)[iseq] : b in Basis(V1) ] >;
      W1, W2, Cas
        := LocalImageEven(lcf, f, p, m1, m2, val, Q1, Q2, resfact, proj, Points, debug)
           where val := Valuation(disc, p);
    end if; // Odd
    if GetVerbose("Selmer") ge 3 then
      if p ne 2 and Dimension(W2) eq 0
          and (Odd or Dimension(Q2) gt 0 or Cas) then
        if Odd then
          printf
           "    Ramified image is trivial -> can drop %o from bad primes.\n", p;
        else
          printf "    Ramified image is trivial and (Cassels kernel = 2 J\n";
          printf "      or some local field has odd ramification index)\n";
          printf "      -> can drop %o from bad primes.\n", p;
        end if; // Odd
      else // not(p ne 2 and Dimension(W2) eq 0 and (Odd or ... or Cas))
        print "    Local basis:";
        PrintBasis(Basis(W1), 6);
        if Dimension(W2) eq 0 then
          print "    Image under valuation map is trivial.";
        else
          print "    Basis of image under valuation map:";
          PrintBasis(Basis(W2), 6);
        end if; // Dimension(W2) eq 0
      end if; // p ne 2 and Dimension(W2) eq 0 and Cas
    end if; // GetVerbose("Selmer") ge 3
    if Odd then
      // With notations as in `Implementing 2-descent for ... curves':
      // add p to S if  p = 2  or  G_p /= 0 (note that  G_p = W2)
      if p eq 2 or Dimension(W2) gt 0 then
        Append(~local_info, [* p, <V1, m1, W1>, <V2, m2, W2>, decomps *]);
      end if;
    else // not Odd
      // With notations as in `Implementing 2-descent for ... curves':
      // add p to S if  p = 2  or  G_p /= 0  or  e_p = 0 and u_p = 1
      // (note that  e_p = 0 and u_p = 1 <==> e_p = 0 and not Cas;
      //  G_p = W2,  e_p = 0 <==> Q2 = 0)
      if p eq 2 or Dimension(W2) gt 0 or (Dimension(Q2) eq 0 and not Cas) then
        Append(~local_info, 
               [* p, <V1, m1, W1, Q1>, <V2, m2, W2, Q2>, decomps *]);
      end if;
      // add p to S' if  G_p /= 0  or  e_p = 0.
      if Dimension(W2) gt 0 or Dimension(Q2) eq 0 then
        Append(~added_gens, p);
      end if;
    end if; // Odd
  end for; // p in bad_primes
  
  // Deal with infinity
  vprint Selmer, 2: "   p = infinity";
  rmax := Maximum([Modulus(rt[1]) : rt in Roots(f, ComplexField())]);
  lrmaxd := Ceiling(degree^2*Log(rmax)/Log(10));
  // increase precision
  prec := 50; // size of coefficients
  pprec := lrmaxd + degree*prec + 10;
  roots := [Real(r[1]) : r in Roots(f, RealField(pprec)) | IsReal(r[1]) ];
  Sort(~roots); // bring real roots into increasing order
  if GetVerbose("Selmer") ge 3 then
    printf "    Real roots:\n";
    PrintBasis(roots, 6);
  end if;
  V := KSpace(GF(2), #roots);
  // Be careful to increase precision when necessary
  m := map< Parent(f) -> V |
            z :-> V![ GF(2) | Evaluate(z, r) lt 0 select 1 else 0
                               : r in roots1
                               where roots1 := pr le prec select roots
                                     else ( r() where 
                         r := function()
                            pprec := lrmaxd + degree*pr + 10;
                            rr := [Real(rt[1]) : rt in 
				    Roots(f, RealField(pprec)) | IsReal(rt[1])];
                            Sort(~rr);
                            return rr;
                          end function )
                                where pr := Ceiling(Log(&+[Abs(c)
                                                           : c in Eltseq(z)])
                                                      / Log(10)) 
                     ] >;
  if Odd then
    W := sub< V | [ [GF(2) | j lt 2*i select 0 else 1 : j in [1..#roots]]
                      : i in [1..(#roots div 2)] ] >;
  else
    Q := sub< V | m(Parent(f)!-1) >;
    if lcf gt 0 then
      W := sub< V | [ [GF(2) | j le 2*i select 0 else 1 : j in [1..#roots]]
                        : i in [0..(#roots div 2) - 1] ] >;
    else
      W := sub< V | Q, [ [GF(2) | j in [2*i,2*i+1] select 1 else 0
                                   : j in [1..#roots]]
                          : i in [1..(#roots div 2) - 1] ] >;
    end if;
  end if; // Odd
  if GetVerbose("Selmer") ge 3 then
    if Dimension(W) gt 0 then
      printf "    Local basis:\n";
      PrintBasis(Basis(W), 6);
    else
      print "    Local image at infinity is trivial.";
    end if;
  end if; // GetVerbose("Selmer") ge 3
  if Odd then
    Append(~local_info, [* 0, <V, m, W>, <V0, m0, V0> *]
                         where m0 := map< Parent(f) -> V0 | z :-> V0!0 >
                         where V0 := KSpace(GF(2), 0));
  else
    Append(~local_info, [* 0, <V, m, W, Q>, <V0, m0, V0, V0> *]
                         where m0 := map< Parent(f) -> V0 | z :-> V0!0 >
                         where V0 := KSpace(GF(2), 0));
    Append(~added_gens, -1);
  end if; // Odd
  
  // Now we have collected the local information.
  // Let us proceed to do the global stuff.
  
  // First put together the local stuff into one big structure.
  // This means (if I understand correctly  -- Steve):
  // bigV1 is the direct sum of all the local Lv/Lv^2
  // bigW1 is the subspace satisfying all local conditions
  // bigV2 is the direct sum of the S-subgroups of I_L/I_L^2,
  // i.e. it exactly records the valuations of elements of bigV1
  // bigW2 is the image of bigW1 in bigV1 (via the valuation maps)
  bigV1 := KSpace(GF(2), &+[Dimension(li[2,1]) : li in local_info]);
  bigm1 := map< Parent(f) -> bigV1 |
                z :-> bigV1!&cat[ Eltseq(li[2,2](z)) : li in local_info ] >;
  bigW1 := sub< bigV1 | &cat[ [&cat[j eq i select Eltseq(b) else Eltseq(wl[j]!0)
                              : j in [1..#local_info]]
                         : b in Basis(wl[i])]
                       : i in [1..#local_info] ]
                       where wl := [ li[2,3] : li in local_info ] >;
  bigV2 := KSpace(GF(2), &+[Dimension(li[3,1]) : li in local_info]);
  bigm2 := map< Parent(f) -> bigV2 |
                z :-> bigV2!&cat[ Eltseq(li[3,2](z)) : li in local_info ] >;
  bigW2 := sub< bigV2 | &cat[ [&cat[j eq i select Eltseq(b) else Eltseq(wl[j]!0)
                              : j in [1..#local_info]]
                         : b in Basis(wl[i])]
                       : i in [1..#local_info] ]
                       where wl := [ li[3,3] : li in local_info ] >;
  // Some technical preliminaries
  cfact := [ f div h : h in fact ]; // cofactors of the factors of f
  // injs is a sequence of pairs of maps  K --> Q[x]/(f); the first injects
  // K^* into (Q[x]/(f))^* (taking 1 at all other components), the second
  // injects K into Q[x]/(f) (taking 0 at all other components).
  // In both, the images are given as elements of Q[x].
  injs := [ <map<fields[i] -> Parent(f) | z :-> (u + v*invhoms[i](z)) mod f>,
             map<fields[i] -> Parent(f) | z :-> (v*invhoms[i](z)) mod f> >
            where u := u1*h where v := v1*hc
            where _, u1, v1 := XGCD(h, hc)
            where h := fact[i] where hc := cfact[i]
             : i in [1..#fact] ];
  
  // If the degree is odd, then the Selmer group is contained in the 
  // subgroup of L^*/(L^*)^2 consisting of elements mapping into bigW2
  // under the valuation map bigm2.
  
  // If the degree is even, then the Selmer group is contained in the
  // image in H of the subgroup of L^*/(L^*)^2 consisting of elements
  // mapping into bigW2 under the valuation map bigm2.
  
// NEW !!!!!
if compare_new_vs_old then
  t0cl := Cputime();
  cltime := 0;  // Cumulative time spent on ClassGroup
  tnew := 0;    // Cumulative time spent on pSelmerGroup

  // List the bad primes for each field.
  // (TO DO: I may be throwing away a lot by this, 
  //  I really should figure out which primes don't
  //  need to be considered at all, which happens in the old version)
  // (i.e. kick out ideals that are ruled out by the local conditions
  // purely because of their valuations, in other words ideals that
  // make no contribution to any element of W2.)
  // Format: badprimes is [* [bad primes for F] : F = fields[i] *]
  badprimes := [* {} : i in [1..#fact] *];
  for i := 1 to #fact do
      for li in local_info do
         if li[1] ne 0 then   // if it's a nonarchimedean place
     // the additional step, for greater efficiency, would be:
     // figure out which coordinate of W2 corresponds to each ideal below,
     // and test if any basis vector in W2 has a nonzero coordinate there
     // ... if none do, then leave that ideal out of badprimes.
            badprimes[i] join:= { factor[1] : factor in li[4][i] };
         end if;
      end for;
  end for;

  // Compute F(S,2) for each field F in L.
  bigFB := [ Parent(f) | ];   // factor base: S-units will be written 
                              // as products of these elements of L
  Vecs := [* *];   // List of tuples, one for each field F, of the form
                   //    <#FB, [ Vectors determining F(S,2) in terms of FB>
                   // where FB is the factor base given by pSelmerGroup(2,S) for F.
  for i := 1 to #fact do
      F := fields[i];
      vprintf Selmer, 2: "Getting pSelmerGroup of %o\n", F;
      inj := injs[i,1];   // The homomorphism  F* --> L*,
                          // except that images are given as elements 
                          // of the polynomial ring Parent(f),
                          // where L = Q[x]/f(x).
      if Type(F) eq FldRat then 
         primes := [-1] cat [ Generator(id) : id in badprimes[i] ];
         bigFB cat:= [ inj(p) : p in primes ];
         Append( ~Vecs, <#primes, [ Eltseq(basisvec) : basisvec in Basis(VectorSpace(GF(2), #primes)) ]> );
      else
         // Compute a ClassGroup (which pSelmerGroup will then use)
         if Bound ne 0 then
            // first do a class group computation, using the user-desired Bound,
            vprintf Selmer, 2: "Calling ClassGroup with Bound := %o\n", Bound;
            _ := ClassGroup(F : Bound := Bound, Proof := "Bound");
         else
            _ := ClassGroup(F : Proof := "Current");
            // Current will use whatever is cached (at the C level),
            // and if nothing is cached then it will use the global class group bounds.
         end if;
         t0new := Cputime();
         cltime +:= t0new - t0cl;

         F2S, F2StoAlg, toVec, FB := pSelmerGroup(2, badprimes[i] : Raw);
         FB := Eltseq(FB);
         bigFB cat:= [ inj(fb) : fb in FB ];
         Append( ~Vecs, <#FB, [Eltseq(toVec(g)) : g in Generators(F2S)]> ); 
         tnew +:= Cputime() - t0new;
      end if;
  end for;
  // Repackage the Vecs. 
  // Make vectors w.r.t bigFB by padding with zeros at both ends:
  bigFBSpace := VectorSpace( GF(2), #bigFB );
  bigV := sub<bigFBSpace | [] >;
  n0 := 0;
  for i := 1 to #fact do
      n := Vecs[i][1];
      for v in Vecs[i][2] do 
         vv := bigFBSpace!( [0 : i in [1..n0]] cat v cat [0 : i in [n0+n+1..#bigFB]] );
         bigV := sub<bigFBSpace | bigV, vv>;
      end for;
      n0 +:= n;
  end for;
  bigFBimages := [ bigm1(b) : b in bigFB ];   // images in bigV1
  newBimage := [ &+[ bigFBimages[i] : i in [1..#bigFB] | v[i] eq 1 ] 
             : v in Basis(bigV) ];
newbigV := bigV;   // temporary name, for testing

end if;   // compare_new_vs_old
// END OF NEW STUFF

// OLD !!!!

//  ... TO DO: Remove the old stuff, and of course the compare_new_vs_old vararg.

  // Class groups
  vprint Selmer, 2: "OLD METHOD ...  Computing class groups, in case", BoundType;
  t1 := Cputime(t0);
  case BoundType:
    when "Default":
      Cls := [ <C, m> where C, m := ClassGroup(fields[i] : Proof:="Current") 
                : i in [1..#fields] ];
    when "Minkowski":
      Cls := [ <C, m>
               where C, m := ClassGroup(fields[i] :
                                         Bound := MinkowskiBound(fields[i])) 
                : i in [1..#fields] ];
    when "Bach":
      Cls := [ <C, m>
               where C, m := ClassGroup(K : Bound := bound)
                             where bound := Min(BachBound(K), MinkowskiBound(K))
                             where K := fields[i]
                : i in [1..#fields] ];
    when "Absolute":
      Cls := [ <C, m>
               where C, m := ClassGroup(fields[i] :
                                         Bound := Bound)
                : i in [1..#fields] ];
    when "Relative":
      Cls := [ <C, m>
               where C, m := ClassGroup(K : Bound := bound)
                             where bound
                                 := Min(MinkowskiBound(K),
                                        Floor( 1+Bound*Log(Abs(Discriminant(K)))^2 ))
                             where K := fields[i]
                : i in [1..#fields] ];
    else error "Wrong BoundType argument!";
  end case;
  t2 := Cputime(t0) - t1;
  dims := [ Integers() |
            #[ n : n in Invariants(Cm[1]) | IsEven(n) ] : Cm in Cls ];
  dimCl2 := &+dims;
  if IsVerbose("Selmer", 2) then
    print "  Class group data of the fields:";
    for i := 1 to #fact do
      printf "   Field given by %o:  %o\n", fact[i], Invariants(Cls[i,1]);
    end for;
    printf "  Dimension of Cl[2] = %o.\n", dimCl2;
  end if;

  // Find the map from bigV2 into Cl(L)/2*Cl(L).
  // (Recall bigV2 is a subgroup of I_L/I_L^2)
  Cl2 := KSpace(GF(2), dimCl2);
  ims := [];
  pids := [];
  for li in local_info do
    if li[1] ne 0 then
      for j1 := 1 to #fact do
        dec := li[4,j1]; Cl := Cls[j1,1]; Clm := Cls[j1,2];
        sleft := [ GF(2) | 0 : k in  [1..&+dims[1..j1-1]] ];
        sright := [ GF(2) | 0 : k in  [1..&+dims[j1+1..#dims]] ];
        inds := [ i : i in [1..#invs] | IsEven(invs[i]) ]
          where invs := Invariants(Cl);
        inj := func< id | Cl2!(sleft cat seq cat sright)
                          where seq := ChangeUniverse(Eltseq(c)[inds], GF(2))
                          where c := ClassRepresentative(id) @@ Clm >; // ClassRepresentative appears pointless
               // WARNING: "inj" is used inside TwoSelmerWork 
               // as a name for two unrelated kinds of maps. 
        for pid in dec do
          Append(~ims, inj(pid[1]));
          // a sequence of ideals in different rings is not possible
          ids := [* *];
          for j := 1 to #fact do
            Append(~ids, j eq j1 select pid[1]
                                 else ideal<Integers(fields[j])|1>);
          end for;
          Append(~pids, ids);
        end for;
      end for;
    end if;
  end for;
  homCl2 := hom< bigV2 -> Cl2 | ims >;
  
  // find the kernel of homCl2 in bigW2
  kerW2 := bigW2 meet Kernel(homCl2);
  // find signatures of the fields in order to get upper bound on dim S
  sigs := [ [r1,r2] where r1, r2 := Signature(fields[i]) : i in [1..#fields] ];
  dimU := &+[ &+s : s in sigs ];
  if IsVerbose("Selmer",2) then
    printf "  Signatures:";
    for s in sigs do printf " %o", s; end for; printf "\n";
    printf "  Dimension of units mod squares = %o.\n", dimU;
  end if;
  dimSupper := dimU + dimCl2 + Dimension(kerW2);
  if Odd then
    dimSupper -:= 1;
  else
    dimSupper -:= #added_gens;
    if not CasGlob then
      // We get only the `fake' Selmer group, the real Selmer group has a
      // dimension that is larger by one.
      dimSupper +:= 1;
    end if;
    if HaveQuadraticSubextension then
      // Here, the exact sequence describing the fake Selmer group
      // has a non-zero first term.
      dimSupper +:= 1;
    elif exists{ a : a in fact | IsOdd(Degree(a)) } then
      // In this case, there are elements in the bounding group
      // (-1 in a field of odd degree, 1 everywhere else) that have norm -1
      dimSupper -:= 1;
    end if;
    // There might be elements of negative norm also in the other cases,
    // but this is not so easy to check without actually doing the expensive
    // computations below.
  end if;
  vprintf Selmer, 1:
          "  Upper bound for Selmer group dimension: %o.\n", dimSupper;
  vprintf Selmer, 1:
          "   ==> Upper bound for rank = %o.\n", dimSupper - rank2t;
  if not UseUnits then
    return dimSupper - rank2t, rank2t, Cas, <>, nfields;
  end if;
  // Now the units
  vprint Selmer, 2: "  Computing unit groups...";
  tu := Cputime();
// Remove this unit computation
  Us := [ <U, m> where U, m := pFundamentalUnits(fields[i], 2)
           : i in [1..#fields] ];
  if GetVerbose("Selmer") ge 2 then
    print "  Class group and unit data of the fields:";
    for i := 1 to #fact do
      printf "   Field given by %o:\n", fact[i];
      printf "    Class group = %o, units = %o\n",
             Invariants(Cls[i,1]), Invariants(Us[i,1]);
    end for;
  end if;
  t3 := Cputime(tu);
  // Find a basis of the kernel of the map L^*/(L^*)^2 --> I_L/I_L^2.
  B := [ Parent(f) | ];
 
  for i := 1 to #fact do
    inj := injs[i,1];
    U := Us[i,1]; Um := Us[i,2];
    // root of unity
    zeta := Um((ord div (2^Valuation(ord, 2)))*U.1) where ord := Order(U.1);
    B cat:= [ inj(zeta) ];
    // other units
    B cat:= [ inj(Um(U.j)) : j in [2..#Generators(U)] ];
    // Cl[2]
    Cl := Cls[i,1]; Clm := Cls[i,2];
    Clbasis := [ Clm((n div 2)*c) : c in Generators(Cl)
                                         | IsEven(n) where n := Order(c) ];
    // CLASS GROUP GUYS:
    B cat:= [ inj(gen) where _, gen := IsPrincipal(c*c) : c in Clbasis ];
  end for;
  if GetVerbose("Selmer") ge 3 then
    printf "  Kernel of valuation map has basis\n";
    PrintBasis(B, 4);
  end if;
  // So far, B is a basis of the kernel of the valuation map.
  // (IT HAS ALL THE UNITS AND CLASS GROUP GUYS)
  // We must enlarge B to get the inverse image of bigW2.
  B1 := [ ];
  prod := function(s)
            res := s[1];
            for i := 2 to #s do res := res * s[i]; end for;
            return res;
  end function;
  getgen := func< id, Cl, Clm | 
                    gen
                    where _, gen := IsPrincipal(id * Clm(c1)^2)
                    where c1 := -Cl![ IsOdd(c[i]) select (c[i] + invs[i]) div 2
                                                  else c[i] div 2
                                       : i in [1..#c] ]
                    where invs := Invariants(Cl)
                    where c := Eltseq(ClassRepresentative(id) @@ Clm) >; // ClassRepresentative appears pointless
  // GET S-UNITS THAT ARE RELEVANT
  // i.e. look in kerW2, the elements of which determine ideals 
  // that are principal mod squares, and that have a generator
  // which satisfies all local conditions 
  // (or, which might have such a generator??)
  // Recall that the format for pids is: 
  // every relevant pid from every field is in the SeqEnum pids,
  // represented as a list [* 1, 1, ... , pid, 1, 1, .. *] 
  // in which there is one entry for each field, and they are 
  // all trivial except the jth entry, where pid is an ideal for the jth field.
  for b in Basis(kerW2) do
    b1 := Parent(f)!0;
    for j := 1 to #fact do
      b1 +:= injs[j,2](getgen(prod([pids[i,j] : i in [1..#s]
                                              | s[i] eq GF(2)!1]),
                              Cls[j,1],
                              Cls[j,2]))
             where s := Eltseq(b);
    end for;
    Append(~B1, b1);
  end for; // b in Basis(kerW2)
  if not IsEmpty(B1) then
    if GetVerbose("Selmer") ge 3 then
      printf "  Additional generators of bounding group:\n";
      PrintBasis(B1, 4);
    end if;
    B cat:= B1;
  end if;
  bigV := KSpace(GF(2), #B);
  Bimage := [bigm1(b) : b in B];

// END OF OLD 

// TEST whether old and new agree: 
// run the next bit of the program on both Bimage and newBimage:
  
  if GetVerbose("Selmer") ge 3 then
    printf "  Images of generators of bounding group:\n";
    PrintBasis(Bimage, 4);
  end if;
  bighom := hom<bigV -> bigV1 | Bimage>;
  if Odd then
    Selmer := (bigW1 meet Image(bighom)) @@ bighom;
    BS := Basis(Selmer);
  else
    // The Big Fake Selmer group; the fake Selmer group is its quotient
    // modulo the image of Q^*
    BFSelmer := (bigW1 meet Image(bighom)) @@ bighom;
    vprintf Selmer, 3:
            "    dim(Big Fake Selmer group) = %o.\n", Dimension(BFSelmer);
    // image of added_gens is contained in BFSelmer
    if GetVerbose("Selmer") ge 3 then
      printf "    dim(subgp of Q^*/(Q^*)^2 mapping into BFS) = %o.\n",
             #added_gens;
      printf "    Basis = %o.\n", added_gens;
    end if;
    // Return basis of Big Fake Selmer group
    BS := Basis(BFSelmer);
  end if; // Odd

if compare_new_vs_old then
  // SECOND RUN, TESTING newBimage
  if GetVerbose("Selmer") ge 3 then
    printf "  Images of generators of bounding group:\n";
    PrintBasis(Bimage, 4);
  end if;
  bighom := hom<newbigV -> bigV1 | newBimage>;
  if Odd then
    Selmer := (bigW1 meet Image(bighom)) @@ bighom;
    newBS := Basis(Selmer);
  else
    // The Big Fake Selmer group; the fake Selmer group is its quotient
    // modulo the image of Q^*
    BFSelmer := (bigW1 meet Image(bighom)) @@ bighom;
    vprintf Selmer, 3:
            "    dim(Big Fake Selmer group) = %o.\n", Dimension(BFSelmer);
    // image of added_gens is contained in BFSelmer
    if GetVerbose("Selmer") ge 3 then
      printf "    dim(subgp of Q^*/(Q^*)^2 mapping into BFS) = %o.\n",
             #added_gens;
      printf "    Basis = %o.\n", added_gens;
    end if;
    // Return basis of Big Fake Selmer group
    newBS := Basis(BFSelmer);
  end if; // Odd

// COMPARE THE TWO 
  assert #BS eq #newBS;
  oldbighom := hom<bigV -> bigV1 | Bimage>;
  newbighom := hom<newbigV -> bigV1 | newBimage>;
  assert sub< bigV1 | [oldbighom(bs) : bs in BS] > eq sub< bigV1 | [newbighom(bs) : bs in newBS] >;
  vprint Selmer, 1: "The new method (which calls pSelmergroup) agrees with the old method!!";

// MY SELMER ELEMENTS
bigV := newbigV;  // drop the temporary name

  // multiply out the Selmer elements
  BS1 :=  [ &*[ bigFB[i] : i in [1..#bigFB] | bs[i] eq 1 ] mod f : bs in newBS ]; 
              // newBS is a subspace of bigV, which is a subspace of bigFBSpace.
end if;  // compare_new_vs_old

// OLD
if not compare_new_vs_old then
  BS1 := [ &*[ B[i] : i in [1..#B] | bs[i] eq GF(2)!1 ] mod f : bs in BS ];
end if;

  

  if Odd then
    dimS := #BS;
  else
    dimS := #BS - #added_gens;
    // If we have a quadratic subextension of L, then the dimension of
    // the image of BFQ in BFSelmer is one less.
    if HaveQuadraticSubextension then dimS +:= 1; end if;
    if CasGlob then
      // fake = no fake
      vprintf Selmer, 2:
              "  The Selmer group has dimension %o.\n\n", dimS;
    else
      // fake != no fake
      vprintf Selmer, 2:
              "  The fake Selmer group has dimension %o.\n", dimS;
      dimS +:= 1;
      vprintf Selmer, 2:
              "  The Selmer group has dimension %o.\n\n", dimS;
    end if;
  end if;
  vprintf Selmer, 2:
          "  Time for local computations: %o ms.\n", Round(1000*t1);
if compare_new_vs_old then t2 := cltime; end if;
  vprintf Selmer, 2:
          "  Time for class groups:       %o ms.\n", Round(1000*t2);
  vprintf Selmer, 2:
          "  Time for unit groups:        %o ms.\n", Round(1000*t3);
  vprintf Selmer, 2:
     "  Total time for old class/unit stuff: %o ms.\n", Round(1000*(t2+t3));

// TO DO: Remove this:
if compare_new_vs_old then
 oldms := Round(1000*(t2+t3));
 newms := Round(1000*(cltime+tnew));
 vprintf Selmer, 2: "  Time for new pSelmer stuff:          %o ms.\n", newms;
// if newms ge oldms + 1000 then
//    Write("~/TwoSelmerGroupDataTimings", <f, "NEW", newms, "OLD", oldms, Round(1000*cltime)>); 
// end if;
end if;

  return dimS - rank2t, rank2t, Cas,
         < ChangeUniverse(BS1, quo< Parent(f) | f>),
           Odd select [ Integers() | ] else added_gens,
           Odd or not HaveQuadraticSubextension
            select [ Integers() | ] else [ subext_disc ] >,
         nfields;
end function;

// The following produces a model suitable for TwoSelmerGroupData.

function ModelForTSG(C)
    g := Genus(C);
    // First simplify
    C1, m := SimplifiedModel(C);
    // Then make integral
    C1, m1 := IntegralModel(C1 : Reduce := true);
    m := m*m1;
    // Now, we have to do different things according to the parity of deg(f)
    f := HyperellipticPolynomials(C1);
    if IsOdd(Degree(f)) then
	a := LeadingCoefficient(f);
	C1, m1 := Transformation(C1, [a,0,0,1], a^g);
	m := m*m1;
    else // IsEven(Degree(f))
	a := Abs(LeadingCoefficient(f))/
             GCD(ChangeUniverse(Coefficients(f),Integers()));
	C1, m1 := Transformation(C1, [a,0,0,1], a^(g+1));
	m := m*m1;
    end if;
    return C1, m;
end function;

intrinsic TwoSelmerGroupData(J::JacHyp : Bound := 0,
                                         BachBound := false,  // new option
                                         BachBoundFrac := 0,  // new option
                                         BoundType := "",     // old option, still works
                                         Points := {},
                                         Fields := {})
           -> RngIntElt, RngIntElt, Tup, List, GrpAb, Map
{This intrinsic is now replaced by TwoSelmerGroup and may not work in future versions.}
/* {Compute the 2-Selmer group of J (a Jacobian of a hyperelliptic curve
  defined over the rationals). The first value is the upper bound for the
  Mordell-Weil rank deduced from the computation, the second value is
  the dimension of the Selmer group. The third value gives a presentation
  of the (fake) Selmer group (but is only defined when UseUnits is true).
  It is a triple <seq1, seq2, seq3>, where seq1 is a sequence of elements
*/
//  in L = Q[x]/(f(x)) representing a basis of some subgroup S1 of L^*/(L^*)^2,
//  seq2 and seq3 are sequences of integers representing bases of subgroups
//  S2 and S3 of Q^*/(Q^*)^2, respectively, and the (fake) Selmer group S
//  fits into the exact sequence 0 --> S3 --> S2 --> S1 --> S --> 0.
//  This data is in terms of the possibly modified model of the curve
//  that the algorithm actually uses. As a fourth value, a set of the
//  umber fields used in the function is returned.} 
  
// New optional parameters for controlling the class group
// computation have been added by Steve 
// (a less confusing way of packaging of the same choices).
// The new options now appear in the documentation,
// but the old options should still work as before.
//  The (old) parameters have the following meaning. BoundType and Bound
//  determine the parameter Bound for the calls to ClassGroup.
//  BoundType can be one of "Default" (no Bound parameter for ClassGroup),
//  "Absolute" (use Min(MinkowskiBound(field), Bound)), "Relative" (use
//  Min(MinkowskiBound(field), Floor(Bound*Log(Abs(Discriminant(field)))))),
//  "Minkowski" (use MinkowskiBound(field)) or "Bach" (use 
//  Min(MinkowskiBound(field), BachBound(field))). Bound specifies the
//  Bound in case BoundType is "Absolute" or "Relative". If a (positive)
//  Bound is specified, but no BoundType is given, the BoundType is taken
//  to be "Absolute", otherwise "Default". 
//  If UseUnits is false, the program does not attempt to compute the
//  fundamental units of the number fields involved. This saves much time
//  in many cases, but does only lead to an upper bound for the Selmer group
//  dimension (and the parity information is lost).
//  You can use Points to specify a sequence or (indexed) set of rational
//  points on J; they will be used to find the local images. This can make
//  this part of the computation faster. 
//  Fields can be used to pass a sequence or set of number fields to the
//  algorithm. If one of the fields coming up in the computation is
//  isomorphic to one of the given fields, the given field will be used.
//  This can be useful if the class and unit groups of these fields are
//  already known. 

  compare_new_vs_old := false;  // refers to the introduction of pSelmerGroup
  UseUnits := true;   // deprecated vararg

  t0 := Cputime();
  C := Curve(J);
  Cin:=C;
  require BaseField(C) cmpeq Rationals():
          "TwoSelmerGroupData: J must have the rationals as its base field.";
  require Genus(C) ge 1: "The curve must have genus at least one.";
  vprintf Selmer, 1: "TwoSelmerGroupData of %o\n", J;
  // Put curve into required form
  C1, m := ModelForTSG(C);
  if C1 ne C then
    vprintf Selmer: "Change curve into %o\n", C1;
    // transform the curve, Jacobian, and the points
    C := C1;
    J := Jacobian(Codomain(m));
    Points := [ pt@m : pt in Points ];
  end if;
  f,h := HyperellipticPolynomials(C);  assert h eq 0;

  // PROCESS THE OPTIONAL PARAMETERS (regarding the Bound parameter in ClassGroup)
   
  // Express the new options in terms of the old parameters.
  if Bound gt 0 and BoundType eq "" then 
     BoundType := "Absolute"; 
  end if;
  if BachBound then BoundType := "Bach"; end if;
  if BachBoundFrac gt 0 then
     error if Bound ne 0, "Specify either Bound or BachBoundFrac, not both!";
     BoundType := "Relative";
     Bound := 12*BachBoundFrac;   // in the old system, Bound has this
  end if;                         // meaning when BoundType is "Relative"

  // Now proceed as before. (What follows has not been changed)
  if BoundType eq "" then
    BoundType := Bound gt 0 select "Absolute" else "Default";
  end if;
  require BoundType in ["Default", "Absolute", "Relative", "Minkowski", "Bach"]:
          "The BoundType must be one of ",
          "\"Default\", \"Absolute\", \"Relative\", \"Minkowski\" or \"Bach\".";
  if BoundType eq "Absolute" or BoundType eq "Relative" then
    require Bound gt 0: "Bad optional parameters (see the documentation)";
  end if;
  
  if not IsEmpty(Points) then
    require Universe(Points) cmpeq J:
            "Points must be a sequence or set of points on J.";
    // eliminate 2-torsion points (they are not necessary)
    Points := { pt : pt in Points | 2*pt ne J!0 };
    // eliminate divisors containing a Weierstrass point in their support
    // (better solutions are possible...)
    Points := { pt : pt in Points | Degree(GCD(pt[1],pt[2])) eq 0 };
    vprintf Selmer: " Use Points = %o\n", Points;
  end if;
  if not IsEmpty(Fields) then
    require forall{K : K in Fields | Category(K) eq FldNum}:
            "Fields must be a set or sequence of number fields.";
  end if;
  if IsOdd(Degree(f)) then
    b, t, _, S, fields 
      := TwoSelmerWork(C, BoundType, Bound, UseUnits, Points, Fields, compare_new_vs_old);
    if GetVerbose("Selmer") ge 1 then
      printf " Selmer group dimension = %o,\n", b+t;
      printf " Dimension of 2-torsion = %o,\n", t;
      printf "  ==> Bound for the MW-rank = %o.\n", b;
    end if;
    if (UseUnits or b+t eq 0) and GetVerbose("Selmer") ge 3 then
      if b+t gt 0 then
        printf "  Basis of Selmer group:\n";
        PrintBasis(S[1], 4);
      else
        print "  Selmer group is trivial.";
      end if;
    end if;
    vprintf Selmer, 1: " Total time: %o ms.\n", Round(1000*Cputime(t0));
    f,h:=HyperellipticPolynomials(Cin);
    if Cin ne C and h eq 0 then
      vprint Selmer:"Transforming presentation of S back to model C.";
      ACin:=quo<Parent(f)|f>;
      AC:=Universe(S[1]);
      meq:=DefiningEquations(m);
      ACtoACin:=hom<AC->ACin|
          Evaluate(meq[1],[ACin.1,0,1])/Evaluate(meq[3],[ACin.1,0,1])>;
      S:=<[ACin|ACtoACin(f):f in S[1]],S[2],S[3]>;
    end if;
    SelGroup := AbelianGroup([ 2 : i in [1..b+t] ]);
    SelGroupToAlg := map< SelGroup -> Universe(S[1]) |
                                s :-> &+[ Eltseq(s)[i]*S[1][i] : i in [1..#S[1]] ]>;
    return b, b+t, S, fields, SelGroup, SelGroupToAlg;
  else
    require Degree(f) eq 6:
            "TwoSelmerGroup for equations of even degree is only implemented",
            "for genus 2.";
    lcf := LeadingCoefficient(f);
    f1 := (1/lcf)*f;
    b, t, Cas, S, fields 
      := TwoSelmerWork(C, BoundType, Bound, UseUnits, Points, Fields, compare_new_vs_old);
    dimS := b+t;
    if GetVerbose("Selmer") ge 1 then
      printf " Selmer group dimension = %o,\n", dimS;
      printf " Dimension of 2-torsion = %o,\n", t;
      printf "  ==> Bound for the MW-rank = %o.\n", b;
    end if;
    if IsOdd(J) then
      b -:= 1;
      vprintf Selmer, 1:
              " Jacobian is odd ==> Better bound for the MW-rank = %o.\n", b;
    end if;
    if (UseUnits or dimS eq 0) and GetVerbose("Selmer") ge 3 then
      if dimS gt 0 then
        printf "  Presentation of fake Selmer group:\n";
        printf "  ---------------------------------------------------------\n";
        PrintBasis(S[1], 4);
        printf "  ---------------------------------------------------------\n";
        printf "    %o\n", S[2];
        if not IsEmpty(S[3]) then
          printf
               "  ---------------------------------------------------------\n";
          printf "    %o\n", S[3];
        end if;
        printf "  ---------------------------------------------------------\n";
      else
        print "  Selmer group is trivial.";
      end if;
    end if;
    vprintf Selmer, 1: " Total time: %o ms.\n", Round(1000*Cputime(t0));

    require #S[1] ge #S[2]-#S[3] : "Wrong number of generators in the computed data S";
    if #S[1] eq #S[2] and #S[3] eq 0 then 
      S[1] := S[2];  // S[2] generates S[1] in A*/A^2
    elif #S[1] gt #S[2]-#S[3] then
      // Sort S[1] so that its initial elements form a basis of S[1]/S[2]
      // (this is used in the map returned below)
      S21 := S[2] cat S[1];
      badps := Seqset(BadPrimes(C) cat 
                 &cat[PrimeDivisors(Denominator(cc)) : cc in Coefficients(s), s in S21]);
      M := Matrix(GF(2), #S21, 0, []);
      p := 2;
      repeat
        // collect residue maps to finite fields (for good primes), and 
        // define a matrix M over F_2 with M[i,j] = 0 iff S[1][i] is a 
        // square in the jth finite field.
        p := NextPrime(p);  
        while p in badps do p := NextPrime(p); end while;
        fp := Polynomial([GF(p)!Integers()!cc : cc in Coefficients(f)]);
        for tup in Factorization(fp) do 
          if Degree(tup[1]) gt 1 then continue; end if; // because creation of finite fields is slow
          assert tup[2] eq 1;
          r := -Coefficients(tup[1])[1];
          S21residues := [ &+[cc[i]*r^(i-1) : i in [1..#cc]] 
                             where cc is Coefficients(s) : s in S21 ];
          if &or[IsZero(s) : s in S21residues] then continue; end if;
          col := Matrix(GF(2), #S21, 1, 
                        [IsSquare(s) select 0 else 1 : s in S21residues]);
          M := HorizontalJoin(M, col);
        end for; 
        error if Ncols(M) gt 100 and Rank(M) gt #S[1], "Something is wrong in TwoSelmerGroupData";
      until Rank(M) eq #S[1];
      basis := [];  nonbasis := [];  // partition of S[1]
      rk := Rank(RowSubmatrix(M,1,#S[2]));  assert rk eq #S[2]-#S[3];
      for i := 1 to #S[1] do 
        if rk lt #S[1] and Rank(RowSubmatrix(M,1,#S[2]+i)) gt rk then 
          rk +:= 1;
          Append( ~basis, S[1][i]);
        else
          Append( ~nonbasis, S[1][i]);
        end if;
      end for;
      S[1] := basis cat nonbasis;
    end if;
    
    f,h:=HyperellipticPolynomials(Cin);
    if Cin ne C and h eq 0 then
      vprint Selmer:"Transforming presentation of S back to model C.";
      ACin:=quo<Parent(f)|f>;
      AC:=Universe(S[1]);
      meq:=DefiningEquations(m);
      ACtoACin:=hom<AC->ACin|
          Evaluate(meq[1],[ACin.1,0,1])/Evaluate(meq[3],[ACin.1,0,1])>;
      S:=<[ACtoACin(f):f in S[1]],S[2],S[3]>;
    end if;
    
    Selgens := S[1];
    if #Selgens lt dimS then 
      // phi must have a kernel of order 2, even into A*/A*^2 
      // (I'm not sure whether this can happen anyway) 
      Append( ~Selgens, 1);
    end if;
    assert #Selgens ge dimS;
    SelGroup := AbelianGroup([ 2 : i in [1..dimS] ]);
    EtAl := Universe(S[1]);
    SelGroupToAlg := map< SelGroup -> EtAl |
                                s :-> &*[EtAl| Selgens[i]^ss[i] : i in [1..dimS]] where ss is Eltseq(s)>;
    return b, dimS, S, fields, SelGroup, SelGroupToAlg;
  end if;
end intrinsic;
