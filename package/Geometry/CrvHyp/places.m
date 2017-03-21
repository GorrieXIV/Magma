freeze;

/*******************************************
 * Hyperelliptic/places.m                  *
 *                                         *
 * An attempt to implement a unified place *
 * machinery                               *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 12-Oct-2001                     *
 *******************************************/

/*
 17/04/03 Nicole Sutherland
    Change creation intrinsics which are used to functions so that creation
    can be restricted to certain package files.
    Intrinsics on rational places are left as intrinsics for generality
    with proper places.
*/

/*----------------------------------------------------------------------
  Basically, we want to implement the ingredients of places for field
  with divisor theory.
  ----------------------------------------------------------------------*/
/* The field is determined by the prime so is unnecessary as input */

MyPlace := recformat< name : RngElt, field : Fld, unif : RngElt, val : Map, 
		      res : Fld, rmap : Map, lift : Map, 
		      deg : RngIntElt >;

function MakePlaceIntElt(p)
// Create a MyPlace object from the given data.
    assert Type(p) eq RngIntElt;

    assert IsPrime(p);
    F := Rationals();
    return rec< MyPlace | name := p,
                          field := F,
                          unif := F!p,
                          val := map<F -> Integers() | x :-> Valuation(x, p)>,
                          res := GF(p),
                          rmap := Bang(F, GF(p)),
                          lift := Bang(GF(p), Integers())*Bang(Integers(), F),
                          deg := 1 >;
end function;

/*
Unused
intrinsic MakePlace(F::FldRat, I::RngInt) -> Rec
{Create a MyPlace object from the given data.}
    return MakePlaceIntElt(F, Generator(I));
end intrinsic;
*/

function MakePlaceRatElt(p)
// Create a MyPlace object from the given data.
    assert Type(p) eq FldRatElt;
    assert Denominator(p) eq 1;

    return MakePlaceIntElt(Integers()!p);
end function;

/*
Unused : and number fields have there own places now anyway
intrinsic MakePlace(F::FldNum, p::RngOrdIdl) -> Rec
{Create a MyPlace object from the given data.}
    require Integers(F) eq Order(p):
            "p must be an ideal of the maximal order in F.";
    require IsPrime(p): "p must be a prime ideal.";
    RF, rm := ResidueClassField(p);
    return rec< MyPlace | name := p,
                          field := F,
                          unif := F!UniformizingElement(p),
                          val := map<F -> Integers() | x :-> Valuation(x, p)>,
                          res := RF,
                          rmap := rm,
                          lift := map< RF -> F | x :-> F!(x @@ rm) >,
                          deg := Degree(p) >;
end intrinsic;
*/

function MakePlaceUPolElt(p)
// Create a MyPlace object from the given data.}
    assert Type(p) eq RngUPolElt;
    /*
    assert Integers(F) eq Parent(p);
    Above assertion is slightly stronger : Rank 1 function fields
    can use dpolys
    require Rank(F) eq 1:
            "F must be a rational function field of one variable.";
    require CoefficientRing(Parent(p)) cmpeq CoefficientRing(F):
            "F must be the field of fractions of the parent of p.";
    */
    assert IsIrreducible(p);
    F := FieldOfFractions(Parent(p));
    val0 := function(y)
              v := 0;
              while IsDivisibleBy(y, p) do
                v +:= 1;
                y := ExactQuotient(y, p);
              end while;
              return v;
            end function;
    val1 := function(x)
              if x eq 0 then return Infinity(); end if;
              return val0(Parent(p)!Numerator(x))
                      - val0(Parent(p)!Denominator(x));
            end function;
    B := CoefficientRing(Parent(p));
    if Degree(p) eq 1 then
      RF := B;
      rm := hom< F -> B | -Coefficient(p, 0) >;
      li := Bang(B, F);
    else
      RF := ext< B | p >;
      rm := hom<F -> RF | RF.1>;
      li := map<RF -> F | x :-> F!Parent(p)!Eltseq(x)>;
    end if;
    return rec< MyPlace | name := p,
                          field := F,
                          unif := F!p,
                          val := map<F -> Integers() | x :-> val1(x)>,
                          res := RF,
                          rmap := rm,
                          lift := li,
                          deg := Degree(p) >;
end function;

function MakePlaceFunRatElt(p)
// Create a MyPlace object from the given data.
    assert Type(p) eq FldFunRatUElt;
    assert Denominator(p) eq 1;
    return MakePlaceUPolElt(Numerator(p));
end function;

function MakePlaceFunRatInfty(F, p)
// Create a MyPlace object from the given data.
    assert Type(F) eq FldFunRat;
    assert Rank(F) eq 1;
    assert Type(Integers(F)) eq RngUPol;
    assert Type(p) eq Infty;

    B := CoefficientRing(F);
    return rec< MyPlace | name := Infinity(),
                          field := F,
                          unif := F.1^-1,
                          val := map<F -> Integers() | x :-> -Degree(x)>,
                          res := B,
                          rmap := hom<F -> F | F.1^-1>*hom<F -> B | 0>,
                          lift := Bang(B, F),
                          deg := 1 >;
end function;

//---------------------------------------------------------------------

intrinsic Valuation(x::FldElt, pl::Rec) -> RngIntElt
{Valuation function at a place on a hyperelliptic curve.}
    require ["name", "field", "unif", "val", "res", "rmap", "lift", "deg"] 
			eq Names(pl) : "Record must represent a place";
    require Parent(x) cmpeq pl`field:
            "Parent of x must be the field pl belongs to.";
    if x eq 0 then
      return Infinity();
    else
      return (pl`val)(x);
    end if;
end intrinsic;

intrinsic ResidueClassField(pl::Rec) -> Fld, Map, Map
{Construct residue class field of pl on a hyperelliptic curve, together with reduction and lifting maps.}
    require ["name", "field", "unif", "val", "res", "rmap", "lift", "deg"] 
			eq Names(pl) : "Record must represent a place";
    return pl`res, pl`rmap, pl`lift;
end intrinsic;

intrinsic Degree(pl::Rec) -> RngIntElt
{The degree of the place pl on a hyperelliptic curve.}
    require ["name", "field", "unif", "val", "res", "rmap", "lift", "deg"] 
			eq Names(pl) : "Record must represent a place";
    return pl`deg;
end intrinsic;

intrinsic UniformizingElement(pl::Rec) -> FldElt
{A uniformizer at the place pl on a hyperelliptic curve.}
    require ["name", "field", "unif", "val", "res", "rmap", "lift", "deg"] 
			eq Names(pl) : "Record must represent a place";
    return pl`unif;
end intrinsic;
