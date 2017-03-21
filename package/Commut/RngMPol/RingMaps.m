freeze;

// import <other needed files>


/////////////////////////////////////////////////////////


intrinsic DisplayPolyMap(phi::Map)
{Display a map between polynomial rings.}

    require (Type(Domain(phi))   eq RngMPol) and 
            (Type(Codomain(phi)) eq RngMPol) :
         "not a map between polynomial rings.";


  print [phi(Domain(phi).i) : i in [1..Rank(Domain(phi))] ];

end intrinsic;


/////////////////////////////////////////////////////////


intrinsic PolyMapKernel (phi::Map) -> RngMPol
{ Creates the kernel of a homomorphism "phi" between polynomial rings.}
//  Based on code by Jon Carlson (Athens, GA). 
// 
    P1 := Domain(phi);
    P2 := Codomain(phi);

    require (Type(P1) eq RngMPol) and (Type(P2) eq RngMPol) :
         "not a map between polynomial rings.";

    r1 := Rank(P1);
    r2 := Rank(P2);
    f := CoefficientRing(P1);
    T := PolynomialRing(f,r1+r2);
    h1 := hom<P1->T|[T.(r2+i): i in [1 .. r1]]>;
    h2 := hom<P2->T|[T.i: i in [1 .. r2]]>;
    I := ideal<T|[h1(P1.i) - h2(phi(P1.i)):i in [1 .. r1]]>;
    Groebner(I: Al := "Direct");
    J := EliminationIdeal(I,r2);
    seq := [P1!0: i in [1 .. r2]] cat [P1.i: i in [1 .. r1]];
    g := hom<T->P1|seq>;
    BB := [g(x): x in Basis(J)];
    L := ideal<P1|BB>;
    return L;
end intrinsic;



/////////////////////////////////////////////////////////

/*
intrinsic Annihilator (idel::RngMPol) -> RngMPol
{Creates the annihilator of the ideal as an ideal of the polynomial ring.}

    return ColonIdeal(ideal< Parent(idel) | 0 >, idel);

end intrinsic;
*/

/*
intrinsic Annihilator (ring_elt::RngMPolElt, idel::RngMPol) -> RngMPol
{Creates the ideal corresponding to the .}
//  Based on code by  Jon Carlson (Athens, GA). 

    require idel subset Parent(ring_elt) : 
     "Runtime error in 'Annihilator': polynomial and ideal are in different rings";

    return ColonIdeal(idel, ideal< Parent(ring_elt) | ring_elt >);
end intrinsic;
*/


/*
intrinsic Annihilator (idel::RngMPol) -> RngMPol
{ Returns the annihilator of an ideal by a polynomial ring. }
//  Based on code by  Jon Carlson (Athens, GA). 

//    require idel subset ring : 
//           "Runtime error in 'Annihilator': the ideal is not in the ring";

    return ColonIdeal(idel, Generic(idel));
end intrinsic;
*/

/////////////////////////////////////////////////////////


intrinsic IsInImage (phi::Map, the_poly::RngMPolElt) -> BoolElt
{ Returns True if the polynomial the_poly is in the image of the ring map phi.}
//
// Algorithm taken from Adams and Loustanau, p.82
//
// Recycles the code from PKernel() due to  Jon Carlson.
// 
    domain_of_phi := Domain(phi);
    codomain_of_phi := Codomain(phi);

    require (Type(domain_of_phi)   eq RngMPol) and 
            (Type(codomain_of_phi) eq RngMPol) :
             "not a map between polynomial rings.";

    require Parent(the_poly) eq codomain_of_phi : 
                   "Runtime error in 'IsInImage': polynomial is in wrong ring";

    rank_of_domain := Rank(domain_of_phi);
    rank_of_codomain := Rank(codomain_of_phi);
    cr := CoefficientRing(domain_of_phi);

                  // We lift everything up to this big ring T
    T := PolynomialRing(cr,rank_of_domain+rank_of_codomain, "lex");
    h1 := hom< domain_of_phi -> T | 
                   [T.(i+rank_of_codomain) : i in [1 .. rank_of_domain]]>;
    h2 := hom< codomain_of_phi -> T | [T.i : i in [1 .. rank_of_codomain]]>;

                 // and form the ideal I
    I := ideal< T | [h1(domain_of_phi.i)-h2(phi(domain_of_phi.i)) :
                                           i in [1 .. rank_of_domain]]>;
    Groebner(I: Al := "Direct");

    // the poly is in the image of phi iff its reduced form (w.r.t I)
    // is in the rank_of_domain'th elimination ideal of I
    poly_reduced := NormalForm(h2(the_poly), I);
    return forall{
	i : i in [1..rank_of_codomain] | Degree(poly_reduced, T.i) le 0
    };

end intrinsic;



////////////////////////////////////////////////////


intrinsic IsSurjective (phi::Map[RngMPol, RngMPol]) -> BoolElt
{ Returns True if the ring map phi is surjective. }
// This is true iff each indeterminate in the codomain is in the image.
// 
    codomain_of_phi := Codomain(phi);

    /*
    require (Type(Domain(phi)) eq RngMPol) and 
           (Type(codomain_of_phi) eq RngMPol) :
         "not a map between polynomial rings.";
    */

    for index in [1..Rank(codomain_of_phi)] do
        if not IsInImage(phi, codomain_of_phi.index) then
             return false;
        end if;
    end for;
    return true;
end intrinsic;



////////////////////////////////


intrinsic Implicitization (phi::Map) -> RngMPol
{ Assumes that phi is a parametrization of a variety
  defined by equations y_i = f_i(x_i) where the x_i 
  are in the CODOMAIN of phi and the y_i are in the DOMAIN of phi.
  Returns the smallest variety containing the points defined
  by these equations.}

/*
  Assumes that phi is a parametrization of a variety.
  The variety is defined by equations y_i = f_i(x_i)
  where the x_i are the paramenters.

  NOTE: the x_i are in the CODOMAIN of phi and the y_i are in
  the DOMAIN of phi.  It's done like this so that the f_i can be
  read off the usual representation of the variety in terms of the
  paramenters.

  These equations may not define a variety: this function
  actually returns the smallest variety containing the set of points
  (the Zariski closure of the set).
 
  The algorithm is taken from Cox, Little and O'Shea, p.97
*/

    ambient_space := Domain(phi);
    parameters    := Codomain(phi);

    require (Type(ambient_space) eq RngMPol) and 
            (Type(parameters)   eq RngMPol) :
         "not a map between polynomial rings.";

    rank_of_ambient_space := Rank(ambient_space);
    rank_of_parameters    := Rank(parameters);
    cr := CoefficientRing(ambient_space);

                  // We lift everything up to this big ring T
    T := PolynomialRing(cr, rank_of_ambient_space + rank_of_parameters);
    h1 := hom< ambient_space  -> T | 
             [T.(i+rank_of_parameters) : i in [1 .. rank_of_ambient_space]]>;
    h2 := hom< parameters -> T |
                                  [T.i : i in [1 .. rank_of_parameters]]>;

                 // and form the ideal I
    I := ideal< T | [h1(ambient_space.i)-h2(phi(ambient_space.i)) :
                                           i in [1 .. rank_of_ambient_space]]>;
    Zariski_raw := EliminationIdeal(I, rank_of_parameters);

              // push this back into the ambient space - this code is a
              // workaround for something in Magma that's behaving unexpectedly
    h1inv :=  hom< T  -> ambient_space | 
                    [ambient_space!0 : i in [1 .. rank_of_parameters]] cat 
                    [ambient_space.i : i in [1 .. rank_of_ambient_space]] >;

    Zariski :=  ideal< ambient_space | [ h1inv(basis_elt) :
                                  basis_elt in Basis(Zariski_raw)] >;
    return(Zariski);
end intrinsic;
