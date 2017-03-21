freeze;

/////////////////////////////////////////////////////////////////////////
// ehrhart.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38137 $
// $Date: 2012-04-13 00:14:20 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating Ehrhart data.
/////////////////////////////////////////////////////////////////////////

import "../convexhull/sublattice.m": fp_emb_has_volume_form;
import "../convexhull/convexhull.m": fp_get_dimension, fp_get_pullback_vertices, fp_decomposition_of_cone_at_pullback_vertex, fp_get_nonvanishing_form;
import "smooth.m": calculate_smooth_ehrhart_data;
import "reflexive.m": calculate_reflexive_ehrhart_data;
import "simplex.m": calculate_simplex_ehrhart_data;

declare attributes TorPol:
    Ehrhart_gen_func,           // The generating function of the Ehrhart series
    Ehrhart_delta,              // The Ehrhart delta-vector (also called the
                                // h*-vector)
    Ehrhart_qpoly,              // The Ehrhart quasi-polynomial for P
    Ehrhart_coeffs;             // The Ehrhart coefficients for 1*P,...,l*P

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the value (t + k) choose r, where t is an indeterminate of a
// polynomial ring.
function binomial_contribution(t,k,r)
    rfac:=Factorial(r);
    return &+[(StirlingFirst(r,i) / rfac) * (t + k)^i : i in [0..r]];
end function;

// Convert a decomposition into its univariate form, keeping track of the
// largest power of t that can remove from the numerator, and tidying
// the denominators. The generating function is represented as a sequence:
//      [<N1,D1,E1>, <N2,D2,E2>, ...]
// where each triple represents the rational function:
//      Ei * t^Ni / &*[t^DD - 1 : DD in Di];
// Each of the DD are positive. The term t^c is factored out of the generating
// function.
function reduce_to_univariate(decomp,lambda)
    c:=0;
    d:=#lambda;
    genfuncs:=[];
    for triple in decomp do
        E:=triple[3];
        N:=Integers() ! &+[lambda[i] * triple[1][i] : i in [1..d]];
        D:=[Integers()|];
        for ray in triple[2] do
            DD:=Integers() ! &+[lambda[i] * ray[i] : i in [1..d]];
            if DD lt 0 then
                DD:=-DD;
                N+:=DD;
            else
                E*:=-1;
            end if;
            Append(~D,DD);
        end for;
        if N lt 0 then
            if N lt c then c:=N; end if;
        elif c ge 0 and (c eq 0 or N lt c) then
            c:=N;
        end if;
        Append(~genfuncs,<N,D,E>);
    end for;
    // Remove the common factor t^c from the numerators
    for i in [1..#genfuncs] do
        genfuncs[i][1] -:= c;
    end for;
    // Return the data
    return genfuncs,c;
end function;

// Uses Henrici's (1974) recurrance relation to calculate the coefficient of
// s^#D in P(s) / Q(s), where P(s) = (1 + s)^N and Q(s) =
// &*[((1 + s)^DD - 1) / s : DD in D].
// R = Power series ring for expansions up to (and including) s^(#D + 1).
function calculate_coefficient(N,D,R)
    s:=R.1;
    P:=Power(1 + s,N);
    Q:=&*[((1 + s)^DD - 1) div s : DD in D];
    // Get the coefficients from P and Q for s^0,...,s^d
    coeffsP,i:=Coefficients(P);
    if i ne 0 then coeffsP:=[0 : j in [1..i]] cat coeffsP; end if;
    if #coeffsP ne #D + 1 then
        coeffsP cat:= [0 : j in [1..#D + 1 - #coeffsP]]; end if;
    coeffsQ,i:=Coefficients(Q);
    assert i eq 0;
    if #coeffsQ ne #D + 1 then
        coeffsQ cat:= [0 : j in [1..#D + 1 - #coeffsQ]]; end if;
    // Now we use the recurrance relation to calculate the coefficient we need
    coeffs:=[Rationals() | coeffsP[1] / coeffsQ[1]];
    for k in [2..#D + 1] do
        Append(~coeffs, (1 / coeffsQ[1]) * (coeffsP[k] - 
                            &+[coeffsQ[i] * coeffs[k + 1 - i] : i in [2..k]]));
    end for;
    return coeffs[#D + 1];
end function;

// Returns the number of lattice points in P
function number_of_points(P)
    // Check that P lies in a sublattice
    if not fp_emb_has_volume_form(P) then return 0; end if;
    // Check that P isn't 0-dimensional
    if fp_get_dimension(P) eq 0 then return 1; end if;
    // Get the decomposition of the supporting cones into univariate cones and
    // associated numerators
    decomp:=&cat[fp_decomposition_of_cone_at_pullback_vertex(P,v) :
                                              v in fp_get_pullback_vertices(P)];
    // Reduce the decomposition from multivariate to univariate form
    genfuncs:=reduce_to_univariate(decomp,fp_get_nonvanishing_form(P));
    // Making the transformation t = s + 1, each contribution to the generating
    // function can we written as:
    //      Ei * s^-d * Pi(s) / Qi(s)
    // where Pi(s) = (1 + s)^Ni and Qi(s) = &*[((1 + s)^DD - 1) / s : DD in Di].
    // Thus to calculate the constant term in the expansion around s = 0 it is
    // enough to find the coefficient of the s^d term in Pi(s) / Qi(s).
    R:=PowerSeriesRing(Integers(),fp_get_dimension(P) + 2);
    num:=&+[triple[3] * calculate_coefficient(triple[1],triple[2],R) :
                                                            triple in genfuncs];
    bool,num:=IsCoercible(Integers(),num);
    assert bool;
    return num;
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure ehrhart_apply_translation(P,CP,Q)
    if IsIntegral(Q) then
        if assigned P`Ehrhart_gen_func then
            CP`Ehrhart_gen_func:=P`Ehrhart_gen_func; end if;
        if assigned P`Ehrhart_delta then
            CP`Ehrhart_delta:=P`Ehrhart_delta; end if;
        if assigned P`Ehrhart_qpoly then
            CP`Ehrhart_qpoly:=P`Ehrhart_qpoly; end if;
        if assigned P`Ehrhart_coeffs then
            CP`Ehrhart_coeffs:=P`Ehrhart_coeffs; end if;
    end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure ehrhart_apply_negation(P,CP)
    if assigned P`Ehrhart_gen_func then
        CP`Ehrhart_gen_func:=P`Ehrhart_gen_func; end if;
    if assigned P`Ehrhart_delta then
        CP`Ehrhart_delta:=P`Ehrhart_delta; end if;
    if assigned P`Ehrhart_qpoly then
        CP`Ehrhart_qpoly:=P`Ehrhart_qpoly; end if;
    if assigned P`Ehrhart_coeffs then
        CP`Ehrhart_coeffs:=P`Ehrhart_coeffs; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure ehrhart_change_ambient(P,CP,L)
    if assigned P`Ehrhart_gen_func then
        CP`Ehrhart_gen_func:=P`Ehrhart_gen_func; end if;
    if assigned P`Ehrhart_delta then
        CP`Ehrhart_delta:=P`Ehrhart_delta; end if;
    if assigned P`Ehrhart_qpoly then
        CP`Ehrhart_qpoly:=P`Ehrhart_qpoly; end if;
    if assigned P`Ehrhart_coeffs then
        CP`Ehrhart_coeffs:=P`Ehrhart_coeffs; end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure ehrhart_change_to_maximal(P,CP,emb,trans)
    if assigned P`Ehrhart_qpoly then
        CP`Ehrhart_qpoly:=P`Ehrhart_qpoly; end if;
    if assigned P`Ehrhart_coeffs then
        CP`Ehrhart_coeffs:=P`Ehrhart_coeffs; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic EhrhartCoefficient(P::TorPol,k::RngIntElt) -> RngIntElt
{The number of lattice points in the dilation k*P of the polytope P}
    require IsPolytope(P): "Polyhedron must be a polytope";
    // First we see if we know the value already
    if IsEmpty(P) then return 0; end if;
    if k eq 0 then return 1; end if;
    // When k is non-negative we check whether we have the coefficient to hand
    if k ge 0 then
        if assigned P`Ehrhart_coeffs and IsDefined(P`Ehrhart_coeffs,k) then
            return P`Ehrhart_coeffs[k];
        end if;
        // Is it worth creating the Ehrhart quasi-polynomial?
        if not assigned P`Ehrhart_qpoly and not assigned P`Ehrhart_gen_func then
            return EhrhartCoefficients(P,k)[k + 1];
        end if;
    end if;
    // We calculate the coefficient using the quasi-polynomial
    qpol:=EhrhartPolynomial(P);
    m:=k mod #qpol;
    k:=Integers() ! (k - m) / #qpol;
    return Evaluate(qpol[m + 1],k);
end intrinsic;

intrinsic EhrhartCoefficients(P::TorPol,l::RngIntElt) -> SeqEnum[RngIntElt]
{The first l+1 coefficients of the Ehrhart series for the polytope P (i.e. from 0*P up to and including l*P)}
    require l ge 0: "l must be a non-negative integer";
    if not assigned P`Ehrhart_coeffs or #P`Ehrhart_coeffs lt l then
        require IsPolytope(P): "Polyhedron must be a polytope";
        // Get the degenerate case out of the way
        if IsEmpty(P) then
            P`Ehrhart_coeffs:=[Integers() | 0 : i in [1..l]];
            return [0] cat P`Ehrhart_coeffs;
        end if;
        // Calculate the missing coefficients
        if not assigned P`Ehrhart_coeffs then
            P`Ehrhart_coeffs:=[Integers()|];
        end if;
        // We need to decide whether it's going to be worth just calculating the
        // Ehrhart generating function
        if not assigned P`Ehrhart_gen_func then
            if IsSmooth(P) then
                _:=EhrhartSeries(P);
            elif l gt 2 and Dimension(P) le 5 and IsReflexive(P) then
                _:=EhrhartSeries(P);
            else
                kr:=(Dimension(P) + 1) * LCM(&cat[[Integers() |
                          Denominator(c) : c in Eltseq(v)] : v in Vertices(P)]);
                if l ge kr then _:=EhrhartSeries(P); end if;
            end if;
        end if;
        // If we know the generating function then we use that, otherwise we
        // fill in the missing coefficients the hard way
        if assigned P`Ehrhart_gen_func then
            S:=PowerSeriesRing(Integers(),l + 1);
            coeffs,i:=Coefficients(S ! P`Ehrhart_gen_func);
            if i eq 0 then
                Remove(~coeffs,1);
            elif i gt 1 then
                coeffs:=[Integers() | 0 : j in [1..i - 1]] cat coeffs;
            end if;
            if #coeffs lt l then
                coeffs cat:= [Integers() | 0 : j in [1..l - #coeffs]];
            end if;
            P`Ehrhart_coeffs:=coeffs;
        else
            for k in [1..l] do
                if not IsDefined(P`Ehrhart_coeffs,k) then
                    P`Ehrhart_coeffs[k]:=number_of_points(k * P);
                end if;
            end for;
        end if;
    end if;
    return [1] cat P`Ehrhart_coeffs[1..l];
end intrinsic;

intrinsic EhrhartDeltaVector(P::TorPol) -> SeqEnum[RngIntElt]
{The Ehrhart delta-vector for the polytope P}
    if not assigned P`Ehrhart_delta then
        require IsPolytope(P): "Polyhedron must be a polytope";
        // Collect the data we need
        Ehr:=EhrhartSeries(P);
        // It's possible that computing the Ehrhart series has computed the
        // delta-vector, so we recheck
        if assigned P`Ehrhart_delta then
            return P`Ehrhart_delta;
        end if;
        // No such luck -- continue our calculation...
        k:=Dimension(P) + 1;
        r:=LCM(&cat[PowerSequence(Integers()) |
                   [Integers() | Denominator(c) : c in Eltseq(v)] :
                                                  v in Vertices(P)]);
        // The point is that our choice of r might be too large. Instead there
        // might be a smaller choice rr | r. This is called quasi-period
        // collapse, and isn't well understood yet (although see the paper
        // "Quasi-period Collapse and GL Rational Polytopes" by Haase for some
        // ideas). Instead we check each possibility in turn.
        t:=Parent(Ehr).1;
        for rr in Divisors(r) do
            ff:=Ehr * (1 - t^rr)^k;
            if Denominator(ff) eq 1 then
                coeffs:=Coefficients(Numerator(ff));
                if #coeffs ne rr * k then
                    coeffs cat:= [Integers() | 0 : i in [1..rr * k - #coeffs]];
                end if;
                break;
            end if;
        end for;
        P`Ehrhart_delta:=coeffs;
    end if;
    return P`Ehrhart_delta;
end intrinsic;

intrinsic EhrhartPolynomial(P::TorPol) -> SeqEnum[RngUPolElt]
{The Ehrhart (quasi-)polynomial for the polytope P}
    if not assigned P`Ehrhart_qpoly then
        require IsPolytope(P): "Polyhedron must be a polytope";
        // Build the polynomial ring and get the degenerate case out of the way
        R:=PolynomialRing(Rationals());
        if IsEmpty(P) then
            P`Ehrhart_qpoly:=[R | 0];
            return P`Ehrhart_qpoly;
        end if;
        // Collect the data we need
        delta:=EhrhartDeltaVector(P);
        k:=Dimension(P) + 1;
        r:=Integers() ! (#delta / k);
        t:=R.1;
        // Create the sequence of polynomials that represent the quasi-poly'l
        P`Ehrhart_qpoly:=[R|];
        for i in [0..r - 1] do
            c:=[Integers() | delta[r * j + i + 1] : j in [0..k - 1]];
            Append(~P`Ehrhart_qpoly,
                 &+[c[j] * binomial_contribution(t,k - j,k - 1) : j in [1..k]]);
        end for;
    end if;
    return P`Ehrhart_qpoly;
end intrinsic;

intrinsic EhrhartSeries(P::TorPol) -> FldFunRatUElt
{The rational generating function of the Ehrhart series for the polytope P}
    if not assigned P`Ehrhart_gen_func then
        require IsPolytope(P): "Polyhedron must be a polytope";
        // Get the degenerate case out of the way
        if IsEmpty(P) then
            P`Ehrhart_gen_func:=PolynomialRing(Integers()) ! 0;
            return P`Ehrhart_gen_func;
        end if;
        // If P is smooth then this easy
        if IsSmooth(P) then
            return calculate_smooth_ehrhart_data(P);
        end if;
        // If P is reflexive and of low dimension then we know the answer
        if Dimension(P) le 5 and IsReflexive(P) then
            return calculate_reflexive_ehrhart_data(P);
        end if;
        // If P is an integral simplex of dimension >= 5 then we use a different
        // algorithm
        if Dimension(P) ge 5 and IsIntegral(P) and IsSimplex(P) then
            return calculate_simplex_ehrhart_data(P);
        end if;
        // OK, we'll have to actually do some work...
        // Calculate the dilation factor required to make P integral
        r:=LCM(&cat[[Integers() | Denominator(c) : c in Eltseq(v)] :
                                                        v in Vertices(P)]);
        // Calculate the coefficients we'll need
        k:=Dimension(P) + 1;
        if k * r - 1 gt 10^4 then
            printf "This will require calculating the first %o terms of the Ehrhart series - it could take some time\n",k * r - 1;
        end if;
        E:=EhrhartCoefficients(P,k * r - 1);
        // Create the rational generating function
        R:=PolynomialRing(Integers());
        t:=R.1;
        f:=&+[E[i] * t^(i - 1) : i in [1..k * r]] * (1 - t^r)^k;
        coeffs:=[Integers() | Coefficient(f,i) : i in [0..k * r - 1]];
        P`Ehrhart_gen_func:=
                    &+[coeffs[i] * t^(i - 1) : i in [1..k * r]] / (1 - t^r)^k;
    end if;
    return P`Ehrhart_gen_func;
end intrinsic;
