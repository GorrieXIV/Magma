freeze;

////////////////////////////////////////////////////////////////////////
// generators.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 47359 $
// $Date: 2014-06-07 20:49:18 +1000 (Sat, 07 Jun 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating generators and inequalities of cones.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": negate_sequence, seq_of_k_subsets, remove_repetitions;
import "../lattice/point.m": move_points_to_lattice, lattice_element_cmp;
import "triangulation.m": cone_simplicial_subdivision;

declare attributes TorCon:
    are_Rgens_minimal,      // Are the R-generators known to be minimal?
    Rgens,                  // The R-generators of the cone C. Either Rgens or
                            // dual`Rgens must be assigned
    Zgens,                  // The Z-generators of the cone
    dual;                   // The cone dual to C

/////////////////////////////////////////////////////////////////////////
// Local Functions
/////////////////////////////////////////////////////////////////////////

// Copies the data from "C" to "dC".
// Note: Does not attempt to set the dual data.
procedure generators_copy(C,dC)
    if assigned C`are_Rgens_minimal then
        dC`are_Rgens_minimal:=C`are_Rgens_minimal; end if;
    if assigned C`Rgens then
        dC`Rgens:=C`Rgens; end if;
    if assigned C`Zgens then
        dC`Zgens:=C`Zgens; end if;
end procedure;

// Sets the data of "dC" equal to minus "C".
// Note: Does not attempt to set the dual data.
procedure generators_minus(C,dC)
    if assigned C`are_Rgens_minimal then
        dC`are_Rgens_minimal:=C`are_Rgens_minimal; end if;
    if assigned C`Rgens then
        dC`Rgens:=negate_sequence(C`Rgens); end if;
    if assigned C`Zgens then
        dC`Zgens:=negate_sequence(C`Zgens); end if;
end procedure;

// Sets the data of "dC" equal to "C", but with the ambient changed to "L".
// Note: Does not attempt to set the dual data.
procedure generators_change_ambient(C,dC,L)
    if assigned C`are_Rgens_minimal then
        dC`are_Rgens_minimal:=C`are_Rgens_minimal; end if;
    if assigned C`Rgens then
        dC`Rgens:=move_points_to_lattice(C`Rgens,L); end if;
    if assigned C`Zgens then
        dC`Zgens:=move_points_to_lattice(C`Zgens,L); end if;
end procedure;

// True iff the cone knows its defining inequalities
function cone_has_inequalities(C)
    return assigned C`dual and assigned Dual(C)`Rgens;
end function;

// True iff the cone knows its generators and they are minimal
function are_R_generators_minimal(C)
    return assigned C`are_Rgens_minimal and C`are_Rgens_minimal;
end function;

// True iff the cone knows its defining inequalities and they are minimal
function are_inequalities_minimal(C)
    return assigned C`dual and are_R_generators_minimal(Dual(C));
end function;

// True iff g is a minimal generator of the generating set 'gens' of the cone C
function is_minimal(C, gens, g)
    return not &or[(g - h) in  C : h in gens];
end function;

// Computes the difference g[i] - h[i] and checks whether this lies in the cone
// defined by the inequalities
function difference_of_pts_in_cone(g,h,ineqs)
    v:=[Integers() | g[i] - h[i] : i in [1..#h]];
    return &and[&+[v[i] * ineq[i] : i in [1..#v]] ge 0 : ineq in ineqs];
end function;

// Returns true iff this defines a min impr
function is_minimal_impr(ineqs, gens, g, half_level)
    return not &or[&or[difference_of_pts_in_cone(g,h, ineqs) : h in gens[i]]
                                    : i in [1..half_level] | IsDefined(gens,i)];
end function;

// Uses the Fourier-Motzkin algorithm to determine the dual description of a
// cone generated by the sequence 'gens'.
function cone_duality_algorithm_FM(gens)
    L:=Dual(Universe(gens));
    gens:=[PowerSequence(Rationals()) | Eltseq(gen) : gen in gens];
    ineqs:=SetToSequence(FourierMotzkin(gens));
    ChangeUniverse(~ineqs,L);
    return ineqs;
end function;

// Calculate the dual description of a simplicial cone generated by the
// sequence 'gens'
// Note: Assumes that the cone really is simplicial.
function cone_duality_algorithm_simplicial(gens,ind)
    L:=Universe(gens);
    M:=Transpose(ChangeRing(Matrix(gens),Rationals()));
    ineqs:=ChangeUniverse(RowSequence(M^(-1)),Dual(L));
    if ind ne 1 then
        ineqs:=[Dual(L) | PrimitiveLatticeVector(ineq) : ineq in ineqs];
    end if;
    return ineqs;
end function;

// Uses the naive approach to calculate the dual description of a cone generated
// by the sequence 'gens'
function cone_duality_algorithm_silly(gens)
    L:=Universe(gens);
    ineqs:=[Dual(L)|];
    dim:=Dimension(L);
    candidates:=seq_of_k_subsets([1..#gens],dim - 1);
    while not IsEmpty(candidates) do
        face_indices:=Representative(candidates);
        face:=[Universe(gens) | gens[i] : i in face_indices];
        new_face:=Basis(Kernel(Transpose(Matrix(face))));
        if #new_face eq 1 then
            new_face:=Representative(new_face);
            which_side:=[Sign(&+[Eltseq(ray)[i] * Eltseq(new_face)[i] :
                                                 i in [1..dim]]) : ray in gens];
            on_this_face:=[Integers()|i : i in [1..#gens] | which_side[i] eq 0];
            for element in seq_of_k_subsets(on_this_face,dim - 1) do
                Exclude(~candidates,element);
            end for;
            which_side:=Seqset(which_side) diff {0};
            if #which_side eq 1 then
                new_face:=Dual(L) ! (Representative(which_side) * new_face);
                Include(~ineqs,new_face);
            end if;
        else
            Exclude(~candidates,face_indices);
        end if;
    end while;
    return ineqs;
end function;

// Given a singular simplex (whose RGens are rows of a matrix) returns its
// \Z generators (without the RGens, if 'with_RGens' is 'false').
// 'det' is Abs(determinant of M).
function zgenerators_of_singular_simplex(M, det: with_RGens:=true)
    M_mod_det:=ChangeRing(M,quo<Integers() | det>);
    // Basis of kernel of M mod determinant:
    B:=[PowerSequence(Integers())| Eltseq(ChangeRing(v,Integers()))
            :  v in Basis(Kernel(M_mod_det))];
    // create the basis sequence
    cube_basis:=RowSequence(det* IdentityMatrix(Integers(), NumberOfColumns(M)));
    // solve simplex using Hemmecke's method:
    points:=MinimalPositiveGenerators(B cat cube_basis);
    // remove the basis if does not needed:
    if not with_RGens then
        indices:=Sort(Setseq({1..#points} diff {Index(points, pt) : pt in cube_basis}));
        points:=points[indices];
    end if;
    // turn into right coordinates:
    points:=RowSequence(ChangeRing(1/det*
    ChangeRing(Matrix(points)*M,Rationals()), Integers()));
    return Seqset(points);
end function;

// Returns the index in (the ordered sequence) 'set_of_gradings' of the largest
// entry at most half the given height, or 0 if no such entry exists.
function half_level_index(set_of_gradings,h)
    for i in [#set_of_gradings..1 by -1] do
        if 2 * set_of_gradings[i] le h then return i; end if;
    end for;
    return 0;
end function;

// Adds minimal Z generators to 'generators' from 'candidates'.
// 'ineqs' are cone inequalities,
// 'start' and 'set_of_gradings' say about the structure and order of data, to
// avoid redundand operations.
procedure eliminate_redundant_candidates(~generators, candidates, start, set_of_gradings, ineqs)
    for i in [start..#set_of_gradings] do
        // we search the candidates from level = 'start'.
        // we only need to search if it decomposes with something of
        // level at most half_level
        half_level:=half_level_index(set_of_gradings,set_of_gradings[i]);
        for gen in candidates[i] do
            if is_minimal_impr(ineqs, generators,  gen, half_level) then
                if IsDefined(generators,i) then
                    Append(~generators[i], gen);
                else
                    generators[i]:=[gen];
                end if;
            end if;
        end for;
    end for;
end procedure;

// Returns the index of the first value in S[2..#S] ge l. If no such value
// exists, returns 0.
function fetch_start_index(S,l)
    for i in [2..#S] do
        if S[i] ge l then return i; end if;
    end for;
    return 0;
end function;

function zgenerators_algorithm_Bsubdiv(C)
    // if C is simplicial, then we just use zgenerators_of_singular_simplex function.
    if IsSimplicial(C) then
        det:=Index(C);
        if det ne 1 then
	    M:=Matrix(MinimalRGenerators(C));
	    result:=zgenerators_of_singular_simplex(M, det);
	    // we convert the result into a sensible form
            result:=Sort(Setseq(result));
	    ChangeUniverse(~result, Ambient(C));
            return result;
        end if;
	return Sort(MinimalRGenerators(C));
    end if;

    // we will collect candidates here
    candidates:={PowerSequence(Integers())|};

    // we run through simplices, subdividing C
    for S in cone_simplicial_subdivision(C) do
        M:=Matrix(S);
        det:=Index(S);
        if det ne 1 then
            candidates join:= zgenerators_of_singular_simplex(M, det : with_RGens:=false);
        end if;
    end for;

    // it is possible, that there is no candidates:
    if IsEmpty(candidates) then
        return Sort(MinimalRGenerators(C));
    end if;

    // choose a form positive on all of C, which we then use for grading
    grading_form:=Matrix(Dimension(Ambient(C)), 1,Eltseq(PointInInterior(Dual(C))));
    candidates:=Setseq(candidates);
    // calculate the gradings of candidates and \R-generators
    gradings:=RowSequence(Transpose(Matrix(candidates)*grading_form))[1];
    Rgens:=Matrix(MinimalRGenerators(C));
    gradings_of_Rgens:=RowSequence(Transpose(Rgens*grading_form))[1];
    // 'set_of_gradings' is the sequence of all gradings
    set_of_gradings:=Sort(Setseq(Seqset(gradings cat gradings_of_Rgens)));
    // this is our starting point for reduction.
    start:=fetch_start_index(set_of_gradings,2 * set_of_gradings[1]);
    // If 'start' is zero, then there is nothing left, so we do not check anything.
    if start eq 0 then
	return Sort([Ambient(C)| gen : gen in candidates] cat MinimalRGenerators(C));
    end if;
    // we sort the candidates with respect to the gradings
    candidates:=[[candidates[i] : i in [1..#gradings]| gradings[i] eq l]
		: l in set_of_gradings];
    // Everythining before the starting point must be a generator.
    generators:=candidates[1..start-1];
    // Convert Rgens from a matrix to a sequence and put them in appropriate gradings
    Rgens:=RowSequence(Rgens);
    for i in [1..#Rgens] do
	place:=Index(set_of_gradings,gradings_of_Rgens[i]);
	if IsDefined(generators, place) then
	    Append(~generators[place], Rgens[i]);
	else
	    generators[place]:=
	      [PowerSequence(Integers())|Rgens[i]];
	end if;
    end for;
    // perform the elimination
    ineqs:=[Eltseq(ineq) : ineq in MinimalInequalities(C)];
    eliminate_redundant_candidates(~generators, candidates, start, set_of_gradings, ineqs);

    // prepare the result in a nice form:
    generators:=[ gen : gen in gens , gens in generators];
    Sort(~generators);
    ChangeUniverse(~generators, Ambient(C));
    return generators;
end function;

// Returns true iff the given graded cone is generated at height 1. If so, also
// returns the generators.
function is_generated_at_height_1(C)
    // Recover the grading
    grading:=Transpose(Matrix([Eltseq(Grading(C))]));
    // If C is simplicial, then we just use zgenerators_of_singular_simplex
    if IsSimplicial(C) then
        det:=Index(C);
        if det ne 1 then
            M:=Matrix(MinimalRGenerators(C));
            generators:=SetToSequence(zgenerators_of_singular_simplex(M,det));
        else
            generators:=MinimalRGenerators(C);
        end if;
        heights:=Matrix(generators) * grading;
        if &and[heights[i][1] eq 1 : i in [1..NumberOfRows(heights)]] then
            Sort(~generators);
            ChangeUniverse(~generators,Ambient(C));
            return true,generators;
        else
            return false,_;
        end if;
    end if;
    // Calculate the gradings of the \R-generators -- they had better all be at
    // height 1
    Rgens:=Matrix(MinimalRGenerators(C));
    heights:=Rgens * grading;
    gradings_of_Rgens:=[Integers() | heights[i][1] :
                                               i in [1..NumberOfRows(heights)]];
    if &or[h ne 1 : h in gradings_of_Rgens] then
        return false,_;
    end if;
    // Fetch the sequence of candidate generators and calculate their gradings
    candidates:={PowerSequence(Integers())|};
    for S in cone_simplicial_subdivision(C) do
        M:=Matrix(S);
        det:=Index(S);
        if det ne 1 then
            gens:=zgenerators_of_singular_simplex(M,det : with_RGens:=false);
            candidates join:= gens;
        end if;
    end for;
    candidates:=SetToSequence(candidates);
    if #candidates ne 0 then
        heights:=Matrix(candidates) * grading;
        gradings:=[Integers() | heights[i][1] :i in [1..NumberOfRows(heights)]];
    else
        gradings:=[Integers()|];
    end if;
    // 'set_of_gradings' is the (ordered) sequence of all distinct gradings
    set_of_gradings:=Sort(SetToSequence(SequenceToSet(Append(gradings,1))));
    // Is there anything to do?
    if #set_of_gradings eq 1 then
        generators:=RowSequence(Rgens) cat candidates;
        Sort(~generators);
        ChangeUniverse(~generators,Ambient(C));
        return true,generators;
    end if;
    // We partition the candidates by grading -- those at height 1 must be
    // generators, along with the \R-generators
    candidates:=[[candidates[i] : i in [1..#gradings] | gradings[i] eq l]
                                                        : l in set_of_gradings];
    generators:=RowSequence(Rgens) cat candidates[1];
    // We now look for a generator amongst the candidates -- if we find one,
    // then the cone isn't generated at height 1
    ineqs:=[PowerSequence(Integers()) | Eltseq(v) :
                                        v in MinimalInequalities(C)];
    for i in [2..#set_of_gradings] do
        for g in candidates[i] do
            if not &or[difference_of_pts_in_cone(g,h,ineqs) :
                                                           h in generators] then
                return false,_;
            end if;
        end for;
    end for;
    // If we're here then the cone is generated at height 1
    Sort(~generators);
    ChangeUniverse(~generators,Ambient(C));
    return true,generators;
end function;

// Given a matrix over the rationals, scales it to be over the integers
function make_matrix_integral(M)
    k:=LCM([Integers() | Denominator(c) : c in Eltseq(M)]);
    M:=k*M;
    return ChangeRing(M,Integers());
end function;

// Given a cone C, returns the \Z-generators of C using Hemmecke's algorithm.
// C must be strictly convex.
function zgenerators_algorithm_Hemmecke(C)
    P:=Transpose(Matrix(Inequalities(C)));
    if BaseRing(P) ne Integers() then
        P:=make_matrix_integral(P);
    end if;
    H:=MinimalPositiveGenerators(RowSequence(P));
    return Sort([Ambient(C) |
             Representative(RowSequence(Solution(P,Matrix(1,#u,u)))) : u in H]);
end function;

function zgenerators_algorithm_smooth(C)
    assert IsNonsingular(C);
    gens:=MinimalRGenerators(C);
    Sort(~gens);
    return gens;
end function;

function zgenerators_decide_algorithm(C)
    S:=SimplicialSubdivision(C);
    a:=Maximum([Abs(w) : w in &cat [Eltseq(v) : v in MinimalInequalities(C)]]);
    b:=Maximum([Abs(w) : w in &cat [Eltseq(v) : v in MinimalRGenerators(C)]]);
    ind:=RealField(10)!Maximum([Index(c) : c in Cones(S)]);
    factor:=(a/b)/Root(ind, 2*Dimension(C));
    border:=0.4;
    if factor ge border then
        return "Bsubdiv";
    end if;
    return "Hemmecke";
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

// THINK: Needs updating.
intrinsic MinimalRGenerators(C::TorCon : algorithm:="FM")
    -> SeqEnum[TorLatElt]
{The minimal generators of the cone C. If C is full dimensional then these are the rays of C. The parameter 'algorithm' specifies the algorithm that will be used for calculations: if set to "auto" (default) Magma will choose the algorithm to execute; "FM" will use Fourier-Motzkin elimination; "silly" checks nearly every hyperplane spanned by dim(C) - 1 generators/inequalities; "simplex" works only for simplicial cones.}
   if not are_R_generators_minimal(C) then
        L:=Ambient(C);
        if assigned C`Rgens then
        	if #RGenerators(C) eq Dimension(C) then
                C`Rgens:=[L | PrimitiveLatticeVector(v) : v in RGenerators(C)];
                C`are_Rgens_minimal:=true;
                C`is_simplicial:=true;
                return RGenerators(C);
            end if;
            // THINK: If RGens are known, then it should be faster to run
            // through known generators and eliminate unnecessary ones.
        end if;
        if not are_inequalities_minimal(C) then
            D:=Dual(C);
            D`Rgens:=[Dual(L) | v : v in Inequalities(C) | not IsZero(v)];
        end if;
        ineqs:=Inequalities(C);
        if IsEmpty(ineqs) then
            C`Rgens:=LinearConeGenerators(Basis(L));
            return C`Rgens;
        end if;
        mtrx:=Matrix(ineqs);
        rays:=LinearConeGenerators([L | Eltseq(ray) :
                                      ray in Basis(Kernel(Transpose(mtrx)))]);
        C2,phi:= ConeQuotientByLinearSubspace(C);
        if Dimension(Dual(C2)) eq 1 then
            candidates:=[Ambient(C2) | v :
                                v in LinearConeGenerators(Basis(Ambient(C2))) |
                                &and[v * w ge 0 : w in Inequalities(C2)]];
            rays cat:= candidates @@ phi;
        elif Dimension(Dual(C2)) gt 1 then
            D2:=Dual(C2);
            if not are_R_generators_minimal(D2) then
                D2`Rgens:=[Ambient(D2) | PrimitiveLatticeVector(v) :
                                v in RGenerators(D2)];
                remove_repetitions(~D2`Rgens);
            end if;
            ineqs:=D2`Rgens;
            // Decide on the algorithm and apply it
            proportion:=6/5;
            case algorithm:
                when "auto":
                    if #ineqs eq Dimension(D2) then
                        D2`is_simplicial:=true;
                        rays1 := cone_duality_algorithm_simplicial(ineqs,
                                                              Index(D2)) @@ phi;
                        C2`is_simplicial:=true;
                        D2`are_Rgens_minimal:=true;
                    elif #ineqs ge proportion*Dimension(Dual(C2)) then
                        rays1 := cone_duality_algorithm_FM(ineqs) @@ phi;
                    else
                        rays1 := cone_duality_algorithm_silly(ineqs) @@ phi;
                    end if;
                when "FM":
                    rays1 := cone_duality_algorithm_FM(ineqs) @@ phi;
                when "silly":
                    rays1 := cone_duality_algorithm_silly(ineqs) @@ phi;
                when "simplex":
                    if  #ineqs eq Dimension(Dual(C2)) then
                        rays1 := cone_duality_algorithm_simplicial(ineqs,
                                                              Index(D2)) @@ phi;
                        C2`is_simplicial:=true;
                        D2`are_Rgens_minimal:=true;
                    else
                        error "Algorithm error: cone has more inequalities than Dimension.";
                    end if;

                when "all":
                    // Runs each algorithm and prints verbose output
        	        printf "< ConeWithInequalities(%o),",
        	                                   [Eltseq(ineq) : ineq in ineqs];
                    if #ineqs eq Dimension(D2) then
             		    printf "3,";
                    elif #ineqs ge proportion * Dimension(Dual(C2)) then
            		    printf "1,";
                    else
	               	    printf "2,";
                    end if;
                    printf "[";
                    time rays1:=cone_duality_algorithm_FM(ineqs) @@ phi;
                    printf ",";
                    time rays2:=cone_duality_algorithm_silly(ineqs) @@ phi;
                    A:=[Sort(rays1),Sort(rays2)];
                    if #ineqs eq Dimension(D2) then
                        D2`is_simplicial:=true;
            		    printf ",";
                        time rays3:=cone_duality_algorithm_simplicial(ineqs,
                                                              Index(D2)) @@ phi;
                        Append(~A, Sort(rays3));
                    end if;
                    printf "]>,\n";
                    test:=[[a eq b: a in A] : b in A];
                    if not &and[&and t : t in test] then
                        error "Algorithms give different answer: ",test;
                    end if;
                else
                    require false: "Invalid algorithm";
            end case;
            Sort(~rays1,lattice_element_cmp);
            rays cat:= rays1;
        end if;
        C`Rgens:= rays;
        C`are_Rgens_minimal:=true;
    end if;
    return C`Rgens;
end intrinsic;

intrinsic RGenerators(C::TorCon) -> SeqEnum[TorLatElt]
{The real generators of the cone C}
    if not assigned  C`Rgens then
        C`Rgens:=MinimalRGenerators(C);
    end if;
    return C`Rgens;
end intrinsic;

intrinsic MinimalInequalities(C::TorCon) -> SeqEnum[TorLatElt]
{The minimal inequalities of the cone C. If C does not contain any linear subspace (i.e. if C is strictly convex) then these define the facets of C.}
    return MinimalRGenerators(Dual(C));
end intrinsic;

intrinsic Inequalities(C::TorCon) -> SeqEnum[TorLatElt]
{The inequalities of the cone C}
    return RGenerators(Dual(C));
end intrinsic;

intrinsic MatrixOfInequalities(C::TorCon)-> ModMatRngElt
{}
    return Matrix(Inequalities(C));
end intrinsic;

intrinsic MatrixOfInequalities(R::Rng,C::TorCon)-> ModMatRngElt
{The inequalities of C arranged in a matrix, with each row representing an inequality}
    return Matrix(R,Inequalities(C));
end intrinsic;

intrinsic ZGenerators(C::TorCon : level:=Infinity(), algorithm:="Hemmecke") -> SeqEnum[TorLatElt]
{The sequence of generators of the monoid given by the intersection of C with its ambient lattice.}
    if not assigned C`Zgens then
        // Work through easy and degenerate cases first:
        if IsNonsingular(C) then
	     C`Zgens:=zgenerators_algorithm_smooth(C);
	elif not IsStrictlyConvex(C) then
	     lin:=LinearSubspaceGenerators(C);
             Append(~lin, -&+lin);
             CC,psi:=ConeQuotientByLinearSubspace(C);
             C`Zgens:=Sort($$(CC) @@ psi cat lin);
        elif not IsMaximumDimensional(C) then
	     lin:=LinearSpanEquations(C);
             CC,psi:=ConeInSublattice(C);
             C`Zgens:=Sort(Image(psi,$$(CC : algorithm:=algorithm)));
        else
	     // this is the main case, where we actually do some work
	     // first we decide the algorithm to use
	     if algorithm eq "auto" then
	         algorithm:=zgenerators_decide_algorithm(C);
             end if;
             case algorithm:
                 when "Bsubdiv":
	              C`Zgens:=zgenerators_algorithm_Bsubdiv(C);
		 when "Hemmecke":
		      C`Zgens:=zgenerators_algorithm_Hemmecke(C);
		 when "all":
		      algorithm:=zgenerators_decide_algorithm(C);
		      printf "Preferred algorithm: %o\n", algorithm;
		      printf "Bsubdiv...";
                      t:=Cputime();
                      res1:=zgenerators_algorithm_Bsubdiv(C);
                      Bsubdiv_time:=Cputime(t);
                      printf " (%os); Hemmecke...",Bsubdiv_time;
                      t:=Cputime();
                      res2:=zgenerators_algorithm_Hemmecke(C);
                      Hemmecke_time:= Cputime(t);
                      printf " (%os)\n",Hemmecke_time;
		      if (Bsubdiv_time le Hemmecke_time and algorithm eq "Bsubdiv") or
		         (Bsubdiv_time ge Hemmecke_time and algorithm eq "Hemmecke") then
			  printf "OK \n";
		      else
		          printf "Bad choice!\n";
		      end if;
                      if res1 ne res2 then
                          error if true, "Discrepency";
                      end if;
		      C`Zgens:=res1;
                 else
		     error "Wrong algorithm.";
             end case;
	end if;
    end if;
    if level eq Infinity()  then
        return C`Zgens;
    end if;
    return [Ambient(C) | v : v in C`Zgens | v*Grading(Ambient(C)) le level];
end intrinsic;

// This is an alias for ZGenerators
intrinsic HilbertBasis(C::TorCon : level:=Infinity(), algorithm:="Hemmecke") -> SeqEnum[TorLatElt]
{The sequence of generators of the monoid given by the intersection of C with its ambient lattice.}
    return ZGenerators(C : level:=level, algorithm:=algorithm);
end intrinsic;