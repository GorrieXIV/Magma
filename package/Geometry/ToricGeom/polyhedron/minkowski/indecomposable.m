freeze;

/////////////////////////////////////////////////////////////////////////
// indecomposable.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 39263 $
// $Date: 2012-07-16 03:40:21 +1000 (Mon, 16 Jul 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander M Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Performs some easy checks to try to spot cases when the lattice
// polytope P is Minkowski indecomposable.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true iff there exists an integer 1 <= i <= d such that s1 * i = a
// and s2 * i = b.
function has_solution(s1,s2,d,a,b)
    if s1 eq 0 then
        if a ne 0 then return false; end if;
        if s2 eq 0 then return b eq 0; end if;
        bool,m:=IsDivisibleBy(b,s2);
        return bool and m gt 0 and m le d;
    else
        bool,m:=IsDivisibleBy(a,s1);
        return bool and m gt 0 and m le d and s2 * m eq b;
    end if;
end function;

// Input are three sequences S1,S2,d of length k. We assume that all values
// are integers, and that the d[i] are strictly positive.
// Returns true iff there exists a sequence
//      0 <= d_i <= d[i]
// satisfying
//      d_1 * S1[1] + ... + d_k * S1[k] = 0,
//      d_1 * S2[1] + ... + d_k * S2[k] = 0,
// such that at least one of the d_i > 0, and at least one of the d_i < d[i].
function decomposition_knapsack_recurse(S1,S2,d,a,b,has_one,has_all)
    l:=#S1;
    if l gt 1 then
        s1:=S1[l];
        s2:=S2[l];
        di:=d[l];
        if has_solution(s1,s2,di,a,b) then return true; end if;
        Prune(~S1);
        Prune(~S2);
        Prune(~d);
        if $$(S1,S2,d,a,b,has_one,false) then return true; end if;
        for i in [1..di - 1] do
            if $$(S1,S2,d,a - i * s1,b - i * s2,true,false) then
                return true;
            end if;
        end for;
        if $$(S1,S2,d,a - di * s1,b - di * s2,true,has_all) then
            return true;
        end if;
    elif l eq 1 then
        if not has_all then
            if has_one then
                return (a eq 0 and b eq 0) or
                       has_solution(S1[1],S2[1],d[1],a,b);
            else
                return has_solution(S1[1],S2[1],d[1],a,b);
            end if;
        end if;
        if has_one then
            return (a eq 0 and b eq 0) or
                   has_solution(S1[1],S2[1],d[1] - 1,a,b);
        else
            return has_solution(S1[1],S2[1],d[1] - 1,a,b);
        end if;
    end if;
    return false;
end function;

function decomposition_knapsack(S1,S2,d)
    // Sanity checks
    error if #S1 ne #S2 or #S1 ne #d,
        "decomposition_knapsack: The sequences must be of the same length";
    error if &or[c le 0 : c in d],
        "decomposition_knapsack: The multiplicities must be (strictly) positive";
    // Do the search
    return decomposition_knapsack_recurse(S1,S2,d,0,0,false,true);
end function;

// Given a seqeunce of edge indices Es and a vertex index i, returns the index
// of the first edge in Es containing i. If no match is found, return 0.
function edge_for_vertex(Es,i)
    for idx in [1..#Es] do
        if i in Es[idx] then return idx; end if;
    end for;
    return 0;
end function;

// Returns the ordered, oriented edge sequence of the polygon P. This sequence
// is unique up to sign and starting position.
function polygon_edge_sequence(P)
    // Collect the data we'll need
    verts:=Vertices(P);
    edges:=EdgeIndices(P);
    // Create the initial data
    lastidx,curidx:=Explode(SetToSequence(edges[#edges]));
    es:=[Universe(verts) | verts[curidx] - verts[lastidx]];
    Prune(~edges);
    // Start building the edge sequence
    while #edges ne 0 do
        // Find the connecting edge
        idx:=edge_for_vertex(edges,curidx);
        assert idx ne 0;
        i1,i2:=Explode(SetToSequence(edges[idx]));
        Remove(~edges,idx);
        // Update the data
        lastidx:=curidx;
        curidx:=i1 eq curidx select i2 else i1;
        Append(~es,verts[curidx] - verts[lastidx]);
    end while;
    // Return the edge sequence
    return es;
end function;

// Returns the oriented edge sequence of the polygon P as a parallel sequence
// of primitive vectors and a sequence of integers giving the multiples.
function primitive_edge_sequence(P)
    // First we calculate the edge sequence
    es:=polygon_edge_sequence(P);
    // Now we calculate the multiples
    pes:=[PowerSequence(Integers())|];
    ds:=[Integers()|];
    for e in es do
        pe:=PrimitiveLatticeVector(e);
        Append(~pes,Eltseq(pe));
        Append(~ds,e / pe);
    end for;
    // Return the two sequences
    return pes,ds;
end function;

// Returns true iff the given 2-dimensional polygon is indecomposable.
function is_polygon_indecomposable(P : use_lp:=false)
    // Sanity check
    assert Dimension(P) eq 2;
    // Is this a triangle?
    if NumberOfVertices(P) eq 3 then
        verts:=Vertices(P);
        return GCD(Eltseq(verts[1] - verts[2]) cat
                    Eltseq(verts[1] - verts[3])) eq 1;
    end if;
    // Do there exist parallel edges?
    verts:=Vertices(P);
    es:={Ambient(P)|};
    for E in EdgeIndices(P) do
        i1,i2:=Explode(SetToSequence(E));
        e:=PrimitiveLatticeVector(verts[i1] - verts[i2]);
        if e in es or -e in es then return false; end if;
        Include(~es,e);
    end for;
    // OK, the cheap tests are out of the way -- calculate the edge data
    es,ds:=primitive_edge_sequence(P);
    // If you trust the linear programming package, this is an excellent way of
    // testing for a non-trivial decomposition. As things currently stand,
    // however, I'm not happy enough with the state of the C code it to use it
    // by default.
    if use_lp then
        // Create the corresponding linear programming problem
        lhs:=[[Integers() | e[1] : e in es],[Integers() | e[2] : e in es]] cat
                RowSequence(IdentityMatrix(Integers(),#es)) cat
                RowSequence(IdentityMatrix(Integers(),#es));
        Append(~lhs,[Integers() | 1 : i in [1..#es]]);
        lhs:=Matrix(lhs);
        rel:=[Integers() | 0,0] cat [Integers() | 1 : i in [1..#es]] cat
                                    [Integers() | -1 : i in [1..#es + 1]];
        rel:=Matrix(#rel,1,rel);
        rhs:=ZeroSequence(Integers(),#es + 2) cat ds;
        Append(~rhs,&+ds - 1);
        rhs:=Matrix(#rhs,1,rhs);
        obj:=Matrix(1,#es,[Integers() | 1 : i in [1..#es]]);
        // Is there a non-trivial solution?
        sol,soltype:=MaximalIntegerSolution(lhs,rel,rhs,obj);
        assert soltype eq 0;
        return IsZero(sol);
    else
        // Knapsack for a non-trivial decomposition
        S1:=[Integers() | e[1] : e in es];
        S2:=[Integers() | e[2] : e in es];
        return not decomposition_knapsack(S1,S2,ds);
    end if;
end function;

// If all but one of the vertices of P are contained in a common hyperplane,
// then it's easy to check for indecomposability.
function hyperplane_and_point_test(P)
    // Study the vertex-facet indicence matrix to find a candidate
    M:=Transpose(VertexFacetIncidenceMatrix(P));
    k:=NumberOfColumns(M) - 1;
    for R in RowSequence(M) do
        if &+R eq k then
            // Extract the vertex not lying in the hyperplane
            verts:=Vertices(P);
            vidx:=Index(Eltseq(R),0);
            v:=verts[vidx];
            // Test for reduction
            return true,GCD(&cat[Eltseq(v - verts[i]) :
                                            i in [1..#verts] | i ne vidx]) eq 1;
        end if;
    end for;
    // If we're here then we didn't find an example
    return false,_;
end function;

// This is a more general version of the hyperplane test. If we can find a
// hyperplane containing at least two vertices of P such that the corresponding
// polytope Q is indecomposable, and if there exists a (not necessarily
// lattice) point v such that P \subset conv(v,Q), then P is indecomposable.
forward is_indecomposable;
function general_hyperplane_test(P : max_attempts:=5, range:=3, use_lp:=false)
    // Sanity check
    assert Dimension(P) ge 3;
    // We need a reference point in the interior of P
    verts:=Vertices(P);
    u1:=ContainsZero(P) select Zero(Ambient(P))
                          else &+verts / #verts;
    // We work over the inequalities of P
    Fs:=FacetIndices(P);
    I:=Inequalities(P);
    for i in [1..#Fs] do
        // Check that we can cone over the corresponding facet and subsume P.
        // We do this by "sending the reference point to infinity".
        complement:={1..#verts} diff Fs[i];
        u2:=&+[verts[j] : j in complement] / #complement - u1;
        if &and[Sign(u2 * I[j][1]) lt 0 : j in [1..#Fs] | j ne i] then
            // OK, now look for a cheap reason why the facet might be
            // indecomposable
            Q:=Facets(P)[i];
            if Dimension(Q) eq 2 then
                if is_polygon_indecomposable(Q : use_lp:=use_lp) then
                    return true;
                end if;
            elif is_indecomposable(Q : max_attempts:=max_attempts,
                                       range:=range, use_lp:=use_lp) then
                return true;
            end if;
        end if;
    end for;
    // If we're here, no luck spotting a problem
    return false;
end function;

// Finds a random projection of ZZ^n -> ZZ^2 such that the image is distinct
// for all vertices of P, and the resulting polytope Q is two-dimensional.
// Returns true followed by Q if a projection was found, false otherwise.
function find_projection(P : range:=3)
    // Sanity check
    assert Dimension(P) ge 3;
    // Get hunting
    n:=Dimension(Ambient(P));
    verts:=Transpose(Matrix(Vertices(P)));
    attempt:=1;
    while attempt le 20 do
        // Create two random projections
        u1:=[Random(-range,range) : i in [1..n]];
        u2:=[Random(-range,range) : i in [1..n]];
        // Compute the image and check for uniqueness
        img:=RowSequence(Transpose(Matrix([u1,u2]) * verts));
        if #SequenceToSet(img) eq NumberOfColumns(verts) then
            // Is the image two-dimensional?
            Q:=Polytope(img);
            if Dimension(Q) eq 2 then
                return true,Q;
            end if;
        end if;
        // Move on
        attempt +:= 1;
    end while;
    // No luck
    return false,_;
end function;

// Randomly projects P to ZZ^2 and tests whether the image is indecomposable.
function random_projection_test(P : max_attempts:=5, range:=3, use_lp:=false)
    while max_attempts ge 1 do
        // First we need to find a projection that seperates the vertices of P
        bool,Q:=find_projection(P : range:=range);
        if not bool then
            return false;
        end if;
        // Is the image indecomposable?
        if is_polygon_indecomposable(Q : use_lp:=use_lp) then
            return true;
        end if;
        // Move on
        max_attempts -:= 1;
    end while;
    // No luck
    return false;
end function;

// Returns true if we have detected that P is indecomposable. Note that
// returning false does NOT mean that P is certainly decomposable.
function is_indecomposable(P : max_attempts:=5, range:=3, use_lp:=false)
    // First we look for the case where P has a supporting hyperplane containing
    // all but one vertex
    success,bool:=hyperplane_and_point_test(P);
    if success then return bool; end if;
    if Dimension(P) ge 3 then
        // The next test is to a more general version of the hyperplane test
        if general_hyperplane_test(P : max_attempts:=max_attempts,
                                       range:=range, use_lp:=use_lp) then
            return true;
        end if;
        // Finally, we try a few random projections to ZZ^2
        if random_projection_test(P : max_attempts:=max_attempts,
                                      range:=range, use_lp:=use_lp) then
            return true;
        end if;
    end if;
    // If we're here then we didn't find a reason -- we don't know the answer
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsic
/////////////////////////////////////////////////////////////////////////

intrinsic InternalIsMinkowskiIndecomposable( P::TorPol :
    max_attempts:=100, range:=7, use_lp:=false ) -> BoolElt
{True if the polytope P is detected to be Minkowski indecomposable. Note that in dimension 3 or more this is a probabilistic algorithm, and returning false does NOT guarantee that a non-trivial Minkowski decomposition exists. You can reduce the probability of returning false when P actually is indecomposable by increasing the value of 'max_attempts' [default: 100].}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P):
        "The polyhedron must be an integral polytope";
    require Type(max_attempts) eq RngIntElt and max_attempts gt 0:
        "Parameter 'max_attempts' must be a positive integer";
    require Type(range) eq RngIntElt and range gt 0:
        "Parameter 'range' must be a positive integer";
    require Type(use_lp) eq BoolElt:
        "Parameter 'use_lp' must be a boolean";
    // Get the dimension 0, 1, and 2 cases out of the way
    if Dimension(P) eq 0 then
        return true;
    elif Dimension(P) eq 1 then
        vs:=Vertices(P);
        return IsPrimitive(vs[1] - vs[2]);
    elif Dimension(P) eq 2 then
        return is_polygon_indecomposable(P : use_lp:=use_lp);
    end if;
    // Have a go in dimension >= 3
    return is_indecomposable(P : max_attempts:=max_attempts, range:=range,
                                 use_lp:=use_lp);
end intrinsic;
