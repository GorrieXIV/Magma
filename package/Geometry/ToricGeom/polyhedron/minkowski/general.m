freeze;

/////////////////////////////////////////////////////////////////////////
// general_minkowski.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 39231 $
// $Date: 2012-07-13 05:16:06 +1000 (Fri, 13 Jul 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander M Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the Minkowski decompositions for a lattice polytope.
/////////////////////////////////////////////////////////////////////////
// Based on the algorithm in:
//   K. Altmann, "The versal deformation of an isolated toric Gorenstein
//   singularity", Invent. math. 128, 443-479 (1997).
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns a sequence of edge indices (corresponding to Edges(P)) of the
// 2-faces of P (in the same order as Faces(P,2)).
// i.e. Equivalent to the one-liner:
//   [{Index(edges,E) : E in Edges(F)} : F in Faces(P,2)] where edges:=Edges(P)
function edge_indices_for_2faces(P)
    // Fetch the face graph for P
    G:=Graph(P);
    // Recover the vertices of the graph that correspond to the edges and
    // the 2-faces
    verts:=Vertices(G);
    S:=VertexLabels(G);
    edges:={Universe(verts) | verts[i] : i in [1..#S] | S[i] eq 1};
    faces:=[Universe(verts) | verts[i] : i in [1..#S] | S[i] eq 2];
    // Now build the "edge vector" for each 2-face
    Ev:=[PowerSet(Universe(verts)) | Neighbours(F) meet edges : F in faces];
    // Convert the data into edge indices rather than vertices
    verts:=SetToSequence(verts);
    offset:=Minimum([Integers() | Index(verts,E) : E in edges]) - 1;
    Ev:=[PowerSet(Integers()) | {Index(verts,E) - offset : E in EE} : EE in Ev];
    // Return the result
    return Ev;
end function;

// Given the edge indices defining a 2-face F, and the edges Es, returns an
// oriented cycle of edges defining F.
function oriented_edge_cycle(F,Es,vertmap)
    // Pick a starting edge
    E1:=Representative(F);
    Exclude(~F,E1);
    cycle:=[Integers() | E1];
    v:=Es[E1][2];
    // And start building the cycle
    while #F ne 0 do
        E:=Representative(F meet vertmap[v]);
        Exclude(~F,E);
        if v eq Es[E][1] then
            Append(~cycle,E);
            v:=Es[E][2];
        else
            Append(~cycle,-E);
            v:=Es[E][1];
        end if;
    end while;
    // Return the cycle
    return cycle;
end function;

// Assigns an orientation to the edge indices of the 2-faces so that they form
// a cycle. Also returns the sequence of direction vectors for the edges.
// The returned data satisfies:
//  &and[IsZero(&+[Sign(i) * dirs[Abs(i)] : i in cycle]) : cycle in cycles]
function orient_edges_for_2faces(P)
    // Fix an orientation on the edges by sorting the defining vertex indices
    Es:=EdgeIndices(P);
    vertmap:=[PowerSet(Integers()) | {i : i in [1..#Es] | v in Es[i]} :
                                                 v in [1..NumberOfVertices(P)]];
    Es:=[Sort(SetToSequence(E)) : E in Es];
    // Now we make the edges of each 2-face form an oriented cycle
    cycles:=[PowerSequence(Integers()) | oriented_edge_cycle(F,Es,vertmap) :
                                               F in edge_indices_for_2faces(P)];
    // Create the direction vectors for the edges and return the data
    verts:=Vertices(P);
    return cycles,[Ambient(P) | verts[E[2]] - verts[E[1]] : E in Es];
end function;

// Returns a sequence of vectors (corresponding to Edges(P)) giving paths from
// Vertices(P)[base] to Vertices(P)[i].
function vertex_edges(P,base)
    // Create the vertex-edge graph
    Es:=EdgeIndices(P);
    G:=Graph<NumberOfVertices(P) | SequenceToSet(Es)>;
    // Build the map from edges to data
    edgemap:=AssociativeArray(Universe(Edges(G)));
    for i in [1..#Es] do
        E:=Sort(SetToSequence(Es[i]));
        edgemap[Es[i]]:=[E[1],E[2],i];
    end for;
    // Create the edge vectors between vertices
    n:=#Es;
    vs:=Vertices(G);
    edgevecs:=[PowerSequence(Integers())|];
    for i in [1..#vs] do
        pos:=base;
        vec:=ZeroSequence(Integers(),n);
        for E in Path(vs[base],vs[i]) do
            data:=edgemap[E];
            if data[1] eq pos then
                vec[data[3]]:=1;
                pos:=data[2];
            else
                vec[data[3]]:=-1;
                pos:=data[1];
            end if;
        end for;
        Append(~edgevecs,vec);
    end for;
    return edgevecs;
end function;

// Repackages the given sequence of directed edge indices as an edge vector.
function edge_cycle_to_vector(cycle,weights)
    vector:=ZeroSequence(Integers(),#weights);
    for i in cycle do
        vector[Abs(i)]:=Sign(i) * weights[Abs(i)];
    end for;
    return vector;
end function;

// Given a collection of vectors 'Hs' and a target vector 'cs', returns all
// non-negative solutions to t[i] * H[i] = cs[i] for all H in Hs.
function hyperplane_knapsack(Hs,cs)
    // Sanity check
    error if #Hs eq 0,
        "There must be at least one hyperplane";
    error if #Hs ne #cs,
        "The number of hyperplanes must equal the number of heights";
    d:=#Hs[1];
    error if d eq 0,
        "The ambient space cannot be zero dimensional";
    error if not &and[#H eq d : H in Hs],
        "Hyperplanes must be of the same dimension";
    // Move to the graded lattice
    D:=GradedToricLattice(Dual(Parent(LatticeVector(Hs[1]))));
    Hs:=[D | [-cs[i]] cat Hs[i] : i in [1..#Hs]];
    // We start with the positive orthant
    C:=ConeWithInequalities([D.i : i in [2..d + 1]]);
    // Intersect with the hyperplanes as necessary
    for H in Hs do
        if &or[H * r ne 0 : r in RGenerators(C)] then
            C:=ConeWithInequalities(Inequalities(C) cat [H,-H]);
        end if;
    end for;
    // Finally, return the points
    return [PowerSequence(Integers()) | Eltseq(u) : u in Points(Polyhedron(C))];
end function;

/////////////////////////////////////////////////////////////////////////
// Core Minkowski functions
/////////////////////////////////////////////////////////////////////////
/*
This example illustrates the functions below
--------------------------------------------
k:=5;
P:=k * RandomPolytope(3,5,5);
C,prim,lambdas,v0,target:=cone_of_summands(P);
t:=ZGenerators(C)[1];
assert k * t eq target;     // Note: If you're unlucky, this might fail
Q:=Polytope(point_to_generators(t,lambdas,prim));
assert k * Q eq P - v0;
*/

// Returns the cone of Minkowski summands for the polytope P, along with the
// corresponding direction vectors, the vertex lambdas and base point, and the
// point that represents P.
function cone_of_summands(P)
    // Sanity check
    error if not IsPolytope(P) or not IsIntegral(P),
        "Argument must be an integral polytope";
    // First we need to create the arrays of signs and edge vectors
    cycles,dirs:=orient_edges_for_2faces(P);
    num:=#dirs;
    prim:=[Ambient(P) | PrimitiveLatticeVector(v) : v in dirs];
    weights:=[Integers() | dirs[i] / prim[i] : i in [1..#dirs]];
    eprim:=[Eltseq(v) : v in prim];
    vectors:=[PowerSequence(Integers()) | edge_cycle_to_vector(cycle,weights) :
                                                               cycle in cycles];
    signs:=[PowerSequence(Integers()) | [Sign(c) : c in vector] :
                                                             vector in vectors];
    // Build the vertex vectors
    verts:=Vertices(P);
    idx:=Index(verts,Zero(Universe(verts)));
    base:=idx eq 0 select 1 else idx;
    lambdas:=vertex_edges(P,base);
    v0:=verts[base];
    // Create the inequalities for the cone
    d:=Dimension(Ambient(P));
    ineqs:=[PowerSequence(Integers()) | [s[i] * eprim[i][j] : i in [1..num]] :
                                                        j in [1..d],s in signs];
    ineqs cat:= [PowerSequence(Integers()) | [-c : c in ineq] : ineq in ineqs];
    ineqs cat:= RowSequence(IdentityMatrix(Integers(),num));
    // Create the cone
    C:=ConeWithInequalities(ineqs);
    // Return the data
    return C,prim,lambdas,v0,Ambient(C) ! weights;
end function;

// Given a point 'pt' in the summand cone C, and the vertices of P expressed in
// terms of the direction vectors 'prim' (based at some point v0, returns the
// generators of the corresponding polytope (based at v0).
function point_to_generators(pt,lambdas,prim)
    // Sanity check
    error if #lambdas eq 0, "The sequence of vertex vectors must not be empty";
    d:=#lambdas[1];
    pt:=Eltseq(pt);
    error if &or[#v ne d : v in lambdas],
        Sprintf("The vertex vectors must all be of length %o",d);
    error if #pt ne d,
        Sprintf("The point must be of dimension %o",d);
    // Create the vertices
    return [Universe(prim) | &+[pt[i] * v[i] * prim[i] : i in [1..d]] :
                                                                  v in lambdas];
end function;

// Returns all possible primitive Minkowski decompositions of the lattice
// polytope P.
function general_decomposition(P)
    // Collect the Minkowski data
    C,prim,lambdas,v0,target:=cone_of_summands(P);
    // An associative array mapping ZZ-generators of C to polytopes
    zgens:=ZGenerators(C);
    primQs:=AssociativeArray(Integers());
    // Compute all irreducible solutions to the target
    decomps:=[];
    Hs:=RowSequence(Transpose(Matrix(zgens)));
    for u in hyperplane_knapsack(Hs,Eltseq(target)) do
        // Construct thedecomposition into primitive polytopes
        decomp:=[];
        for i in [1..#u] do
            if u[i] ne 0 then
                bool,Q:=IsDefined(primQs,i);
                if not bool then
                    Q:=Polytope(point_to_generators(zgens[i],lambdas,prim));
                    primQs[i]:=Q;
                end if;
                for j in [1..u[i]] do
                    Append(~decomp,Q);
                end for;
            end if;
        end for;
        // Record the decomposition
        Append(~decomps,decomp);
    end for;
    // If the base point is non-zero, we need to add it to the decompositions
    if not IsZero(v0) then
        Q0:=Polytope([v0] : areVertices:=true);
        for i in [1..#decomps] do
            Append(~decomps[i],Q0);
        end for;
    end if;
    // Return the decomposition
    return decomps;
end function;
