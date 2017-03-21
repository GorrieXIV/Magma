freeze;

/////////////////////////////////////////////////////////////////////////
// decomposition.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48074 $
// $Date: 2014-08-09 03:38:09 +1000 (Sat, 09 Aug 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for decomposing an integral polygon into Minkowski
// summands.
/////////////////////////////////////////////////////////////////////////
// We fix notation here:
// U = sequence of edge vectors; these uniquely define P up to translation
//      and are necessarily sorted by increasing angle w.r.t. U[1]
// E = corresponding sequence of primitive vectors
// d = sequence of scalars s.t. d[i] * E[i] = U[i]
// A = the sequence k * E[i] for all k in [1..d[i]] and i in [1..#E],
//      sorted first by angle and then by increasing value of k.
// (In fact we never explicitly construct A.)
/////////////////////////////////////////////////////////////////////////

import "indecomposable.m": is_indecomposable;
import "simplex.m": simplex_decomposition;
import "general.m": general_decomposition;
import "../../utilities/functions.m": distinct_unordered_partitions, bi_knapsack_k_terms;
import "../../lattice/point.m": primitive_nonzero_lattice_vector;
import "../convexhull/sublattice.m": fp_emb_map, embedded_lattice_to_ambient_lattice;
import "../convexhull/convexhull.m": fp_get_pullback_vertices;

declare attributes TorPol:
    decomposition;              // The Minkowski decomposition of the polytope

/////////////////////////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////////////////////////

// Returns of sequence of distinct Minkowski sums Q + R of P.
function minkowski_pairs(P)
    // First compute the decomposition
    M:=MinkowskiDecomposition(P);
    // We ensure that every decomposition contains a 0-dimensional component
    // by adding in the origin if necessary
    L:=Ambient(P);
    for i in [1..#M] do
        if not &or[Dimension(Q) eq 0 : Q in M[i]] then
            Append(~M[i],Polytope([L | Zero(L)] : areVertices:=true));
        end if;
    end for;
    // Assign IDs to the polytopes occuring in the Minkowski decompositions
    // and re-express them in terms of these IDs
    polys:=SetToIndexedSet(SequenceToSet(&cat M));
    M:={PowerSequence(Integers()) | Sort([Integers() |
                            Index(polys,P) : P in decomp]) : decomp in M};
    // Now, for each decomposition, create all possible pairs
    idsToPoly:=AssociativeArray(PowerSequence(Integers()));
    decompPolys:={@ PowerStructure(TorPol)| @};
    pairs:={PowerSequence(Integers())|};
    for decomp in M do
        for pair in distinct_unordered_partitions(decomp) do
            // The following code is simply an effort to reduce the number of
            // polytopes we need to construct. The end result is an id (the
            // index in decompPolys) of each polytope in the pair.
            S:=Sort(pair[1]);
            bool,P1:=IsDefined(idsToPoly,S);
            if not bool then
                P1:=&+[polys[i] : i in S];
                idsToPoly[S]:=P1;
            end if;
            S:=Sort(pair[2]);
            bool,P2:=IsDefined(idsToPoly,S);
            if not bool then
                P2:=&+[polys[i] : i in S];
                idsToPoly[S]:=P2;
            end if;
            id1:=Index(decompPolys,P1);
            if id1 eq 0 then
                Include(~decompPolys,P1);
                id1:=#decompPolys;
            end if;
            id2:=Index(decompPolys,P2);
            if id2 eq 0 then
                Include(~decompPolys,P2);
                id2:=#decompPolys;
            end if;
            // Add the pair to the list we're constructing
            Include(~pairs,Sort([Integers() | id1, id2]));
        end for;
    end for;
    // Finally, return the decompositions
    return [PowerSequence(PowerStructure(TorPol)) |
                [decompPolys[I[1]],decompPolys[I[2]]] : I in pairs];
end function;

/////////////////////////////////////////////////////////////////////////
// Helper functions
/////////////////////////////////////////////////////////////////////////

// Input are three sequences S1,S2,d of the same length, target 'a', and a
// size 'k'. We assume that all values are integers, and that the d[i] are
// strictly positive.
// Output is a set of all possible sequences S of length k of the form
//      [idx_1,d_1],...,[idx_k,d_k],
// satisfying
//      d_1 * S1[idx_1] + ... + d_k * S1[idx_k] = a,
//      d_1 * S2[idx_1] + ... + d_k * S2[idx_k] = 0,
// subject to the restrictions
//      idx_1 < ... < idx_k,
//      1 <= d_i <= d[idx_i] for all 1 <= i <= k.
function minkowski_knapsack_recurse(S1,S2,d,a,b,k)
    results:=[PowerSequence(PowerSequence(Integers()))|];
    if k gt 1 then
        l:=#S1;
        if l ge 2 then
            s1:=S1[l];
            s2:=S2[l];
            di:=d[l];
            Prune(~S1);
            Prune(~S2);
            Prune(~d);
            if k ge l - 1 then
                results cat:= $$(S1,S2,d,a,b,k);
            end if;
            for i in [1..di] do
                for W in $$(S1,S2,d,a - i * s1,b - i * s2,k - 1) do
                    Append(~results,Append(W,[l,i]));
                end for;
            end for;
        end if;
    elif k eq 1 then
        for i in [1..#S1] do
            if S1[i] eq 0 then
                if a eq 0 then
                    if S2[i] eq 0 then
                        if b eq 0 then
                            for j in [1..d[i]] do
                                Append(~results,[[i,j]]);
                            end for;
                        end if;
                    else
                        bool,m:=IsDivisibleBy(b,S2[i]);
                        if bool and m ge 1 and m le d[i] then
                            Append(~results,[[i,m]]);
                        end if;
                    end if;
                end if;
            else
                bool,m:=IsDivisibleBy(a,S1[i]);
                if bool and m ge 1 and m le d[i] and m * S2[i] eq b then
                    Append(~results,[[i,m]]);
                end if;
            end if;
        end for;
    end if;
    return results;
end function;

function minkowski_knapsack(S1,S2,d,a,k)
    // Sanity checks
    error if #S1 ne #S2 or #S1 ne #d,
        "minkowski_knapsack: The sequences must be of the same length";
    error if &or[c le 0 : c in d],
        "minkowski_knapsack: The multiplicities must be (strictly) positive";
    error if not IsIntegral(k) or k lt 0,
        "minkowski_knapsack: The target length must be a non-negative integer";
    // Do the search
    results:=minkowski_knapsack_recurse(S1,S2,d,a,0,k);
    return {PowerSequence(PowerSequence(Integers())) | Sort(S) : S in results};
end function;

// Given a sequence of edge vectors U (in the sublattice L' of P), returns the
// corresponding lattice polygon (with the initial vertex assumed to be
// the origin of the ambient lattice L).
function edge_vectors_to_polygon(P,U)
    v:=ZeroSequence(Integers(),2);
    verts:=[PowerSequence(Integers()) | v];
    for u in U do
       v:=[Integers() | v[1] + u[1], v[2] + u[2]];
       Append(~verts,v);
    end for;
    _,emb:=fp_emb_map(P);
    return Polytope(emb(verts) : areVertices:=true);
end function;

// Given a sequence of vectors sorted in increasing angle, return the index j
// of the first entry in U such that the angle from U[0] to U[j] (via U[1])
// is >= \pi.
function get_pi_index(U)
    sgn:=Sign(Determinant(Matrix(U[1..2])));
    j:=0;
    for i in [3..#U] do
        if Sign(Determinant(Matrix([U[1],U[i]]))) ne sgn then
            j:=i;
            break;
        end if;
    end for;
    return j;
end function;

// Create the sequence U of edge vectors. Returns the sequence, along with the
// initial vertex v_0, and the index j of the first entry in U such that
// the angle from U[0] to U[j] (via U[1]) is >= \pi.
function get_edge_vectors(P)
    verts:=fp_get_pullback_vertices(P);
    edges:=EdgeIndices(P);
    // First build U
    U:=[PowerSequence(Integers())|];
    i1,i2:=Explode(Setseq(edges[#edges]));
    Prune(~edges);
    v0:=verts[i1];
    while #edges gt 0 do
        u:=verts[i2] - verts[i1];
        Append(~U,Eltseq(u));
        i1:=i2;
        for i in [1..#edges] do
            if i2 in edges[i] then
                t1,t2:=Explode(Setseq(edges[i]));
                Remove(~edges,i);
                i2:=t1 eq i2 select t2 else t1;
                break;
            end if;
        end for;
    end while;
    u:=verts[i2] - verts[i1];
    Append(~U,Eltseq(u));
    // Now figure out when the angle >= \pi
    j:=get_pi_index(U);
    // Return the data
    return U,Eltseq(v0),j;
end function;

// Returns the sequence of primitive edge vectors E, along with a sequence
// d where d[i] * E[i] is equal to U[i], where U is the sequence of edge
// vectors.
function get_primitive_edge_vectors(U)
    E:=[PowerSequence(Integers())|];
    d:=[Integers()|];
    for u in U do
        k:=GCD(u);
        v:=[Integers() | c div k : c in u];
        Append(~E,v);
        Append(~d,k);
    end for;
    return E,d;
end function;

/////////////////////////////////////////////////////////////////////////
// Decomposition functions
/////////////////////////////////////////////////////////////////////////
// These are divided into the special cases when one of the summands is
// a line, a triangle, or a an n-gon (n > 3).
/////////////////////////////////////////////////////////////////////////

// Returns the decomposition P = L + Q for the given edge data, where L is
// a line. Q will be recursively decomposed.
forward polygon_decomposition_with_edges;
function line_summands(U,E,d,j)
    // Make a note of the direction of travel
    sgn:=Sign(Determinant(Matrix(E[1..2])));
    // Start walking round E looking for opposite vectors
    i1:=1;
    i2:=j;
    pairs:=[PowerSequence(Integers())|];
    while i1 lt j and i2 le #E do
        val:=Sign(Determinant(Matrix([E[i1],E[i2]])));
        if val eq 0 then
            Append(~pairs,[i1,i2]);
            i1 +:= 1;
        elif val eq sgn then
            i2 +:= 1;
        else
            i1 +:= 1;
        end if;
    end while;
    // Now we have out collection of opposite vectors we can write down
    // the decompositions P = L + Q, where L is a line.
    decomp:={PowerSequence(PowerSequence(PowerSequence(Integers())))|};
    for pair in pairs do
        for k in [1..Minimum(d[pair[1]],d[pair[2]])] do
            // Calculate the edge data for Q
            QU:=U;
            QU[pair[1]]:=[Integers()| QU[pair[1]][1] - k * E[pair[1]][1],
                                      QU[pair[1]][2] - k * E[pair[1]][2]];
            QU[pair[2]]:=[Integers()| QU[pair[2]][1] + k * E[pair[1]][1],
                                      QU[pair[2]][2] + k * E[pair[1]][2]];
            QE:=E;
            Qd:=d;
            Qd[pair[1]]-:=k;
            Qd[pair[2]]-:=k;
            Qj:=j;
            if Qd[pair[2]] eq 0 then
                Remove(~QU,pair[2]);
                Remove(~QE,pair[2]);
                Remove(~Qd,pair[2]);
            end if;
            if Qd[pair[1]] eq 0 then
                Remove(~QU,pair[1]);
                Remove(~QE,pair[1]);
                Remove(~Qd,pair[1]);
                if pair[1] eq 1 then
                    if #QU ne 2 then Qj:=get_pi_index(QU); end if;
                else
                    Qj -:= 1;
                end if;
            end if;
            // Are we done? If not, recurse on Q
            decompE:=[PowerSequence(PowerSequence(Integers())) |
                                                    [E[pair[1]]] : i in [1..k]];
            if #QU eq 2 then
                m:=GCD(QU[1]);
                if m eq 1 then
                    Append(~decompE,[QE[1]]);
                    Sort(~decompE);
                    Include(~decomp,decompE);
                else
                    decompQ:=[PowerSequence(PowerSequence(Integers())) |
                                                         [QE[1]] : i in [1..m]];
                    Include(~decomp,Sort(decompE cat decompQ));
                end if;
            else
                decomp join:= {Sort(decompE cat decompQ) :
                      decompQ in polygon_decomposition_with_edges(QU,QE,Qd,Qj)};
            end if;
        end for;
    end for;
    // Return the decomposition
    return decomp;
end function;

// Returns the decomposition P = T + Q for the given edge data, where T is
// a triangle and Q will be recursively decomposed and will not contain any
// lines in its decomposition.
function triangle_summands(U,E,d,j)
    // Walk through the primitive vectors collecting together the triangle sums
    sums:={PowerSequence(PowerSequence(Integers()))|};
    for ei in [1..#E-2] do
        e:=E[ei];
        de:=d[ei];
        // We avoid explicitly building the set A of possible edge vectors;
        // instead we collect the indices of the primitive vectors we need.
        // We subdivide A into those pointing to the "left" of e, and those
        // pointing to the "right" of e.
        Aind:=[ei+1..#E];
        split:=false;
        sgn:=0;
        for i in [1..#Aind] do
            idx:=Aind[i];
            val:=Sign(E[idx][1] * e[2] - E[idx][2] * e[1]);
            if val eq 0 then
                split:=true;
                Aind_left:=Aind[1..i-1];
                Aind_right:=Aind[i+1..#Aind];
                break;
            elif sgn eq 0 then
                sgn:=val;
            elif sgn ne val then
                split:=true;
                Aind_left:=Aind[1..i-1];
                Aind_right:=Aind[i..#Aind];
                break;
            end if;
        end for;
        // Is there anything to do?
        if (not split) or #Aind_left eq 0 or #Aind_right eq 0 then
            continue;
        end if;
        // Start walking through Aind_left
        lE:=1;
        ld:=1;
        while lE le #Aind_left do
            // Walk through Aind_right
            rE:=1;
            rd:=1;
            while rE le #Aind_right do
                // Does this choice give a triangle sum?
                found:=false;
                wx:=ld * E[Aind_left[lE]][1] + rd * E[Aind_right[rE]][1];
                wy:=ld * E[Aind_left[lE]][2] + rd * E[Aind_right[rE]][2];
                if e[1] ne 0 then
                    bool,kx:=IsDivisibleBy(-wx,e[1]);
                    if bool and kx ge 1 and kx le de then
                        if e[2] ne 0 then
                            bool,ky:=IsDivisibleBy(-wy,e[2]);
                            if bool and kx eq ky then
                                Include(~sums,[[ei,kx],[Aind_left[lE],ld],
                                                          [Aind_right[rE],rd]]);
                                found:=true;
                            end if;
                        elif wy eq 0 then
                            Include(~sums,[[ei,kx],[Aind_left[lE],ld],
                                                          [Aind_right[rE],rd]]);
                        end if;
                    end if;
                elif wx eq 0 then
                    bool,ky:=IsDivisibleBy(-wy,e[2]);
                    if bool and ky ge 1 and ky le de then
                        Include(~sums,[[ei,ky],[Aind_left[lE],ld],
                                                          [Aind_right[rE],rd]]);
                        found:=true;
                    end if;
                end if;
                // Move on
                if found then
                    rE+:=1;
                    rd:=1;
                else
                    // Is it worth us incrementing d?
                    if rd lt d[Aind_right[rE]] and
                       Sign(wx * e[2] - wy * e[1]) eq sgn then
                        rd+:=1;
                    else
                        rE+:=1;
                        rd:=1;
                    end if;
                end if;
            end while;
            // Move on to the next ray
            if ld eq d[Aind_left[lE]] then
                ld:=1;
                lE+:=1;
            else
                ld+:=1;
            end if;
        end while;
    end for;
    // OK, that was slightly painful, but now we've got the possible triangles
    // stored in "sums", in the form of triples of [idx in E, multiple]
    // describing each edge of a triangle.
    decomp:={PowerSequence(PowerSequence(PowerSequence(Integers())))|};
    for tri in sums do
        // Create the edge vector data for the compliment Q such that P = T + Q
        UQ:=U;
        EQ:=E;
        dQ:=d;
        jQ:=j;
        for edge in tri do
            UQ[edge[1]]:=[Integers()| UQ[edge[1]][1] - edge[2] * E[edge[1]][1],
                                      UQ[edge[1]][2] - edge[2] * E[edge[1]][2]];
            dQ[edge[1]]-:=edge[2];
        end for;
        for i in Reverse(Sort([edge[1] : edge in tri])) do
            if dQ[i] eq 0 then
                Remove(~UQ,i);
                if #UQ le 2 then break; end if;
                Remove(~EQ,i);
                Remove(~dQ,i);
                if i eq 1 then
                    jQ:=get_pi_index(UQ);
                elif i le jQ then
                    jQ -:= 1;
                end if;
            end if;
        end for;
        // Is there anything to do?
        if #UQ gt 2 then
            // Create the edge vector data for the triangle T
            UT:=[PowerSequence(Integers()) | [edge[2] * E[edge[1]][1],
                                        edge[2] * E[edge[1]][2]] : edge in tri];
            ET:=[PowerSequence(Integers()) | E[edge[1]] : edge in tri];
            dT:=[Integers() | edge[2] : edge in tri];
            // Recurse
            decompT:=polygon_decomposition_with_edges(UT,ET,dT,3 : depth:=3);
            if #decompT ne 0 then
                decompQ:=polygon_decomposition_with_edges(UQ,EQ,dQ,jQ:depth:=3);
                // Modge them together
                decomp join:= {Universe(decomp) | Sort(TT cat QQ) :
                                                  TT in decompT, QQ in decompQ};
            end if;
        end if;
    end for;
    // Return the decomposition
    return decomp;
end function;

// Returns the decomposition P = R + Q for the given edge data, where R is
// an n-gon and Q will be recursively decomposed and will not contain any
// (n-1)-gons in its decomposition.
function ngon_summands(U,E,d,j,n)
    // Walk through the primitive vectors collecting together the n-gon sums
    sums:={PowerSequence(PowerSequence(Integers()))|};
    // We can use a faster technique in the case when when all the U are
    // primitive vectors (in practise this is quite common)
    if &and[dd eq 1 : dd in d] then
        for ei in [1..#E-n+1] do
            e:=E[ei];
            // We work with two forms -- e and e^\perp
            vale:=-&+[c^2 : c in e];
            // Create the knapsack vectors
            si:=[Integers()|];
            S1:=[Integers()|];
            S2:=[Integers()|];
            for i in [ei+1..#E] do
                val2:=E[i][1] * e[2] - E[i][2] * e[1];
                if val2 ne 0 then
                    val1:=E[i][1] * e[1] + E[i][2] * e[2];
                    Append(~S1,val1);
                    Append(~S2,val2);
                    Append(~si,i);
                end if;
            end for;
            // Do the search
            sums join:= {PowerSequence(PowerSequence(Integers())) |
                            [[ei,1]] cat [[si[i],1] : i in idxs] :
                            idxs in bi_knapsack_k_terms(S1,S2,vale,0,n-1)};
        end for;
    else
        for ei in [1..#E-n+1] do
            e:=E[ei];
            // We work with two forms -- e and e^\perp
            vale:=-&+[c^2 : c in e];
            // Create the knapsack vectors
            si:=[Integers()|];
            S1:=[Integers()|];
            S2:=[Integers()|];
            for i in [ei+1..#E] do
                val2:=E[i][1] * e[2] - E[i][2] * e[1];
                if val2 ne 0 then
                    val1:=E[i][1] * e[1] + E[i][2] * e[2];
                    Append(~S1,val1);
                    Append(~S2,val2);
                    Append(~si,i);
                end if;
            end for;
            di:=[Integers() | d[i] : i in si];
            // Do the search
            for k in [1..d[ei]] do
                sums join:= {PowerSequence(PowerSequence(Integers())) |
                            [[ei,k]] cat [[si[f[1]],f[2]] : f in edges] :
                            edges in minkowski_knapsack(S1,S2,di,k*vale,n-1)};
            end for;
        end for;
    end if;
    // OK, now we've got the possible n-gons stored in "sums", in the form of
    // sequences of length n with entries [idx in E, multiple] describing each
    // edge of the n-gon.
    decomp:={PowerSequence(PowerSequence(PowerSequence(Integers())))|};
    for ngon in sums do
        // Create the edge vector data for the compliment Q such that P = R + Q
        UQ:=U;
        EQ:=E;
        dQ:=d;
        jQ:=j;
        for edge in ngon do
            UQ[edge[1]]:=[Integers()| UQ[edge[1]][1] - edge[2] * E[edge[1]][1],
                                      UQ[edge[1]][2] - edge[2] * E[edge[1]][2]];
            dQ[edge[1]]-:=edge[2];
        end for;
        for i in Reverse(Sort([edge[1] : edge in ngon])) do
            if dQ[i] eq 0 then
                Remove(~UQ,i);
                if #UQ lt n then break; end if;
                Remove(~EQ,i);
                Remove(~dQ,i);
                if i eq 1 then
                    jQ:=get_pi_index(UQ);
                elif i le jQ then
                    jQ -:= 1;
                end if;
            end if;
        end for;
        // Is there anything to do?
        if #UQ ge n then
            // Create the edge vector data for the ngon R
            UR:=[PowerSequence(Integers()) | [edge[2] * E[edge[1]][1],
                                       edge[2] * E[edge[1]][2]] : edge in ngon];
            ER:=[PowerSequence(Integers()) | E[edge[1]] : edge in ngon];
            dR:=[Integers() | edge[2] : edge in ngon];
            jR:=get_pi_index(UR);
            // Recurse
            decompR:=polygon_decomposition_with_edges(UR,ER,dR,jR : depth:=n);
            if #decompR ne 0 then
                decompQ:=polygon_decomposition_with_edges(UQ,EQ,dQ,jQ:depth:=n);
                // Modge them together
                decomp join:= {Universe(decomp) | Sort(RR cat QQ) :
                                                  RR in decompR, QQ in decompQ};
            end if;
        end if;
    end for;
    // Return the decomposition
    return decomp;
end function;

// Computes the decomposition of the polygon represented by the given edge data.
function polygon_decomposition_with_edges(U,E,d,j : depth:=2)
    decomp:={PowerSequence(PowerSequence(PowerSequence(Integers())))|};
    // Is there anything to do?
    if #U lt depth then return decomp; end if;
    // Compute the decomposition
    for i in [2..#U] do
        if i eq 2 then
            decomp2:=line_summands(U,E,d,j);
            if depth gt 2 and #decomp2 ne 0 then return decomp; end if;
            decomp:=decomp2;
        elif i eq 3 then
            decomp3:=triangle_summands(U,E,d,j);
            if depth gt 3 and #decomp3 ne 0 then return decomp; end if;
            if #decomp eq 0 then
                decomp:=decomp3;
            else
                decomp join:= decomp3;
            end if;
        else
            decompi:=ngon_summands(U,E,d,j,i);
            if depth gt i and #decompi ne 0 then return decomp; end if;
            if #decomp eq 0 then
                decomp:=decompi;
            else
                decomp join:= decompi;
            end if;
        end if;
    end for;
    // If we have no decompositions, the polygon is irreducible
    if #decomp eq 0 then Include(~decomp,[U]); end if;
    return decomp;
end function;

/////////////////////////////////////////////////////////////////////////
// The main decomposition functions
/////////////////////////////////////////////////////////////////////////

// Computes all possible primitive decompositions of the given line.
function line_decomposition(L)
    pt1,pt2:=Explode(Vertices(L));
    if IsZero(pt1) then
        pt,k:=primitive_nonzero_lattice_vector(pt2);
        LL:=k eq 1 select L else Polytope([pt1,pt] : areVertices:=true);
        return [[LL : i in [1..k]]];
    elif IsZero(pt2) then
        pt,k:=primitive_nonzero_lattice_vector(pt1);
        LL:=k eq 1 select L else Polytope([pt2,pt] : areVertices:=true);
        return [[LL : i in [1..k]]];
    else
        pt,k:=primitive_nonzero_lattice_vector(pt2 - pt1);
        LL:=Polytope([Zero(Parent(pt)),pt] : areVertices:=true);
        return [[Polytope([pt1] : areVertices:=true)] cat [LL : i in [1..k]]];
    end if;
end function;

// Computes all possible primitive decompositions of the given polygon.
function polygon_decomposition(P)
    // If we're here then we're dealing with a polygon.
    // We work with the maximum polytope
    P,emb,trans:=PolyhedronInSublattice(P);
    // Build the sequence of edge vectors.
    U,v0,j:=get_edge_vectors(P);
    // Create the sequence of primitive edge vectors and associated d_i
    E,d:=get_primitive_edge_vectors(U);
    // Compute the decomposition for the edge data
    decomp:=polygon_decomposition_with_edges(U,E,d,j);
    // Convert the edge vectors back into polygons
    decomp:=[[edge_vectors_to_polygon(P,U) : U in polys] : polys in decomp];
    if &or[c ne 0 : c in v0] then
        v0:=embedded_lattice_to_ambient_lattice(P,v0);
        pt:=Polytope([v0] : areVertices:=true);
        decomp:=[Append(polys,pt) : polys in decomp];
        point:=true;
    else
        point:=false;
    end if;
    // Move the polygons back into the correct space
    embdecomp:=[PowerSequence(PowerStructure(TorPol))|];
    for polys in decomp do
        embpolys:=[PowerStructure(TorPol)|];
        for P in polys do
            Q:=Image(emb,P);
            if point and Dimension(Q) eq 0 and not IsZero(trans) then
                Q:=Q + trans;
            end if;
            Append(~embpolys,Q);
        end for;
        if not point and not IsZero(trans) then
            Append(~embpolys,Polytope([trans] : areVertices:=true));
        end if;
        Append(~embdecomp,embpolys);
    end for;
    return embdecomp;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic MinkowskiDecomposition(P::TorPol) -> SeqEnum[SeqEnum[TorPol]]
{The possible primitive Minkowski decompositions of the integral polytope P}
    // Do we already know the answer?
    if not assigned P`decomposition then
        // Sanity checks
        require IsPolytope(P) and IsIntegral(P):
            "The polyhedron must be an integral polytope";
        // Get the dimension 0, 1, and 2 cases out of the way
        if Dimension(P) eq 0 then
            P`decomposition:=[[P]];
        elif Dimension(P) eq 1 then
            P`decomposition:=line_decomposition(P);
        elif Dimension(P) eq 2 then
            P`decomposition:=polygon_decomposition(P);
        // If this is a simplex, then things are pretty easy
        elif IsSimplex(P) then
            P`decomposition:=simplex_decomposition(P);
        // See if there's a cheap reason to be indecomposable
        elif is_indecomposable(P) then
            P`decomposition:=[[P]];
        // Finally, use the general dimension algorithm
        else
            P`decomposition:=general_decomposition(P);
        end if;
    end if;
    return P`decomposition;
end intrinsic;
