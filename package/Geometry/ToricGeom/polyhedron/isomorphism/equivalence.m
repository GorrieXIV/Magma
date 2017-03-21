freeze;

/////////////////////////////////////////////////////////////////////////
// equivalence.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42147 $
// $Date: 2013-02-20 01:03:59 +1100 (Wed, 20 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Equivalence of polytopes.
/////////////////////////////////////////////////////////////////////////

import "isomorphism.m": easy_checks;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Reembeds the polytopes P and Q so that they're at most codim 1. In order to
// do this it might be necessary to translate the polytopes first. Returns the
// reembedded polytopes, followed by the embeddings and any translations.
function reembed_polytopes(P,Q)
    // We want to reembed P and Q so that they're at most codim 1. In order to
    // do this we might have to translate P or Q in order to get going. So
    // we initialize the translations as zero.
    L_P:=Ambient(P);
    L_Q:=Ambient(Q);
    transP:=Zero(L_P);
    transQ:=Zero(L_Q);
    // Are the polytopes of maximal dimension? If not, move to the sublattice.
    if not IsMaximumDimensional(P) then
        // We want to move to the (non-affine) sublattice, so we use the cone
        // machinery to recover the embedding.
        _,embP:=ConeInSublattice(Cone(Vertices(P)));
        _,embQ:=ConeInSublattice(Cone(Vertices(Q)));
        // If P and Q weren't in sufficiently general position the dimensions
        // might not agree -- if that happens we translate and retry
        while Dimension(Domain(embP)) ne Dimension(Domain(embQ)) do
            if Dimension(Domain(embP)) lt Dimension(Domain(embQ)) then
                shift:=L_P ! [Random(5) : i in [1..Dimension(L_P)]];
                P:=P + shift;
                transP +:= shift;
            else
                shift:=L_Q ! [Random(5) : i in [1..Dimension(L_Q)]];
                Q:=Q + shift;
                transQ +:= shift;
            end if;
            // Recalculate the embeddings
            _,embP:=ConeInSublattice(Cone(Vertices(P)));
            _,embQ:=ConeInSublattice(Cone(Vertices(Q)));
        end while;
        // Calculate the preimages of P and Q
        P:=P @@ embP;
        Q:=Q @@ embQ;
    else
        embP:=IdentityMap(L_P);
        embQ:=IdentityMap(L_Q);
    end if;
    // Return the data
    return P,Q,embP,embQ,transP,transQ;
end function;

// Given a polytope P of codim <= 1 such that the barycentre of P is at the
// origin, returns the finite part of the automorphism of P in the ambient
// lattice.
function automorphism_group(P)
    if IsMaximumDimensional(P) then
        return AutomorphismGroup(P);
    end if;
    d:=Dimension(Ambient(P));
    assert Dimension(P) eq d - 1;
    PP,emb:=PolyhedronInSublattice(P);
    M:=DefiningMatrix(emb);
    B:=emb(Basis(Domain(emb)));
    _,proj:=Quotient(B);
    K:=Representative(Basis(Codomain(proj)) @@ proj);
    inv:=Transpose(Solution(Transpose(Matrix(Append(B,K))),
                            Transpose(Matrix(Append(B,-K)))));
    if Dimension(P) gt 0 then
        B:=VerticalJoin(M,Vector(Eltseq(K)));
        I:=ZeroSequence(Integers(),d);
        I[d]:=1;
        I:=Vector(I);
        G:={B^-1 * VerticalJoin(g * M * B^-1,I) * B :
                            g in AutomorphismGroup(PP)};
        Include(~G,inv);
        I:=Inequalities(P);
    else
        G:={inv};
    end if;
    return sub<GL(d,Integers()) | G>;
end function;

// Given a polytope P of codim = 1 such that the barycentre of P is at the
// origin, returns a change of basis B such that P * B^-1 places the points of
// P into the form (*,...,*,0).
function codim_1_change_of_basis(P)
    _,emb:=PolyhedronInSublattice(P);
    M:=DefiningMatrix(emb);
    _,proj:=Quotient(emb(Basis(Domain(emb))));
    K:=Representative(Basis(Codomain(proj)) @@ proj);
    return VerticalJoin(M,Vector(Eltseq(K)));
end function;

// Determines whether the polytopes P and Q (codim <= 1) are equivalent by using
// the barycentre technique. Returns true if they are, false otherwise. If true,
// also returns the matrix M and translation v such that P * M + v = Q.
function barycentre_equivalence(P,Q)
    // Calculate the barycentres. (Yes, I know these aren't *really*
    // barycentres! Call them "vertex averages" if you must.)
    baryP:=&+Vertices(P) / NumberOfVertices(P);
    baryQ:=&+Vertices(Q) / NumberOfVertices(Q);
    // Translate the polytopes to their barycentres and compute the isomorphism
    shiftedQ:=Q - baryQ;
    bool,phi:=IsIsomorphic(P - baryP,shiftedQ);
    if not bool then
        // Equivalent polytopes must be isomorphic at this stage
        return false,_,_;
    end if;
    // We try to score an integral translation by modifying phi with elements
    // in the automorphism group
    M:=DefiningMatrix(phi);
    G:=automorphism_group(shiftedQ);
    if IsMaximumDimensional(shiftedQ) then
        // If codim = 0 them G is the entire automorphism group
        for g in G do
            trans:=baryQ - phi(baryP) * g;
            // If we've scored an integral translation then we've won
            if IsIntegral(trans) then
                return true,M * g,trans;
            end if;
        end for;
    else
        // Otherwise we have an infinite automorphism group generated by G and
        // shear transformations. Begin by calculating a basis putting
        // shiftedQ into the hyperplane with final coordinate equal to zero.
        B:=codim_1_change_of_basis(shiftedQ);
        // Create the shear transformation matrix (w.r.t. this basis)
        d:=NumberOfRows(B);
        MM:=Submatrix(IdentityMatrix(Integers(),d),1,1,d - 1,d);
        // Start hunting
        bQ:=baryQ * B^-1;
        for g in G do
            // Recalculate the barycentre
            bP:=baryP * M * g * B^-1;
            // We can easily recover the integral translation later, so for now
            // we keep the numbers small whilst clearing the denominators
            k:=LCM(LCM([Denominator(c) : c in Eltseq(bP)]),
                   LCM([Denominator(c) : c in Eltseq(bQ)]));
            bbP:=[(Integers() ! (k * c)) mod k : c in Eltseq(bP)];
            bbQ:=[(Integers() ! (k * c)) mod k : c in Eltseq(bQ)];
            // Calculate the target
            target:=[Integers() | bbQ[i] - bbP[i] : i in [1..d]];
            // Is there a solution
            X:=VerticalJoin(bbP[d] * MM,k * IdentityMatrix(Integers(),d));
            bool,x:=IsConsistent(X,Vector(target));
            if bool then
                // We've found a solution -- calculate the change of basis
                x:=Eltseq(x);
                BB:=IdentityMatrix(Integers(),d);
                for i in [1..d - 1] do
                    BB[d,i]:=x[i];
                end for;
                augM:=g * B^-1 * BB * B;
                // Calculate the translation
                trans:=baryQ - phi(baryP) * augM;
                // Return success
                return true,M * augM,trans;
            end if;
        end for;
    end if;
    // If we're here then the polytopes are not equivalent
    return false,_,_;
end function;

// Returns a new polytope Q in ZZ^n x Z such that Q is given by the convex
// hull of P x {1} union the origin.
function cone_polytope(P)
    if IsIntegral(P) then
        verts:=[PowerSequence(Integers()) | Append(Eltseq(v),1) :
                                                              v in Vertices(P)];
        Append(~verts,ZeroSequence(Integers(),Dimension(Ambient(P)) + 1));
    else
        verts:=[PowerSequence(Rationals()) | Append(Eltseq(v),1) :
                                                              v in Vertices(P)];
        Append(~verts,ZeroSequence(Rationals(),Dimension(Ambient(P)) + 1));
    end if;
    return Polytope(verts : areVertices:=true);
end function;

// Given a change of basis matrix M sending the codim 1 coned polytope cP to
// the codim 1 coned polytope cQ, this function attempts to fix up M so that
// the height 1 slice is preserved. If it succeeds, returns true followed
// by the modified M. There's no guarantee this technique will succeed, however,
// so may return false (in which case you need to use a different method).
function are_equivalent_codim_1(L,M)
    // All we know is that the isomorphism preserves a codim 2 slice, one
    // of whose sopporting hyperplane is (0,...,0,1). Find the other.
    d:=NumberOfRows(M);
    I:=IdentityMatrix(Integers(),d);
    for i in [1..d] do
        I[i,d]:=1;
    end for;
    u:=Dual(L) ! Eltseq(Solution(Transpose(I * M),
                                   Matrix(1,d,[Integers() | 1 : i in [1..d]])));
    v:=Dual(L).d;
    // We need to rig up a change of basis preserving the hyperplane
    if u ne v then
        // We can calculate a sub-basis K in H_u\cap H_v; this can then be
        // extended to a basis in H_u for the entire lattice by adding in
        // one more element b_u, and similarly for H_v and b_v.
        // We want the change of basis that fixes all basis elements but
        // sends b_u to b_v. This will send H_u to H_v whilst fixing cQ.
        // First we build the sub-basis. The existence of this basis is where
        // we will succeed or fail: it depends on whether H_u\cap H_v contains
        // any lattice points.
        subu:=Prune(Eltseq(u));
        h,x:=XGCD(subu);
        if not IsDivisibleBy(u.d - 1,h) then
            // Urgh, it's not going to work
            return false,_;
        end if;
        s:=(1 - u.d) div h;
        x:=L ! Append([s * x[i] : i in [1..d - 1]],1);
        K:=Kernel(Matrix(d - 1,1,subu));
        K:=[Parent(x) | Append(Eltseq(k),0) : k in Basis(K)];
        K:=[x + y : y in K];
        Append(~K,x);
        assert #K eq d - 1;
        // Now we find b_u and b_v.
        LL,proj:=Quotient(K);
        b:=LL.1 @@ proj;
        b_u:=b - (b * u - 1) * K[1];
        b_v:=b - (b * v - 1) * K[1];
        // OK, now figure out the change of basis BB sending H_u to H_v
        // whilst leaving cQ unchanged.
        Mu:=Matrix(Append(K,b_u));
        Mv:=Matrix(Append(K,b_v));
        BB:=Mu^-1 * Mv;
        assert Abs(Determinant(BB)) eq 1;
        // Now we need to fix M
        M *:= BB;
    end if;
    // Return success followed by the change of basis matrix M
    return true,M;
end function;

// Attempts to build an equivalence between P and Q (codim <= 1) by coning them
// and constructing a change of basis preserving the hyperplane ZZ^n x {1}.
// This isn't guaranteed to work if the polytopes don't contain any lattice
// points. Returns true if it worked, followed by true or false if the
// polytopes are equivalent. If true,true then also returns the matrix M and
// translation v such that P * M + v = Q.
function cone_equivalence(P,Q)
    // First we cone over the polytopes
    cP:=cone_polytope(P);
    cQ:=cone_polytope(Q);
    // Hunt for an isomorphism between the coned polytopes
    bool,phi:=IsIsomorphic(cP,cQ);
    if not bool then
        // If there isn't one, P and Q cannot be equivalent
        return true,false,_,_;
    end if;
    // Note the defining matrix and size
    M:=DefiningMatrix(phi);
    d:=NumberOfRows(M);
    // If the coned polytopes are not maximum dimensional, we need to do work
    if not IsMaximumDimensional(cP) then
        // The coned polytopes must be codim 1 by construction
        assert Dimension(cP) eq Dimension(Ambient(cP)) - 1;
        // We really need to be able to compute a particular basis. This just
        // might not be possible, so we have to accept the possibility of
        // failure at this stage.
        bool,M:=are_equivalent_codim_1(Ambient(cQ),M);
        if not bool then
            return false,_,_,_;
        end if;
    end if;
    // The translation is given by the bottom row of M, and the isomorphism we
    // want is the top-left (d-1) x (d-1) submatrix
    assert &and[M[i,d] eq 0 : i in [1..d - 1]] and M[d,d] eq 1;
    trans:=Ambient(Q) ! Prune(Eltseq(M[d]));
    M:=Submatrix(M,1,1,d - 1,d - 1);
    bool,M:=CanChangeRing(M,Integers());
    assert bool;
    // Return success
    return true,true,M,trans;
end function;

/////////////////////////////////////////////////////////////////////////
// Instrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic IsEquivalent(P::TorPol,Q::TorPol)
    -> BoolElt,Map[TorLat,TorLat],TorLatElt
{True iff the polytopes P and Q are equivalent, i.e. if there exists an element in GL(n,Z) and lattice translation sending P to Q. If true, also gives the map as a lattice map phi and translation v such that phi(P) + v = Q.}
    // Sanity checks
    require IsPolytope(P): "Argument 1 must be a polytope";
    require IsPolytope(Q): "Argument 2 must be a polytope";
    // Record the ambients and check their dimensions agree
    L_P:=Ambient(P);
    L_Q:=Ambient(Q);
    if Dimension(L_P) ne Dimension(L_Q) then
        return false,_,_;
    end if;
    // Test for equality
    if P eq Q then
        return true,IdentityMap(L_P),Zero(L_P);
    end if;
    // We do the easy checks before we continue
    if not easy_checks(P,Q) then
        return false,_,_;
    end if;
    // We begin by reembedding the polytopes (after possible translation) so
    // that they're at most codim 1.
    P,Q,embP,embQ,transP,transQ:=reembed_polytopes(P,Q);
    // Try the cone method first
    success,bool,M,trans:=cone_equivalence(P,Q);
    if not success then
        // No luck -- we use the barycentre method.
        bool,M,trans:=barycentre_equivalence(P,Q);
    end if;
    // If the polytopes aren't equivalent, return false
    if not bool then
        return false,_,_;
    end if;
    // Now we need to top and tail by the embeddings. First we take into account
    // P's embedding...
    BP:=Image(embP,Basis(Domain(embP)));
    _,proj:=Quotient(BP);
    K:=Basis(Codomain(proj)) @@ proj;
    BP:=Matrix(Integers(),BP cat K);
    // ...and now Q's embedding.
    trans:=embQ(trans);    
    embQ:=LatticeMap(Domain(embQ),L_Q,M * DefiningMatrix(embQ));
    BQ:=Image(embQ,Basis(Domain(embQ)));
    _,proj:=Quotient(BQ);
    K:=Basis(Codomain(proj)) @@ proj;
    BQ:=Matrix(Integers(),BQ cat K);
    // Rebuild the isomorphism matrix...
    M:=BP^-1 * BQ;
    // ...and convert the matrix into a map.
    phi:=LatticeMap(L_P,L_Q,M);
    // We also have to chase through any translations we were forced to do
    trans +:= phi(transP);
    trans -:= transQ;
    // Return success
    return true,phi,trans;
end intrinsic;
