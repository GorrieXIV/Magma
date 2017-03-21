freeze;

/////////////////////////////////////////////////////////////////////////
// normal_form.m
/////////////////////////////////////////////////////////////////////////
// Authors: Roland Grinis and Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// $Revision: 40983 $
// $Date: 2012-11-20 06:44:13 +1100 (Tue, 20 Nov 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// For further details on PALP Normal Form see:
//  * Maximilian Kreuzer, Harald Skarke, "PALP: A Package for Analysing
//    Lattice Polytopes with applications to toric geometry", Computer
//    Physics Communications, 157 (1), 2004, 87--106.
//  * Roland Grinis and Alexander Kasprzyk, "Normal forms of convex
//    lattice polytopes", in preparation.
// See also Kreuzer's web page:
//    http://hep.itp.tuwien.ac.at/~kreuzer/CY/CYpalp.html
// and the PALP+ wiki:
//    http://palp.itp.tuwien.ac.at/wiki/index.php/Main_Page
/////////////////////////////////////////////////////////////////////////

declare attributes TorPol:
    palp_normal_form,       // The PALP normal form of P
    palp_perm,              // The permutation of the vertices used
    affine_normal_form,     // The affine normal form of P
    affine_perm;            // The permutation of the vertices used

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a sequence S, exchanges the i-th and j-th entries.
procedure swap(~S,i,j)
    a:=S[i];
    S[i]:=S[j];
    S[j]:=a;
end procedure;

// The special case of max_pairing_matrix when the matrix has just 2 rows.
function max_pairing_matrix_2_rows(M)
    // Extract the rows
    Mrows:=RowSequence(M);
    // We begin by calculating the maximal row of M
    rows:=[Reverse(Sort(Mrows[1])),Reverse(Sort(Mrows[2]))];
    maxR:=Max(rows);
    rowidxs:=[i : i in [1..#rows] | rows[i] eq maxR];
    // Build the permutation vector
    a:=Max(Max(Mrows[1]),Max(Mrows[2]));
    perm:=ZeroSequence(Integers(),#maxR);
    perm[#perm]:=a;
    for i in [#perm - 1..1 by -1] do
        if maxR[i] ne maxR[i + 1] then
            a +:= 1;
        end if;
        perm[i]:=a;
    end for;
    // Now we work through the possibilities
    possrows:=[];
    for idx in rowidxs do
        // Now we recover a permutation of the columns placing the row in
        // the order maxR
        row:=Mrows[idx];
        cperm:=[I[2] : I in Reverse(Sort([[row[i],i] : i in [1..#perm]]))];
        // Reorder the columns
        r:=idx eq 1 select Mrows[2] else Mrows[1];
        r:=[r[cperm[i]] : i in [1..#perm]];
        // We now maximise the second row with respect to the permutation
        r:=[I[2] : I in Reverse(Sort([[perm[i],r[i]] : i in [1..#perm]]))];
        // Record the resulting row
        Append(~possrows,r);
    end for;
    // Return the matrix
    return Matrix([maxR,Max(possrows)]);
end function;

// The recursive part of max_pairing_matrix below.
function max_pairing_matrix_recurse(M,perm)
    // If we're here then there are still symmetries of the columns to exploit.
    // We begin by calculating the maximal rows of M with respect to the
    // available column symmetries.
    rows:=[Reverse(Sort([[perm[i],r[i]] : i in [1..#perm]])) :
                                                           r in RowSequence(M)];
    rows:=[[I[2] : I in r] : r in rows];
    maxR:=Max(rows);
    rowidxs:=[i : i in [1..#rows] | rows[i] eq maxR];
    // Update the permutation vector
    newperm:=perm;
    for i in [#perm - 1..1 by -1] do
        if newperm[i] eq newperm[i + 1] and maxR[i] ne maxR[i + 1] then
            for j in [1..i] do
                newperm[j] +:= 1;
            end for;
        end if;
    end for;
    // Note the permutation group that we'll be using
    S:=Sym(#perm);
    // Now we work through the possibilities
    possN:=[];
    augNs:=[];
    for idx in rowidxs do
        // The first thing we do is exchange this row with the first row
        N:=SwapRows(M,1,idx);
        // Now we recover a permutation of the columns placing the row in
        // the order maxR
        cperm:=S ! [I[3] : I in Reverse(Sort([[perm[i],N[1][i],i] :
                                                            i in [1..#perm]]))];
        // Reorder the columns
        N:=Transpose(Matrix(PermuteSequence(RowSequence(Transpose(N)),cperm)));
        // If this is new, record it
        augN:=N;
        augN[1]:=Vector(newperm);
        if not &or[IsIsomorphic(augNN,augN) : augNN in augNs] then
            Append(~augNs,augN);
            Append(~possN,N);
        end if;
    end for;
    perm:=newperm;
    // Possibly we've exhausted all the column symmetries, so are done
    nr:=NumberOfRows(M);
    maxR:=Vector(maxR);
    if &and[perm[i] ne perm[i + 1] : i in [1..#perm - 1]] then
        N:=possN[1];
        maxN:=Matrix(Reverse(Append(Sort(N[2..nr]),maxR)));
        for i in [2..#possN] do
            N:=possN[1];
            newN:=Matrix(Reverse(Append(Sort(N[2..nr]),maxR)));
            if newN gt maxN then
                maxN:=newN;
            end if;
        end for;
        return maxN;
    end if;
    // If there's only one row left to consider, we do that now
    if nr eq 2 then
        N:=possN[1];
        maxN:=[I[2] : I in Reverse(Sort([[perm[j],N[nr][j]] :
                                                            j in [1..#perm]]))];
        for i in [2..#possN] do
            N:=possN[i];
            row:=[I[2] : I in Reverse(Sort([[perm[j],N[nr][j]] :
                                                            j in [1..#perm]]))];
            if row gt maxN then
                maxN:=row;
            end if;
        end for;
        return Matrix([maxR,Vector(maxN)]);
    end if;
    // Otherwise, we recurse for each possible N
    maxN:=VerticalJoin(maxR,$$(Matrix(possN[1][2..nr]),perm));
    for i in [2..#possN] do
        newN:=VerticalJoin(maxR,$$(Matrix(possN[i][2..nr]),perm));
        if newN gt maxN then
            maxN:=newN;
        end if;
    end for;
    return maxN;
end function;

// Given a rectangular matrix with no repeated column or row, return the maximal
// lexicographic (row by row) matrix.
function max_pairing_matrix(M)
    // If there are just two rows in the matrix we use a special function
    if NumberOfRows(M) eq 2 then
        return max_pairing_matrix_2_rows(M);
    end if;
    // Otherwise use use the generic recursive function
    a:=Max(Eltseq(M)) + 1;
    perm:=[Integers() | a : i in [1..NumberOfColumns(M)]];
    return max_pairing_matrix_recurse(M,perm);
end function;

// The classic PALP normal form algorithm. P is a polytope, n is the dimension,
// and PM is the pairing matrix. The algorithm is intended for integer polytopes
// of maximal dimension only!
function palp_normal_form(P,PM,n : apply_palp_twist:=true)
    // Save the data we need
    nv:=NumberOfVertices(P);
    nf:=NumberOfFacets(P);
    V:=Transpose(Matrix(Vertices(P)));
    // If the equations of the hyperplanes bounding the polytope are of the
    // form a[i].x + c[i] >= 0 where i = 0,...,nf-1 (and c[i] = 1 given a
    // reflexive polytope) then, letting V[][i]=v[i], i.e. we pick the i-th
    // vertex, we have:
    // PM[i][j] = a[i].v[j] + c[i]  for i = 0,...,nf - 1  and  j = 0,...,nv - 1
    // Note the computation of PM is the most expensive operation in this
    // algorithm.
    // We will compute the maximal matrix PMmax, in the lexicographic sense
    // (row by row), by swapping rows and columns of PM. It always exists and
    // is clearly unique.
    // If one could obtain PMmax by doing another combination of permutations
    // this will be recorded in the integer ns. In other words, ns is the number
    // of permutations which leaves PMmax invariant.
    // * C[i] is a permutation of columns.
    // * L[i] is a permutation of rows (lines).
    // * i = 1,...,ns
    // * C and L always go in pair (they do not make sense alone)
    // * ns is the number of this pairs.
    // Note that two columns or lines of PM can not be identical.
    ns:=1;
    C:=[[1..nv] : i in [1..ns]];    // (array of column permutations)
    L:=[[1..nf] : i in [1..ns]];    // (array of line permutations)
    // We know construct the first line of PMmax, this will contain the maximal
    // entry of PM and the entries of this line should be in decreasing order.
    // We find the permutation C[1] which maximize the first line of PM
    // PM[1][[C[1][i]] >= PM[1][[C[1][j]]] if i < j.
    for j in [1..nv] do
        _,m:=Max([PM[1][C[1][i]] : i in [j..nv]]);
        if m + j - 1 gt j then
            swap(~C[1],j,m + j - 1);
        end if;
    end for;
    // We let this to be our reference/best line for the moment
    b:=PM[1];
    // We seek for a better line, the one which has greater entries, or one
    // which will be equal b, while both are in maximal order, in which case ns
    // will increase.
    for k in [2..nf] do
        // Pick new permutations, initialized to the identity
        C[ns+1]:=[1..nv];
        L[ns+1]:=[1..nf];
        // Find the maximal entry in the k-th line, recall it in the permutation
        _,m:=Max([PM[k][C[ns + 1][j]] : j in [1..nv]]);
        if m gt 1 then
            swap(~C[ns + 1],1,m);
        end if;
        // Compare the maximal entry with the maximal entryof the current
        // "best" first line
        d:=PM[k][C[ns + 1][1]] - b[C[1][1]];
        if d lt 0 then
            continue;     // (if smaller continue with the next line)
        end if;
        // If not, then we should maximize this line but still comparing at
        // each step since if at some point an entry smaller, then this line
        // will not fill the requirements for being the first line, it will be
        // smaller than the current.
        for i in [2..nv] do
            _,m:=Max([PM[k][C[ns + 1][j]] : j in [i..nv]]);
            if m + i - 1 gt i then
                swap(~C[ns + 1],i,m + i - 1);
            end if;
            if d eq 0 then
                d:=PM[k][C[ns + 1][i]] - b[C[1][i]];
                if d lt 0 then
                    break;
                end if;
            end if;  
        end for;
        // If a smaller entry is found we continue with the next line
        if d lt 0 then
            continue;
        end if;
        // If not, then we have found another first line, we recall its position
        // in  L[ns + 1], i.e. it will be moved to the top.
        swap(~L[ns + 1],1,k);
        if d eq 0 then
            // The line is equal to the current best line. We can obtain the
            // first line by doing another permutation hence ns increase.
            ns:=ns + 1;
        else
            // If the current line is actually bigger then we take it as a new
            // first line and we forget about the previous
            C[1]:=C[ns + 1];
            L[1]:=L[ns + 1];
            // ns drops to 1
            ns:=1;
            // We have our new best/reference line
            b:=PM[k];
        end if;
    end for;
    // Once we have constructed our first line and the associated C[i] and L[i]
    // permutations we determine the sub-symmetry imposed by the first line for
    // the permutations of columns C
    S:=[1 : i in [1..nv]];
    for i in [2..nv] do
        if PM[L[1][1]][C[1][i]] eq PM[L[1][1]][C[1][i - 1]] then
            S[i]:=S[i - 1];
            S[S[i]]:=S[S[i]] + 1;
        else
            S[i]:=i;
        end if;
    end for;
    // The array is such that:
    //    S = [i, 1, ..., 1 (ith), j, i+1, ..., i+1 (jth), k ... ]
    // We construct the next lines, but not the last one since the subsymmetry
    // S will be determined, S = [1,...,nv], completely
    for l in [2..nf - 1] do
        // We remember the current number of symmetries = the number of cases
        // to treat
        k:=ns;
        cf:=0;                  // (comparing flag)
        r:=[0 : i in [1..nv]];  // (reference line to be constructed)
        // For each case we construct the new line l respecting the subsymmetry
        // S. While constructing we might obtain a new case, i.e. the line l can
        // be constructed from different lines, or we might loose one case if
        // the configuration, {C,L} in which we are, we give rise to a smaller
        // maximal matrix.
        while k gt 0 do
            k -:= 1;
            c:=1;     // The first entry, column 1)
            np:=1;    // np will rise if the line can be constructed differently
            ccf:=cf;  // Column comparing flag
            kC:=[C[k + 1]];
            kL:=[L[k + 1]];
            // We look for the line with the maximal entry in the first
            // subsymmetry block, i.e. we are allowed to swap elements between
            // 1 and S[1]
            for K in [l..nf] do
                for j in [2..S[1]] do
                    if PM[kL[np][K]][kC[np][c]] lt PM[kL[np][K]][kC[np][j]] then
                        swap(~kC[np],c,j);
                    end if;
                end for;
                if ccf eq 0 then
                    r[1]:=PM[kL[np][K]][kC[np][1]];   // (reference entry)
                    swap(~kL[np],l,K);
                    np +:= 1;
                    // We will compare this maximal entry, r[1], against entries
                    // of other lines in the first symmetry block
                    kC[np]:=C[k + 1];   // (initialize the new permutations)
                    kL[np]:=L[k + 1];   // (for an eventual symmetry)
                    ccf:=1;
                else
                    d:=(PM[kL[np][K]][kC[np][1]] - r[1]);  // comparing to r[1]
                    if d lt 0 then
                        // Consider the next line
                        continue;
                    elif d eq 0 then
                        // The maximal values agree, so we have an eventual
                        // case a of symmetry
                        swap(~kL[np],l,K);
                        np +:= 1;
                        // Initialize the the new permutations
                        kC[np]:=C[k + 1];
                        kL[np]:=L[k + 1];
                    else
                        // We have found a greater maximal value for the first
                        // entry. It will be our new reference.
                        r[1]:=PM[kL[np][K]][kC[np][1]];
                        cf:=0;
                        // We forget the work previously done
                        kC[1]:=kC[np];
                        kL[1] := kL[np];
                        // Will look for an eventual better or equal maximal
                        // value
                        np:=2;
                        kC[np]:=C[k + 1];
                        kL[np]:=L[k + 1];
                        // ns should return to the initial value as the
                        // symmetries related to the old line l are not valid
                        ns:=k + 1;
                        swap(~kL[1],l,K);
                    end if;
                end if;
            end for;
            // We should construct the entries in the line respecting the
            // sub-symmetries of blocks imposed by S
            for c in [2..nv] do
                s:=S[c];
                ccf:=cf;        // (comparing flag)
                if s lt c then
                    // We locate the column in the subsymmetry block
                    s:=S[s];
                end if;
                // We go through all the new symmetry cases, and delete the one
                // which lead to smaller values
                K:=np;
                while K gt 1 do
                    K:=K - 1;
                    // Find the greatest value
                    for j in [c + 1..s] do
                        if PM[kL[K][l]][kC[K][c]] lt PM[kL[K][l]][kC[K][j]] then
                            swap(~kC[K],c,j);
                        end if;
                    end for;
                    if ccf eq 0 then
                        // Set the current value to be the reference and
                        // consider the next symmetry
                        r[c]:=PM[kL[K][l]][kC[K][c]];
                        ccf:=1;
                    else
                        d:=PM[kL[K][l]][kC[K][c]] - r[c];
                        if d lt 0 then
                            // Compared to the current np-th case we have a
                            // better value for this entry, so the considered
                            // case will lead to a smaller matrix, hence should
                            // be deleted and the number of symmetries np drop.
                            np:=np - 1;
                            if np gt K then
                                kC[K]:=kC[np];
                                kL[K]:=kL[np];
                            end if;
                        elif d gt 0 then
                            // The current case will lead to smaller matrix,
                            // hence take the considered case to reference.
                            r[c]:=PM[kL[K][l]][kC[K][c]];
                            cf:=0;
                            // Update the number of symmetries
                            np:=K + 1;
                            ns:=k + 1;
                        end if;
                    end if;
                end while;
            end for;
            // Write the new np cases obtained to C and L
            ns:=ns - 1;
            if ns gt k then
                C[k + 1]:=C[ns + 1];
                L[k + 1]:=L[ns + 1];
            end if;
            // Update comparison flag
            cf:=ns + np - 1;
            for K in [1..np - 1] do
                C[ns + 1]:=kC[K];
                L[ns + 1]:=kL[K];
                ns:=ns + 1;
            end for;
        end while;
        // Otherwise S need not to be updated
        if S  ne [1..nv] then
            c:=1;
            while c lt nv + 1 do
                s:=S[c] + 1;
                S[c]:=c;
                c:=c + 1;
                while c lt s  do
                    if PM[L[1][l]][C[1][c]] eq PM[L[1][l]][C[1][c - 1]] then
                        S[c]:=S[c - 1];
                        S[S[c]]:=S[S[c]] + 1;
                    else
                        S[c]:=c;
                    end if;
                    c:=c + 1;
                end while;
            end while;
        end if;
    end for;
    // The maximal pairing matrix
    PNF:=[[PM[L[1][i]][C[1][j]] : j in [1..nv]] : i in [1..nf]];
    // We compute a new order for the column (i.e. vertices of the polytope)
    // permutations which is independ of the order of facets (i.e. vertices of
    // the polar), so independent of L
    pi:=[1..nv];
    if apply_palp_twist then
        // We define two invariants, the maximal element and the sum of a column
        maxP:=[0 : j in [1..nv]];
        sumP:=[0 : j in [1..nv]];
        for j in [1..nv] do
            maxP[j]:=Max([PNF[i][j] : i in [1..nf]]);
            for i in [1..nf] do
                sumP[j] +:= PNF[i][j];
            end for;
        end for;
        // We sort the columns with respect to these invariants, from minimal to
        // maximal, the maximal element having the priority over the sum, and
        // one should take in account the current position of the column if both
        // of the latter invariants are equal
        for i in [1..nv] do
            k:=i;
            for j in [i + 1..nv] do
                if maxP[j] lt maxP[k] or
                    (maxP[j] eq maxP[k] and sumP[j] lt sumP[k]) then
                    k:=j;
                end if;
            end for;
            if k ne i then
                swap(~maxP,i,k);
                swap(~sumP,i,k);
                swap(~pi,i,k);
            end if;
        end for;
    end if;
    // Hence we obtain ns canonical orders of vertices for a given polytope and
    // the permutations C[i] which map the matrix odf vertices to this canonical
    // orders
    return [[C[i][pi[j]] : j in [1..nv]] : i in [1..ns]],Matrix(PNF);
end function;

// A modified PALP normal form algorithm that uses matrix isomorphism to reduce
// the number of comparisons to be made. This is intended for use with polytopes
// with a large number of symmetries in PM!
function normal_form_for_symmetries(P,PM,G,n : apply_palp_twist:=true)
    // Record the values we need
    nv:=NumberOfVertices(P);
    nf:=NumberOfFacets(P);
    // Compute the maximal lexicographic matrix associated to the pairing matrix
    PMmax:=max_pairing_matrix(PM);
    // Compute the permutation taking PM to PMmax
    bool,perm:=IsIsomorphic(PM,PMmax);
    assert bool;
    perm:=perm^-1;
    PNF:=[[PMmax[i,j] : i in [1..nf]] : j in [1..nv]];
    // As in PALP we need to compute the row-invariant permutation of columns pi
    pi:=[1..nv];
    if apply_palp_twist then
        maxP:=[Max(PNF[i]) : i in [1..nv]];
        sumP:=[&+PNF[i] : i in [1..nv]];
        for i in [1..nv] do
            k:=i;
            for j in [i + 1..nv] do
                if maxP[j] lt maxP[k] or
                    (maxP[j] eq maxP[k] and sumP[j] lt sumP[k]) then
                    k := j;
                end if;
            end for;
            if k ne i then
                swap(~maxP,i,k);
                swap(~sumP,i,k);
                swap(~pi,i,k);
            end if;
        end for;
    end if;
    // Return the permutations for the canonical order for the vertices of the
    // polytope
    return [[((pi[i] + nf)^perm)^p - nf : i in [1..nv]] : p in G],PMmax;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic MaximalVertexFacetHeightMatrix( P::TorPol : algorithm:="palp" )
    -> AlgMatElt
{The maximum vertex-facet height matrix of the polyhedron P}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P) and
        IsMaximumDimensional(P) and not IsEmpty(P):
        "Polyhedron must be a maximum dimensional non-empty lattice polytope";
    require Type(algorithm) eq MonStgElt and (algorithm eq "palp" or
        algorithm eq "symmetry"):
        "Parameter 'algorithm' must be either \"palp\" or \"symmetry\"";
    // Collect the data we need
    n:=Dimension(P);
    PM:=VertexFacetHeightMatrix(P);
    // Compute the maximum paring matrix
    if algorithm eq "palp" then
        _,PMMax:=palp_normal_form(P,PM,n);
    else
        G:=AutomorphismGroup(PM);
        _,PMMax:=normal_form_for_symmetries(P,PM,G,n);
   end if;
   // Return the matrix
   return PMMax;
end intrinsic;

// This is an alias for NormalForm
intrinsic PALPNormalForm( P::TorPol : algorithm:="palp" )
    -> SeqEnum[TorLatElt],GrpPermElt
{The PALP normal form of the maximum dimensional lattice polytope P. Also gives the permutation of the vertices used to calculate this normal form.}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P) and
        IsMaximumDimensional(P) and not IsEmpty(P):
        "Polyhedron must be a maximum dimensional non-empty lattice polytope";
    require Type(algorithm) eq MonStgElt and (algorithm eq "palp" or
        algorithm eq "symmetry"):
        "Parameter 'algorithm' must be either \"palp\" or \"symmetry\"";
    // Return the normal form
    Q,sigma:=NormalForm(P : algorithm:=algorithm);
    return Q,sigma;
end intrinsic;

intrinsic NormalForm( P::TorPol : algorithm:="palp" )
    -> SeqEnum[TorLatElt],GrpPermElt
{The PALP normal form of the maximum dimensional lattice polytope P. Also gives the permutation of the vertices used to calculate this normal form.}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P) and
        IsMaximumDimensional(P) and not IsEmpty(P):
        "Polyhedron must be a maximum dimensional non-empty lattice polytope";
    require Type(algorithm) eq MonStgElt and (algorithm eq "palp" or
        algorithm eq "symmetry"):
        "Parameter 'algorithm' must be either \"palp\" or \"symmetry\"";
    if not assigned P`palp_normal_form then
        // Collect the data we need
        n:=Dimension(P);
        PM:=VertexFacetHeightMatrix(P);
        // Compute the permutation group
        if algorithm eq "palp" then
            C:=palp_normal_form(P,PM,n);
        else
            G:=AutomorphismGroup(PM);
            C:=normal_form_for_symmetries(P,PM,G,n);
        end if;
        // We're left with the GL(n,Z) degeneracy only, so we compute the
        // Hermite normal form for each matrix of vertices and choose the
        // lexicographically (row by row) smallest one
        nv:=NumberOfVertices(P);
        V:=Transpose(Matrix(Vertices(P)));
        NF,idx:=Min([HermiteForm(Matrix([[V[i][C[k][j]] : j in [1..nv]] :
                                                i in [1..n]])) : k in [1..#C]]);
        // Cast the result into the ambient lattice and record the data
        P`palp_normal_form:=ChangeUniverse(RowSequence(Transpose(NF)),
                                                                    Ambient(P));
        P`palp_perm:=Sym(NumberOfVertices(P)) ! C[idx];
    end if;
    return P`palp_normal_form,P`palp_perm;
end intrinsic;

intrinsic AffineNormalForm( P::TorPol : algorithm:="palp" )
    -> SeqEnum[TorLatElt],GrpPermElt
{The affine normal form of the maximum dimensional lattice polytope P. Also gives the permutation of the vertices used to calculate this normal form.}
    // Sanity check
    require IsPolytope(P) and IsIntegral(P) and
        IsMaximumDimensional(P) and not IsEmpty(P):
        "Polyhedron must be a maximum dimensional non-empty lattice polytope";
    require Type(algorithm) eq MonStgElt and (algorithm eq "palp" or
        algorithm eq "symmetry"):
        "Parameter 'algorithm' must be either \"palp\" or \"symmetry\"";
    if not assigned P`affine_normal_form then
        // Collect the data we need
        n:=Dimension(P);
        PM:=VertexFacetHeightMatrix(P);
        // Compute the permutation group
        if algorithm eq "palp" then
            C:=palp_normal_form(P,PM,n);
        else
            G:=AutomorphismGroup(PM);
            C:=normal_form_for_symmetries(P,PM,G,n);
        end if;
        // The only difference between this and the NormalForm is that the
        // Hermite normal form is computed for each translation of the polytope
        // by one of its vertex as well as for each canonical order of vertices.
        nv:=NumberOfVertices(P);
        T:=[Transpose(Matrix(Vertices(P - v))) : v in Vertices(P)];
        NF,idx:=Min([HermiteForm(Matrix([[T[1][i][C[k][j]] : j in [1..nv]] :
                                                i in [1..n]])) : k in [1..#C]]);
        for h in [2..nv] do
            cNF,cidx:=Min([HermiteForm(Matrix([[T[h][i][C[k][j]] :
                                j in [1..nv]] : i in [1..n]])) : k in [1..#C]]);
            if cNF lt NF then
                NF:=cNF;
                idx:=cidx;
            end if;
        end for;
        // Cast the result into the ambient lattice and record the data
        P`affine_normal_form:=ChangeUniverse(RowSequence(Transpose(NF)),
                                                                    Ambient(P));
        P`affine_perm:=Sym(NumberOfVertices(P)) ! C[idx];
    end if;
    return P`affine_normal_form,P`affine_perm;
end intrinsic;
