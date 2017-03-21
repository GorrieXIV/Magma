freeze;

/////////////////////////////////////////////////////////////////////////
// minimalgenerators.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Implements Hemmecke's algorithm for computing the set of minimal
// generators of the semigroup L\cap\Z^n_{\geq 0} for a lattice
// L\subset\Z^n.
// See: arXiv:math/0203105v1 [math.CO]
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the matrix M in upper triang form such that the entries on the
// diagonal are always non-zero. In order to do this we might need to perform
// column operations or drop zero rows. Second return value is a matrix I that
// records the column operations we did. Thid value is true if a row was pruned.
function upper_triangular(M)
    // First redurce to Echelon form
    M:=EchelonForm(M);
    d:=NumberOfColumns(M);
    pruned:=false;
    // Prune any empty rows
    for i in [NumberOfRows(M)..1 by -1] do
        if &and[M[i][j] eq 0 : j in [i..d]] then
            RemoveRow(~M,i);
            pruned:=true;
        end if;
    end for;
    // Now reorder the columns if necessary to make sure that the leading
    // diagonal is non-empty. We also take this oportunity to remove any
    // common factors from each column.
    I:=IdentityMatrix(Rationals(),d);
    r:=NumberOfRows(M);
    for i in [1..Minimum(d,r)] do
        if M[i][i] eq 0 then
            k:=GCD([Integers() | M[j][i] : j in [1..r]]);
            if k gt 1 then
                for j in [1..r] do
                    M[j][i] div:= k;
                    I[j][i] /:= k;
                end for;
            end if;
            for j in [i+1..d] do
                if M[i][j] ne 0 then
                    SwapColumns(~M,i,j);
                    SwapColumns(~I,i,j);
                    break;
                end if;
            end for;
        end if;
    end for;
    return M,I,pruned;
end function;

// Returns the lift F of H_j^+. Hpj (=H_j^+) is a sequence of vectors, P is
// the (upper triangular) matrix of points, and j is the current
// dimension/index. Returns a sequence of vectors.
// Note: This is the place where the dimension of the vectors increases by 1.
function lift(Hpj,P,j)
    // We want to calculate the lift of H_j^+\mapsto H_{j+1}^+
    // First we do the kernel case
    if j lt NumberOfRows(P) then
        K:=Submatrix(P,1,1,j,j);
        finalcol:=Submatrix(P,1,j+1,j,1);
        finalelt:=P[j+1][j+1];
        F:=[PowerSequence(Integers())|];
        // For each point h in H_j^+ we need to calculate the lift (h,h') where
        // h' is the smallest positive integer
        for h in Hpj do
            a:=Solution(K,Matrix(1,j,h));
            c:=a * finalcol;
            c:=c[1][1];     // NB: This isn't doing anything -- c is a 1x1 mat
            // We get h'
            hp:=c + Ceiling(-c / finalelt) * finalelt;
            // Record (h,h')
            Append(~F,Append(h,hp));
        end for;
        // We need to tag on sub-lattice generators
        B:=Submatrix(P,j+1,1,1,j+1);
        F:=F cat RowSequence(B) cat RowSequence(-B);
    // And now the (easier) non-kernel case
    else
        K:=Submatrix(P,1,1,NumberOfRows(P),j);
        finalcol:=Submatrix(P,1,j+1,NumberOfRows(P),1);
        F:=[PowerSequence(Integers())|];
        // For each point h in H_j^+ we need to calculate the lift (h,h') where
        // h' is the smallest positive integer
        for h in Hpj do
            a:=Solution(K,Matrix(1,j,h));
            c:=a * finalcol;
            hp:=c[1][1];
            Append(~F,Append(h,hp));
        end for;
    end if;
    return F;
end function;

// Returns the grading of v
function grading(v)
    return &+[v[i] : i in [1..#v-1]];
end function;

// Returns the ith graded component of F
function graded_component(F,Fgradings,i)
    return [PowerSequence(Integers()) | F[k] : k in [1..#Fgradings] |
                                                           Fgradings[k] eq i];
end function;

// Returns the S-vector of the vectors f and g, defined by:
//     f + g,    if f[d] * g[d] lt 0, where d = dim f = dim g
//     nohing,   otherwise.
// To capture the idea of "nothing" we return false.
function s_vector(f,g)
    return Sign(f[#f]) * Sign(g[#g]) lt 0 select
           [Integers() | f[i] + g[i] : i in [1..#f]] else false;
end function;

// Implements the "square-subset" definition at the top of page 4. Input is two
// vectors u and v of the same length, output is a boolean. (Returns true if
// u and v lie in the same orthant.)
function cmp_orthant(u,v)
    return &and[u[i] le v[i] : i in [1..#u - 1]] and Abs(u[#u]) le Abs(v[#v])
            and Sign(u[#u]) * Sign(v[#v]) ge 0;
end function;

// Algorithm 2.4 refined - Normal form. s is a vector, GG is a graded sequence
// of vectors. Returns a vector.
function normal_form(s,GG)
    grad:=grading(s);
    while true do
        // Is there a g in G s.t. cmp_orthant(g,s)?
        g:=false;
        for i in {0..grad} meet Keys(GG) do
            for gg in GG[i] do
                if cmp_orthant(gg,s) then
                    g:=gg;
                    ggrad:=i;
                    break i;
                end if;
            end for;
        end for;
        if Type(g) eq BoolElt then break; end if;
        // Calculate \alpha
        a:=Minimum([Floor(s[i]/g[i]) : i in [1..#g] | g[i] ne 0]);
        // Adjust s
        s:=[Integers() | s[i] - a * g[i] : i in [1..#g]];
        grad -:= a * ggrad;
    end while;
    // Return s
    return s;
end function;

// Returns true iff the vector s is reduced w.r.t. GG. Assumes that GG contains
// a minimal generating set.
function is_reduced(s,GG)
    // Is there a g in G s.t. cmp_orthant(g,s)?
    grad:=grading(s);
    for i in {0..Floor(grad / 2)} meet Keys(GG) do
        for gg in GG[i] do
            if cmp_orthant(gg,s) then
                return false;
            end if;
        end for;
    end for;
    // If we're here then s is minimal
    return true;
end function;

// reduce_final_coeff - Reduces the jth coefficient of the vector w.r.t. the
// given integer p.
function reduce_final_coeff(s,p,j)
    if Abs(s[j]) ge p then
        if s[j] gt 0 then
            s[j] -:= Floor(s[j] / p) * p;
        else
            s[j] +:= Ceiling(-s[j] / p) * p;
        end if;
    end if;
    return s;
end function;

// Algorithm 2.3 refined -- computes H_{j+1}^+
// Input is a sequence of vectors, output is a sequence of vectors.
// Note: This case works for all j, but if j < s then low_j_pos_neg_H below
// is significantly faster.
function high_j_H(F,j)
    // Calculate the s-vectors
    C:={PowerSequence(Integers())|};
    for i in [2..#F] do
        for j in [1..i-1] do
            s:=s_vector(F[i],F[j]);
            if Type(s) ne BoolElt then
                Include(~C,s);
            end if;
        end for;
    end for;
    // Decompose F into its graded buckets
    Fgradings:=[Integers() | grading(v) : v in F];
    GG:=AssociativeArray(Integers());
    for i in SequenceToSet(Fgradings) do
        GG[i]:=graded_component(F,Fgradings,i);
    end for;
    // Add in enough generators
    while #C ne 0 do
        s:=Representative(C);
        Exclude(~C,s);
        f:=normal_form(s,GG);
        if &or[c ne 0 : c in f] then
            for i in Keys(GG) do
                for g in GG[i] do
                    s:=s_vector(f,g);
                    if Type(s) ne BoolElt then
                        Include(~C,s);
                    end if;
                end for;
            end for;
            grad:=grading(f);
            if grad in Keys(GG) then
                Append(~GG[grad],f);
            else
                GG[grad]:=[PowerSequence(Integers()) | f];
            end if;
        end if;
    end while;
    // Refine the generators
    for i in Sort(SetToSequence(Keys(GG))) do
        num:=#[j : j in Fgradings | j eq i];
        newG:=[PowerSequence(Integers()) | g :
                                    g in GG[i][1..num] | g[j+1] ge 0];
        oldG:=GG[i][num+1..#GG[i]];
        newG:=[PowerSequence(Integers())|];
        oldG:=GG[i];
        Remove(~GG,i);
        for g in oldG do
            if g[j+1] ge 0 and is_reduced(g,GG) then
                Append(~newG,g);
            end if;
        end for;
        GG[i]:=newG;
    end for;
    // Return the generators
    return &cat[GG[i] : i in Keys(GG)];
end function;

// Algorithm 2.3 combined with Section 3 -- computes H_{j+1}^+
// Input is a sequence of vectors, output is a sequence of vectors.
// Note: This case only works when j < s
function low_j_H(F,P,j)
    // Record P[j+1][j+1] for all time
    p:=P[j+1][j+1];
    // Record the grandings once and for all
    Fgradings:=[Integers() | grading(v) : v in F];
    max:=Maximum(Fgradings);
    last_nonempty:=max;
    // Build the base list of all pairs
    grad_sums:=Exclude(SequenceToSet(Fgradings),0);
    // The base base -- extract G_0
    GG:=AssociativeArray(Integers());
    GG[0]:=graded_component(F,Fgradings,0);
    gradings:=[Integers() | 0];
    k:=Minimum(grad_sums) - 1;
    // Get going...
    repeat
        Exclude(~grad_sums,k+1);
        // Add the start of G_{k+1}
        if k+1 in Fgradings then
            GG[k+1]:=graded_component(F,Fgradings,k+1);
            Append(~gradings,k+1);
            grad_sums join:= {Integers() | g + k + 1 : g in gradings | g ne 0};
        end if;
        // Create the S-vectors
        C:={PowerSequence(Integers())|};
        for m in Keys(GG) do
            l:=k+1-m;
            if l le m and l in Keys(GG) then
                if l eq m then
                    for i in [2..#GG[m]] do
                        for n in [1..i-1] do
                            s:=s_vector(GG[m][i],GG[m][n]);
                            if Type(s) ne BoolElt then
                                s:=reduce_final_coeff(s,p,j+1);
                                Include(~C,s);
                            end if;
                        end for;
                    end for;
                else
                    for f in GG[m], g in GG[l] do
                        s:=s_vector(f,g);
                        if Type(s) ne BoolElt then
                            s:=reduce_final_coeff(s,p,j+1);
                            Include(~C,s);
                        end if;
                    end for;
                end if;
            end if;
        end for;
        // Loop through them
        for s in C do
            found:=false;
            for i in gradings[2..#gradings] do
                if i gt Ceiling(k/2) then
                    break;
                end if;
                for u in GG[i] do
                    if cmp_orthant(u,s) then
                        found:=true;
                        break i;
                    end if;
                end for;
            end for;
            if not found then
                // We've found a new basis element
                if IsDefined(GG,k+1) then
                    Append(~GG[k+1],s);
                else
                    GG[k+1]:=[PowerSequence(Integers()) | s];
                    Append(~gradings,k+1);
                    grad_sums join:= {Integers() | g + k + 1 : g in gradings |
                                                                        g ne 0};
                end if;
            end if;
        end for;
        if k ge max and k + 1 in gradings then
            last_nonempty:=k + 1;
        end if;
        if #grad_sums eq 0 then
            k:=2 * last_nonempty + 1;
        else
            k:=Minimum(grad_sums) - 1;
        end if;
    until 2 * last_nonempty lt k;
    // Return the positive generators
    return [PowerSequence(Integers()) | h : h in GG[i], i in Keys(GG) |
                                                                   h[j+1] ge 0];
end function;

// The iterative step -- input is H_j^+, output is H_{j+1}^+, where H_j^+ is
// a sequence of vectors of dimension j, and H_{j+1}^+ is a sequence of
// vectors of dimension j+1.
function inductive_step(Hpj,P,j)
    // First we lift the vectors to dimension j+1
    F:=lift(Hpj,P,j);
    // Now we compute a minimal generating set for H_{j+1}^+.
    return j lt NumberOfRows(P) select low_j_H(F,P,j) else
                                       high_j_H(F,j);
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic MinimalPositiveGenerators(S::SeqEnum[SeqEnum[RngIntElt]])
    -> SeqEnum[SeqEnum[RngIntElt]]
{}
    // Sanity checks
    require #S gt 0: "Argument 1 must be non-empty";
    d:=#Representative(S);
    require d gt 0: "The dimension of the lattice must not be zero";
    require &and[#pt eq d : pt in S]:
        "The points must all be of the same dimension";
    // Make the Echelon matrix of points
    P,I,pruned:=upper_triangular(Matrix(S));
    // Was this a degenerate case?
    if NumberOfRows(P) eq 0 then
        if pruned then
            return [PowerSequence(Integers()) | ZeroSequence(Integers(),d)];
        else
            return [PowerSequence(Integers())|];
        end if;
    end if;
    // The base case
    Hpj:=[PowerSequence(Integers()) | [Integers() | P[1][1]]];
    // Lift up though to the ambient dimension
    for j in [1..d-1] do
        Hpj:=inductive_step(Hpj,P,j);
    end for;
    // Was this a degenerate case?
    if #Hpj eq 0 then
        if pruned then
            return [PowerSequence(Integers()) | ZeroSequence(Integers(),d)];
        else
            return [PowerSequence(Integers())|];
        end if;
    end if;
    // Revert the column operations
    H:=Matrix(Rationals(),Hpj);
    H:=ChangeRing(H * I^(-1),Integers());
    // Return the minimal generators (as a sequence)
    return RowSequence(H);
end intrinsic;

intrinsic MinimalPositiveGenerators(S::SeqEnum[TorLatElt])
    -> SeqEnum[TorLatElt]
{The minimal generators of the semigroup given by intersecting the lattice generated by the points in S with the positive orthant}
    // Sanity checks
    require #S gt 0: "Argument 1 must be non-empty";
    require Dimension(Universe(S)) gt 0:
        "The dimension of the lattice must not be zero";
    // If the points are all integral then this is a doddle
    if IsIntegral(S) then
        gens:=MinimalPositiveGenerators([PowerSequence(Integers()) |
                                                         Eltseq(pt) : pt in S]);
        return ChangeUniverse(gens,Universe(S));
    end if;
    // Multiply through by the denominators
    k:=LCM([Integers() | Denominator(pt) : pt in S]);
    pts:=[PowerSequence(Integers()) | [Integers() | k * c : c in Eltseq(pt)] :
                                                                       pt in S];
    // Calculate the generators
    gens:=MinimalPositiveGenerators(pts);
    // Divide back through and return the generators as lattice points
    return [Universe(S) | [Rationals() | c / k : c in pt] : pt in gens];
end intrinsic;
