freeze;

/////////////////////////////////////////////////////////////////////////
// functions.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43422 $
// $Date: 2013-06-13 20:51:16 +1000 (Thu, 13 Jun 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// A collection of useful utility functions and intrinsics.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Functions
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// distinct_unordered_partitions
/////////////////////////////////////////////////////////////////////////
// Input: A sequence S.
// Output: All distinct, non-empty, partitions S1,S2 of S, where the order
// of the elements in S1 and S2 doesn't matter.
/////////////////////////////////////////////////////////////////////////

function distinct_unordered_partitions_compliment(S,S1)
    for s in S1 do
        Remove(~S,Index(S,s));
    end for;
    return S;
end function;

procedure distinct_unordered_partitions_recurse(i,vals,nums,S1,~S1s)
    if i eq 0 then
        Append(~S1s,S1);
    elif #nums gt 0 then
        sum:=&+nums;
        if sum - nums[1] ge i then
            $$(i,vals[2..#vals],nums[2..#nums],S1,~S1s);
        end if;
        if sum ge i then
            Append(~S1,vals[1]);
            if nums[1] eq 1 then
                vals:=vals[2..#vals];
                nums:=nums[2..#nums];
            else
                nums[1] -:= 1;
            end if;
            $$(i - 1,vals,nums,S1,~S1s);
        end if;
    end if;
end procedure;

function distinct_unordered_partitions(S)
    vals:=SetToSequence(SequenceToSet(S));
    nums:=[Integers() | #[Integers() | 1 : s in S | s eq val] : val in vals];
    S1s:=[PowerSequence(Universe(S))|];
    for i in [1..Floor(#S / 2)] do
        subS1s:=[Universe(S1s)|];
        distinct_unordered_partitions_recurse(i,vals,nums,
                                                    [Universe(S)|],~subS1s);
        S1s cat:= subS1s;
    end for;
    return [PowerSequence(Universe(S1s)) |
               [S1,distinct_unordered_partitions_compliment(S,S1)] : S1 in S1s];
end function;

/////////////////////////////////////////////////////////////////////////
// mapping_of_sequences
/////////////////////////////////////////////////////////////////////////
// Input: Two sequences A and B such that A is a subset of B.
// Output: A sequence M which we regard as a map from A to B, such that
//         A[i] equals B[M[i]].
/////////////////////////////////////////////////////////////////////////

function mapping_of_sequences(A,B)
    M:=[Integers()|];
    idxs:=[1..#B];
    for i in [1..#A] do
        for j in idxs do
            if A[i] eq B[j] then
                M[i]:=j;
                Remove(~idxs,Index(idxs,j));
                break;
            end if;
        end for;
    end for;
    return M;
end function;

/////////////////////////////////////////////////////////////////////////
// reorder_wrt_mapping
/////////////////////////////////////////////////////////////////////////
// Input: Two sequences A and B such that A is a subset of B.
// Output: A sequence M which we regards as a map from A to itself,
//        such that [A[i] : i in M] places the elements of A
//        into the same order in which they occur in B.
/////////////////////////////////////////////////////////////////////////

function reorder_wrt_mapping(A,B)
    ord:=[1..#B];
    Maug:=[PowerSequence(Integers())|];
    for i in [1..#A] do
        j:=Index(B,A[i]);
        assert j ne 0;
        Append(~Maug,[ord[j],i]);
        Remove(~ord,j);
        Remove(~B,j);
    end for;
    Sort(~Maug);
    return [Integers() | m[2] : m in Maug];
end function;

/////////////////////////////////////////////////////////////////////////
// variables_of_ring, variables_of_scheme
/////////////////////////////////////////////////////////////////////////
// Input: A ring or scheme
// Output: A sequence containing the variables
/////////////////////////////////////////////////////////////////////////

function variables_of_ring(R)
    return [R.i : i in [1..Rank(R)]];
end function;

function variables_of_scheme(R)
    return [R.i : i in [1..Length(R)]];
end function;

//////////////////////////////////////////////////////////////////////
// bounding_box
//////////////////////////////////////////////////////////////////////
// Input: A sequence of points S (all of the same dimension)
// Output: Two points 'min' and 'max' such that the cube min<=x<=max
//        contains all the points in S.
//////////////////////////////////////////////////////////////////////

function bounding_box(S)
    error if #S eq 0, "bounding_box: Argument must be a non-empty sequence";
    if Type(S) eq SetEnum then
        S:=Setseq(S);
    end if;
    min:=ChangeUniverse(S[#S],Rationals());
    max:=min;
    dim:=#min;
    Prune(~S);
    for s in S do
        error if not #s eq dim,
           "bounding_box: Points must be of the same dimension";
        for i in [1..dim] do
            if s[i] lt min[i] then
                min[i]:=s[i];
            end if;
            if s[i] gt max[i] then
                max[i]:=s[i];
            end if;
        end for;
    end for;
    return min,max;
end function;

//////////////////////////////////////////////////////////////////////
// points_in_simplex
//////////////////////////////////////////////////////////////////////
// Returns a sequence of all points contained in the codimension 1
// simplex in ZZ^k at height n.
//////////////////////////////////////////////////////////////////////
/*
    points_in_simplex(3,2);
    [
        [ 2, 0, 0 ],
        [ 1, 1, 0 ],
        [ 1, 0, 1 ],
        [ 0, 2, 0 ],
        [ 0, 1, 1 ],
        [ 0, 0, 2 ]
    ]
*/

function indexseq_to_vector(S,k)
    return [Integers() | #[1 : s in S | s eq i] : i in [1..k]];
end function;

function points_in_simplex_recurse(S,l,k,n)
    if n eq 1 then
        return &cat[[Append(s,i) : i in [s[l]..k]] : s in S];
    else
        return $$(&cat[[Append(s,i) : i in [s[l]..k]] : s in S],l + 1,k,n - 1);
    end if;
end function;

function points_in_simplex(k,n)
    if k eq 1 then
        return [[n]];
    elif n eq 1 then
        return RowSequence(IdentityMatrix(Integers(),k));
    else
        return [indexseq_to_vector(S,k) :
                 S in points_in_simplex_recurse([[i] : i in [1..k]],1,k,n - 1)];
    end if;
end function;

/////////////////////////////////////////////////////////////////////////
// seq_of_subsets
/////////////////////////////////////////////////////////////////////////
// Input: A sequence S.
// Output: A sequence of subsequences of S.
/////////////////////////////////////////////////////////////////////////
// Note: The subsequences will be monotonic with respect to the order of
// the elements in S.
/////////////////////////////////////////////////////////////////////////

function seq_of_subsets_recurse(S)
    if #S eq 0 then
        return [PowerSequence(Universe(S)) | S];
    end if;
    if #S eq 1 then
        return [PowerSequence(Universe(S)) | [Universe(S)|],S];
    end if;
    half:=#S div 2;
    parts:=Partition(S, [half, #S - half]);
    subsets:=[$$(part) : part in parts];
    return [PowerSequence(Universe(S)) | i cat j : i in subsets[1],
                                                               j in subsets[2]];
end function;

function seq_of_subsets(S)
    error if not Type(S) eq SeqEnum,
        "seq_of_subsets: Argument is of invalid type";
    return seq_of_subsets_recurse(S);
end function;

/////////////////////////////////////////////////////////////////////////
// seq_of_k_subsets
/////////////////////////////////////////////////////////////////////////
// Input: A sequence S and a non-negative integer k.
// Output: A sequence of monotonic subsequences of S of length k.
/////////////////////////////////////////////////////////////////////////
// Note: The subsequences will be monotonic with respect to the order of
// the elements in S.
/////////////////////////////////////////////////////////////////////////

function seq_of_k_subsets_recurse(S,k)
    if k eq 0 then
        return [[Universe(S)|]];
    end if;
    if #S lt k then
        return [PowerSequence(Universe(S))|];
    end if;
    if #S eq k then
        return [PowerSequence(Universe(S)) | S];
    end if;
    if k eq 1 then
        return [PowerSequence(Universe(S)) | [s] : s in S];
    end if;
    rest:=Remove(S,1);
    return [PowerSequence(Universe(S)) | [S[1]] cat i : i in $$(rest,k-1)]
                                                               cat $$(rest,k);
end function;

function seq_of_k_subsets(S,k)
    error if not Type(S) eq SeqEnum,
        "seq_of_k_subsets: Argument 1 is of invalid type";
    error if (not Type(k) eq RngIntElt) or (k lt 0),
        "seq_of_k_subsets: Argument 2 must be a non-negative integer";
    return seq_of_k_subsets_recurse(S,k);
end function;

/////////////////////////////////////////////////////////////////////////
// next_seq_of_k_subsets
/////////////////////////////////////////////////////////////////////////
// Input: A sequence of integers s, an integer n and integer k. 
// Output: A boolean and a sequence of integers which is the next element
//       (after s) among k-subsets  of [1..n]. The boolean is false if
//       such an element does not exists.
/////////////////////////////////////////////////////////////////////////
// Note: The subsequences will be monotonic. The first input (to obtain
// [1..k]) should be [0].
/////////////////////////////////////////////////////////////////////////

function next_seq_of_k_subsets(s,n,k) 
    if k gt n then  
        return false,_; 
    end if;
    if s eq [0] then
        return true, [Integers()|1..k];
    end if; 
    if k eq 0 then
        return false,_;
    end if;
    if s[1] gt n-k then
        return false,_;
    end if;
    if s[k] lt n then 
        ss:=s;
        ss[k] +:=1;
        return true, ss;
    end if;
    if s[k] eq n then 
        bool,ss:= $$(s[1..k-1] ,n-1,k-1 );
        if bool then 
            Append(~ss, ss[k-1]+1);
                return true,ss;
        end if;
        return false,_;
    end if;
end function;

/////////////////////////////////////////////////////////////////////////
// sequence_to_integers
/////////////////////////////////////////////////////////////////////////
// Input: A sequence S
// Output: True iff the elements of S can be coerced into integers. If
//        true then also returns the coercion of S.
/////////////////////////////////////////////////////////////////////////

function sequence_to_integers(S)
    SS:=[Integers()|];
    for i in S do
        bool,j:=IsCoercible(Integers(),i);
        if not bool then
            return false,_;
        end if;
        Append(~SS,j);
    end for;
    return true,SS;
end function;

/////////////////////////////////////////////////////////////////////////
// subsequences_to_integers
/////////////////////////////////////////////////////////////////////////
// Input: A sequence of sequences S.
// Output: True iff the elements of s for each subsequence s of S can
//         be coerced into integers. If true, then also returns the
//         coercion of S.
/////////////////////////////////////////////////////////////////////////

function subsequences_to_integers(S)
    SS:=[PowerSequence(Integers())|];
    for s in S do
        bool,ss:=sequence_to_integers(s);
        if not bool then
            return false,_;
        end if;
        Append(~SS,ss);
    end for;
    return true,SS;
end function;

/////////////////////////////////////////////////////////////////////////
// maximal_sets_by_inclusion
/////////////////////////////////////////////////////////////////////////
// Input: A sequence (or set) S of sets
// Output: The set of maximal sets in S ordered by inclusion
/////////////////////////////////////////////////////////////////////////

function maximal_sets_by_inclusion(S)
    tmp:=[Universe(S)|];
    for s in S do
        if &and[not s subset ss : ss in tmp] then Append(~tmp,s); end if;
    end for;
    Reverse(~tmp);
    res:={Universe(S)|};
    for s in tmp do
        if &and[not s subset ss : ss in res] then Include(~res,s); end if;
    end for;
    return res;
end function;

//////////////////////////////////////////////////////////////////////
// prod_sequences
//////////////////////////////////////////////////////////////////////
// Input: Two sequences S and Q, where the elements of Q are integers,
//        S and Q of the same length.
// Output: The product of the powers S[i]^Q[i].
//////////////////////////////////////////////////////////////////////

function prod_sequences(S,Q)
    error if (not Type(S) eq SeqEnum) or (not Type(Q) eq SeqEnum),
        "prod_sequences: Arguments of invalid type";
    error if not #S eq #Q,
        "prod_sequences: Arguments must have the same length";
    return &*[Power(S[i],Q[i]) : i in [1..#S]];
end function;

/////////////////////////////////////////////////////////////////////////
// negate_sequence
/////////////////////////////////////////////////////////////////////////
// Input: A sequece of objects for which it makes sense to take -'ve.
// Output: A sequence given by taking the -'ves.
/////////////////////////////////////////////////////////////////////////

function negate_sequence(S)
    return [Universe(S) | -v : v in S];
end function;

/////////////////////////////////////////////////////////////////////////
// negate_subsequences
/////////////////////////////////////////////////////////////////////////
// Input: A sequence of sequences for which it makes sense to take -'ve.
// Output: Takes -'ves.
/////////////////////////////////////////////////////////////////////////

function negate_subsequences(S)
    return [Universe(S) | negate_sequence(s) : s in S];
end function;

/////////////////////////////////////////////////////////////////////////
// is_superset_of
/////////////////////////////////////////////////////////////////////////
// Input: A sequence (or set, or list, etc.) of sequences K, and a
//        sequence S.
// Output: True iff there exists an element F of K such that F is a
//        set-wise subsequence of S.
/////////////////////////////////////////////////////////////////////////

function is_superset_of(S, K)
    for F in K do
        if IsSubsequence(F, S : Kind:="Setwise") then
            return true;
        end if;
    end for;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// is_strict_subset_of
/////////////////////////////////////////////////////////////////////////
// Input: A sequence (or set, or list, etc.) of sequences K, and a
//        sequence S.
// Output: True iff there exists an element F ne S of K such that S is a
//        set-wise subsequence of F.
/////////////////////////////////////////////////////////////////////////

function is_strict_subset_of(S, K)
    for F in K do
        if S ne F and IsSubsequence(S, F : Kind:="Setwise") then
            return true;
        end if;
    end for;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// is_elmt_of
/////////////////////////////////////////////////////////////////////////
// Input: A sequence (or set, or list, etc.) of sequences (or sets, etc.)
//        K, and an element i.
// Output: True iff there exists an element F of K such that i is in F.
/////////////////////////////////////////////////////////////////////////

function is_elmt_of(i, K)
    for F in K do
        if i in F then
            return true;
        end if;
    end for;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// is_nonunitary_elmt_of
/////////////////////////////////////////////////////////////////////////
// Input: A sequence (or set, or list, etc.) of sequences (or sets, etc.)
//        K, and an element i.
// Output: True iff there exists an element F of K such that #F > 1 and
//        is i lies in F.
/////////////////////////////////////////////////////////////////////////

function is_nonunitary_elmt_of(i, K)
    for F in K do
        if #F ne 1 and i in F then
            return true;
        end if;
    end for;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// remove_repetitions
/////////////////////////////////////////////////////////////////////////
// Input: A sequence S.
// Output: S is modified to remove any repetitions.
/////////////////////////////////////////////////////////////////////////
// Note: This is different from calling Setseq(Seqset(S)), because the
// order of the elements in S is preserved.
// S can also be a tuple, a list, an ordered set, etc.
/////////////////////////////////////////////////////////////////////////

procedure remove_repetitions(~S)
    error if not (Type(S) eq SetEnum or Type(S) eq SeqEnum or Type(S) eq Tup or
        Type(S) eq SetIndx or Type(S) eq List),
        "remove_repetitions: Argument is of invalid type";
    SS:=Seqset(S);
    if #SS ne #S then
        S:=[Universe(S)| S[i] : i in Sort([Integers() | Index(S,s) : s in SS])];
    end if;
end procedure;

//////////////////////////////////////////////////////////////////////
// bi_knapsack_k_terms
//////////////////////////////////////////////////////////////////////
// Input: S1 and S2 are a sequences of integers of the same length.
// Output: Set of all indices of entries in S1 and S2 of length k
// such that the sum from S1 equals 'a', and the sum from S2 equals
// 'b'. The sequences of indices are sorted in increasing order.
//////////////////////////////////////////////////////////////////////
// Note: S1 and S2 can also be tuples orordered sets.
//////////////////////////////////////////////////////////////////////

function bi_knapsack_k_terms_recurse(S1,S2,idx,a,b,k)
    results:={PowerSequence(Integers())|};
    if k gt 1 and #S1 ge k then
        recalc:=true;
        while recalc and #S1 ge k do
            num:=#S1;
            smallest_sum_a:=&+S1[1..k-1];
            largest_sum_a:=&+S1[num-k+2..num];
            tmp:=Sort(S2);
            smallest_sum_b:=&+tmp[1..k-1];
            largest_sum_b:=&+tmp[num-k+2..num];
            recalc:=false;
            for i in [num..1 by -1] do
                if S1[i] + smallest_sum_a gt a or S1[i] + largest_sum_a lt a or
                   S2[i] + smallest_sum_b gt b or S2[i] + largest_sum_b lt b then
                    Remove(~S1,i);
                    Remove(~S2,i);
                    Remove(~idx,i);
                    if i le k - 1 or i ge num - k + 2 then
                        recalc:=true;
                    end if;
                end if;
            end for;
        end while;
        if #S1 gt k then
            first:=true;
            for i in [#S1..1 by -1] do
                newa:=a - S1[i];
                newb:=b - S2[i];
                thisi:=idx[i];
                Prune(~S1);
                Prune(~S2);
                Prune(~idx);
                if first then
                    results join:= $$(S1,S2,idx,a,b,k);
                    first:=false;
                end if;
                for Wini in $$(S1,S2,idx,newa,newb,k-1) do
                    Include(~results, [thisi] cat Wini);
                end for;
            end for;
        elif #S1 eq k and &+S1 eq a and &+S2 eq b then
            Include(~results,idx);
        end if;
    elif k eq 1 then
        for i in [1..#S1] do
            if S1[i] eq a and S2[i] eq b then
                Include(~results,[idx[i]]);
            end if;
        end for;
    end if;
    return results;
end function;

function bi_knapsack_k_terms(S1,S2,a,b,k)
    // Sanity checks
    error if #S1 ne #S2,
        "bi_knapsack_k_terms: The sequences must be of the same length";
    error if not IsIntegral(k) or k lt 0,
        "bi_knapsack_k_terms: The target length must be a non-negative integer";
    // Do the search
    idx:=[1..#S1];
    ParallelSort(~S1,~idx);
    S2:=[Integers() | S2[i] : i in idx];
    results:=bi_knapsack_k_terms_recurse(S1,S2,idx,a,b,k);
    return {PowerSequence(Integers()) | Sort(S) : S in results};
end function;

//////////////////////////////////////////////////////////////////////
// knapsack_repeats
//////////////////////////////////////////////////////////////////////
// Input: A sequence integers Q all of which are non-zero and of the
// same sign.
// Output: A set of all sequences of elements of Q (with repeats) such
// that their sum is n. Each subsequence is sorted in reverse
// numerical order.
//////////////////////////////////////////////////////////////////////
/*
   Q := [-2,-3,-4];
   KnapsackRepeats( Q, -8 );
   {
       [ -2, -2, -2, -2 ],
       [ -2, -3, -3 ],
       [ -4, -4 ],
       [ -2, -2, -4 ]
   }
*/

procedure negative_knapsack_repeats_recurse( ~results, working, Q, n )
    Q := [ c : c in Q | c ge n ];
    first:=true;
    while #Q gt 0 do
        b := Q[1];
        Remove( ~Q, 1 );
        newworking := working;
        newn := n;
        if first then
            $$( ~results, newworking, Q, newn );
            first:=false;
        end if;
        while b ge newn do
            Append( ~newworking, b );
            newn := newn - b;
            if newn eq 0 then
                Include( ~results, newworking );
            else
                $$( ~results, newworking, Q, newn );
            end if;
        end while;
    end while;
end procedure;

procedure positive_knapsack_repeats_recurse( ~results, working, Q, n )
    Q := [ c : c in Q | c le n ];
    first:=true;
    while #Q gt 0 do
        b := Q[1];
        Remove( ~Q, 1 );
        newworking := working;
        newn := n;
        if first then
            $$( ~results, newworking, Q, newn );
            first:=false;
        end if;
        while b le newn do
            Append( ~newworking, b );
            newn := newn - b;
            if newn eq 0 then
                Include( ~results, newworking );
            else
                $$( ~results, newworking, Q, newn );
            end if;
        end while;
    end while;
end procedure;

function knapsack_repeats( Q, n )
    results := {PowerSequence(Integers())|};
    Q := Reverse(Sort(Setseq(Seqset(Q))));
    if #Q eq 0 then
        return results;
    end if;
    sgn:=Sign(Representative(Q));
    error if not &and[Sign(c) eq sgn : c in Q], "knapsack_repeats: Q must consist of non-zero integers all of the same sign";
    if sgn eq -1 then
        negative_knapsack_repeats_recurse(~results,[Integers()|],Q,n);
    else
        positive_knapsack_repeats_recurse(~results,[Integers()|],Q,n);
    end if;
    return results;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// FractionalPart
/////////////////////////////////////////////////////////////////////////
// Input: A rational number x.
// Output: The rational number y such that 0 <= y < 1 and x - y is
//        an integer.
/////////////////////////////////////////////////////////////////////////

intrinsic FractionalPart( x::FldRatElt ) -> FldRatElt
{}
    return x - Floor(x);
end intrinsic;

intrinsic FractionalPart( x::RngIntElt ) -> FldRatElt
{The fractional part of x: the unique rational number y such that 0 <= y < 1 and x - y is an integer.}
    return Rationals() ! 0;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Power
/////////////////////////////////////////////////////////////////////////
// Input: A ring inteterminate 'x' and an integral power 'n'.
// Output: x^n if n is non-negative, or 1/(x^-n) otherwise.
/////////////////////////////////////////////////////////////////////////

intrinsic Power(x::RngElt, n::RngIntElt)->.
{Raises x to the power of n}
    if n ge 0 then
        return x^n;
    else
        require not IsZero(x): "Illegal zero denominator";
        return (1/x)^-n;
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// IsMonomial
/////////////////////////////////////////////////////////////////////////
// Input: A polynomial or rational function f
// Output: True iff f is a monomial
/////////////////////////////////////////////////////////////////////////

intrinsic IsMonomial(f::RngMPolElt) -> BoolElt
{}
    return #Terms(f) eq 1 and IsOne(Coefficients(f)[1]);
end intrinsic;

intrinsic IsMonomial(f::FldFunRatElt) -> BoolElt
{True iff f is a monomial}
    return IsMonomial(Numerator(f)) and IsMonomial(Denominator(f));
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// IsWellformed
/////////////////////////////////////////////////////////////////////////
// Input: W is a sequence of weights.
// Output: True iff \Proj(W) is a wellformed w.p.s.
/////////////////////////////////////////////////////////////////////////

intrinsic IsWellformed( W::SeqEnum[RngIntElt] ) -> BoolElt
{True iff the sequence W of integer weights are those of a well-formed weighted projective space}
    return &and[w ge 1 : w in W] and &and[GCD(Remove(W,i)) eq 1 : i in [1..#W]];
end intrinsic;
