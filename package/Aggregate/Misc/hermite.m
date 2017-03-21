freeze;

/////////////////////////////////////////////////////////////////////////
// hermite.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43732 $
// $Date: 2013-07-04 03:28:44 +1000 (Thu, 04 Jul 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Intrinsics for working with Hermite normal forms.
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a matrix M, returns M flipped along the anti-diagonal.
function flip_matrix(M)
    return ReverseColumns(Transpose(ReverseColumns(M)));
end function;

// Given positive integers l and k, returns the sequence of all sequences of
// length k whose product is l.
function divisors(l,k)
    return k eq 1 select [[l]]
        else SetToSequence(&join[{Append(S,d) : S in $$(l div d,k - 1)} :
                                                             d in Divisors(l)]);
end function;

// Given positive integers n and k, returns the set of all sequences of length
// k with entries < n.
function bounded_rows(n,k)
    return k eq 0 select {[Integers()|]}
        else &join[{Append(S,d) : S in $$(n,k - 1)} : d in [0..n - 1]];
end function;

// Returns a set whose elements are all possible sequences of length #S where
// the first element is taken from S[1], the second from S[2], etc.
function one_from_each(S)
    return #S eq 1 select {[s] : s in S[1]}
        else &join[{[s] cat Q : s in S[1]} : Q in $$(S[2..#S])];
end function;

// Converts the given index into a bounded row, i.e. a sequence of length k
// with entries < n.
function hn_index_to_bounded_row(idx,k,n)
    // Sanity check
    assert idx gt 0 and idx le n^k;
    // Convert the index into a row
    idx -:= 1;
    S:=[Integers()|];
    for j in [k..1 by -1] do
        c:=idx div n^(j - 1);
        Append(~S,c);
        idx -:= c * n^(j - 1);
    end for;
    return S;
end function;

// Converts the given index into a sequence of rows.
function hn_index_to_rows(n,idx,offset,diag)
    // First we convert the index into a sequence of row indices
    idx:=idx - 1;
    S:=[Integers()|];
    for c in offset do
        a:=idx div c;
        Append(~S,a + 1);
        idx -:= a * c;
    end for;
    Reverse(~S);
    // Now we convert each row index into a row sequence
    rows:=[ZeroSequence(Integers(),i - 1) cat [diag[i]] cat 
              hn_index_to_bounded_row(S[i],n - i,diag[i]) : i in [1..n - 1]];
    Append(~rows,Append(ZeroSequence(Integers(),n - 1),diag[n]));
    return rows;
end function;

// Computes the next sequence of rows.
function hn_next_row(n,divs)
    // Sanity check
    assert #divs ne 0;
    // Fetch the next diagonal from the sequence of divisors
    diag:=divs[#divs];
    Prune(~divs);
    // Compute the maximum row indices
    max_row_idx:=[Integers() | diag[i]^(n - i) : i in [1..n]];
    // Reset the index and compute the offset array
    offset:=[1] cat max_row_idx;
    offset:=Reverse([Integers() | &*[Integers() | offset[i] : i in [1..j]] :
                                                        j in [1..#offset - 1]]);
    index:=1;
    max_index:=&*max_row_idx;
    // Return the updated data
    return divs,diag,offset,index,max_index;
end function;

// Returns true iff the process is empty.
function hn_is_empty(info)
    return info[10];
end function;

// Increments the process.
procedure hn_advance(~info)
    // Has this process finished?
    error if info[10], "The process has finished.";
    // Increment the index
    info[6] +:= 1;
    // Have we exhausted the possibilities for the current sequence of rows?
    if info[6] gt info[7] then
        // Are there any divisors left?
        if #info[3] eq 0 then info[10]:=true; return; end if;
        // Compute the rows
        divs,diag,offset,index,max_index:=hn_next_row(info[2],info[3]);
        info[3]:=divs;
        info[4]:=diag;
        info[5]:=offset;
        info[6]:=index;
        info[7]:=max_index;
    end if;
    // Compute the matrix and bump the label
    info[8]:=Matrix(hn_index_to_rows(info[2],info[6],info[5],info[4]));
    info[9] +:= 1;
end procedure;

// Returns the current matrix from the process.
function hs_current(info)
    error if info[10], "The process has finished.";
    return info[11] select info[8] else flip_matrix(info[8]);
end function;

// Returns the current label from the process.
function hs_label(info)
    error if info[10], "The process has finished.";
    return info[9];
end function;

// Returns a new Hermite normal form process.
function new_hn_process(d,n,column)
    // Compute the rows
    divs,diag,offset,index,max_index:=hn_next_row(n,divisors(d,n));
    // Calculate the initial matrix
    H:=Matrix(hn_index_to_rows(n,index,offset,diag));
    // Initialize the info
    info:=< d,         // The determinant
            n,         // The dimension
            divs,      // The remaining possible entries on the diagonal
            diag,      // The current diagonal
            offset,    // The offset array to convert the index to row entries
            index,     // The current matrix index for the rows
            max_index, // The maximum matrix index for the rows
            H,         // The current matrix
            1,         // The current matrix label
            false,     // Has the process reached the end?
            column >;  // Do we want column or row forms?
    // Create the new process object
    return InternalCreateProcess("Hermite normal form",info,
                                 hn_is_empty,hn_advance,hs_current,hs_label);
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic HermiteNormalForms( d::RngIntElt, n::RngIntElt : column:=false )
    -> SetEnum[AlgMatElt]
{The set of all n x n (row) Hermite forms with determinant d. Set 'column' to true for the column Hermite forms.}
    // Sanity check
    require d gt 0: "Argument 1 must be a positive integer";
    require n gt 0: "Argument 2 must be a positive integer";
    require Type(column) eq BoolElt: "Parameter 'column' must be a boolean";
    // Return the normal forms
    if column then
        return &join[{Matrix(n,n,S) : S in one_from_each(rows)}
                where rows:=[[ZeroSequence(Integers(),i-1) cat [diag[i]] cat S :
                              S in bounded_rows(diag[i],n - i)] : i in [1..n]] :
                              diag in divisors(d,n)];
    else
        return &join[{flip_matrix(Matrix(n,n,S)) : S in one_from_each(rows)}
                where rows:=[[ZeroSequence(Integers(),i-1) cat [diag[i]] cat S :
                              S in bounded_rows(diag[i],n - i)] : i in [1..n]] :
                              diag in divisors(d,n)];
    end if;
end intrinsic;

intrinsic HermiteNormalFormProcess( d::RngIntElt, n::RngIntElt : column:=false )
    -> Process
{A process P for enumerating all n x n (row) Hermite normal forms with determinant d. Set 'column' to true for the column Hermite forms.}
    // Sanity check
    require d gt 0: "Argument 1 must be a positive integer";
    require n gt 0: "Argument 2 must be a positive integer";
    require Type(column) eq BoolElt: "Parameter 'column' must be a boolean";
    // Create and return the new process
    return new_hn_process(d,n,column);
end intrinsic;
