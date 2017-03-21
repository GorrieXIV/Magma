freeze;

/////////////////////////////////////////////////////////////////////////
// concatenate.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36914 $
// $Date: 2012-01-13 12:00:32 +1100 (Fri, 13 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Concatenates multiple processes into a single Process.
/////////////////////////////////////////////////////////////////////////
// Example
// -------
// We use the concatenation intrinsic to create a process to generate
// all n x n Hermite forms of determinant <= d.
//
//  S := [HermiteNormalFormProcess( n, k ) : k in [1..d]];
//  P := ConcatenateProcesses( S );
//
// We can now read the values in the usual way, for example:
//
//  while not IsEmpty( P ) do
//      H := Current(P);
//      ... do something with the Hermite form H ...
//      Advance( ~P );
//  end while;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function cat_is_empty(info)
    return #info[1] eq 0;
end function;

// Advances the process to the next value.
procedure cat_advance(~info)
    error if #info[1] eq 0, "The process has finished.";
    P:=info[1][#info[1]];
    if not IsEmpty(P) then
        Advance(~P);
        if not IsEmpty(P) then return; end if;
    end if;
    while #info[1] gt 0 do
        P:=info[1][#info[1]];
        if not IsEmpty(P) then return; end if;
        Prune(~info[1]);
    end while;
end procedure;

// Returns the current value.
function cat_value(info)
    error if #info[1] eq 0, "The process has finished.";
    return Current(info[1][#info[1]]);
end function;

// Returns the current label.
function cat_label(info)
    error if #info[1] eq 0, "The process has finished.";
    return CurrentLabel(info[1][#info[1]]);
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic ConcatenateProcesses( S::SeqEnum[Process] ) -> Process
{Given a sequence S of processes, creates a new process whose values are given by the values of the process S[1], followed by the values of the process S[2], and so forth.}
    Reverse(~S);
    while #S gt 0 and IsEmpty(S[#S]) do Prune(~S); end while;
    return InternalCreateProcess("Concatenated",<S>,cat_is_empty,cat_advance,
                                                           cat_value,cat_label);
end intrinsic;
