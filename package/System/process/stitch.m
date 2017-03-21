freeze;

/////////////////////////////////////////////////////////////////////////
// stitch.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37558 $
// $Date: 2012-02-27 22:58:22 +1100 (Mon, 27 Feb 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Stitches multiple processes together into a single Process.
/////////////////////////////////////////////////////////////////////////
// Example
// -------
// We begin by creating a sequence of five random polytopes:
//
//  Ps := [ RandomPolytope( 3, 4, 5 ) : i in [1..5] ];
//
// We use StitchProcesses to simultaneously iterate over points from each
// of the polytopes:
//
//  Q := StitchProcesses( [ PointProcess( P ) : P in Ps ] );
//  i := 0;
//  while not IsEmpty( Q ) do
//      i +:= 1;
//      printf "%o: %o\n", i, Current( Q );
//      Advance( ~Q );
//  end while;
//
// Note that the number of elements in the process Q is equal to the
// minimum number of points in one of the polytopes:
//
//  numpts := [ NumberOfPoints( P ) : P in Ps ];
//  numpts;
//  assert Minimum( numpts ) eq i;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true iff the stitch is non-empty. If true, also returns the current
// value and label.
function current_for_stitch(S)
    vs:=[* *];
    ls:=[* *];
    for P in S do
        if IsEmpty(P) then return false,_,_; end if;
        Append(~vs,Current(P));
        Append(~ls,CurrentLabel(P));
    end for;
    return true,<v : v in vs>,<l : l in ls>;
end function;

// Returns true iff the stitch is non-empty. If true, also returns the next
// value and label.
function next_for_stitch(S)
    vs:=[* *];
    ls:=[* *];
    for i in [1..#S] do
        P:=S[i];
        if IsEmpty(P) then return false,_,_; end if;
        Advance(~P);
        if IsEmpty(P) then return false,_,_; end if;
        Append(~vs,Current(P));
        Append(~ls,CurrentLabel(P));
    end for;
    return true,<v : v in vs>,<l : l in ls>;
end function;

// True iff the process is empty.
function stitch_is_empty(info)
    return info[1];
end function;

// Advances the process to the next value.
procedure stitch_advance(~info)
    error if info[1], "The process has finished.";
    bool,vs,ls:=next_for_stitch(info[2]);
    if bool then
        info:=<false,info[2],vs,ls>;
    else
        info:=<true>;
    end if;
end procedure;

// Returns the current value.
function stitch_value(info)
    error if info[1], "The process has finished.";
    return info[3];
end function;

// Returns the current label.
function stitch_label(info)
    error if info[1], "The process has finished.";
    return info[4];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic StitchProcesses( S::SeqEnum[Process] ) -> Process
{Given a sequence S of processes P1,...,Pn, creates a new process Q with values <v1,...,vn>, where vi is the current value of Pi. Q is regarded as empty as soon as any of the Pi become empty.}
    bool,vs,ls:=current_for_stitch(S);
    if bool then
        info:=<false,S,vs,ls>;
    else
        info:=<true>;
    end if;
    Reverse(~S);
    return InternalCreateProcess("Stitch",info,stitch_is_empty,stitch_advance,
                                                     stitch_value,stitch_label);
end intrinsic;
