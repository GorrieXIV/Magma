freeze;

/////////////////////////////////////////////////////////////////////////
// filter.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37558 $
// $Date: 2012-02-27 22:58:22 +1100 (Mon, 27 Feb 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Filter the values returned by a Process.
/////////////////////////////////////////////////////////////////////////
// Summary
// -------
// Let us suppose that we have an existing Process P, and we are only
// interested in those values of P that satisfy a certain property F.
// Then we can create a new process Q, which we call a filter, that will
// only give those values v of P such that F(v) is true.
//
//  FilterProcess( <Process>P, <Program>F ) -> Process
//
// * F( <Any>v ) -> BoolElt
//   The filter F should return a boolean, where true means that the
//   given value v of P should be included in the new process Q, and
//   false means that the value v should be omitted.
//
// Example
// -------
// Given a polytope Q, we create a new process P that only returns the
// primitive lattice points in Q.
//
//  Q := Polytope( [[0,6,10], [2,8,6], [6,8,10], [2,10,2]] );
//  P := FilterProcess( PointProcess( Q ), IsPrimitive );
//  while not IsEmpty( P ) do
//      Current( P );
//      Advance( ~P );
//  end while;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Applies the filter F to the value v. Returns true followed by the value of
// F(v), or false followed by an error message.
function apply_function(F,v)
    try
        res:=F(v);
        success:=true;
    catch e;
        success:=false;
        res:=Sprintf("Error calling filter function.\n%o",e`Object);
    end try;
    if not success then return false,res; end if;
    if not Type(res) cmpeq BoolElt then
        return false,Sprintf("Error calling filter function.\nExpected return type BoolElt but got type %o",Type(res));
    end if;
    return true,res;
end function;

// Initializes the data for the first call to any data access.
procedure first_call(~info)
    P:=info[2];
    Q:=info[3];
    F:=info[4];
    empty:=true;
    while empty and not IsEmpty(Q) do
        x:=Current(Q);
        l:=CurrentLabel(Q);
        bool,result:=apply_function(F,x);
        error if not bool, result;
        if result then
            empty:=false;
            data:=[* x, l *];
        else
            Advance(~Q);
        end if;
    end while;
    info:=empty select <true, true> else <true, false, Q, F, data>;
    InternalSetProcessInfo(P,info);
end procedure;

// True iff the process is empty.
function f_is_empty(info)
    if not info[1] then first_call(~info); end if;
    return info[2];
end function;

// Advances the process to the next value.
procedure f_advance(~info)
    if not info[1] then
        first_call(~info);
        error if info[2], "The process has finished.";
    else
        error if info[2], "The process has finished.";
        Q:=info[3];
        F:=info[4];
        Advance(~Q);
        while not IsEmpty(Q) do
            x:=Current(Q);
            l:=CurrentLabel(Q);
            bool,res:=apply_function(F,x);
            error if not bool, res;
            if res then
                data:=[* x, l *];
                info:=<true, false, Q, F, data>;
                return;
            end if;
            Advance(~Q);
        end while;
        info:=<true, true>;
    end if;
end procedure;

// Returns the current value.
function f_value(info)
    if not info[1] then first_call(~info); end if;
    error if info[2], "The process has finished.";
    return info[5][1];
end function;

// Returns the current label.
function f_label(info)
    if not info[1] then first_call(~info); end if;
    error if info[2], "The process has finished.";
    return info[5][2];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic FilterProcess( P::Process, F::Program ) -> Process
{Create a filter Q from the process P using the program F. F should accept a value from P, and return a boolean indicating whether the value is to be included in Q.}
    PP:=InternalCreateProcess("Filter",<>,f_is_empty,f_advance,f_value,f_label);
    info:=<false,PP,P,F>;
    InternalSetProcessInfo(PP,info);
    return PP;
end intrinsic;
