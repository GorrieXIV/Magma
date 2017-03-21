freeze;

/////////////////////////////////////////////////////////////////////////
// modify.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37558 $
// $Date: 2012-02-27 22:58:22 +1100 (Mon, 27 Feb 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Modifies the values returned by a Process.
/////////////////////////////////////////////////////////////////////////
// Summary
// -------
// Let us suppose that we have an existing Process P, and we wish to
// modify the return values via some function F (for example, we may
// wish to convert strings to integers). The easiest way to achieve this
// is via the ModifyProcess intrinsic:
//
//  ModifyProcess( <Process>P, <Program>F ) -> Process
//
// * F( <Any>v ) -> Any
//   The user program F should accept a value from P, and return the
//   curresponding new value.
//
// Example
// -------
// We use ModifyProcess to create a process to read a file f, and
// convert each line of the file to an integer. We then sum all the
// values.
//
//  P := FileProcess( f );
//  Q := ModifyProcess( P, StringToInteger );
//  total := 0;
//  while not IsEmpty( Q ) do
//      total +:= Current( Q );
//      Advance( ~Q );
//  end while;
//  printf "Total: %o\n", total;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Applies the function F to the value v. Returns true followed by the value of
// F(v), or false followed by an error message.
function apply_function(F,v)
    try
        res:=F(v);
        success:=true;
    catch e;
        res:=Sprintf("Error calling modification function.\n%o",e`Object);
        success:=false;
    end try;
    if not success then
        return false,res;
    else
        return true,res;
     end if;
end function;

// True iff the process is empty.
function m_is_empty(info)
    return info[1];
end function;

// Advances the process to the next value.
procedure m_advance(~info)
    error if info[1], "The process has finished.";
    P:=info[2];
    if IsEmpty(P) then
        info:=<true>;
    else
        Advance(~P);
        if IsEmpty(P) then
            info:=<true>;
        else
            v:=Current(P);
            l:=CurrentLabel(P);
            F:=info[3];
            bool,v:=apply_function(F,v);
            error if not bool, v;
            info:=<false,P,F,v,l>;
        end if;
    end if;
end procedure;

// Returns the current value.
function m_value(info)
    error if info[1], "The process has finished.";
    return info[4];
end function;

// Returns the current label.
function m_label(info)
    error if info[1], "The process has finished.";
    return info[5];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic ModifyProcess( P::Process, F::Program ) -> Process
{Create a process Q from the process P using the program F. F should accept a value from P, and return the value for Q.}
    if IsEmpty(P) then
        info:=<true>;
    else
        v:=Current(P);
        l:=CurrentLabel(P);
        bool,v:=apply_function(F,v);
        require bool: v;
        info:=<false,P,F,v,l>;
    end if;
    return InternalCreateProcess("Modified",info,m_is_empty,m_advance,m_value,
                                                                       m_label);
end intrinsic;
