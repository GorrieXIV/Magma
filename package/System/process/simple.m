freeze;

/////////////////////////////////////////////////////////////////////////
// simple.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36914 $
// $Date: 2012-01-13 12:00:32 +1100 (Fri, 13 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Simple interface for creating a Process from a Program.
/////////////////////////////////////////////////////////////////////////
// Introduction
// ------------
// A Process is an iterative object in Magma. Given a Process P, the
// standard intrinsics are:
//
//  IsEmpty( <Process>P ) -> BoolElt
//  Advance( <Process>~P )
//  Current( <Process>P ) -> Any
//  CurrentLabel( <Process>P ) -> Any
//
// A typical use is to walk over a process looking for a particular
// value, for example:
//
//  function has_value( P, target )
//      while not IsEmpty(P) do
//          val:=Current(P);
//          if val cmpeq target then
//              return true;
//          end if;
//          Advance(~P);
//      end while;
//      return false;
//  end function;
//  
// 
// Full interface
// --------------
// Any user can create a new Process in Magma via the intrinsic:
//
//  InternalCreateProcess( <MonStgElt>name, <Tup>info,
//                         <Program>is_empty, <Program>advance,
//                         <Program>current_value, <Program>current_label )
//                         -> Process
//
// * "name" is used in printing the process, and will form part of the
//   phrase "'name' Process").
// * "info" is a tuple containing all the data needed by your process.
//   It is passed as an argument to the Programs.
// * is_empty( <Tup>info ) -> BoolElt
//   Returns true iff the process has finished.
// * advance( <Tup>~info )
//   Increments the process. If this process has already finished, this
//   should generate an error. Note: This is a procedure and not a
//   function.
// * current_value( <Tup>info ) -> Any
//   Returns the current value. If the process has finished, this should
//   generate an error.
// * current_label( <Tup>info ) -> Any
//   Returns a label for the current value. If this process has finished,
//   this should generate an error.
//
// Simplified interface
// --------------------
// The intrinsics in this file simplify the creation of a Process from
// a Program. To create a new Process, call one of:
//
//  UserProcess( <MonStgElt>name, <Program>initial_value,
//               <Program>next_value ) -> Process
//  UserProcess( <MonStgElt>name, <Program>initial_value,
//               <Program>next_value, <Any>data ) -> Process
//
// * initial_value( <Process>P ) -> BoolElt, Any
//   Given the owning process P, should return true followed by the
//   the first value in the process, or false if the process is empty.
//   Note: initial_value will be called once and only once -- namely,
//   on the first occasion a value is required. All subsequent values
//   will be obtained by calling next_value. If initial_value returns
//   false then P will be regarded as empty and next_value will never
//   be called.
//   
// * next_value( <Process>P ) -> BoolElt, Any
//   Given the owning process P, should return true followed by the
//   next value in the process, or false if the process has finished.
//   Note: next_value will only be called after initial_value has been
//   called (and returned a value). If next_value returns false, it will
//   not be called again.
//
// Your initial_value and next_value functions will no-doubt require access
// to data specific to that particular Process. This data can be set at the
// time of creation as the fourth argument to UserProcess. It can also be
// accessed and modified via two intrinsics:
//
//  SetUserProcessData( <Process>P, <Any>data )
//  GetUserProcessData( <Process>P ) -> Any
//
// Note that this simplified interface does not allow you to specify the
// label associated with each value. Instead the label will be an
// integer, starting at 1 for the first value and incrementing with each
// new value.
//
// Example
// -------
// We shall create a Process to generate all words of length k from a set S.
//
//  function initial_value( P )
//      // Recover the data for this process
//      data:=GetUserProcessData( P );
//      S:=data[1];
//      k:=data[2];
//      // Is there anything to do?
//      if k le 0 or #S eq 0 then return false,_; end if;
//      // We begin by converting S to a sequence
//      S:=SetToSequence(S);
//      // Update the data and return the initial value
//      I:=[Integers() | 1 : i in [1..k]];
//      SetUserProcessData( P, [* S, k, I *] );
//      return true, &cat [S[1] : i in [1..k]];
//  end function;
//
//  function next_value( P )
//      // Recover the data for this process
//      data:=GetUserProcessData( P );
//      S:=data[1];
//      k:=data[2];
//      I:=data[3];
//      n:=#S;
//      // Compute the next index
//      i:=#I;
//      I[i] +:= 1;
//      while I[i] gt n do
//          // Are we finished?
//          if i eq 1 then return false,_; end if;
//          // No -- move on
//          I[i]:=1;
//          i -:= 1;
//          I[i] +:= 1;
//      end while;
//      // Update the process data and return the result
//      SetUserProcessData( P, [* S, k, I *] );
//      return true, &cat [S[i] : i in I];
//  end function;
//
// Now we apply this process to generate all words of length three from four
// letters:
//
//  S:={"a","b","c","d"};
//  k:=3;
//  P:=UserProcess( "Word", initial_value, next_value, [* S, k *] );
//  while not IsEmpty(P) do
//      printf "%o: %o\n", CurrentLabel(P), Current(P);
//      Advance(~P);
//  end while;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true iff the given process is a user process.
function is_user_process(P)
    info:=InternalGetProcessInfo(P);
    return (#info eq 4 or #info eq 7 or #info eq 9) and info[1] cmpeq "up";
end function;

// Sets the user data for the given process.
procedure set_user_data(P,data)
    info:=InternalGetProcessInfo(P);
    if #info eq 4 then
        info:=<"up",[* data *],info[3],info[4]>;
    elif #info eq 7 then
        info:=<"up",[* data *],info[3],info[4],info[5],info[6],P>;
    elif #info eq 9 then
        info:=<"up",[* data *],info[3],info[4],info[5],info[6],P,
                                                               info[8],info[9]>;
    else
        error "This is not a user process.";
    end if;
    InternalSetProcessInfo(P,info);
end procedure;

// Returns true followed by the user data for the given process, or false if
// no user data is set.
function get_user_data(P)
    info:=InternalGetProcessInfo(P);
    if #info[2] eq 1 then
        return true,info[2][1];
    else
        return false,_;
    end if;
end function;

// Initializes the user process.
procedure initialize_user_process(~info)
    P:=info[7];
    bool,X:=info[5](P);
    data:=InternalGetProcessInfo(P)[2];
    if bool then
        info:=<"up", data, true, false, info[5], info[6], P, X, 1>;
    else
        info:=<"up", data, true, true>;
    end if;
    InternalSetProcessInfo(P,info);
end procedure;

// Returns true iff the user process is empty.
function up_is_empty(info)
    if not info[3] then initialize_user_process(~info); end if;
    return info[4];
end function;

// Advances the user process to the next value.
procedure up_advance(~info)
    if not info[3] then initialize_user_process(~info); end if;
    error if info[4], "The process has finished.";
    P:=info[7];
    bool,X:=info[6](P);
    data:=InternalGetProcessInfo(P)[2];
    if bool then
        info:=<"up", data, true, false, info[5], info[6], P, X, info[9] + 1>;
    else
        info:=<"up", data, true, true>;
    end if;
end procedure;

// Returns the current value of the user process.
function up_value(info)
    if not info[3] then initialize_user_process(~info); end if;
    error if info[4], "The process has finished.";
    return info[8];
end function;

// Returns the current label of the user process.
function up_label(info)
    if not info[3] then initialize_user_process(~info); end if;
    error if info[4], "The process has finished.";
    return info[9];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic UserProcess( name::MonStgElt, initial_value::Program,
    next_value::Program ) -> Process
{}
    P:=InternalCreateProcess(name,<>,up_is_empty,up_advance,up_value,up_label);
    info:=<"up", [* *], false, false, initial_value, next_value, P>;
    InternalSetProcessInfo(P,info);
    return P;
end intrinsic;

intrinsic UserProcess( name::MonStgElt, initial_value::Program,
    next_value::Program, data::Any ) -> Process
{Create the process P with name given by 'name', and programs for the initial value and next value. Both functions should accept the process P as the single argument, and return a boolean indicating whether a value exists. If a function returns true, then it should also return the value.}
    P:=InternalCreateProcess(name,<>,up_is_empty,up_advance,up_value,up_label);
    info:=<"up", [* data *], false, false, initial_value, next_value, P>;
    InternalSetProcessInfo(P,info);
    return P;
end intrinsic;

intrinsic SetUserProcessData( P::Process, data::Any )
{Set the data for the user process P}
    require is_user_process(P): "The process is not a user process.";
    set_user_data(P,data);
end intrinsic;

intrinsic GetUserProcessData( P::Process ) -> Any
{Recover the data for the user process P}
    require is_user_process(P): "The process is not a user process.";
    bool,data:=get_user_data(P);
    require bool: "No data has been assigned to this process.";
    return data;
end intrinsic;
