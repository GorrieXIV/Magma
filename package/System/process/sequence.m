freeze;

/////////////////////////////////////////////////////////////////////////
// sequence.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 37567 $
// $Date: 2012-02-28 06:32:01 +1100 (Tue, 28 Feb 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Convert a sequence to a process.
/////////////////////////////////////////////////////////////////////////
// Example
// -------
// We give a detailed real-world example using many of the Process
// intrinsics.
//
// The user has a directory "/path/to/input" contains many input files,
// "data_1.txt", "data_2.txt", etc. Each line of each file contains some
// data, represented by a sequence of integers. For example, "data_1.txt"
// might begin:
//
//  1,3,3,-10,5
//  3,1,1,5,9
//  1,1,1,-10,5,5,3
//  ...
//
// The user wishes to convert each line into a set, and output the
// distinct sets to a file. For example, "data_1.txt" corresponds to the
// sets:
//
//  { -10, 1, 3, 5 }
//  { 1, 3, 5, 9 }
//  { -10, 1, 3, 5 }
//  ...
//
// Here the first and third sets are identical; we only want them to
// appear once in the output file.
//
//  inputdir := "/path/to/input";
//  outfile := "/path/to/output.txt";
//
//  found := {};
//  
//  function create_file_process( file )
//      to_set := func< x | eval "{" cat x cat "}" >;
//      filter := func< x | not x in found >;
//      P := FileProcess( inputdir cat "/" cat file );
//      return FilterProcess( ModifyProcess( P, to_set ), filter );
//  end function;
//  
//  function create_dir_process()
//      files := Split( Pipe( "ls " cat inputdir cat "/", "" ) );
//      filter := func< x | Regexp( "data_[0-9]+\.txt", x ) >;
//      P := FilterProcess( SequenceToProcess( files ), filter );
//      return ModifyProcess( P, create_file_process );
//  end function;
//  
//  for Q in create_dir_process() do
//      for x in Q do
//          fprintf outfile, "%o\n", x;
//          Include( ~found, x );
//      end for;
//  end for;
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// True iff the process is empty.
function seq_is_empty(info)
    return info[1];
end function;

// Advances the process to the next value.
procedure seq_advance(~info)
    error if info[1], "The process has finished.";
    Q:=info[2];
    if #Q eq 0 then
        info:=<true>;
    else
        x:=Q[#Q];
        Prune(~Q);
        info:=<false,Q,x,info[4] + 1>;
    end if;
end procedure;

// Returns the current value.
function seq_value(info)
    error if info[1], "The process has finished.";
    return info[3];
end function;

// Returns the current label.
function seq_label(info)
    error if info[1], "The process has finished.";
    return info[4];
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic SequenceToProcess( Q::SeqEnum ) -> Process
{A process whose elements are given by the sequence Q.}
    if #Q eq 0 then
        info:=<true>;
    else
        Reverse(~Q);
        x:=Q[#Q];
        Prune(~Q);
        info:=<false,Q,x,1>;
    end if;
    return InternalCreateProcess("Sequence",info,seq_is_empty,seq_advance,
                                                           seq_value,seq_label);
end intrinsic;
