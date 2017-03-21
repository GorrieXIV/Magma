freeze;

/*
  $Id: Conj.m 18789 2008-11-29 05:12:52Z murray $
  
  Scott H. Murray
  Sergei Haller (tables for coxeter groups of exceptional types)

  Conjugacy classes for Coxeter groups and groups of Lie type.

  Coxeter groups:
  
     Geck+Pfeiffer (2000) was used for classical types.
 
     Algorithms for permutation groups and
     brute force for G_2,F_4,E_6,E_7.
 
     A very nifty combination of algorithms in Geck+Pfeiffer (2000),
     algorithms for permutation groups and
     some brute force "on top" were used for E_8.
 
*/

declare attributes GrpFPCox : Classes, ClassParameters;
declare attributes GrpPermCox : ClassParameters;

import "GrpCox.m" : groupToType;

// ===================================================================
//
// Finite Coxeter groups
//


// -------------------------------------------------------------------
//
// Representatives
//
// The representatives are always of minimal length in the class.
// The representatives are lexicographically least, provided the 
// numbering of the simple roots agrees with the standard numbering.
//



// Type A

partitionToWordA := function( lambda )
  w := [Integers()|];  pos := 0;
  for m in lambda do
    w cat:= [pos+1..pos+m-1];
    pos +:= m;
  end for;
  return w;
end function;

coxeterClassRepsA := function( l )

  partitionToLength := function( lambda, l )
    return Factorial(l+1) div
      &*[ Integers() | m^n*Factorial(n) where n is #[r:r in lambda|r eq m] : 
      m in Seqset(lambda) ];
  end function;

  parts := Partitions( l+1 );
  return {@ < Lcm(lambda), partitionToLength( lambda, l ),
    partitionToWordA( lambda ) > : lambda in parts @}, parts;
  
end function;


// Types B and C

partitionToWordBC := function( lambdap, lambdam, l )
  w := [Integers()|];  a := 0;
  for b in lambdam do
    w cat:= [a+1..l-1] cat [l..a+b by -1];
    a +:= b;
  end for;
  for b in Reverse( lambdap ) do
    w cat:= [a+1..a+b-1];
    a +:= b;
  end for;
  return w;
end function;

partitionToOrderBCD := function( lambdap, lambdam, l )
  return Lcm( [ 2*m : m in lambdam ] cat lambdap );
end function;

partitionToLengthBC := function( lambdap, lambdam, l )
  return (2^l * Factorial(l)) div 
    ( &*[ Integers() | (2*m)^n * Factorial(n) 
      where n is #[r:r in lambdam|r eq m] : m in Seqset(lambdam) ]
    * &*[ Integers() | (2*m)^n * Factorial(n) 
      where n is #[r:r in lambdap|r eq m] : m in Seqset(lambdap) ] );
end function;

coxeterClassRepsBC := function( l )
  
  first := {@@};  last := {@@};
  fparams := [];  lparams := [];
  for neg in [0..(l) div 2] do
    parts1 := Partitions( neg );
    parts2 := Partitions( l-neg );
    first join:= {@ < partitionToOrderBCD( lambdap, lambdam, l ), 
      partitionToLengthBC( lambdap, lambdam, l ), 
      partitionToWordBC( lambdap, lambdam, l ) > : 
      lambdap in parts1, lambdam in parts2 @};
    fparams cat:= [ <lambdap,lambdam> : lambdap in parts1, lambdam in parts2 ];
    if neg ne l-neg then
      last := {@ < partitionToOrderBCD( lambdap, lambdam, l ), 
        partitionToLengthBC( lambdap, lambdam, l ), 
        partitionToWordBC( lambdap, lambdam, l ) > : 
        lambdam in parts1, lambdap in parts2 @} join last;
      lparams := [ <lambdap,lambdam> : lambdam in parts1, lambdap in parts2 ]
        cat lparams;
    end if;
  end for;
  return first join last, fparams cat lparams;

end function;


// Type D

partitionToWordD := function( lambdap, lambdam, l, sign )
  w := [Integers()|];  a := 0;
  for b in lambdam do
    w cat:= [a+1..l-1];
    back := [l-1..a+b by -1];
    if not IsEmpty(back) then  back[1] := l;  end if;
    w cat:= back;
    a +:= b;
  end for;
  for b in Reverse( lambdap ) do
    w cat:= [a+1..a+b-1];
    a +:= b;
  end for;
  if sign eq -1 then
    Prune( ~w );  Append( ~w, l );
  end if;
  return w;
end function;

partitionToLengthD := function( lambdap, lambdam, l )
  len := (2^l * Factorial(l)) div
    ( &*[ Integers() | (2*m)^n * Factorial(n) 
      where n is #[r:r in lambdam|r eq m] : m in Seqset(lambdam) ]
    * &*[ Integers() | (2*m)^n * Factorial(n) 
      where n is #[r:r in lambdap|r eq m] : m in Seqset(lambdap) ] );
  if #lambdam eq 0 and forall{m:m in lambdap|IsEven(m)} then
    len div:= 2;
  end if;
  return len;
end function;

coxeterClassRepsD := function( l )

  if l eq 1 then
    return coxeterClassRepsA( 1 );
  end if;
  
  first := {@@};  last := {@@};
  fparams := [];  lparams := [];
  for neg in [0..(l) div 2] do
    parts1 := Partitions( neg );
    parts2 := Partitions( l-neg );
    first join:= {@ < partitionToOrderBCD( lambdap, lambdam, l ), 
      partitionToLengthD( lambdap, lambdam, l ), 
      partitionToWordD( lambdap, lambdam, l, +1 ) > : 
      lambdap in parts1, lambdam in parts2 | IsEven(#lambdam) @};
    fparams cat:= [ <lambdap,lambdam,+1> : 
      lambdap in parts1, lambdam in parts2 | IsEven(#lambdam) ];
    if neg ne l-neg then
      last := {@ < partitionToOrderBCD( lambdap, lambdam, l ), 
        partitionToLengthD( lambdap, lambdam, l ), 
        partitionToWordD( lambdap, lambdam, l, +1 ) > :
        lambdam in parts1, lambdap in parts2 | IsEven(#lambdam) @} join last;
      lparams := [ <lambdap,lambdam,+1> : 
        lambdam in parts1, lambdap in parts2 | IsEven(#lambdam) ] cat lparams;
    end if;
    if neg eq 0 and IsEven(l) then
      empty := [Integers()|];
      first join:= {@ < partitionToOrderBCD( lambdap, empty, l ), 
        partitionToLengthD( lambdap, empty, l ), 
        partitionToWordD( lambdap, empty, l, -1 ) > : 
        lambdap in parts2 | forall{m:m in lambdap|IsEven(m)} @};
      fparams cat:= [ <lambdap,empty,-1> : 
        lambdap in parts2 | forall{m:m in lambdap|IsEven(m)} ];
    end if;
  end for;
  
  return first join last, fparams cat lparams;

end function;



// Exceptional types

coxeterClassRepsExc := function( X, l )

     case X :
     when "G": return
          // the conjugacy classes were computed by standard permutation group methods. 
          // the representatives were computed by brute force 
          // total CPU time on a Pentium III mobile 1.6 GHz: 0.000 sec
          {@
               <1, 1, []>,
               <2, 3, [1]>,
               <2, 3, [2]>,
               <6, 2, [1,2]>,
               <3, 2, [1,2,1,2]>,
               <2, 1, [1,2,1,2,1,2]>
          @}, [[]:i in [1..6]];

     when "F": return
          // the conjugacy classes were computed by standard permutation group methods. 
          // the representatives were computed by brute force 
          // total CPU time on a Pentium III mobile 1.6 GHz: 0.420 sec
          {@
               <1,  1,  []>,
               <2,  12, [1]>,
               <2,  12, [3]>,
               <3,  32, [1,2]>,
               <2,  72, [1,3]>,
               <4,  36, [2,3]>,
               <3,  32, [3,4]>,
               <6,  96, [1,2,3]>,
               <6,  96, [1,2,4]>,
               <6,  96, [1,3,4]>,
               <6,  96, [2,3,4]>,
               <12, 96, [1,2,3,4]>,
               <2,  18, [2,3,2,3]>,
               <4,  72, [1,2,3,2,3]>,
               <4,  72, [2,3,2,3,4]>,
               <8,  144,[1,2,3,2,3,4]>,
               <6,  16, [1,2,1,3,2,3,4,3]>,
               <2,  12, [1,2,1,3,2,1,3,2,3]>,
               <2,  12, [2,3,2,3,4,3,2,3,4]>,
               <6,  32, [1,2,1,3,2,1,3,2,3,4]>,
               <6,  32, [1,2,3,2,3,4,3,2,3,4]>,
               <4,  12, [1,2,1,3,2,1,3,4,3,2,3,4]>,
               <4,  36, [1,2,1,3,2,1,3,2,3,4,3,2,3,4]>,
               <3,  16, [1,2,1,3,2,1,3,4,3,2,1,3,2,3,4,3]>,
               <2,  1,  [1,2,1,3,2,1,3,2,3,4,3,2,1,3,2,3,4,3,2,1,3,2,3,4]>
          @}, [[]:i in [1..26]];
     when "E": 
     case l :
     when 6: return
          // the conjugacy classes were computed by standard permutation group methods. 
          // the representatives were computed by brute force 
          // total CPU time on a Pentium III mobile 1.6 GHz: 9.800 sec
          {@
               <1,  1,    []>,
               <2,  36,   [1]>,
               <2,  270,  [1,2]>,
               <3,  240,  [1,3]>,
               <6,  1440, [1,2,3]>,
               <2,  540,  [1,2,5]>,
               <4,  1620, [1,3,4]>,
               <5,  5184, [1,2,3,4]>,
               <6,  2160, [1,2,3,5]>,
               <4,  3240, [1,2,4,5]>,
               <3,  480,  [1,3,5,6]>,
               <6,  1440, [2,3,4,5]>,
               <8,  6480, [1,2,3,4,5]>,
               <10, 5184, [1,2,3,4,6]>,
               <6,  1440, [1,2,3,5,6]>,
               <6,  4320, [1,3,4,5,6]>,
               <12, 4320, [1,2,3,4,5,6]>,
               <4,  540,  [2,3,4,2,5,4]>,
               <12, 4320, [1,2,3,4,2,5,4]>,
               <9,  5760, [1,2,3,4,2,5,4,6]>,
               <6,  720,  [1,2,3,1,4,2,3,4,5,4,6,5]>,
               <2,  45,   [2,3,4,2,3,4,5,4,2,3,4,5]>,
               <4,  540,  [1,2,3,4,2,3,4,5,4,2,3,4,5]>,
               <6,  1440, [1,2,3,4,2,3,4,5,4,2,3,4,5,6]>,
               <3,  80,   [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6]>
          @}, [[]:i in [1..25]];
     when 7: return
          // the conjugacy classes were computed by standard permutation group methods. 
          // the representatives were computed by brute force 
          // total CPU time on a Pentium III mobile 1.6 GHz: ~10 min
          {@
               <1,  1,      []>,
               <2,  63,     [1]>,
               <2,  945,    [1,2]>,
               <3,  672,    [1,3]>,
               <6,  10080,  [1,2,3]>,
               <2,  3780,   [1,2,5]>,
               <4,  7560,   [1,3,4]>,
               <2,  315,    [2,5,7]>,
               <5,  48384,  [1,2,3,4]>,
               <6,  30240,  [1,2,3,5]>,
               <4,  45360,  [1,2,4,5]>,
               <2,  3780,   [1,2,5,7]>,
               <3,  13440,  [1,3,5,6]>,
               <6,  10080,  [2,3,4,5]>,
               <4,  7560,   [2,4,5,7]>,
               <8,  90720,  [1,2,3,4,5]>,
               <10, 145152, [1,2,3,4,6]>,
               <6,  40320,  [1,2,3,5,6]>,
               <6,  10080,  [1,2,3,5,7]>,
               <4,  45360,  [1,2,4,5,7]>,
               <6,  120960, [1,3,4,5,6]>,
               <12, 60480,  [1,3,4,6,7]>,
               <6,  30240,  [2,3,4,5,7]>,
               <6,  40320,  [2,4,5,6,7]>,
               <12, 120960, [1,2,3,4,5,6]>,
               <8,  90720,  [1,2,3,4,5,7]>,
               <15, 96768,  [1,2,3,4,6,7]>,
               <12, 60480,  [1,2,3,5,6,7]>,
               <6,  120960, [1,2,4,5,6,7]>,
               <7,  207360, [1,3,4,5,6,7]>,
               <4,  3780,   [2,3,4,2,5,4]>,
               <10, 145152, [2,3,4,5,6,7]>,
               <12, 60480,  [1,2,3,4,2,5,4]>,
               <18, 161280, [1,2,3,4,5,6,7]>,
               <4,  11340,  [2,3,4,2,5,4,7]>,
               <9,  161280, [1,2,3,4,2,5,4,6]>,
               <12, 60480,  [1,2,3,4,2,5,4,7]>,
               <8,  90720,  [2,3,4,2,5,4,6,7]>,
               <14, 207360, [1,2,3,4,2,5,4,6,7]>,
               <6,  40320,  [2,3,4,2,5,4,6,5,4,7]>,
               <12, 120960, [1,2,3,4,2,5,4,6,5,4,7]>,
               <6,  20160,  [1,2,3,1,4,2,3,4,5,4,6,5]>,
               <2,  315,    [2,3,4,2,3,4,5,4,2,3,4,5]>,
               <30, 96768,  [1,2,3,1,4,2,3,4,5,4,6,5,7]>,
               <4,  7560,   [1,2,3,4,2,3,4,5,4,2,3,4,5]>,
               <2,  945,    [2,3,4,2,3,4,5,4,2,3,4,5,7]>,
               <6,  40320,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6]>,
               <4,  7560,   [1,2,3,4,2,3,4,5,4,2,3,4,5,7]>,
               <6,  10080,  [2,3,4,2,3,4,5,4,2,3,4,5,6,7]>,
               <10, 48384,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,7]>,
               <4,  11340,  [2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6]>,
               <8,  90720,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6]>,
               <6,  2240,   [1,2,3,1,4,2,3,1,4,3,5,4,2,3,4,6,5,4,7,6,5]>,
               <6,  13440,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,6,5,7,6]>,
               <3,  2240,   [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6]>,
               <6,  20160,  [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7]>,
               <2,  63,     [2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,
                             4,5,6,7]>,
               <6,  672,    [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,
                             3,4,5,6,7]>,
               <4,  3780,   [1,2,3,1,4,2,3,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,5,
                             4,2,3,4,5,6,7]>,
               <2,  1,      [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,
                             4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
                             1,7,6,5,4,2,3,4,5,6,7]>
          @}, [[]:i in [1..60]];
     when 8: return
          // the conjugacy classes were computed by standard permutation group methods. 
          // the representatives were computed
          //    - cuspidal classes: using Algorithms G and H from Geck+Pfeiffer (2000) 
          //    - other    classes: using the above and some brute force to get lex. smallest words.
          // total CPU time on a Pentium III mobile 1.6 GHz: ~25 min
          {@
               <1,  1,        []>,
               <2,  120,      [1]>,
               <2,  3780,     [1,2]>,
               <3,  2240,     [1,3]>,
               <6,  80640,    [1,2,3]>,
               <2,  37800,    [1,2,5]>,
               <4,  45360,    [1,3,4]>,
               <5,  580608,   [1,2,3,4]>,
               <6,  604800,   [1,2,3,5]>,
               <4,  907200,   [1,2,4,5]>,
               <2,  113400,   [1,2,5,7]>,
               <3,  268800,   [1,3,5,6]>,
               <6,  100800,   [2,3,4,5]>,
               <8,  1814400,  [1,2,3,4,5]>,
               <10, 5806080,  [1,2,3,4,6]>,
               <6,  1612800,  [1,2,3,5,6]>,
               <6,  1209600,  [1,2,3,5,7]>,
               <4,  2721600,  [1,2,4,5,7]>,
               <6,  4838400,  [1,3,4,5,6]>,
               <12, 3628800,  [1,3,4,6,7]>,
               <6,  1209600,  [2,3,4,5,7]>,
               <12, 4838400,  [1,2,3,4,5,6]>,
               <8,  10886400, [1,2,3,4,5,7]>,
               <15, 11612160, [1,2,3,4,6,7]>,
               <10, 8709120,  [1,2,3,4,6,8]>,
               <12, 7257600,  [1,2,3,5,6,7]>,
               <6,  2419200,  [1,2,3,5,6,8]>,
               <6,  14515200, [1,2,4,5,6,7]>,
               <7,  24883200, [1,3,4,5,6,7]>,
               <4,  5443200,  [1,3,4,6,7,8]>,
               <4,  37800,    [2,3,4,2,5,4]>,
               <10, 8709120,  [2,3,4,5,6,7]>,
               <12, 1209600,  [1,2,3,4,2,5,4]>,
               <18, 19353600, [1,2,3,4,5,6,7]>,
               <12, 14515200, [1,2,3,4,5,6,8]>,
               <24, 14515200, [1,2,3,4,5,7,8]>,
               <20, 17418240, [1,2,3,4,6,7,8]>,
               <30, 11612160, [1,2,3,5,6,7,8]>,
               <14, 24883200, [1,2,4,5,6,7,8]>,
               <8,  43545600, [1,3,4,5,6,7,8]>,
               <4,  453600,   [2,3,4,2,5,4,7]>,
               <12, 29030400, [2,3,4,5,6,7,8]>,
               <9,  6451200,  [1,2,3,4,2,5,4,6]>,
               <12, 7257600,  [1,2,3,4,2,5,4,7]>,
               <30, 23224320, [1,2,3,4,5,6,7,8]>,
               <8,  5443200,  [2,3,4,2,5,4,6,7]>,
               <14, 24883200, [1,2,3,4,2,5,4,6,7]>,
               <18, 19353600, [1,2,3,4,2,5,4,6,8]>,
               <12, 9676800,  [1,2,3,4,2,5,4,7,8]>,
               <20, 17418240, [2,3,4,2,5,4,6,7,8]>,
               <6,  3225600,  [1,2,3,4,2,5,4,2,7,8]>,
               <24, 29030400, [1,2,3,4,2,5,4,6,7,8]>,
               <6,  2419200,  [2,3,4,2,5,4,6,5,4,7]>,
               <12, 14515200, [1,2,3,4,2,5,4,6,5,4,7]>,
               <24, 14515200, [2,3,4,2,5,4,6,5,4,7,8]>,
               <6,  806400,   [1,2,3,1,4,2,3,4,5,4,6,5]>,
               <12, 1209600,  [1,2,3,1,4,2,3,4,5,4,7,8]>,
               <20, 34836480, [1,2,3,4,2,5,4,6,5,4,7,8]>,
               <2,  3150,     [2,3,4,2,3,4,5,4,2,3,4,5]>,
               <30, 11612160, [1,2,3,1,4,2,3,4,5,4,6,5,7]>,
               <6,  2419200,  [1,2,3,1,4,2,3,4,5,4,6,5,8]>,
               <4,  151200,   [1,2,3,4,2,3,4,5,4,2,3,4,5]>,
               <2,  37800,    [2,3,4,2,3,4,5,4,2,3,4,5,7]>,
               <18, 12902400, [1,2,3,1,4,2,3,4,5,4,6,5,7,8]>,
               <6,  1612800,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6]>,
               <4,  907200,   [1,2,3,4,2,3,4,5,4,2,3,4,5,7]>,
               <6,  604800,   [2,3,4,2,3,4,5,4,2,3,4,5,6,7]>,
               <10, 5806080,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,7]>,
               <6,  4838400,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,8]>,
               <12, 1209600,  [1,2,3,4,2,3,4,5,4,2,3,4,5,7,8]>,
               <8,  1814400,  [2,3,4,2,3,4,5,4,2,3,4,5,6,7,8]>,
               <15, 23224320, [1,2,3,1,4,2,3,4,5,4,6,5,7,6,5,8]>,
               <18, 6451200,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,7,8]>,
               <4,  680400,   [2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6]>,
               <8,  10886400, [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6]>,
               <12, 3628800,  [2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6,8]>,
               <14, 24883200, [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,7,6,8]>,
               <12, 2419200,  [1,2,3,1,4,2,3,4,5,4,2,3,6,5,4,7,6,5,4,8]>,
               <6,  268800,   [1,2,3,1,4,2,3,1,4,3,5,4,2,3,4,6,5,4,7,6,5]>,
               <4,  907200,   [2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,7,6,5,8,7,6]>,
               <6,  100800,   [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,7,8]>,
               <12, 2419200,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,4,6,5,4,7,6,5,8]>,
               <12, 9676800,  [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,7,6,5,8,7,6]>,
               <6,  1612800,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,6,5,7,6]>,
               <12, 4838400,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,6,5,7,6,8]>,
               <3,  89600,    [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6]>,
               <10, 1161216,  [1,2,3,1,4,2,3,1,4,5,4,2,3,4,5,6,5,4,7,6,5,8,7,6]>,
               <6,  2419200,  [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7]>,
               <6,  268800,   [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,8]>,
               <30, 11612160, [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,3,5,6,5,4,7,6,5,8,7,6]>,
               <12, 2419200,  [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,8]>,
               <9,  12902400, [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,8,7]>,
               <8,  3628800,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,6,5,4,2,3,4,7,6,5,4,8,7,6,5]>,
               <2,  3780,     [2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7]>,
               <6,  80640,    [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7]>,
               <4,  45360,    [2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7,8]>,
               <10, 580608,   [1,2,3,4,2,3,4,5,4,2,3,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7,8]>,
               <4,  453600,   [1,2,3,1,4,2,3,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7]>,
               <8,  5443200,  [1,2,3,1,4,2,3,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7,8]>,
               <6,  4480,     [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,5,6,5,4,2,3,1,4,5,6,7,6,5,4,2,3,4,5,6,
                               7,8,7,6,5]>,
               <6,  89600,    [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,5,6,7,6,5,4,2,3,
                               4,5,6,7,8,7,6]>,
               <6,  403200,   [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,6,5,4,2,3,4,5,6,7,6,5,4,3,1,8,7,
                               6,5,4,2,3,4,5,6,7]>,
               <6,  268800,   [1,2,3,1,4,2,3,1,4,3,5,4,2,3,4,5,6,5,4,2,3,1,4,5,6,7,6,5,4,2,3,1,4,3,5,
                               4,6,5,7,6,8,7,6,5]>,
               <12, 1209600,  [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,5,6,5,4,2,3,1,4,3,5,6,7,6,5,4,2,3,1,4,
                               3,5,4,6,5,7,6,8,7,6,5]>,
               <6,  806400,   [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,4,5,6,7,6,5,4,2,3,4,5,6,7,8,
                               7,6,5,4,2,3,4,5,6,7,8]>,
               <5,  1161216,  [1,2,3,1,4,2,3,1,4,5,4,2,3,1,4,5,6,5,4,2,3,1,4,5,6,7,6,5,4,2,3,1,4,5,6,
                               7,8,7,6,5,4,2,3,4,5,6,7,8]>,
               <4,  15120,    [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,4,5,7,6,5,4,2,3,1,4,
                               3,5,4,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,7,6,5,8,7,6]>,
               <2,  120,      [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
                               1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7]>,
               <6,  2240,     [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
                               1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8]>,
               <4,  37800,    [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
                               1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,8,7,6,5,4,2,3,4,5,6,7,8]>,
               <3,  4480,     [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,6,5,4,2,3,1,4,3,5,4,2,6,7,6,5,4,2,
                               3,1,4,3,5,4,2,6,5,4,3,1,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,
                               2,3,4,5,6,7,8,7,6,5]>,
               <2,  1,        [1,2,3,1,4,2,3,1,4,3,5,4,2,3,1,4,3,5,4,2,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,
                               1,7,6,5,4,2,3,1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,
                               1,4,3,5,4,2,6,5,4,3,1,7,6,5,4,2,3,4,5,6,7,8,7,6,5,4,2,3,1,4,3,5,4,2,6,
                               5,4,3,1,7,6,5,4,2,3,4,5,6,7,8]>
          @}, [[]:i in [1..112]];


     end case;

     else return false, [];
     end case;

end function;

// The intrinsics

classWords := function( type )
  pretype := car< Integers(), Integers(), PowerSequence(Integers()) >;
  C := [ pretype | < 1, 1, [Integers()|] > ];
  P := [ <> ];
  for t in type do
    case t[1] :
    when "A": reps, params := coxeterClassRepsA  ( #t[2] );
    when "B": reps, params := coxeterClassRepsBC ( #t[2] );
    when "C": reps, params := coxeterClassRepsBC ( #t[2] );
    when "D": reps, params := coxeterClassRepsD  ( #t[2] );
    else      reps, params := coxeterClassRepsExc( t[1], #t[2] );
    end case;
    if Category(reps) eq BoolElt then
	return reps, params;
    end if;
    if t[2] ne [1..#t[2]] then
      reps := {@ pretype | < r[1], r[2], [ t[2][i] : i in r[3] ] > : 
        r in reps @};
    end if;
    C := {@ pretype |
      < Lcm(c[1],r[1]), c[2]*r[2], c[3] cat r[3] > : c in C, r in reps @};
    P := [ Append( p, r ) : p in P, r in params ]; 
  end for;
  return C, P;
end function;

order := function( x, y )
  if x[1] eq y[1] then
    return x[2] lt y[2] select -1 else x[2] gt y[2] select 1 else 0;
  else
    return x[1] lt y[1] select -1 else 1;
  end if;
end function;

intrinsic ConjugacyClasses( W::GrpFPCox ) -> SeqEnum
{The conjugacy classes of W}
  require IsFinite( W ) : "The Coxeter group must be finite";

  if not assigned W`Classes then
    C, P := classWords( groupToType( W ) );
    Sort( ~C, order, ~p );
    P := [ P[i^p] : i in [1..#P] ];
    ChangeUniverse( ~C, car< Integers(), Integers(), W > );
    W`Classes := SequenceToConjugacyClasses( Setseq(C) );
    W`ClassParameters := P;
  end if;

  return W`Classes, W`ClassParameters;
end intrinsic;    

intrinsic ConjugacyClasses( W::GrpPermCox ) -> SeqEnum
{The Conjugacy classes of W}
  if not assigned W`Classes then
    C, P := classWords( groupToType( W ) );
    if Category(C) eq BoolElt then
      G := CoxeterGroup( GrpPerm, W );
      C := ConjugacyClasses( G );
      W`Classes := [ <c[1],c[2],W!c[3]> : c in C ];
      W`ClassParameters := [];
    else
      C := {@ car< Integers(), Integers(), W > | 
        < c[1], c[2], &*[ W | W.i : i in c[3] ] > : c in C @};
    
      // CHANGE AFTER BUG FIX
      W`Classes := [ <c[3],c[2]> : c in C ];
      W`ClassParameters := [ P[Position(C,W`Classes[i])] : i in [1..#C] ];
    end if;
  end if;
  
  return W`Classes, W`ClassParameters;
end intrinsic;
    

