freeze;

/////////////////////////////////////////////////////
//                                                 //
//  special case for Farey Symbol for PSL_2(Z)     //
//  and for Gamma_0(N)                             //
//                                                 //
/////////////////////////////////////////////////////

import "farey_symbol.m": init_farey_seq,
                         UpdateAttributes;

import "farey_gamma1.m": transformSequence,
                         transformLabels;

			 
import "../GrpPSL2/coercion.m": init_psl2_elt_from_integer_matrix;
			    
			 
function FareySequenceForPSL(PSL)
    farey_seq := [Cusps()|Infinity(),0,Infinity()];
    farey_labels := [-2,-3];
    S := PSL![0,-1,1,0];
    R := PSL![0,1,-1,1];
    gens := [S,R];
    other := [];
    FS := init_farey_seq(farey_seq,farey_labels,gens);
    FS`group := PSL;
    FS`cosets := [PSL!1];
    UpdateAttributes(PSL,FS);
    return FS;
end function;

forward LiftToCosetRep;
forward MakeEndsAndLabels;
forward reNumber;
forward MakeOtherEdges;

function mv(M,x)
    // assume x is an integer or rational
    // M in PSL_2(Z) or GL_2(Z)
    // assume nothing is mapping to infinity
    // which is true in application below,
    // as we don't apply the function to the
    // first matrices added to the coset list.
    return (M[1,1]*x[1]+M[1,2]*x[2])/(M[2,1]*x[1]+M[2,2]*x[2]);
end function;

// the following constructs the next farey sequence from a given one:

function NextFareyFrac(f)
   if #f eq 0 then return [Rationals()|0,1];
   else
      Fold := f;
      FoldDs := [Denominator(a) : a in Fold];
      FoldNs := [Numerator(a) : a in Fold];
      newF := [Rationals()!0];
      for i := 2 to #FoldDs do
	 Append(~newF,(FoldNs[i]+FoldNs[i-1])/(FoldDs[i]+FoldDs[i-1]));
	 Append(~newF,FoldNs[i]/FoldDs[i]);
      end for;
      return newF;
   end if;
end function;


// the following finds a nice set of cosets for
// gamma0(N), such that they are related to a
// Farey sequence.
// also returns the "ends" ie, images of
// 0,1,oo under the coset representatives.

function findNiceCosetsForGamma0N(N,P1Elts)
   // define P1 - the elements, and the set.
   P1Set := Parent(P1Elts[1]);
   G := GL(2,Integers());   
   R := G![0,1,-1,1];
   R2 := G![-1,1,-1,0];
   // we're going to have cosets corresponding to each element in P1Elts;
   // we add them to our list in a certain order, and the to_do_list
   // keeps track of what's left to add.
   to_do_list := [i : i in [1..#P1Elts]];

   // start with the basic 3 cosets
   cosets := [G!1,R,R2];
   ends := [Rationals()|0,1];   
   m1 := P1Reduce(P1Set![0,1],P1Elts);
   m2 := P1Reduce(P1Set![-1,1],P1Elts);
   m3 := P1Reduce(P1Set![-1,0],P1Elts);
   Exclude(~to_do_list,m1);
   Exclude(~to_do_list,m2);
   Exclude(~to_do_list,m3);

   // we can just add things from nth Farey sequence for a while:
   Fareyseq := NextFareyFrac([]);   
   while #to_do_list gt 0 do
//      printf "FareySeq = %o\n",Fareyseq;
      for i := 1 to #Fareyseq -1 do
	 a := Numerator(Fareyseq[i+1]);
	 b := Numerator(Fareyseq[i]);
	 c := Denominator(Fareyseq[i+1]);
	 d := Denominator(Fareyseq[i]);
	 M1 := G![a,b,c,d];
//	 printf "m = \n %o, %o\n", M1, Determinant(M1);
	 m1 := P1Reduce(P1Set![c,d],P1Elts);
	 doTolen := #to_do_list;
	 Exclude(~to_do_list,m1);
	 if doTolen ne #to_do_list then
	    Append(~cosets,M1);
	    MR := M1*R;
	    m2 := P1Reduce(P1Set![MR[2,1],MR[2,2]],P1Elts);
	    if m2 ne m1 then 
	       MR2 := M1*R2;
	       m3 := P1Reduce(P1Set![MR2[2,1],MR2[2,2]],P1Elts);
	       Append(~ends,(a+b)/(c+d));
//	       printf "ends = %o\n", ends;
	       Append(~cosets,MR);
	       Append(~cosets,MR2);	
	       Exclude(~to_do_list,m2);
	       Exclude(~to_do_list,m3);
	    end if;
	 end if;
      end for;
      Fareyseq := NextFareyFrac(Fareyseq);
   end while;
	    
   // currently the following is not used; we could debate
   // about whether it's faster at some point to switch to
   // the following method, eg, when the coset list is 90% completed,
   // and possibly use the following at some stage.
   
   while #to_do_list gt 0 do	
      m1 := to_do_list[1];
      M1 := G!LiftToCosetRep(P1Elts[m1],N);
      MR := M1*R;
      m2 := P1Reduce(P1Set![MR[2,1],MR[2,2]],P1Elts);
      if m2 eq m1 then 
	 // elliptic point order 3 case:
	 Append(~cosets,M1);
	 Exclude(~to_do_list,m1);
      else	 
	 MR2 := M1*R2;
	 m3 := P1Reduce(P1Set![MR2[2,1],MR2[2,2]],P1Elts);
	 Append(~ends,Sort([mv(M1,[1,1]),mv(M1,[1,0]),mv(M1,[0,1])])[2]);
	 Append(~cosets,M1);
	 Append(~cosets,MR);
	 Append(~cosets,MR2);	
	 Exclude(~to_do_list,m1);
	 Exclude(~to_do_list,m2);
	 Exclude(~to_do_list,m3);
      end if;
   end while;
   Ends := Sort([x : x in Set(ends)]);
   return cosets, Ends;
end function;


function FareySequenceForGamma0N(group)   
   N := Level(group);
   if N eq 1 then return FareySequenceForPSL(group);
   end if;

   P1 := P1Classes(N);
   cosets, Ends := findNiceCosetsForGamma0N(N,P1);   

   Ends, Labels, generators := MakeEndsAndLabels(Ends,N,P1);

   Labels := reNumber(Labels);
   
   farey_seq :=
   [Cusps()![1,0]] cat [Cusps()| x : x in Ends] cat [Cusps()![1,0]];
   fareylabels := [1] cat  Labels  cat [1];

   FS := init_farey_seq(farey_seq,fareylabels,generators);
   FS`group := group;
   PSL := PSL2(Integers());

   FS`cosets := cosets;

   UpdateAttributes(group,FS);
   return FS;
end function;



function MakeOtherEdges(Ends,Labels);
   // Ends is assumed already sorted, does not include infinity, is
   // a sequence of rationals.
   otheredges := [];
   for i in [1..(#Ends-1)] do
      if Labels[i] eq -3 then
	 Append (~otheredges,[Cusps()|Ends[i],Ends[i+1]]);
      end if;
      for j := i + 2 to #Ends do
	 if Numerator(Ends[j] - Ends[i]) eq 1
	    and Gcd(Denominator(Ends[j]),Denominator(Ends[i])) eq 1 then
	    Append(~otheredges,[Cusps()|Ends[i],Ends[j]]);
	 end if;
      end for;
   end for;
   return otheredges;
end function;


function MakeEndsAndLabels(Ends,N,P1)
   // note that in this function, Ends is a sequence of FldRatElt's
   // representing a Farey sequence; this is assumed to be the
   // input.  The Farey symbol starts at 0/1, ends at 1/1;
   // the infinities are added on to the ends later,
   // so are assumed not to occur in the list "Ends".
   M2 := MatrixAlgebra(Integers(),2);
   if N eq 2 then return [Rationals()|0,1],[-2],
      [M2![1,1,0,1],M2![1,-1,2,-1]];
   end if;
   
   S := M2![0,-1,1,0];
   R := M2![0,1,-1,1];
   Mmod := MatrixAlgebra(Integers(N),2);
   Smod := Mmod![0,-1,1,0];
   
   // find the matrix corresponding to each edge:
   matrices := [];
   for i := 1 to #Ends-1 do
      Append(~matrices,
      M2![Numerator(Ends[i+1]),Numerator(Ends[i]),
          Denominator(Ends[i+1]),Denominator(Ends[i])]);      
   end for;
   // find what matrices look like mod N;
   // create labels corresponding to P1Classes:
   list := [P1[1]*Mmod!x : x in matrices];
   LabelsA := [P1Reduce(listElt,P1) : listElt in list];
   LabelsAS := [P1Reduce(listElt*Smod,P1) : listElt in list];
   // to keep track of generators added, since each one would
   // be found twice, but we only want to count it once.
   LabelsB := LabelsA;
   gens := [M2![1,1,0,1]];
   
   for i := 1 to #LabelsA do
      if LabelsA[i] notin LabelsAS then
	 LabelsA[i] := -3;
	 Append(~gens,matrices[i]*R*matrices[i]^(-1));
      elif LabelsA[i] eq LabelsAS[i] then
	 LabelsA[i] := -2;
	 Append(~gens,matrices[i]*S*matrices[i]^(-1));
      else
	 if LabelsB[i] ne 0 then
	    lab := LabelsA[i];
	    LabelsB[i] := 0;
	    j := Index(LabelsB,LabelsAS[i]);
	    LabelsB[j] := 0;
	    Append(~gens,matrices[i]*S*matrices[j]^(-1));
	 end if;
	 LabelsA[i] := Min(LabelsA[i],LabelsAS[i]);
      end if;
   end for;
   return Ends,LabelsA,gens; 
end function;

function reNumber(L)
   nums := Sort([x : x in Set([ i : i in L | i gt 0])]);
   f := func <i | i lt 0 select i else Index(nums,i)+1>;
   L2 := [f(l) :  l in L];
   return L2;   
end function;

/*

function FindGenerators(Ends,Labels,group)
//     printf "lables = %o\n", Labels;
   M2 := MatrixAlgebra(Integers(),2);
   S := M2![0,-1,1,0];
   R := M2![0,1,-1,1];
   matrices := [];
//   printf "ends= %o ",   Ends;
   for i := 1 to #Ends-1 do
      Append(~matrices,
      M2![Numerator(Ends[i+1]),Numerator(Ends[i]),
      Denominator(Ends[i+1]),Denominator(Ends[i])]);      
      if Determinant(matrices[i]) ne 1 then printf
	 "WARNING something's wrong in FindGenerators!\n %o\n",matrices[i];
	 end if;
   end for;
   // note that the oo ends are assumed not to be included,
   // so assuming that this is a symbol for Gamma0N, add
   // translation, [1,1,0,1].
   gens := [M2![1,1,0,1]];
   i := 1;
//   print Sort(Labels);
   for i := 1 to #Labels do
      if Labels[i] eq -2 then
	 Append(~gens,matrices[i]*S*matrices[i]^(-1));
      elif Labels[i] eq -3 then
	 Append(~gens,matrices[i]*R*matrices[i]^(-1));
      elif Labels[i] gt 0 then
	 lab := Labels[i];
	 Labels[i] := 0;
	 j := Index(Labels,lab);
	 Labels[j] := 0;
	 Append(~gens,matrices[i]*S*matrices[j]^(-1));
      end if;
   end for;
//   print gens;
  return gens;
// return [group!g : g in gens];
end function;


*/

//////////////////////////////////
//
//   LiftToCosetRep function, borrowed
//   from William Stein's core.m package,
//   with some modifications in order to try and
//   get largest possible c and d in returned matrix.
//
//
///////////////////////////////////

forward frac;
forward thelift;

function frac_val(a,MAX)
//printf "a := %o \n",a;
   if Gcd(a[1],a[2]) ne 1 then 
      return MAX;
   else
      return &+ContinuedFraction(frac(a));
   end if;
end function;

// returns the minimal farey level of a[c,d],a[c-N,d],a[c,d-N]

function MinFareyLevel(z,N)
   // WARNING - need to find an upper bound on the farey level for
   // Gamma0(N) and use that instead of 100000.
   MAX := 100000;
    c := Integers()!(z[1]);
    d := Integers()!z[2];
    e := c+d;
    // There are 3 possible denominators of Farey pairs
    // coming from a lift of c,d.  For each, the Farey Level
    // is computed.
    versions := [[c,d,e],[c-N,d,e-N],[c,d-N,e-N]];
    //    a first approximation to the Farey level would be
    //  Max([Abs(v) : v in ver])
    // however, the precice value is given in terms of
    // continued fractions.
    // for fractions [a/c, (a+b)/(c+d), b/d] we will take the
    // level to be given by the pair (c/d); c,d are the smallest
    values := [frac_val(Sort([Abs(v) : v in ver]),MAX)
    : ver in versions];
    a,b := Min(values);
    return [a,versions[b][1],versions[b][2]];
end function;

function frac(a)
   return a[1]/a[2];
end function;

// this choses from 3 possible end points
function cd_choice(z,N,m)
   c := Integers()!(z[1]);
   d := Integers()!z[2];
   e := c+d;
   if m eq 1 then
      return [c,d];
   elif m eq 2 then       
      return [c-N,d];
   else
      return [c,d-N];
   end if;
end function;



function LiftToCosetRep(x, N) 

    Nmod := Integers(N);

    // find (Z/NZ)*
    Nstar := [1..(N-1)];
    if not IsPrime(N) then
       Nstar := [ i : i in Nstar | Gcd(i,N) eq 1];
    end if;

    // list all possible pairs (c,d) in the list Pos_cd:
    Pos_cd := [Nmod!i*x : i in Nstar];
    
    // choose c,d mod N to minimize farey level.
    // Elements of Min_cd consist of triples, [level,c',d']
    // where level is the minimal level, and [c',d']
    // the lifts of [c,d] to achieve this.
    Min_cd := [MinFareyLevel(z,N) : z in Pos_cd];

    u,v := Min([x[1] : x in Min_cd]);
    mins := [x : x in Min_cd | x[1] eq u];

    // if there are several minimal values, choose the
    // one that will give rise to a triangle appearing furthest left.
    if #mins gt 1 then
       G := GL(2,Integers());   
       mats := [G!thelift(m[2],m[3],N) : m in mins];
       fracs := [Min([mv(m,[0,1]),mv(m,[0,1]),mv(m,[0,1])]) : m in mats];
       u1,v1 := Min(fracs);
       return mats[v1];
    else
       c := Min_cd[v][2];
       d := Min_cd[v][3];
       return thelift(c,d,N);       
    end if;

end function;



function thelift(c,d,N)
    g, z1, z2 := Xgcd(c,d);
    // We're lucky: z1*c + z2*d = 1.
    if g eq 1 then
       if z2*c lt 0 or -z1*d lt 0 then
	   return [c+z2, d-z1, c, d];
	else
	   return [z2, -z1, c, d];
       end if;
   end if; 
	
    // Have to try harder.
    if c eq 0 then
	c +:= N;
    end if;
    if d eq 0 then
	d +:= N;
    end if;
    m := c;
    
    // compute prime-to-d part of m.
    repeat
	g := Gcd(m,d);
	if g eq 1 then 
	    break;
	end if;
	m div:= g;
    until false;
    // compute prime-to-N part of m.
    repeat
	g := Gcd(m,N);
	if g eq 1 then 
	    break;
	end if;
	m div:= g;
    until false;
    
    d +:= N*m;
    g, z1, z2 := Xgcd(c,d);
    if g eq 1 then
	if z2*c lt 0 or -z1*d lt 0 then
	    return [c+z2, d-z1, c, d];
	else
	    return [z2, -z1, c, d];
	end if;
    else
	error "LiftToCosetRep: ERROR!!!";
    end if; 
end function;

function Sconjugate(g)
   // returns the conjugate of g by S=[0,-1,1,0], up to sign.
   a,b,c,d := Explode(Eltseq(g));
   return Parent(g)![-d,c,b,-a];   
end function;


function FareySequenceForGammaUpper0N(group)
   N := Level(group);
   if N eq 1 then return FareySequenceForPSL(group);
   end if;
   PSL := PSL2(Integers());
   S := PSL![0,-1,1,0];

   P1 := P1Classes(N);
   Pcosets, PEnds := findNiceCosetsForGamma0N(N,P1);   
   PEnds, PLabels, Pgenerators := MakeEndsAndLabels(PEnds,N,P1);
   PLabels := reNumber(PLabels);

   generators := [Sconjugate(g) : g in Pgenerators];
   
   farey_seq := transformSequence(   
   [Cusps()![1,0]] cat [Cusps()| x : x in PEnds] cat [Cusps()![1,0]]);
   fareylabels := transformLabels([1] cat  PLabels cat [1]);
   
   Ends := [frac(Eltseq(a)) : a in farey_seq | a ne Cusps()![1,0]];
   Labels := [fareylabels[i] : i in [2..#fareylabels-1]];

   FS := init_farey_seq(farey_seq,fareylabels,generators);
   FS`group := group;

   G := GL(2,Integers());   
   M := G![0,-1,1,-1];
   FS`cosets := [M*c : c in Pcosets];
   UpdateAttributes(group,FS);
   return FS;
end function;



