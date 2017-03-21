freeze;

////////////////////////////////////////////////////////////////
//                                                            //
//  Special case of Farey sequence for Gamma1(N)              //
//                                                            //
////////////////////////////////////////////////////////////////

import "farey_symbol.m": init_farey_seq,
                         UpdateAttributes;

import "farey_gamma0.m": reNumber,
			 NextFareyFrac,
			 mv,
			 frac_val,
			 thelift,
			 FareySequenceForPSL;

			 
// the main difference between this function and the function for
// getting farey sequences for Gamma0(N) is that we have
// G1Classes, G1Set and G1Elts instead of P1Classes etc.
// There is also a corresponding G1Reduce function

forward G1Classes;
forward G1Reduce;
forward GGReduce;
forward MakeEndsAndLabelsG1;
forward LiftToCosetRepG1;

function findNiceCosetsForGamma1N(N,M,G1Elts,MmodN)
   // define G1 - the elements, and the set.
   G1Set := Parent(G1Elts[1]);

   G := GL(2,Integers());   
   R := G![0,1,-1,1];
   R2 := G![-1,1,-1,0];
   // we're going to have cosets corresponding to each element in G1Elts;
   // we add them to our list in a certain order, and the to_do_list
   // keeps track of what's left to add.
   to_do_list := [i : i in [1..#G1Elts]];
   index := #to_do_list;
   
   // start with the basic 3 cosets
   cosets := [G!1,R,R2];
   ends := [Rationals()|0,1];   
   m1 := G1Reduce(G1Set![0,1],G1Elts,MmodN);
   m2 := G1Reduce(G1Set![-1,1],G1Elts,MmodN);
   m3 := G1Reduce(G1Set![-1,0],G1Elts,MmodN);
   Exclude(~to_do_list,m1);
   Exclude(~to_do_list,m2);
   Exclude(~to_do_list,m3);

   // we can just add things from nth Farey sequence for a while:
   Fareyseq := NextFareyFrac([]);   
   while #to_do_list gt 0 do
      for i := 1 to #Fareyseq -1 do
	 a := Numerator(Fareyseq[i+1]);
	 b := Numerator(Fareyseq[i]);
	 c := Denominator(Fareyseq[i+1]);
	 d := Denominator(Fareyseq[i]);
	 M1 := G![a,b,c,d];
	 m1 := G1Reduce(G1Set![c,d],G1Elts,MmodN);
	 doTolen := #to_do_list;
	 Exclude(~to_do_list,m1);
	 if doTolen ne #to_do_list then
	    Append(~cosets,M1);
	    MR := M1*R;
	    m2 := G1Reduce(G1Set![MR[2,1],MR[2,2]],G1Elts,MmodN);
	    if m2 ne m1 then 
	       MR2 := M1*R2;	       
	       m3 := G1Reduce(G1Set![MR2[2,1],MR2[2,2]],G1Elts,MmodN);
	       Append(~ends,(a+b)/(c+d));
	       Append(~cosets,MR);
	       Append(~cosets,MR2);	
	       Exclude(~to_do_list,m2);
	       Exclude(~to_do_list,m3);
	    end if;
	 end if;
      end for;
      Fareyseq := NextFareyFrac(Fareyseq);
   end while;

   Ends := Sort([x : x in Set(ends)]);
   return cosets, Ends;
end function;


function MakeOtherEdges(Ends,Labels)   
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


function Sconjugate(g)
   // returns the conjugate of g by S=[0,-1,1,0], up to sign.
   a,b,c,d := Explode(Eltseq(g));
   return Parent(g)![d,-c,-b,a];   
end function;

function Pconjugate(g,P)
   // returns the conjugate of g by S=[1,0,0,P], up to sign.
   a,b,c,d := Explode(Eltseq(g));
   return Parent(g)![a,b*P,Integers()!(c/P),d];
end function;
   

// MmodN is a list of things that are 1 or -1 mod M.

function FareySequenceForGamma1N(group)
   N := Level(group);
   if N eq 1 then return FareySequenceForPSL(group);
   end if;
   M := CongruenceIndices(group)[1][2];
   
   G1,MmodN := G1Classes(N,M);
   cosets, Ends := findNiceCosetsForGamma1N(N,M,G1,MmodN);
   
   Ends, Labels, generators := MakeEndsAndLabelsG1(Ends,N,M,G1,MmodN);
   Labels := reNumber(Labels);

   farey_seq :=
   [Cusps()![1,0]] cat [Cusps()| x : x in Ends] cat [Cusps()![1,0]];
   fareylabels := [1] cat  Labels cat [1];

   FS := init_farey_seq(farey_seq,fareylabels,generators);
   FS`group := group;
   PSL := PSL2(Integers());
   FS`cosets := cosets;
   UpdateAttributes(group,FS);
   return FS;
end function;


function MakeEndsAndLabelsG1(Ends,N,M,G1,MmodN)
   // note that in this function, Ends is a sequence of FldRatElt's
   // representing a Farey sequence; this is assumed to be the
   // input.  The Farey symbol starts at 0/1, ends at 1/1;
   // the infinities are added on to the ends later,
   // so are assumed not to occur in the list "Ends".

   M2 := MatrixAlgebra(Integers(),2);
   if N eq 2 then return [Rationals()|0,1],[-2],
      [M2![1,1,0,1],M2![1,-1,2,-1]];
   end if;
   

   Mmod := MatrixAlgebra(Integers(N),2);
   S := M2![0,-1,1,0];
   R := M2![0,1,-1,1];
   Smod := Mmod![0,-1,1,0];
   
   // find the matrix corresponding to each edge:
   matrices := [];
   for i := 1 to #Ends-1 do
      Append(~matrices,
      M2![Numerator(Ends[i+1]),Numerator(Ends[i]),
          Denominator(Ends[i+1]),Denominator(Ends[i])]);      
   end for;
   // create labels corresponding to G1Classes:
   LabelsA := [G1Reduce(G1[1]*Mmod!x,G1,MmodN) : x in matrices];
   LabelsAS := [G1Reduce((G1[1]*Mmod!x)*Smod,G1,MmodN) : x in matrices];
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

// for two end points a,b, this finds the stabilizer for an elliptic
// point between them
function stabilizer(Me,R)
   return Me*R*Me^(-1);
end function;

// this gives representatives for Gamma_0(N) meet Gamma_1(M),
// where M divides N.

// MmodN is a list of mod N things that are 1 or -1 mod M.
// in the following, the product of MmodN and Mstar should be Nstar.

function G1Classes(N,M)
   P1 := P1Classes(N);
   Nmod := Integers(N);

   // find (Z/NZ)*
   // only need half of it, as we quotient by +/-1

   if IsPrime(N) then
      Nstar := [ i : i in [1..N-1]];
   else
      Nstar := [ i : i in [1..N-1] | Gcd(i,N) eq 1];
   end if;

   // MmodN is a list of things in Z/NZ that are +/- 1 mod M
      
   MmodN := [Nmod!i : i in Nstar | (Gcd(i,N) eq 1) and ((i mod M) eq 1 or
   (-i mod M) eq 1)];
   
   // Mstar is a list of elements of Z/NZ
   // such that if MmodN is a list of things that are +/- 1 mod M,
   // then Mstar*MmodN gives all of Nstar, with no repeats.


   if #MmodN eq #Nstar then
      Mstar := [1];
   elif #MmodN eq 2 then
      Mstar := [i : i in Nstar | i le Ceiling((N-1)/2)];
   else
      Mstar := [];
      // ToDo is the list of everything in Nstar.
      // Nstar = i_1.MmodN + i_2.MmodN + ...
      // as the i_js are added to the list Mstar, we
      // exclude the i_j.MmodN from ToDo.
      ToDo := Nstar;
      for i in Nstar do
	 if i in ToDo then
	    Append(~Mstar,i);
	    for m in MmodN do
	       Exclude(~ToDo,m*i);
	    end for;
	 end if;
      end for;
   end if;

   G1 := [Nmod!i*x : i in Mstar, x in P1];

   return G1,MmodN;
end function;


function G1Reduce(x,list,MmodN)
   for m in MmodN do
      ind := Index(list,m*x);
      if ind ne 0 then
	 return ind;
      end if;
      ind := Index(list,-m*x);
      if ind ne 0 then
	 return ind;
      end if;      
   end for;
   print "error in reduction of matrices!";
   return 0;
end function;

// the following will transform the farey sequence for
// Gamma_1 to one for Gamma^1, and one for Gamma_0 to
// one for Gamma^0
// cusps should be a list of cusps.

function transformSequence(cusps)
   // translate first:
   // Note, we assume that the cusp sequence has been
   // produced by the above function, and starts and
   // ends with 0 and 1, (apart from the infinities)
   seqs := [Eltseq(cusps[i]) : i in [1..#cusps-1]];
   cusps2 := [Cusps()![1,0]] cat [Cusps()![a[2],a[2]-a[1]] : a in seqs]; 
   return cusps2;
end function;

function transformLabels(labels)
   // this function must be used in conjunction with the above
   // transformSequence(cusps) function so that labels and cusps
   // are transformed in a compatible way.
   return [labels[#labels]] cat [labels[i] : i in [1..#labels-1]];      
end function;


// the following version of the above functions is used
// in the case where we compute the Farey sequence of
// a congrunce subgroup with indeces [N,M,P] by working with
// [NP,M,1], and at the end we must conjugate to get back to
// the correct Farey sequence.

function FareySequenceForGammaUpper1N(group)
   N := Level(group);
   if N eq 1 then return FareySequenceForPSL(group);
   end if;
   M := CongruenceIndices(group)[1][2];
   
   G1,MmodN := G1Classes(N,M);
   Pcosets, PEnds := findNiceCosetsForGamma1N(N,M,G1,MmodN);   
   PEnds, PLabels, Pgenerators := MakeEndsAndLabelsG1(PEnds,N,M,G1,MmodN);
   PLabels := reNumber(PLabels);

   generators := [Sconjugate(g) : g in Pgenerators];
   
   farey_seq := transformSequence(   
   [Cusps()![1,0]] cat [Cusps()| x : x in PEnds] cat [Cusps()![1,0]]);
   fareylabels := transformLabels([1] cat  PLabels cat [1]);

   FS := init_farey_seq(farey_seq,fareylabels,generators);
   FS`group := group;

   G := GL(2,Integers());   
   M := G![0,-1,1,-1];
   FS`cosets := [M*c : c in Pcosets];
   UpdateAttributes(group,FS);
   return FS;
end function;

