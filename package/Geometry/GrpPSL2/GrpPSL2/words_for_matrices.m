freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//    function for writing elements of a congruence subgroup in   //
//         terms of a given list of generators                    //
//                                                                //
////////////////////////////////////////////////////////////////////

// first (intrinsics) version:  August 28 2002 (hav)


// import the function for the SL2 case:

import "words_for_matricesSL2.m": MatrixToWord;



// the following function recovers information that is comuted but
// not saved when the Farey Symbol is constructed; so in future it
// would be better to add another attribute to the Farey Symbol,
// and not recompute the following list of how edges are glued to
// each other

// I have added an attribute to the group to store this information,
// "FS_glue_list"

// this function takes the list of generators obtained from a Farey
// symbol, and words out which genererators glue which edges.
// if "gens" is the list of generatos, then this function returns
// a list glu, such that the glu[i] is the index of gens such that
// that the i_th edge of the Farey Sequence is glued to some other
// edge via gens[glu[i]], or via gens[glu[i]]^(-1) if glu[i] is
// negative.


function gluing_matrices(G);   
   FS:=FareySymbol(G);
   gens:=Generators(G);
   cusps  := Cusps(FS);
   labels := [Integers()| l : l in Labels(FS)];
   // make a list of which edges have a given label:
   label_list := [[Integers()|] : i in [1..Max(labels)]];
   for i in [1..#labels] do
      if labels[i] gt 0 then
	 Append(~label_list[labels[i]],i);
      end if;
   end for;
   Group := Parent(gens[1]);  
   Id := Group!1;
   glue_list := [0 : i in labels];
   // we're going to make a list of generators associated to given
   // edges, so make a list of which generators have
   // already been accounted for, so don't have to check twice:
   gens_done := [Integers()|];   
   // make list of which generator joins two edges,
   // in the non elliptic case
   for l in label_list do
      _,matrix := IsEquivalent(G,[cusps[l[1]],cusps[l[1]+1]],
      [cusps[l[2]],cusps[l[2]+1]]);
      matrix_inv := matrix^(-1);
      found := false;
      i := 0;
      while not found and i lt #gens do
	 i +:= 1;
	 if i notin gens_done then
	    if matrix eq gens[i] then
	       index := i;
	       found := true;
	    elif matrix_inv eq gens[i] then
	       index := -i;
	       found := true;
	    end if;
	 end if;
      end while;
      glue_list[l[1]] := index;
      glue_list[l[2]] := -index;
      Append(~gens_done,Abs(index));
   end for;   
   // finally, deal with elliptic elements:
   M2 := MatrixAlgebra(Integers(),2);
   S := M2![0,-1,1,0];
   R := M2![0,1,-1,1];
   for i in [1..#labels] do 
      l := labels[i];
      if l lt 0 then
	 a := Eltseq(cusps[i+1]);
	 b := Eltseq(cusps[i]);
	 mat := M2![a[1],b[1],a[2],b[2]];
	 if l eq -2 then; 
	    matrix := G!(mat*S*mat^(-1));
	 elif l eq -3 then
	    matrix := G!(mat*R*mat^(-1));
	 end if;
	 matrix_inv := matrix^(-1);
	 found := false;
	 j := 0;
	 while not found and j lt #gens do
	    j +:= 1;
	    if j notin gens_done then
	       if matrix eq gens[j] then
		  index := j;
		  found := true;
	       elif matrix_inv eq gens[j] then
		  index := -j;
		  found := true;
	       end if;
	    end if;
	 end while;
	 glue_list[i] := index;
      end if;
   end for;
   return glue_list;	 
end function;
   
//
// any farey symbol can be considered to consist of a sequence of
// gaps (e.g., the symbol with cusps L=[oo,0,1,oo] consists of the
// three gaps [oo,0], [0,1] and [1,oo].
//
// If F is a domain given by a farey symbol for G, and g is in G,
// then F and gF are disjoint, so gF is contained in one of the
// gaps.
// The following function determines which "gap" an image ImL=gF of
// a domain F, given by a list of cusps L, belongs to.
//

// note, this algorithm could probably
// be speeded up a little if T=[1,1,0,1]
// is in the group, by adding an extra return value to this
// function, to say how many times T should be applied to get into
// the group.

function which_gap(L,Fracs,ImL,maxL,minL)
   real_cusps := [c[1]/c[2] where c:= Eltseq(c0) : c0 in ImL |
                                                 c0 ne Cusps()![1,0]];
   max := Max(real_cusps);
   min := Min(real_cusps);


   if (min eq minL) and (max eq maxL) then
      return 0;
   end if;
   
   if min ge maxL then
      return #L-1;
   elif max le minL then
      return 1;
   else
      i := 1;
      found := false;      
      while not found and i lt #ImL do
	 i +:= 1; 
	 if max le Fracs[i] then
	    found := true;
	    index := i;
	 end if;
      end while;
   end if;
   return index;
end function;

//
// this function tests whether an image of a domain is in a
// particular gap
//

function is_in_gap(gap,testFD,Fracs,maxL,minL)
   real_cusps := [c[1]/c[2] where c:= Eltseq(c0) : c0 in testFD |
                                                 c0 ne Cusps()![1,0]];
   max := Max(real_cusps);
   min := Min(real_cusps);

   if gap eq 1 then
      if max le Fracs[1] then
	 return true;
      else
	 return false;
      end if;
   elif gap gt #Fracs then
      if min ge Fracs[#Fracs] then
	 return true;
      else
	 return false;
      end if;
   else
      if (max le Fracs[gap]) and (min ge Fracs[gap-1]) then
	 return true;
      else
	 return false;
      end if;
   end if;
      
end function;


//
// The following algorithm finds the 
//

intrinsic FindWord(G::GrpPSL2,g::GrpPSL2Elt) -> SeqEnum
   {given a congruence subgroup G, and an element g in G, this
   function computes g in terms of the generators of G.  The
   generators of G are those given by the function Generators(G).
   Denote this sequence by "Gen"
   This function returns a sequence of integers [a_1,a_2,....a_m]
   such that g = Gen[Abs(a_1)]^Sign(a_1)*...*Gen[Abs(a_m)]^Sign(a_m).
   }

   require not assigned G`EichlerOrder : "G must be a congruence subgroup";

   require g in G:
      "the matrix is not in the group!";

   gens := Generators(G);
      
   // I assume that in the computation of generators, the Farey
   // symbol is also computed, and these two attributes of the
   // group G are compatible, i.e., no messing with attributes has
   // been done.  I do not check this is the case.

   if G eq PSL2(Integers()) then
      // different case for PSL2(Z)
      // have to write this!
      return MatrixToWord(g);
   end if;

   // if the group is not PSL2(2) we assume it has at least
   // 4 elements in the list of cusps of the Farey sequence.
   // currenently this is always the case, so I do not test for it.

   
   if not assigned G`FS_glue_list then      
      glue_list := gluing_matrices(G);
      G`FS_glue_list := glue_list;
   else
      glue_list := G`FS_glue_list;
   end if;
   FS := FareySymbol(G);
   La := Labels(FS);
   C := Cusps(FS);
   real_Ccusps := [c[1]/c[2] where c:= Eltseq(c0) : c0 in C |
   c0 ne Cusps()![1,0]];
   minC := Min(real_Ccusps);
   maxC := Max(real_Ccusps);
   
   Fracs := [c[1]/c[2] where c:= Eltseq(c0) : c0 in C | c0 ne Cusps()![1,0]];
   imF := g*C;
   word:=[];
   done := false;
   while not done do;      
      gap := which_gap(C,Fracs,imF,maxC,minC);
      if gap eq 0 then
	 done := true;
      else
	 // get next "letter" in the word for the matrix:
	 letter := glue_list[gap];
	 // in the case that the group contains elliptic elements
	 // of order 3, need an extra test:
	 matrix := gens[Abs(letter)]^(Sign(letter));
	 if La[gap] eq -3 then
	    testFD:= matrix*imF;
	    if is_in_gap(gap,testFD,Fracs,maxC,minC) then
	       letter := -letter;
	       matrix := matrix^(-1);
	    end if;	    
	 end if;	 
	 Append(~word,-letter);
	 imF := matrix*imF;
      end if;
   end while;
   return word;
end intrinsic;


// the following function is for testing purposes

// for this function, G must be some congruence
// subgroup, and "word" a sequence of integers, none
// of which is bigger than the size of the list
// of generators, produced by: Generators(G)

function multiply_out_word(G,word)
   if Type(word) ne SeqEnum then
      print "nonsense input!";
      return 0;
   end if;
   gens := Generators(G);
   g := G!1;
   for i in word do
      g := g*gens[Abs(i)]^Sign(i);
   end for;
   return g;
end function;
   


