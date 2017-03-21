freeze;

/********************************************************************
* This file contains all of the functions required to map an element*
* of a black box group to an element of alt_n, on being             *
* given two elements s and t of the black box group which generate  *
* a subgroup of the black box group isomorphic to Alt(n).           * 
*                                                                   * 
* Variable names are a little tricky. When they aren't reasonably   *  
* self-explanatory they match those of the paper by Beals,          *
* Leedham-Green, Niemeyer, Praeger, Seress                          *
********************************************************************/


/* 
 * making the epsilon[i][j]
 */

function MakeEpsilons(k, mprime, m);
  binaries:=[];
  for i in [1..k] do
      binaries[i]:= IntegerToSequence(i, 2);
      while #binaries[i] lt mprime do
          Append(~binaries[i], 0);
      end while;
      Reverse(~binaries[i]);
  end for;
  epsilon:=[ ];
  for j in [1..mprime] do
      epsilon[j]:= [binaries[i][j] : i in [1..k]];
  end for;
  for j in [mprime+1..m] do
      epsilon[j]:= [1 - binaries[i][j-mprime] : i in [1..k]];
  end for;
  return epsilon;
end function;

/********************************************************************/
/* The five_cycles are a bunch of elements which will map to 
 * 5-cycles.
 */

function MakeInitialFiveCycles(three_cycs, n)
  five_cyc_1:= three_cycs[1]*(three_cycs[3])^(three_cycs[2]
                                             *three_cycs[4]^(-1));
  five_cyc_2:= (three_cycs[6])^(three_cycs[5]*three_cycs[4])
             *(three_cycs[8])^(three_cycs[7]*three_cycs[4]);
  return five_cyc_1, five_cyc_2;
end function;

/********************************************************************/

/* making the five_elts - these are a collection of elements 
 * whose images in sym(n) satisfy Support(five_elts[i]) meet 
 * Support(five_elts[i+mprime]) eq emptyset, plus some other 
 * nice properties
 */

function MakeFiveElts(s, t, five_cyc_1, five_cyc_2, epsilon, n, k, m);
  sym_n:= Sym(n);
  five_elts:=[s^0 : i in [1..m]];
  five_elt_perms:= [Identity(sym_n) : i in [1..m]]; /*images of five_elts*/
  five_cyc_temp:= five_cyc_1;
  five_cyc_perm_temp:= sym_n!(1, 2, 3, 4, 5);
  for i in [1..k] do
      for j in [1..m] do
          five_elts[j]:= five_elts[j]*five_cyc_temp^(epsilon[j][i]);
          five_elt_perms[j]:= five_elt_perms[j]*
                               five_cyc_perm_temp^(epsilon[j][i]);
      end for;
      if i eq 1 then
          five_cyc_temp:= five_cyc_2;
          five_cyc_perm_temp:= sym_n!(6, 7, 8, 9, 10);
      elif i lt k then
          five_cyc_temp:= five_cyc_temp^(s^5);
          five_cyc_perm_temp:= sym_n!(5*i+1, 5*i+2, 5*i+3, 5*i+4, 5*i+5);
      end if;
  end for;
  return five_elts, five_elt_perms;
end function;

/*********************************************************************/

/* making the tijk in alt10 - given a number i it produces a collection
 * of 3-cycles whose support sets cover all triples in [i..i+4]*/
 
function GetTijk(i, three_cycs, n, s, t);
  assert 0 lt i and i lt n+1;
  tijk:=[];
  if (i gt 2 or IsOdd(n)) then
      tijk[1]:= three_cycs[6]^(three_cycs[5]*three_cycs[4]); /*678*/
      tijk[2]:= three_cycs[7]^(three_cycs[5]*three_cycs[4]); /*679*/
      tijk[3]:= three_cycs[8]^(three_cycs[5]*three_cycs[4]); /*6710*/
      tijk[4]:= three_cycs[7]^(three_cycs[6]*three_cycs[4]); /*689*/
      tijk[5]:= three_cycs[8]^(three_cycs[6]*three_cycs[4]); /*6810*/
      tijk[6]:= three_cycs[8]^(three_cycs[7]*three_cycs[4]); /*6910*/
      tijk[7]:= three_cycs[7]^(three_cycs[6]*three_cycs[5]); /*789*/
      tijk[8]:= three_cycs[8]^(three_cycs[6]*three_cycs[5]); /*7810*/
      tijk[9]:= three_cycs[8]^(three_cycs[7]*three_cycs[5]); /*7910*/
      tijk[10]:= three_cycs[8]^(three_cycs[7]*three_cycs[6]); /*8910*/
 /* 
  * now need to shift them so so that they start with i
  */
      if i gt 2 then
	  return [elt^(s^(i-6)) : elt in tijk];
      elif i eq 2 then
	  return [elt^(s^(-3)*t^(-1)*s^(-1)) : elt in tijk];
      elif i eq 1  then
	  return [elt^(s^(-3)*t^(-1)*s^(-1)*t^(-1)*s^(-1)) : elt in tijk];
      end if;

  elif (i eq 2 and IsEven(n)) then
      tijk[1]:= three_cycs[2]^three_cycs[1]; /*234*/
      tijk[2]:= three_cycs[3]^three_cycs[1]; /*235*/
      tijk[3]:= three_cycs[4]^three_cycs[1]; /*236*/
      tijk[4]:= three_cycs[3]^three_cycs[2]; /*245*/
      tijk[5]:= three_cycs[4]^three_cycs[2]; /*246*/
      tijk[6]:= three_cycs[4]^three_cycs[3]; /*256*/
      tijk[7]:= three_cycs[3]^(three_cycs[2]*three_cycs[1]); /*345*/
      tijk[8]:= three_cycs[4]^(three_cycs[2]*three_cycs[1]); /*346*/
      tijk[9]:= three_cycs[4]^(three_cycs[3]*three_cycs[1]); /*356*/
      tijk[10]:= three_cycs[4]^(three_cycs[3]*three_cycs[2]); /*456*/
      return tijk;

  else
      assert (i eq 1 and IsEven(n));
      for num in [1..3] do
          tijk[num]:= three_cycs[num]; /*123, 124, 125*/
      end for;
      tijk[4]:= three_cycs[2]^(three_cycs[1]*three_cycs[3]^-1); /*134*/
      tijk[5]:= three_cycs[3]^(three_cycs[1]*three_cycs[4]^-1); /*135*/
      tijk[6]:= three_cycs[3]^(three_cycs[2]*three_cycs[4]^-1); /*145*/
      tijk[7]:= three_cycs[2]^three_cycs[1]; /*234*/
      tijk[8]:= three_cycs[3]^three_cycs[1]; /*235*/
      tijk[9]:= three_cycs[3]^three_cycs[2]; /*245*/ 
      tijk[10]:= three_cycs[3]^(three_cycs[2]*three_cycs[1]); /*345*/
      return tijk;
  end if;
end function;

/********************************************************************/

/* 
 * This takes a triple from the set [i..i+4] and tells you 
 * its index in Tijk.
 */

function WhereInTIJK(i, triple);

  assert i-1 lt triple[1];
  assert triple[1] lt i+3;
  assert i lt triple[2];
  assert triple[2] lt i+4;
  assert i+1 lt triple[3];
  assert triple[3] lt i+5;

  case (triple):
      when [i, i+1, i+2] : result:= 1;
      when [i, i+1, i+3] : result:=  2;
      when [i, i+1, i+4] : result:=  3;
      when [i, i+2, i+3] : result:=  4;
      when [i, i+2, i+4] : result:=  5;
      when [i, i+3, i+4] : result:=  6;
      when [i+1, i+2, i+3] : result:=  7;
      when [i+1, i+2, i+4] : result:=  8;
      when [i+1, i+3, i+4] : result:=  9;
      when [i+2, i+3, i+4] : result:= 10;
  end case;
  
  return result;
end function;

/**********************************************************************/

/*
 * This takes a number pos in the range [1..10] and the number i, and
 * tells you the entries in the triple tijk[num]. It is the inverse
 * function to WhereInTIJK
 */
function WhichTriple(i, pos);

  assert 0 lt pos and pos lt 11;
  
  case (pos):
      when 1 : triple:= [i, i+1, i+2];
      when 2 : triple:= [i, i+1, i+3];
      when 3 : triple:= [i, i+1, i+4];
      when 4 : triple:= [i, i+2, i+3];
      when 5 : triple:= [i, i+2, i+4];
      when 6 : triple:= [i, i+3, i+4];
      when 7 : triple:= [i+1, i+2, i+3];
      when 8 : triple:= [i+1, i+2, i+4];
      when 9 : triple:= [i+1, i+3, i+4];
      when 10: triple:= [i+2, i+3, i+4];
  end case;

  return triple;
end function;

/*****************************************************************/         

function MakeCommutators(j, mprime, five_elts, tijk_z);
  coms_with_five_eltsj:=[];
  coms_with_five_eltsj_plus_mprime:=[];
  for elt in tijk_z do 
      Append(~coms_with_five_eltsj, (five_elts[j], elt));
      Append(~coms_with_five_eltsj_plus_mprime, (five_elts[j+mprime], elt));
  end for;
  return coms_with_five_eltsj cat coms_with_five_eltsj_plus_mprime;
end function;

/******************************************************************/

/* this is to make the s_i - these are the elements that 
 * allow you to decide which of the 9 possible images of 
 * a given point is actually correct. for n gt 11 we 
 * initially make  (1, 3, 4), (1, 5, 6), (1, 7, 8), (1, 9, 10), 
 * (1, 11, 12), and then translate them.. For n eq 11 we 
 * make.. some triples
 */

function makes_i(iota, three_cycs, s, t,n);
  assert n gt 10;
  selts:= [];
  if n gt 11 then 
      selts[1]:= three_cycs[2]^(three_cycs[1]*three_cycs[3]^-1);
      for i in [1..5] do
         Append(~selts, selts[1]^(s^(2*i)));
      end for;
      if iota gt 2 then
          conjelt:= t^2*s^(iota - 3);
          return [x^conjelt : x in selts];
      elif iota eq 2 then
          return [x^t : x in selts];
      elif iota eq 1 then
          return selts;
      else return "fail - iota seems to have wrong value";
      end if;
  else /* n = 11*/
      elt:= three_cycs[3]^(three_cycs[2]*three_cycs[1]);/*3, 4, 5*/
      if iota gt 2 then
          conjelt:= s^(iota -3);
          return [elt^conjelt, elt^(((s^2)^t)*conjelt),
	         elt^(((s^4)^t)*conjelt), elt^(((s^6)^t)*conjelt), 
		 three_cycs[1]^conjelt];
      elif iota eq 2 then
          return [three_cycs[1], elt^(t^2), elt^(t^2*s^2), elt^(t^2*s^4),
	         elt^(t^2*s^6)];
      elif iota eq 1 then
          return [three_cycs[1], elt^t, elt^(t*s^2), elt^(t*s^4), elt^(t*s^6)];
      end if;
  end if;
end function;

/****************************************************************/

/* This picks two elements in tijk whose support sets 
 * intersect in the single point l
 */

function ChooseTwoTijk(tijk, i, l);
  set:= {i, i+1, i+2, i+3, i+4};
  assert l in set;
  if not l in {i, i+1} then
      firsttriple:= Sort([i, i+1, l]);
      secondtriple:= Sort([x : x in set | x gt i+1]);
  else
      firsttriple:= Sort([l, i+3, i+4]);
      secondtriple:= Sort([i, i+1, i+2]);
  end if;
      return tijk[WhereInTIJK(i, firsttriple)], tijk[WhereInTIJK(i,
			   secondtriple)];
end function;

/**************************************************************/

/*This chooses the value of i*/

function GetI(n, l);
  if l lt n-4 then
      return l;
  else return n-4;
  end if;
end function;

/***************************************************************/

/*
 * This deletes images from the possible list
 */

function RemoveImages(triple, k,  images, settokeep, i);
  reducedtriple:= [ijk-i+1 : ijk in triple];      
  for ijk in reducedtriple do
      for elt in [1..5*k] do
          if not elt in settokeep then
               Exclude(~images[ijk], elt);
          end if;
       end for;
  end for;
  return images;
end function;

/****************************************************************/

function CheckComs(is_lower_coms, commutators, num, i, five_elt_perms, j, 
                                            mprime, k, images, id);
  triple:= WhichTriple(i, num);  
  
  if is_lower_coms then
      mult:= 1;
  else 
      mult:= 0;
  end if;          

  settokeep := Support(five_elt_perms[j + mult*mprime]);
  images:= RemoveImages(triple, k, images, settokeep, i);
  rem:= [thing : thing in [i..i+4] | not thing in triple];

  for attempt in [1, 2] do
      newtriple:= Sort([triple[1], triple[2], rem[attempt]]); 
      pos:= WhereInTIJK(i, newtriple);
      if is_lower_coms then
          if commutators[pos] eq id then
              zeroone:= 1;
	  else 
              zeroone:= 0;
	  end if;
      else
          if commutators[pos+10] eq id then
              zeroone:= 0;
          else 
              zeroone:= 1;
          end if;
      end if;  
      settokeep:= Support(five_elt_perms[j + zeroone*mprime]);
      images[rem[attempt] - i + 1]:= [x : x in images[rem[attempt] -
                  i+1] | x in settokeep or x gt (5*k)];
  end for; 
  return images;
end function;

/*******************************************************************/

/* 
 * Input: z \in BBgroup.
 *        integer n st BBgroup cong A_n or S_n.
 *        integer l st 1 \leq l \leq n.
 *        s, t \in BBgroup st s and t satisfy the presentation for
 *             Alt_n given in the Beals et al paper.
 *        three_cycs - a sequence of elements of the BBgroup representing 
 *             a collection of 3-cycles.
 *        five_elts \in BBgroup represents a sequence of
 *             products of disjoint 5-cycles.
 *        five_elt_perms \in S_n is a sequence of product of 
 *             disjoint 5-cycles.
 * 
 * for any z in BBgroup and integer l, constructs the image under 
 * z_perm of 5 consecutive integers, at least one of which is l 
 */
 
function ConstructPartialImage(z, n, l, s, t, three_cycs, five_elts, 
                                                        five_elt_perms);
  k:= Floor(n/5);
  mprime:= Ceiling(Log(2, k+1));
  m:= 2*mprime;
  id:= t^3;


  c:= s^5;
  i:= GetI(n, l);
  images:= [[1..n] : num in [1..5]];
  tijk:= GetTijk(i, three_cycs, n, s, t);
  tijk_z:= [elt^z : elt in tijk];

 /* 
  * This is the real meat of the code - at this stage we take
  * commutators of various five_elts[j]'s with conjugates of the tijk under 
  * z - if these are trivial then support(tijk[num]^z) meet
  * support(five_elts[j+-mprime]) is of size 3, and hence can delete 
  * part of the possible image sets of tijk[num]
  */ 

  for j in [1..mprime] do
      commutators:= MakeCommutators(j, mprime, five_elts, tijk_z);
      assert #commutators eq 20;
      for num in [1..10] do
          if commutators[num] eq id then
              images:= CheckComs(true, commutators, num, i,
                                 five_elt_perms, j, mprime, k, images, id);
          elif commutators[num+10] eq id then
              images:= CheckComs(false, commutators, num, i,
                                 five_elt_perms, j, mprime, k, images, id); 
          end if;
      end for;
  end for;

 /*
  * if the possible image sets have size bigger than 10 then the
  * commutators are not behaving themselves, and so z is neither in alt
  * or sym. 
  */

  if not (#images[1] lt 10 and #images[2] lt 10 and #images[3] lt 10 and
         #images[4] lt 10 and #images[5] lt 10) then
      return false, _, _;
  end if;

 /* 
  * This stage is now the final tidying up - we have at most 9 possible
  * images for each of [i..i+4] and this goes through each of them in
  * turn. We choose an iota in the image set of i+counter-1, and make a
  * set of 5 three-cycles, selts, whose supports pairwise intersect in
  * {iota}. We also pick t_one, t_two from tijk whose supports pairwise
  * intersect in i+counter-1. Taking commutators then tells us whether
  * or not the image of i+counter-1 is iota or not
  */
 
  for counter in [1..5] do
      for iota in images[counter] do
          selts:= makes_i(iota, three_cycs, s, t, n);
          t_one, t_two:= ChooseTwoTijk(tijk, i, i+counter-1);
   
 /*
  * t_one and t_2 should intersect in i+counter-1
  */
        

 /* 
  * if at least 4 of the commutators with t_one^z are nontrivial,
  * and the same for t_2^z then the image of i+counter-1 is iota
  */
          attempts:= 1;
          id_coms_for_t_one:= 0;
	  id_coms_for_t_two:= 0;
          while (attempts lt 6 and id_coms_for_t_one lt 2 and
                              id_coms_for_t_two lt 2) do
              if ((selts[attempts], t_one^z) eq id) then
                  id_coms_for_t_one:= id_coms_for_t_one +1;
              end if;
              if ((selts[attempts], t_two^z) eq id) then 
                  id_coms_for_t_two:= id_coms_for_t_two + 1;
              end if;
              attempts:= attempts+1;
          end while;
          if id_coms_for_t_one lt 2 and id_coms_for_t_two lt 2 then
              images[counter]:= [iota];
              break;
          end if;
      end for;
  end for;

 /*
  * If the size of the image set is not 1 then we have not been 
  * able to apply the homomorphism - probably we have an overgroup 
  * G of the alt or sym that is being looked for, and have now 
  * tried to apply the homomorphism to a generator of G that does 
  * not lie in alt or sym
  */

  for i in [1..5] do
      if not #images[i] eq 1 then
          return false, _, _;
      end if;
  end for;

  return true, [i + num : num in [0..4]], [images[num][1] : num in [1..5]];
end function;
 

/***********************************************************************/

/*
 * This function takes a group element z, and integer n, and two group
 * elements s and t which generate a subgroup of the black box group
 * that is assumed to be isomorphic to alt_n, and returns a
 * permutation of {1, ..., n} representing z.
 */

function EltToPerm(z, n, s, t);

  k:= Floor(n/5);
  mprime:= Ceiling(Log(2, k+1));
  m:= 2*mprime;

 /* The set three_cycs is the preimage of (1, 2, 3), (1, 2, 4),.., 
  * (1, 2, 10)  - when n is even s interacts differently with 
  * t and so we must take inverses
  */

  temp_three_cycs:= [t^(s^num) : num in [0..7]];
  three_cycs:= [];
  if IsEven(n) then
      for num in [1..8] do
          if IsOdd(num) then
              Append(~three_cycs,  temp_three_cycs[num]);
          else
              Append(~three_cycs, temp_three_cycs[num]^-1);
          end if;
      end for;
  else
      three_cycs:= temp_three_cycs;
  end if;

 /* The five_cycs all map to disjoint 5-cycles. We 
  * store no more than 4 at a time. The five_elts's are then 
  * combinations of a's, done in such a way that the support 
  * sets of the images (the five_elt_perm's) have assorted 
  * nice properties, as described in the Beals et al paper. 
  */ 

  five_cyc1, five_cyc2:= MakeInitialFiveCycles(three_cycs, n);
  epsilons:= MakeEpsilons(k, mprime, m); 
  five_elts, five_elt_perms:= 
           MakeFiveElts(s, t, five_cyc1, five_cyc2, epsilons, n, k, m);

 /* 
  * This gets all but the final nmod5 of the images, 
  * producing them 5 at a time
  */

  image:= [];
  for i in [1..k] do
      bool, a, b:= ConstructPartialImage(z, n, 5*i-4, s, t, 
                               three_cycs, five_elts, five_elt_perms);
      if not bool then
          return false, _;            /*z is not in Alt_n*/
      end if;
      for j in [1..5] do
          Append(~image, b[j]);
      end for;
  end for;

 /* 
  * This gets the final 5 images - there is some overlap with previous
  * calculations, but ConstructPartialImages has to process 5 images at
  * once, so this can't be helped. 
  */

  nmodfive:= n mod 5;
  position_first_image:= 5 - nmodfive +1;
  if not nmodfive eq 0 then
      bool, a, b:= ConstructPartialImage(z, n, n, s, t, 
                               three_cycs, five_elts, five_elt_perms);
      if  not bool then 
          return false, _;            /*z is not in Alt_n*/
      end if;
      for i in [position_first_image..5] do
          Append(~image, b[i]);
      end for;
  end if;
  return true, Sym(n)!image;
end function;



