freeze;

/*****************************************************************
* This file contains functions which, on being given a black box *
* group g and an integer n, finds elements s and t that satisfy  *
* the presentation for alt_n as described in the paper by        *
* Beals et al, and returns these along with straight line        *
* programs in the generators of group to produce s and t         *
* If it can't find s and t it returns false.                     *
*****************************************************************/ 

/*****************************************************************/

/* 
 * This is to find 2 elements that we hope have cycle type 
 * a:= 1^k.(n-k)^1, b:= 1^n-3.3^1.  
 */

function FindFirstElts(process, processusage, g, id, n)

 /* the number k is to ensure that a is an even permutation 
  */
  if n mod 2 eq 0 then
      k:= 1;
  else
      k:= 0;
  end if;

 /* the number m is to ensure that b (which will be c^(n-m)) 
  * is as likely as possible to be a 3-cycle 
  */
  case (n mod 6):
      when 0: m:= 5;
      when 1: m:= 6;
      when 2: m:= 3;
      when 3: m:= 4;
      when 4: m:= 3;
      when 5: m:= 4;
  end case;

  i:= 1;
  founda:= false;
 
 /* get a segmentation fault if the word length gets 
  * too big, so reset if necessary 
  */ 
  while ((i lt (2*n)) and not founda) do
      if processusage gt 1000 then
          process:= RandomProcessWithWords(g : Scramble:= 100);
          processusage:= 0;
      end if;
      a, a_word:= Random(process);
      processusage:= processusage + 1;
      if (a^(n-k) eq id) then            // a is hence reasonably likely to
          founda := true;                // correspond to an n-k cycle. 
      end if;   
      i:= i+1;
  end while;

  i:= 1;
  foundc:= false;
  while ((i lt (36*n)) and not foundc) do
      c, c_word:= Random(process);
      processusage:= processusage + 1;
      if (c^(3*(n-m)) eq id) then         // c^(n-m) is hence reasonably
          foundc := true;                 // likely to be a 3-cycle
      end if;
      i:= i+1;
  end while;


  if foundc then
      b:= c^(n-m);
      b_word:= c_word^(n-m);
  end if;

  if founda and foundc then
      return true, process, processusage, a, b, a_word, b_word;
  else
      return false, process, processusage, _, _, _, _; 
  end if;

end function;




/******************************************************************/


/* for n odd, this function takes two elements a and b which 
 * hopefully have cycle type n^1 and 1^(n-3).3^1 and returns two 
 * elements s and t which (if a and b are of correct cycle type) 
 * can be mapped to (3, 4,.., n) and (1, 2, 3). Algorithm is 
 * Las Vegas with probability of success at least 3/4 
 */

function FindOddGens(process, id, n, a, b, a_word, b_word)
  assert n mod 2 eq 1;
  assert n gt 10;

 /*
  * first we find a conjugate c of b such that [c, c^a] neq 1 
  */

  foundc:= false;
  i:= 1;
  while (i lt (1 + n/3) and not foundc) do
      x, x_word:= Random(process);
      c:= b^x;
      if not ((c, c^a) eq id) then
          foundc:= true;
          c_word:= b_word^x_word; 
      end if;
      i:= i+1;
  end while;

  if not foundc then     
     return false, _, _, _, _;
  end if;

 /* c is guaranteed to have support set which can be mapped to
  * {1,  2, k} (mod n), where 3 \leq k \leq n-1. The next
  * stage of the algorithm is to construct t such that the support 
  * set of t can be mapped to {1, 2, 3}
  */

 /* if k eq 3, then c*(c^a) is an involution. otherwise 
  * it has order 5 
  */

  k_eq_three:= (Order(c*(c^a)) eq 2);

 /* if k eq 4 or n-1 then (c, c^(a^2)) is not the identity 
  */

  k_four_or_n_take1:= not ((c, c^(a^2)) eq id);

  if k_eq_three then       /*this means k=3*/
      x:= c^(a^2);
      y:= c^x;
      if (y, y^(a^2)) eq id then
         t:= c^2;
         t_word:= c_word^2;
      else
         t:= c;
         t_word:= c_word;
      end if;

  elif k_four_or_n_take1 then    /*k = 4 or n-1*/
      x:= c^a;
      x_word:= c_word^(a_word);
      y:= c^x;
      if (y, y^a) eq id then
          t:= (c^2, x);
          t_word:= c_word^(-2)*x_word^(-1)*c_word^2*x_word;
      elif (y, y^(a^2)) eq id then
          t:= (c, x^2);
          t_word:= c_word^(-1)*x_word^(-2)*c_word*x_word^2;
      elif (y*(y^a))^5 eq id then
          t:= (c^2, x);
          t_word:= c_word^(-2)*x_word^(-1)*c_word^2*x_word;
      elif (y*(y^a))^2 eq id then
          t:= (c, x^2);
          t_word:= c_word^(-1)*x_word^(-2)*c_word*x_word^2;
      else
          return false, _, _, _, _;
      end if;

  else                                   /* 5 leq k leq n-2*/
      x:= c^a;
      x_word:= c_word^a_word;
      y:= c^x;
      if (y, y^a) eq id then
          t:= (c^2, x);
          t_word:= c_word^(-2)*x_word^(-1)*c_word^2*x_word;
      else
          t:= (c, x^2);
          t_word:= c_word^(-1)*x_word^(-2)*c_word*x_word;
      end if;
  end if;


  return true, a*t^2, t, a_word*t_word^2, t_word;

end function;


/******************************************************************/


/* for n even, this function takes two elements a and b which
 * hopefully have cycle type 1^1.(n-1)^1 and 1^(n-3).3^1 and returns
 * elements s and t which (if a and b are of correct cycle type) 
 * can be mapped to (1,2)(3,4,..,n) and (1,2,3). Algorithm is 
 * Las Vegas, with probability of success at least 3/4 
 */

function FindEvenGens(process, id, n, a, b, a_word, b_word)
  assert n mod 2 eq 0;
  assert n gt 9;

 /*compute these once as we'll use them lots*/
  asquared:= a^2;
  afourth:= a^4;

  foundt:= false;
  i:= 1;
  while (i lt ((2*n)/3) and not foundt) do
      x, x_word:= Random(process);
      c:= b^x;
      if not (((c, c^a) eq id) or ((c, c^asquared) eq id) or ((c,
					c^afourth) eq id)) then
          t:= (c^a, c);
          c_word:= b_word^x_word;
          t_word:= (c_word^a_word)^(-1)*c_word^(-1)*c_word^a_word*c_word;
	  foundt:= true;
      end if;
      i:= i+1;
  end while;

  if foundt then
      return true, a*t, t, a_word*t_word, t_word;
  else 
      return false, _, _, _, _;
  end if;

end function;

/******************************************************************/

/*
 * and now the main function for finding generators.
 */
 
function FindGens(process, id, n, a, b, a_word, b_word)
  if IsEven(n) then
      return FindEvenGens(process, id, n, a, b, a_word, b_word);
  else
      return FindOddGens(process, id, n, a, b, a_word, b_word);
  end if;
end function;

/******************************************************************/

/*
 * The following collection of functions check that two generators
 * s and t satisfy the relations described in Beals et al.
 */

/*******************************************************************/

/*
 * The easy case - n even.
 */

function CheckEvenGens(s, t, n, id);
  assert n mod 2 eq 0;
  assert n gt 10;

  if ((s^(n-2) eq id) and (t^3 eq id) and ((t, s)^2 eq id)) then
     return true;
  else 
     return false;
  end if;

end function;

/**************************************************************/

function CheckNextRelator(elt, s, t, id);    
  nextpower:= elt*s;
  bool:=  ((t*nextpower^(-1)*t*nextpower)^2 eq id);
  return bool, nextpower;
end function;

/********************************************************************/

function CheckOddGens(s, t, n, id);
  assert n mod 2 eq 1;
  assert n gt 6;

/* we check the fast relations first, as 
 * no point going into main loop
 * if these fail 
 */

  easyrelns:=  ((s^(n-2) eq id) and (t^3 eq id) and ((s*t)^n eq id));
  
  if not easyrelns then
     return false;
  end if;

  elt:= id; 
  for i in [1..((n-3) div 12)] do
      bool, elt:= CheckNextRelator(elt, s, t, id);
      if not bool then
          return false;
      end if;
  end for;

 /* if have reached this stage then all relations are true */

  return true;

end function; 


/***************************************************************/

/* 
 * The main checking function.
 */

function CheckGens(s, t, n, id)
  if IsEven(n) then
      return CheckEvenGens(s, t, n, id);
  else
      return CheckOddGens(s, t, n, id);
  end if;
end function;

/***************************************************************/

/*
 * The main function in this file.
 */

/* This takes a group g and an integer, and returns four things: 
 * elements s and t which can be mapped to (3..n) and (1, 2, 3) 
 * if n is odd and to (1,2)(3..n) and (1, 2, 3) if n is even, 
 * followed by straightline programs in the generators of g that 
 * evaluate to s and t. It is Las Vegas - if fails returns false
 */

function GetAltGens(g, n);

  assert n gt 10;

 /* this is set to have a 1 in e^5 chance of failure. paper 
  * claims that for n leq 300 they have calculated precise 
  * conditional probabilities, and hence bound is much better. 
  */

  if n lt 301 then
      max:= 580;
  else max:= 384000;
  end if;

  proc:= RandomProcessWithWords(g);
  length:= 0;
  id:= Identity(g);

  for i in [1..max] do
      bool, proc, length, a, b, a_word, b_word:= 
                            FindFirstElts(proc, length, g, id, n);
    
      if bool then         /* This means have found
                            some plausible elements to start working on */
          bool, s, t, s_word, t_word:= FindGens(proc, id, n, a, b, 
                                                        a_word, b_word);
          if bool then                  /* have found a pair of elts. */
              if CheckGens(s, t, n, id) then
                  return true, s, t, s_word, t_word;
              end if;
          end if;
      end if;
  end for;

  return false, _, _, _, _;

end function;



