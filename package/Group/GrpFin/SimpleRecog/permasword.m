freeze;

/********************************************************************
* This file contains the collection of functions required for       *
* writing an *even* permutation from Alt(n) as a word in            *
* t:= (1, 2, 3) and s:= (2, ..., n) or (3, ..., n) accordingly      *
********************************************************************/



/*This just turns the permutation into a list - makes it much easier
to work with*/

function MakeListFrom(a);
  support:= Support(a);
  permaslist:= [];
  while #support gt 0 do
      Append(~permaslist, Cycle(a, Min(support)));
      for x in permaslist[#permaslist] do
          Exclude(~support, x);
      end for;
  end while;
  return permaslist;
end function;

/*******************************************************************/
/*
 * This then writes the permutation as a product of transpositions
 */

function MakeIntoPairs(permaslist);
  length:= #permaslist;
  listofpairs:=[];
  for i in [1..length] do
      for j in [2..#permaslist[i]] do
        Append(~listofpairs, [permaslist[i][1], permaslist[i][j]]);
      end for;
  end for;
  return listofpairs;
end function;

/**********************************************************************/

/*
 * this will be the length of the final list of pairs. We insert 
 * [n-1, n] when the position is congruent to 2 or 3 mod 4. If 
 * it's congruent to 0 or 1 mod 4 we take the next thing from
 * listofpairs instead.
 */

function InsertTranspositions(listofpairs, n);
  length:= #listofpairs*2;
  finallist:= [];
  PosInListOfPairs:= 1;
  for i in [1..length] do
      case (i mod 4):
         when 0, 1: Append(~finallist,
                  listofpairs[PosInListOfPairs]);
	     PosInListOfPairs:= PosInListOfPairs + 1;
         when 2, 3: Append(~finallist, [n-1, n]);
      end case;
  end for;
  return finallist;
end function;
 
/**********************************************************************/

function PrepareForRewrite(a, n);
  list:= MakeListFrom(a);
  listofpairs:= MakeIntoPairs(list);
  return InsertTranspositions(listofpairs, n);
end function;

/**********************************************************************/

function  MakeNextSigmaTau(sigmalist, taulist, n);
  level:= #sigmalist;
  assert level eq #taulist;
  if (n-level) mod 2 eq 1 then
      tau:= ((taulist[level]^2)^sigmalist[level])^taulist[level];
      sigma:= sigmalist[level]*taulist[level]^2*tau^-1;
  else 
      tau:= (taulist[level]^sigmalist[level])^taulist[level];
      sigma:= sigmalist[level]*tau;
  end if;
  return sigma, tau;
end function;

/******************************************************************/

function conj(sigmalist, taulist, i, k);
  return taulist[i]^(sigmalist[i]^(k - i - 2));
end function;

/*******************************************************************/


/* this function deals with the most frequent case: 
 * (i, i+1)(n-1 n) - it appears that we have to have i lt n-2 
 */

function MakeStandardCase(sigmalist, taulist, i, n);
  assert i lt n-2;
  outside:= conj(sigmalist, taulist, i, n);
  inside:= conj(sigmalist, taulist, i, n-1);	       
  if ((n - i) mod 2 eq 0) then
     result:= outside^-1*inside*outside^-1;
  else
     result:= outside*inside*outside;
  end if;
  return result;
end function;

/**********************************************************************/

/* This is the overall function. It takes a permutation from A_n 
 * and writes it as an SLP in img(s) = (2, .., n) or (3, .., n) 
 * and img(t) = (1, 2, 3).
 */

function PermAsWord(perm, n)
  prepared_perm:= PrepareForRewrite(perm, n);
  g:= SLPGroup(2);
  program:= Identity(g);
  sigmalist:= [g.1];
  taulist:= [g.2];
  i := 1;
  for i in [1..(#prepared_perm div 2)] do
     a:= prepared_perm[2*i - 1];
     b:= prepared_perm[2*i];
     if a eq [n-1, n] then
         currentpair:= b;
     else 
         currentpair:= a;
     end if;


 /* if the first coordinate has increased, then need 
  * to generate more of taulist and sigmalist 
  */
      if not (currentpair[1] eq #sigmalist) then 
          while #sigmalist lt currentpair[1] do
              sigma, tau:= MakeNextSigmaTau(sigmalist, taulist, n);
              Append(~sigmalist, sigma);
              Append(~taulist, tau);
          end while;
      end if;

 /*the case (i, i+1)(n-1 n)*/
      if ((currentpair[2] eq (currentpair[1]+1)) and (currentpair[1] lt n-2))
        then
          program:= program*MakeStandardCase(sigmalist, 
                                       taulist, currentpair[1], n);
	
    
 /*the case (i, j)(n-1 n) where i+2 leq j leq n-2*/
      elif (((currentpair[1] + 1) lt currentpair[2]) and (currentpair[2] lt
            n-1)) then
          conjelt:= conj(sigmalist, taulist, currentpair[1], currentpair[2]);
          if (((n-currentpair[1]) mod 2 eq 0) or ((n - currentpair[2]) mod 2
	  					   eq 1)) then
	      program:= program*(MakeStandardCase(sigmalist, taulist, 
		                  currentpair[1], n)^(conjelt^-1)); 
          else 
	      program:= program*(MakeStandardCase(sigmalist, taulist, 
                                      currentpair[1], n)^conjelt);
          end if;
	  
      
  /*the case (i, n-1)(n-1 n) or (n-1 n)(i n) i lt n-2*/
      elif ((currentpair[2] eq (n-1) and currentpair eq a and currentpair[1] lt
	     n-2)  or (currentpair[2] eq n and (currentpair eq b) 
             and  (currentpair[1] lt n-2))) then
          fac1:= conj(sigmalist, taulist, currentpair[1], n);
          fac2:= conj(sigmalist, taulist, currentpair[1], n-1);
          if ((n - currentpair[1]) mod 2 eq 0) then
             program:= program*fac1^-1*fac2;
          else 
             program:= program*fac1*fac2;
          end if;

      
 /*the cases (n-1, n)(i, n-1) and (i, n)(n-1 n) i lt n-2*/
      elif ((currentpair[2] eq (n-1) and currentpair eq b and currentpair[1] lt
	      n - 2) or ((currentpair[2] eq n)
	      and (currentpair eq a) and  (currentpair[1] lt n-2))) then
          fac1:= conj(sigmalist, taulist, currentpair[1], n-1);
          fac2:= conj(sigmalist, taulist, currentpair[1], n);
          if ((n -currentpair[1]) mod 2 eq 0) then
	      program:= program*fac1^-1*fac2;
          else 
	      program:= program*fac1^-1*fac2^-1;
          end if;


 /* the cases (n-2 n-1)(n-1 n) and (n-1 n)(n-2 n)*/    
      elif ((currentpair[1] eq n-2) and (((currentpair[2] eq n-1) and
            currentpair eq a) or ((currentpair[2] eq n) and currentpair 
            eq b))) then
          program:= program*taulist[n-2]^-1;

 /* the cases (n-2 n)(n-1 n) and (n-1 n)(n-2 n-1)*/ 
      elif ((currentpair[1] eq n-2) and ((currentpair[2] eq n) and currentpair
          eq a) or ((currentpair[2] eq n-1) and currentpair eq b)) then
          program:= program*taulist[n-2];

 /* the case (n-1 n)(n-1 n), just to make sure that I can have a
  * default case which catches anything odd 
  */

      elif ((currentpair[1] eq n-1) and (currentpair[2] eq n)) then
          ;

      else print currentpair; 
          print "unable to decide what to do with this case";
          return "fail";
      end if;

  end for;
  return program;
end function;


