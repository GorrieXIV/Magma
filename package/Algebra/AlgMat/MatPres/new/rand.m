freeze;

//  random_MAX_SUM_LEN := 8;
//  random_MAX_PROD_LEN := 7;

//*******************************************************************

function random_field_element(K)
	if #K eq 2 then
		return K!1;
	else
		repeat
			k := Random(K);
		until k ne 0;
		return k;
	end if;
end function;

//*******************************************************************

function random_word(S, lim1, lim2)

	X := Parent(S[1]);
	K := CoefficientRing(X);

	w := X!0;
	repeat
		for i:= 1 to Random(1, lim2) do
			prod := X ! random_field_element(K);
			for j := 1 to Random(1, lim1) do
				prod *:= Random(S);
			end for;
			w := w + prod;
		end for;
	until w ne 0;			
	return w;

end function;

//*********************************************************************

function random_element_m(gens, f, e_1, e_2, lim1, lim2)

	counter := 0;
	repeat
		counter +:= 1;
		if counter eq 10 then
		    counter := 0;
		    lim1 +:= 1;
		    lim2 +:= 1;
		end if;
		w := random_word(gens, lim1, lim2);
		b := e_1 * f(w) * e_2;
	until b ne 0;
	return w, b;

end function;

//**********************************************************************

function random_element1_m(gens, f, lim1, lim2)

	counter := 0;
	repeat
		counter +:= 1;
		if counter eq 10 then
		    counter := 0;
		    lim1 +:= 1;
		    lim2 +:= 1;
		end if;
		w := random_word(gens, lim1, lim2);
		b := f(w);
	until b ne 0;

	return w, b;

end function;

//***********************************************************************


procedure spin_up_once(~w, gens, ~B, ~mons, ~V, ~boo)

/* 
	if boo, then B is a basis for the algebra generated by gens, 
	otherwise, B is a partial spin of that algebra. 
*/
    F := Parent(mons[1]);
    K := BaseRing(V);
    n := Nrows(B[1]);
    if not boo then 
       VG := Generic(V);
       gens := [VG!x:x in gens];
       d := Dimension(V);
       next := 1;
       flag := true;
       while flag and next le d do
          Y := B[next];
          for i := 1 to #gens do
             Z := Y*gens[i];
             Include(~V, VG!Z, ~f);
             if f then 
                Append(~B, Z);
                Append(~mons, mons[next]*F.i);
                r := Random(VectorSpace(K,#mons));
                w:= &+[r[i]*mons[i]: i in [1 .. #mons]];
                flag := false;
                break;
             end if;
          end for;
          if next eq d then 
             boo := false;
             r := Random(VectorSpace(K,#mons));
             w := &+[r[i]*mons[i]: i in [1 .. #mons]];
          end if;
          next +:= 1;
       end while;
    else
       r := Random(VectorSpace(K,#mons));
       w := &+[r[i]*mons[i]: i in [1 .. #mons]];
       boo := true;
    end if;

end procedure;

///////////////////////////////////////////////////////////////

function random_element(A, f, e_1, e_2)

   gens := A`SpinGenerators;
   nspin := A`SpinMatrices;
   nboo := A`SpinDone;
   nmons := A`SpinMonomials;
   nV := A`SpinVectors;
   w := nmons[1];
   repeat
      spin_up_once(~w, gens, ~nspin, ~nmons, ~nV, ~nboo);
      b := e_1 * f(w) * e_2;
   until b ne 0;
   A`SpinMatrices := nspin;
   A`SpinDone := nboo;
   A`SpinMonomials := nmons;
   A`SpinVectors := nV;

        return w, b;

end function;

////////////////////////////////////////////////////////////////

function random_element1(A, f)

   gens := A`SpinGenerators;
   nspin := A`SpinMatrices;
   nboo := A`SpinDone;
   nmons := A`SpinMonomials;
   nV := A`SpinVectors;
   w := nmons[1];
   repeat
      spin_up_once(~w, gens, ~nspin, ~nmons, ~nV, ~nboo);
      b := f(w);
   until b ne 0;
   A`SpinMatrices := nspin;
   A`SpinDone := nboo;
   A`SpinMonomials := nmons;
   A`SpinVectors := nV;

        return w, b;

end function;

///////////////////////////////////////////////////////////////////////

procedure random_element2(A, ~spin, ~mons, ~V, ~boo, f, e_1, e_2, ~w, ~b)

   gens := A`SpinGenerators;
   repeat
      spin_up_once(~w, gens, ~spin, ~mons, ~V, ~boo);
      b := e_1 * f(w) * e_2;
   until b ne 0;

end procedure;


/* 

The purpose of the last function is to create random elements 
without adding to the spin on the original algebra. However, we do 
add to the spin locally. That is, we add to the spin until we 
come up with a random element that solves the local problem. Then 
the addition to the spin is discarded. This keeps the spin from
becoming too large. 

When we call this we must

1. set up the spin:
   spin := A`SpinMatrices;
   boo := A`SpinDone;
   mons := A`SpinMonomials;
   V := A`SpinVectors;

2. initialize w and b as in :  w := mons[1]; b := e_1;

*/




