freeze;

random_MAX_SUM_LEN := 8;
random_MAX_PROD_LEN := 7;

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

function random_word(S)

	X := Parent(S[1]);
	K := CoefficientRing(X);

	w := X!0;
	repeat
		for i:= 1 to Random(1, random_MAX_SUM_LEN) do
//print "A";
			prod := X ! random_field_element(K);
			for j := 1 to Random(1, random_MAX_PROD_LEN) do
				prod *:= Random(S);
			end for;
			w := w + prod;
		end for;
	until w ne 0;			

	return w;

end function;

//*********************************************************************

function random_element(gens, f, e_1, e_2)

	repeat
		w := random_word(gens);
		b := e_1 * f(w) * e_2;
	until b ne 0;
// print w;
	return w, b;

end function;

//**********************************************************************

function random_element1(gens, f)

	repeat
		w := random_word(gens);
		b := f(w);
	until b ne 0;

	return w, b;

end function;

//***********************************************************************

