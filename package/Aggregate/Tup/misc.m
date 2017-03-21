freeze;

intrinsic Flat(T::Tup) -> Tup
{Returns the flattened version of T.}

    U := <>;
    for x in T do
	if Type(x) in {Tup, SeqEnum} then
	    for y in Flat(x) do
		Append(~U, y);
	    end for;
	else
	    Append(~U, x);
	end if;
    end for;
    return U;

  /*
  P := Flat(Parent(T));
  if P cmpeq Parent(T) then
    return T;
  end if;  
  j := 1;
  N := Representative(P);
  for i in [1..#T] do
    if Category(Parent(T[i])) eq Category(P) then
      S := Flat(T[i]);
      for k in [1..#S] do
        N[j] := S[k];
        j +:= 1;
      end for;  
    else
      N[j] := T[i];
      j +:= 1;
    end if;  
  end for;
  return N;
  */
end intrinsic;
