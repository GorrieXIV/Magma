freeze;

intrinsic Sort(Q::[], compare::UserProgram) -> [], GrpPermElt
{Sort the sequence Q using the diminishing increment sort}
    S := Q;
    Sort(~S, compare, ~p);
    return S, p;
end intrinsic;

intrinsic Sort(~Q::[], compare::UserProgram)
{Sort the sequence Q using the diminishing increment sort}
    Sort(~Q, compare, ~p);
end intrinsic;

intrinsic Sort(~Q::[], ~permut)
{Sort the sequence Q using the diminishing increment sort}
    n := #Q;
    if n eq 0 then
	// see comment in next Sort intrinsic below
	permut := Id(Sym(1));
	return;
    end if;

    perm := [ k : k in [1..n] ];
    ParallelSort(~Q, ~perm);
    permut := Sym(n) ! perm;
end intrinsic;

intrinsic Sort(~Q::[], compare::UserProgram, ~permut)
{Sort the integer sequence Q using the diminishing increment sort}
   n := #Q;
   if n eq 0 then
      // This is grotesque, but we don't have permutations of sets of
      // cardinality 0.
      permut := Id(Sym(1));
      return;
   end if;

   // Create the sequence of increments.
   inc := [1];
   h := 1;
   repeat
      h := 3*h + 1;
      Append(~inc, h);
   until h ge n;

   // Perform the sort.
   perm := [1 .. n];
   t := Max(#inc - 2, 1);
   for s := t to 1 by -1 do
      h := inc[s];
      for j := h + 1 to n do
         i := j - h;
         k := Q[j];
	 kpos := perm[j];
	 while compare(k, Q[i]) lt 0 do
            Q[i+h] := Q[i];
	    perm[i+h] := perm[i];
            i -:= h;
            if i le 0 then
		break;
	    end if;
         end while;
         Q[i+h] := k;
	 perm[i+h] := kpos;
      end for;
   end for;
   permut := Sym(n) ! perm;
end intrinsic;

intrinsic PermuteSequence(Q::[], p::GrpPermElt) -> []
{Permute the entries of sequence Q in accordance with permutation p}
    require #Q eq Degree(Parent(p)): "length of sequence not equal to degree of permutation";
    return [Q[i^p]: i in [1..#Q]];
end intrinsic;

intrinsic RandomOrder(Q::[]) -> []
{Permute the entries of the sequence Q by a random permutation}
    if #Q eq 0 then return Q; end if;
    return PermuteSequence(Q,Random(Sym(#Q)));
end intrinsic;
