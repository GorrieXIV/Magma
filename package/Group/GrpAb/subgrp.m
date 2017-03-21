freeze;

AllHermite := function(s:sub:=[-1], quot:=[-1], clever:=true)
/* s should be a sequence of positive integers of length n.
 * A list of nxn matrices A in Hermite normal form such that
 * Id[i]*s[i] is in the row span of A for 1<=i<=n, where Id[i]
 * is the i-th standard basis vector of Z^n, is returned.
 * If sub or quot is specified, then find only subgroups whose
 * Invariants are sub/quot.
 * (For this to work, sub/quot must be specified as a list of positive
 *  integers with each one dividing the next.)
 */
  local n, cmat, gpgens, list, crow, ccol, bt, R1, R2, ss, qs, sqs,
        ind, subord, subind, subexp, quotexp, csi, d;
  n := #s;

  /* if sub or quot is specified, then we set up lower and upper bounds for
   * the product of the entries on the diagonal from i to n of our
   * Hermite Normal Form matrix
   */
  ind := [ &*[s[j]: j in [i..n]] : i in [1..n] ];
  ss := sub ne [-1]; qs := quot ne [-1]; sqs := ss or qs; 
  if ss and qs then
    error "Subgroup and quotient structures may not both be specified";
  end if;

  cmat := IdentityMatrix(Integers(),n);

  if n eq 0 then
    if (ss and &*sub ne 1) or (qs and &*quot ne 1) then
      return [];
    else return [cmat];
    end if;
  end if;

  if ss then
    subord := sub eq [] select 1 else &*sub;
    subind := ind[1] div subord;
    subexp := sub eq [] select 1 else sub[#sub];
    if sub eq [1] then sub := []; end if;
  end if;
  if qs then
    subind := quot eq [] select 1 else &*quot;
    subord := ind[1] div subind;
    quotexp := quot eq [] select 1 else quot[#quot];
    if quot eq [1] then quot := []; end if;
  end if;

  R1 := RowSpace(cmat);
  gpgens := cmat;
  for i in [1..n] do gpgens[i][i]:=s[i]; end for;
  R2 := RowSpace(gpgens);
  list := [];
  crow := 1; ccol := n;
  // begin backtrack search for HNF matrices
  bt := false;
  while crow le n do
    if bt then
      cmat[crow][ccol] +:=1;
    end if;
    if crow eq ccol then
      d := cmat[crow][ccol];
      if d gt s[ccol] then
        cmat[crow][ccol] := 1; crow +:= 1; ccol := n;
        bt := true;
        continue;
      end if;
      if s[crow] mod d ne 0 then
        bt := true;
        continue;
      end if;
      if sqs and clever then
        if (ss and d div s[crow] gt subexp) or (qs and d gt quotexp) then
          if qs then  cmat[crow][ccol] := 1; crow +:= 1; ccol := n; end if;
          bt := true;
          continue;
        end if;
        csi := &*[cmat[i][i] : i in [crow..n]];
        if csi gt subind or ind[crow] div csi gt subord then
          if csi gt subind then  cmat[crow][ccol] := 1; crow +:= 1; ccol := n;
          end if;
          bt := true;
          continue;
        end if;
      end if;
    else
      if cmat[crow][ccol] ge cmat[ccol][ccol] then
        cmat[crow][ccol] := 0;
        ccol -:= 1;
        bt := true;
        continue;
      end if;
    end if;
    if ccol eq n and not gpgens[crow] in RowSpace(cmat) then
      bt := true;
      continue;
    end if;
    if crow eq 1 and ccol eq n then
      bt := true;
      if ss and Moduli(RowSpace(cmat)/R2) ne sub then
        continue;
      end if;
      if qs and Moduli(R1/RowSpace(cmat)) ne quot then
        continue;
      end if;
      Append(~list,cmat);
    else
      ccol +:= 1;
      if ccol gt n then
        crow -:= 1; ccol := crow;
      end if;
      bt := false;
    end if;
  end while;
  return list;
end function;

intrinsic Subgroups(G::GrpAb :Sub:=[-1],Quot:=[-1]) -> SeqEnum
{Compute the subgroups of the finite abelian group}
/* G must be a finite abelian group.
 * return a list of its subgroups
 */
  if  not IsFinite(G)then
    error "Argument of Subgroups must be finite";
  end if;
  ng := Ngens(G);
  os := [ Order(G.i) : i in Reverse([1..ng]) ];
   //AllHermite is quickest with orders in decreasing order
  hf := AllHermite(os:sub:=Sub,quot:=Quot);
    RF := recformat<order, length, subgroup, presentation>;
    res := [PowerStructure(Rec)|]; // billu: specify universe so null sequence
				   // isn't given the Subgroups attribute
    for m in hf do
	H := sub<G|[G!Reverse(ElementToSequence(m[i])) : i in [1..ng]] >;
	Append(~res, rec<RF|order := #H, length := 1, subgroup := H>);
    end for;
    AssertAttribute(res, "Subgroups", true);
    return res;
end intrinsic;

