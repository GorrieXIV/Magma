freeze;

/*-----------------------------------------------------------
  Shadow receives an element h of G and two subgroups Gi and Gj of G
  It returns a sequence containing one representative of each right coset
  of Gj meeting Gi
-----------------------------------------------------------*/
Shadow := function(h,Gi,Gj);
  return [t*h : t in Transversal(Gi,Gi meet Gj)];
end function;

/*-----------------------------------------------------------
  Intersection receives two sequences of elements of G which are
  representatives of the cosets of Gi forming the i-shadows
  of an element x and a flag F.
  It returns a sequence containing a representative of each coset
  of Gi appearing in both shadows
-----------------------------------------------------------*/
Intersection := function(coef1, coef2, Gi);
  int := [];
  for x in coef1 do
    for y in coef2 do
      if x*y^-1 in Gi then
        Append(~int, x); break y;
      end if;
    end for;
  end for;
  return int;
end function;

/*-----------------------------------------------------------
  AreIncident receives a set x of subgroups of G, a set of indices
  corresponding to subgroups of x having a right coset in the flag F,
  an element h of G such that x[r]*h is a right coset of F,
  a set r2 of indices corresponding to the subgroups of x having a
  right coset in the flag F' and an element t of G such that x[r2]*t is a
  right coset of F'.
  It checks whether all elements of F are incident to all elements of
  F' or not.
-----------------------------------------------------------*/
AreIncident := function(x, r, h, r2, t);
  ok := true;
  for y in r do
    yh := {z*h : z in x[y]};
    for z in r2 do
      zt := {w*t : w in  x[z]};
      if IsEmpty(yh meet zt) then
        ok := false; break y;
      end if;
    end for;
  end for;
  return ok;
end function;

/*-----------------------------------------------------------
  Search performs the search for a flag F' incident to x and F
  and such that its i-shadow is equal to the intersection of
  the i-shadows of x and F.
  It returns true if such an F' exists, false otherwise.
  - alpha is the minimum of the cardinalities of the i-shadows
    of x and F;
  - Gfprime is the stabilizer of a flag F'.
  - Gi is the stabilizer of x;
  - Gj is the stabilizer of F;

-----------------------------------------------------------*/
Search := function(alpha, Gfprime, Gi, Gj, inte, x, r, h, r2);
  if alpha ne (#Gfprime) / (#(Gfprime meet Gi)) then return false;
  else
    for t in Transversal(Gi meet Gj, Gi meet Gj meet Gfprime) do
      shadowt := Shadow(t,Gfprime,Gi);
      if #Intersection(shadowt,inte,Gi) eq alpha then
        if AreIncident(x, r, h, r2, t) then
        return true;
        end if;
      end if;
    end for;
    return false;
  end if;
end function;
/*----------------------------------------------------------
  Property checks whether, for a given type i and a given element
  Gj of type j, for every flag F such that the i-shadows of Gj and F
  have at least one element in common, there exists an F' such that
  F' is incident to x and F and the i-shadow of F' is the intersection
  of the i-shadows of x and F.
  - k is a set of subsets of the set of types of the geometry;
    These subsets of types are the types that the flags F may have.
-----------------------------------------------------------*/
Property := function(G,x, j, i, k);
 ipn := true;
 Gi := x[i];
 Gj := x[j];
 shadowx := Shadow(Id(Gj),Gj,Gi);

 for r in k do
   Gf := G;
   for y in r do
     Gf := Gf meet x[y];
   end for;
   phi, L := CosetAction(Gi, Gi meet Gf);
   phiinv := Inverse(phi);
   O := Orbits(phi(Gi meet Gj));
   for o in O do
     o2 :=  phiinv(o);
     shadowF := Shadow(Representative(o2),Gf,Gi);
     inters:=Intersection(shadowx, shadowF, Gi);
     alpha := #inters;
     ok := true;
     k2 := {};
     if not (alpha in {0, 1}) then
       if alpha eq Min(#shadowx,#shadowF) then
         if #(Set(x[j]) meet Set({xx*Representative(o2): xx in Gf})) eq 0 then
           ok := false;
           k2 := k diff {r};
         end if;
       else
         ok := false;
         k2 := k diff Subsets(r);
       end if;
       Include(~k2,{});
       while not ok and not(IsEmpty(k2)) do
         Gfprime := G;
         r2 := Representative(k2);
         for y in r2 do
           Gfprime := Gfprime meet x[y];
         end for;
         if Search(alpha, Gfprime, Gi, Gj, inters, x, r, Representative(o2), r2) then
           ok := true;
         else
           k2 := k2 diff {r2};
         end if;
       end while;
       if not(ok) then
         ipn := false; break r;
       end if;
     end if;
   end for;
 end for;
 return ipn;
end function;

/*----------------------------------------------------------
  IPn receives a CosetGeometry C and an integer n and checks
  if C satisfies the properties (IP)_n and (WIP)_n
-----------------------------------------------------------*/
intrinsic HasIntersectionPropertyN(C :: CosetGeom, n :: RngIntElt) 
                                                   -> BoolElt, BoolElt
{Determine whether the coset geometry C satisfies the intersection 
property of rank n and the weak intersection property of rank n}

ipn := true;
wip := true;
wipn := true;
if Rank(C) ge n then
  wipn := true;
  G := Group(C);
  t := Types(C);
  subt := Subsets(Set(t),#t-n);
  for y in subt do
    r := Residue(C,y);
    G := Group(r);
    x := MaximalParabolics(r);
    I := {1..n};
    wip := false;
    for i in I do
      iipn := true;
      for j in I diff {i} do
        c := Subsets(I diff {i});
        Exclude(~c,{});
        if not(Property(G,x,j,i,c))
        then
          ipn := false; iipn := false; break j;
        end if;
      end for;
      wip := wip or iipn;
    end for;
    wipn := wipn and wip;
  end for;
end if;
return ipn, wipn;
end intrinsic;

//--------------------------------------------------------------------
intrinsic HasIntersectionProperty(C :: CosetGeom) -> BoolElt
{Determine whether the coset geometry C satisfies the intersection 
property}

  return HasIntersectionPropertyN(C, Rank(C));

end intrinsic;

//--------------------------------------------------------------------
intrinsic HasWeakIntersectionProperty(C :: CosetGeom) -> BoolElt
{Determine whether the coset geometry C satisfies the weak intersection 
property}

  _, wip := HasIntersectionPropertyN(C, Rank(C));

  return wip;

end intrinsic;


