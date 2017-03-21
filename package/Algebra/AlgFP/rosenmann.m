freeze;

/*
A Groebner Basis And a free Schreier basis algorithm for the group
algebra of a free group.

Based on Algorithm 6.1 in Rosenmann: An Algorithm for Constructing Groebner
and Free Schreier Bases in Free Group Algebras.
 
Amnon Rosenmann
*/

// ****************** MONOIDS ************************************
function MonLeftDivides(s, t)
/* 
          Input: elements s,t of the monoid.
          Output: returns true if s is a prefix of t, and
                  false ohterwise.
*/
        if s eq Parent(s)!1 then
                return true;
        end if;
        if t eq Parent(t)!1 then
                return false;    // t eq 1 and s ne 1
        end if;
	if (#s gt #t) then
		return false;
	end if;
	subt := Subword(t, 1, #s);
	return subt eq s;
end function;
	
function MonQuotient(t, s)
/* 
          Input: elements s, t of the monoid, such that t = s*y.
	  Output : the suffix y.
*/

        assert(MonLeftDivides(s, t));
        if s eq Parent(s)!1 then
                return t;
        end if;
        if s eq t then
                return Parent(s)!1;
	end if;
	return Subword(t, #s+1, #t-#s);
end function;

// *********** FREE GROUP ALGEBRAS *************************************

function Monic(p)
/*        Input: a polynomial p of the algebra.
          Output: the monic polynomial which is obtained from p
                  by dividing it by the leading coefficient. If p=0
                  then the function returns 0.
*/
       poly := p;
       if not IsZero(poly) then
            lc:=LeadingCoefficient(poly);
            if lc ne 1 then
                 poly := (1/lc)*poly;
            end if;
       end if;
       return poly;
end function;

function Degree(poly)
/*        Input: a non-zero polynomial poly of the algebra.
          Output: the degree of poly.
*/
        if IsZero(poly) then
              print "Runtime error: undefined degree of the zero polynomial.";
              assert(false);
        end if;
        if IsScalar(poly) then
              return 0;
        end if;
        Supp := Support(poly);
        return #Supp[#Supp];
end function;

function LeadingLetter(poly)
/*
          Input: a polynomial poly.
          Output: the last letter of the leading power product of poly.
*/
        Supp := Support(poly);
        lpp := Supp[#Supp];
        return Subword(lpp,#lpp,1);
end function;

function LeftDivides(poly1,poly2)
/*
          Input: two polynomials poly1 and poly2.
          Output: returns true iff poly1 left-divides poly2.
*/
        if IsScalar(poly1) then
             if IsZero(poly1) then
                return false;
             else                       // poly1 is a non-zero scalar
                return true;
             end if;
        end if;
        if IsScalar(poly2) then       // now poly1 is non-scalar
             if IsZero(poly2) then
                return true;
             else                     
                return false;
             end if;
        end if;
        LTp1 := Support(poly1)[#Support(poly1)];   /* LTp1 is the leading
                                                      term of poly1 */
        if exists(term){pp : pp in Support(poly2) | 
            MonLeftDivides(LTp1,pp)} then
                return true;
        else
                return false;
        end if;
end function;

function Quotient(poly1,poly2)
/*
           Input: two polynomials poly1 and poly2.
           Output: the quotient of the division of poly1 by poly2.
*/
        if IsScalar(poly2) then
             if IsZero(poly2) then
                print "Runtime error in 'Quotient': division by zero.";
                assert(false);
             else                       // poly2 is a non-zero scalar
                return poly1/LeadingCoefficient(poly2);
             end if;
        end if;
        if IsScalar(poly1) then
             return Parent(poly1)!0;
        else                             // both polys are non-scalar
             LTp2 := Support(poly2)[#Support(poly2)];   /* LTp2 is the leading
                                                           term of poly2 */
             p1 := poly1;
             quot := Parent(p1)!0;
             Supp1 := Support(p1);
             while exists(term){pp : pp in Supp1 | MonLeftDivides(LTp2,pp)} do
                c := MonomialCoefficient(p1,term);
                d := LeadingCoefficient(poly2);
                monquot := MonQuotient(term,LTp2);
                m := (c/d)*Parent(p1)!monquot;
                quot := quot+m;
                p1 := p1 - poly2*m; 
                if IsScalar(p1) then
                    return quot;
                end if;
                Supp1 := Support(p1);
             end while;
             return quot;
        end if;
end function;

function LeftMod(poly1,poly2)
/*
           Input: two polynomials poly1 and poly2.
           Output: the remainder of the division of poly1 by poly2.
*/
        quot := Quotient(poly1,poly2);
        return poly1-poly2*quot;
end function;

function MultiLeftMod(poly,Polys)
/*
           Input: a polynomial poly and a set of polynomials Polys.
           Output: the remainder of the division of poly by the
                   members of Polys. The result depends on the order
                   of reductions (divisions), but at the end the 
                   polynomial cannot be reduced anymore.
                   Polys may contain zeros.
*/

        if #Polys eq 0 then
             return poly;
        end if;
        p1 := poly;
        while exists(divisor){p : p in Polys | (p1 ne Parent(p1)!0) and
           (LeftDivides(p,p1))} do
               p1 := LeftMod(p1,divisor);
        end while;
        return p1;
end function;

procedure OrbitReduce(poly,~Pair,~succeeded)
/*
          Input: a polynomial poly.
          Output: a pair Pair - the first (minimal) and second elements 
                  in the orbit of poly. If poly is 0 or monomial then 
                  succeeded becomes false.
*/
        if poly eq Parent(poly)!0 then
            zero := Parent(poly)!0;
            Pair := <zero,zero>;
            succeeded := false;
            return;
        end if;
        if #Support(poly) eq 1 then      // poly is monomial
            one := Parent(poly)!1;
            Pair := <one,one>;
            succeeded := false;
            return;
        end if;
        p2 := Monic(poly);
        repeat
            p1 := p2;
            p2 := p1*Parent(poly)!(LeadingLetter(p1))^-1;
        until p1 lt p2;
        Pair := <Monic(p1),Monic(p2)>;
        return;
end procedure;

procedure DivReduce(~poly,Seq,i,~succeeded)
/*
          Input: a sequence Seq, a polynomial poly and a position i.
          Output: the returned polynomial after trying to reduce poly once
                  with the elements of Seq which are in positions less
                  than i. The boolean succeeded becomes true if reduction 
                  was done.
*/
        succeeded := false;
        k := 1;
        while (not succeeded) and (k lt i) do
            q := Seq[k][1];
            if LeftDivides(q,poly) then
                poly := Monic(LeftMod(poly,q));
                succeeded := true;
            else
                q := Seq[k][2];
                if LeftDivides(q,poly) then
                    poly := Monic(LeftMod(poly,q));
                    succeeded := true;
                else
                    k := k+1;
                end if;
            end if;
        end while;
        return;
end procedure;

procedure GaussReduce(poly,~Pair,Seq,i,~succeeded)
/*
          Input: a polynomial poly, a sequence Seq and a position i.
          Output: the returned pair after trying to reduce the second
                  element in the orbit of poly by elements which are in 
                  the linear span of the elements of Seq of positions less
                  than i.  The boolean succeeded becomes true in case 
                  of reduction.
*/
       p1 := poly;
       let := (LeadingLetter(p1))^-1;
       p2 := p1*Parent(p1)!let;
       for k in [1..i-1] do
           q := Seq[k][1];
           Supp := Support(q);
           lpp := Supp[#Supp];
           leadingletter := Subword(lpp,#lpp,1);
           if leadingletter eq let then
               if lpp in Support(p2) then
                   c := MonomialCoefficient(p2,lpp);
                   d := LeadingCoefficient(q);
                   p2 := p2 - Parent(p2)!(c/d)*q;
               end if;
           else
               q := Seq[k][2];
               Supp := Support(q);
               lpp := Supp[#Supp];
               leadingletter := Subword(lpp,#lpp,1);
               if leadingletter eq let then
                   if lpp in Support(p2) then
                       c := MonomialCoefficient(p2,lpp);
                       d := LeadingCoefficient(q);
                       p2 := p2 - Parent(p2)!(c/d)*q;
                   end if;
               end if;
           end if;
       end for;
       if p2 lt p1 then
           p1 := p2;
           succeeded := true;
       end if;
       Pair := <Monic(p1),Monic(p2)>;
       return;
end procedure;

procedure InsertSeq(~Seq,Pair,~pos);
/*
          Input: a sorted sequence and a pair Pair which is not greater than
                 the element in position pos.
          Output: the new sequence after the element in position pos was
                  removed and the element Pair was added, and also the position
                  next to the position of Pair.
*/
       i := 1;
       while Seq[i][1] lt Pair[1] do
           i := i+1;
       end while;
       for j in [1..pos-i] do
           Seq[pos-j+1] := Seq[pos-j];
       end for;
       Seq[i] := Pair;
       pos := i+1;
       return;
end procedure;

procedure SortSeq(~S);
/*
          Input: a sequence S of pairs <p1,p2>.
          Output: S sorted with regard to the first element of each pair.
*/
       j := #S;
       while j gt 1 do
           for i in [1..j-1] do
               if S[i][1] gt S[i+1][1] then
                   p := S[i];
                   S[i] := S[i+1];
                   S[i+1] := p;
               end if;
           end for;
           j := j-1;
       end while;
       return;
end procedure;
 
procedure Reduce(~Seq,~i)
/*
          Input: a sorted sequence Seq and a position i.
          Output: the new sequence after the element in position i was
                  reduced with respect to the elements below it, and the
                  position of the next element to be reduced.
*/
       if i le 1 then
           i := i+1;
           return;
       end if;
       Pair := Seq[i];
       succeeded := true;
       while succeeded do
           DivReduce(~Pair[1],Seq,i,~succeeded);
           if not succeeded then   // Pair[1] is orbit-div reduced
               GaussReduce(Pair[1],~Pair,Seq,i,~succeeded);
           end if;
           if succeeded then   // Pair[1] was reduced
               OrbitReduce(Pair[1],~Pair,~succeeded);
           end if;
       end while;
       if Pair[1] eq Parent(Pair[1])!0 then
           Remove(~Seq,i);  // the null element is deleted
           return;
       end if;
       InsertSeq(~Seq,Pair,~i);
       return;
end procedure;

function GBasis(I)
/*
          Input: a right ideal I of a free group algebra.
          Output: a Groebner basis for I (relative to the ShortLex order),
                  consisting of pairs of the minimal elements in each orbit.
                  If I is trivial the empty sequence is returned.
*/
       Gens := Generators(I);
       if #Gens eq 0 then
           return [];
       end if;
       Basis := [];
       repeat
             ExtractRep(~Gens, ~poly);
             if poly ne Parent(poly)!0 then
                 mpoly := Monic(poly);
                 OrbitReduce(mpoly,~Pair,~succeeded);
                 if Pair[1] eq Parent(poly)!1 then
                     one := Parent(poly)!1;
                     return [<one,one>]; 
                                               // I is the whole algebra
                 end if;
                 Include(~Basis,Pair);
             end if;
       until #Gens eq 0;
       if #Basis eq 0 then
             return [];                // I is the zero ideal
       end if;
       SortSeq(~Basis);
       pos := 1;
       repeat
           Reduce(~Basis,~pos);
           if Basis[1][1] eq Parent(poly)!1 then
               one := Parent(poly)!1;
               return [<one,one>]; 
                                                // I is the whole algebra
           end if;
       until pos gt #Basis;
       return Basis;
end function;

function GroebnerBasis(I)
/* 
          Input: a right ideal I of a free group algebra.
          Output: a sorted Groebner basis for I (relative to the ShortLex 
                  order). If I is trivial the empty sequence is returned.
*/
       B := GBasis(I);
       if B eq [] then 
           return [];
       end if;
       if B[1][1] eq Parent(B[1][1])!1 then
           return [Parent(B[1][1])!1];
       end if;
       GB := [];
       for i in [1..#B] do
           Include(~GB,B[i][1]);
           Include(~GB,B[i][2]);
       end for;
       GB := Sort(GB);
       return GB;
end function;

function FreeSchreierBasis(I)
/*
          Input: a right ideal I of a free group algebra.
          Output: a sorted free Schreier basis for I (relative to the ShortLex
                  order). If I is trivial the empty set is returned.
*/
       B := GBasis(I);
       if B eq [] then 
           return [];
       end if;
       if B[1][1] eq Parent(B[1][1])!1 then
           return [Parent(B[1][1])!1]; 
       end if;
       FSB := [];
       for i in [1..#B] do
           Include(~FSB,B[i][1]);
       end for;
       FSB := Sort(FSB);
       return FSB;
end function;

function NormalForm(poly,GB)
/*
          Input: a polynomial poly and a Groebner basis GB (which is a
                 sequence of polynomials) for a right ideal I of a free
                 group algebra.
          Output: the normal form of poly modulo I (relative to the ShortLex
                  order).
*/
       if IsEmpty(GB) then       // I is the trivial ideal
           return poly;
       else
           return MultiLeftMod(poly,GB);
       end if;
end function;

function IsMember(poly,GB)
/*
          Input: a polynomial poly and a Groebner basis GB (which is a
                 sequence of polynomials) for a right ideal I of a free
                 group algebra.
          Output: returns true iff poly is in I.
*/
       nform := NormalForm(poly,GB);
       if nform eq Parent(nform)!0 then
            return true;
       else
            return false;
       end if;
end function;
       
function f(j)
       if j eq 1 then return 0;
           else return 1;
       end if;
end function;

procedure Description(I)
/*
          Input: a right ideal I of a free group algebra KG.
          Output: a description of I, Including a Groebner basis for I, the
                  codimension and the generating series of the cogrowth
                  function of I (the growth of the quotient KG/I).
*/
       print (I);
       GBasis := GroebnerBasis(I);
       if IsEmpty(GBasis) then       // I is the trivial ideal
           print "\nThe right ideal is the null ideal. \n";
           return;
       end if;
       if GBasis[1] eq Parent(GBasis[1])!1 then 
                                   // the right ideal is the whole algebra
           print "\nThe right ideal is the whole algebra. \n";
           return;
       end if;
       print "\nA canonical Groebner basis: ";
       for i in [1..#GBasis] do
                 print GBasis[i];
       end for;
       List := [];
       for gen in GBasis do
           deg := Degree(gen);
           Append(~List,deg);
       end for;
       maxdeg := Max(List);
       DegList := [];
       for i in [1..maxdeg] do
           DegList[i] := 0;
       end for;
       for i in [1..#List] do
           deg := List[i];
           DegList[deg] := DegList[deg]+1;
       end for;
       rank := #Generators(Parent(GBasis[1]));
       dim := 1; codim:=1;
       print "\nThe generating series of the cogrowth of the right ideal:";
       string := "1";
       for j in [1..maxdeg-1] do
           dim := dim*(2*rank - f(j)) - DegList[j];
           string := string * " + " * IntegerToString(dim) * "t^" * 
                     IntegerToString(j);
           codim := codim + dim;
       end for;
       dim := dim*(2*rank - f(maxdeg)) - DegList[maxdeg];
       if dim eq 0 then
           print "    f(t) = ",string;
           print "\nThe right ideal is of codimension f(1) =",codim,"\n";
       else 
           print "    f(t) = ",string * " + (" * IntegerToString(dim) * "t^" * 
           IntegerToString(maxdeg) * ")/(1 - "*IntegerToString(2*rank-1)*"t)";
           print "\nThe right ideal is of infinite codimension\n";
       end if;
       return;
end procedure;



// ********************* FREE ALGEBRAS **********************************
/*
An algorithm for constructing a free Groebner basis for a right ideal of
a free associative algebra.
The procedures here are in additions to the ones needed for the free
group algebra case.

*/

procedure FAInsertSeq(~Seq,poly,~pos);
/*
          Input: a sorted sequence and a polynomial poly which is not greater
                 than the element in position pos.
          Output: the new sequence after the element in position pos was
                  removed and the element poly was added, and also the position
                  next to the position of poly.
*/
       i := 1;
       while Seq[i] lt poly do
           i := i+1;
       end while;
       for j in [1..pos-i] do
           Seq[pos-j+1] := Seq[pos-j];
       end for;
       Seq[i] := poly;
       pos := i+1;
       return;
end procedure;


procedure FADivReduce(~poly,Seq,i,~succeeded)
/*
          Input: a sequence Seq, a polynomial poly and a position i.
          Output: the returned polynomial after trying to reduce poly once
                  with the elements of Seq which are in position < i.
                  The boolean succeeded becomes true if reduction was done.
*/
        succeeded := false;
        k := 1;
        while (not succeeded) and (k lt i) do
            q := Seq[k];
            if LeftDivides(q,poly) then
                poly := Monic(LeftMod(poly,q));
                succeeded := true;
            else
                k := k+1;
            end if;
        end while;
        return;
end procedure;

procedure FAReduce(~Seq,~i)
/*
          Input: a sorted sequence Seq and a position i.
          Output: the new sequence after the element in position i was
                  reduced with respect to the elements below it, and the
                  position of the next element to be reduced.
*/
       if i le 1 then
           i := i+1;
           return;
       end if;
       poly := Seq[i];
       succeeded := true;
       while succeeded do
           FADivReduce(~poly,Seq,i,~succeeded);
           if poly eq Parent(poly)!0 then
               succeeded := false;
           end if;
       end while;
       if poly eq Parent(poly)!0 then
           Remove(~Seq,i);  // the null element is deleted
           return;
       end if;
       FAInsertSeq(~Seq,poly,~i);
       return;
end procedure;

function FAGroebnerBasis(I)
/*
          Input: a right ideal I of a free algebra.
          Output: a sorted Groebner basis for I (relative to the ShortLex
                  order). If I is trivial the empty sequence is returned.
*/
       Gens := Generators(I);
       if #Gens eq 0 then
             return [];
       end if;
       Basis := [];
       repeat
             ExtractRep(~Gens, ~poly);
             if poly ne Parent(poly)!0 then
                 mpoly := Monic(poly);
                 if mpoly eq Parent(poly)!1 then
                     return [Parent(poly)!1];  // I is the whole algebra
                 end if;
                 Include(~Basis,mpoly);
             end if;
       until #Gens eq 0;
       if #Basis eq 0 then
             return [];                // I is the zero ideal
       end if;
       Sort(~Basis);
       pos := 1;
       repeat
           FAReduce(~Basis,~pos);
           if Basis[1] eq Parent(poly)!1 then
               return [Parent(poly)!1];        // I is the whole algebra
           end if;
       until pos gt #Basis;
       GB := Sort(Basis);
       return GB;
end function;

procedure FADescription(I)
/*
          Input: a right ideal I of a free algebra A = K<X>.
          Output: a description of I, Including a free Groebner basis for
                  I, its codimension and the generating series of the
                  cogrowth function of I (the growth of the quotient A/I).
*/
       print (I);
       GBasis := FAGroebnerBasis(I);
       if IsEmpty(GBasis) then       // I is the trivial ideal
           print "\nThe right ideal is the null ideal.\n";
           return;
       end if;
       print "\nA canonical free Groebner basis: ";
       print "   ", GBasis;
       g := Rep(GBasis);
       if g eq Parent(g)!1 then
           print "\nThe right ideal is the whole algebra.\n";
           return;
       end if;
       List := [];
       for gen in GBasis do
           deg := Degree(gen);
           Append(~List,deg);
       end for;
       maxdeg := Max(List);
       DegList := [];
       for i in [1..maxdeg] do
           DegList[i] := 0;
       end for;
       for i in [1..#List] do
           deg := List[i];
           DegList[deg] := DegList[deg]+1;
       end for;
       rank := #Generators(Parent(g));
       dim := 1; codim:=1;
       print "\nThe generating series of the cogrowth of the right ideal:";
       string := "1";
       for j in [1..maxdeg-1] do
           dim := dim*rank - DegList[j];
           string := string * " + " * IntegerToString(dim) * "t^" * 
                     IntegerToString(j);
           codim := codim + dim;
       end for;
       dim := dim*rank - DegList[maxdeg];
       if dim eq 0 then
           print "    f(t) = ",string;
           print "\nThe right ideal is of codimension f(1) =",codim,"\n";
       else 
           print "    f(t) = ",string * " + (" * IntegerToString(dim) * "t^" * 
           IntegerToString(maxdeg) * ")/(1 - " * IntegerToString(rank) * "t)";
           print "\nThe right ideal is of infinite codimension\n";
       end if;
       return;
end procedure;

 

// ************************ FREE GROUPS *********************************
/*
Schreier basis for a finitely generated subgroup of a free group.
Also the rank and index of the subgroup, 
membership in the subgroup and normal form modulo the subgroup.
And functions for the coset graphs of subgroups and the intersection
of subgroups.
The procedures are in addition to the ones for free group algebras.
*/

function RightIdeal(F,H)
/*
          Input: a finitely generated free group F and a finitely generated
                 subgroup H.
          Output: the right ideal of the group algebra KF, where K is the
                  field of 2 elements, which is generated by the elements
                  g-1, where g runs over the group generators of H.
*/
       K := GF(2);
       A := FreeAlgebra(K,F);
       Gens := Generators(H);
       if #Gens eq 0 then
           I := rideal<A | {}>;
           return I;
       end if;
       PG :={};
       for g in Gens do
           pg := A!g-A!1;  // mapping the group generators to the group algebra
           Include(~PG,pg);
       end for;
       I:= rideal<A | PG>;
       return I;
end function;

function SchreierBasis(F,H)
/*
          Input: a finitely generated free group F and a finitely generated
                 subgroup H.
          Output: a Schreier (Nilsen-reduced) basis for H (relative to a
                  ShortLex ordering). If H is trivial the empty list is
                  returned.
*/
       I:= RightIdeal(F,H);
       FSB := FreeSchreierBasis(I);
       SB := [];
       for pg in FSB do
           Supp := Support(pg);
           g := Supp[2]*(Supp[1])^-1;  // mapping back to the group
           if g gt g^-1 then
               g := g^-1;
           end if;
           Include(~SB,g);
       end for;
       SB := Sort(SB);
       return SB;
end function;

function FGNormalForm(g,F,H)
/*
          Input: a finitely generated free group F, a finitely generated
                 subgroup H, and  an element g of F.
          Output: the normal form of g modulo H (relative to the ShortLex
                  ordering).
*/
       I:= RightIdeal(F,H);
       GB := GroebnerBasis(I);
       if IsEmpty(GB) then       // I is the trivial ideal
           return g;
       else
           K := GF(2);
           A := FreeAlgebra(K,F);
           pg := Parent(GB[1])!g-Parent(GB[1])!1;
           Inform := MultiLeftMod(pg,GB);
           if IsZero(Inform) then
               return F!1;
           else
               Supp := Support(Inform);
               nform := Supp[2]*(Supp[1])^-1;
           end if;
       end if;
       return nform;
end function;

function FGIsMember(g,F,H)
/*
          Input: a finitely generated free group F, a finitely generated
                 subgroup H, and  an element g of F.
          Output: returns true iff g is in I.
*/
       nform := FGNormalForm(g,F,H);
       if nform eq F!1 then
            return true;
       else
            return false;
       end if;
end function;
       
function FGIndex(F,H)
/*
          Input: a finitely generated free group F and a finitely generated
                 subgroup H.
          Output: the index of H in F. If the index is infinite then 0 is
                  returned.
                  The index of H equals the codimension of the associated 
                  "right augmentation ideal" of the corresponding group 
                  algebra, which is what we compute here.
*/
       I := RightIdeal(F,H);
       GBasis := GroebnerBasis(I);
       if IsEmpty(GBasis) then       // I is the trivial ideal
           return 0;
       end if;
       List := [];
       for gen in GBasis do
           deg := Degree(gen);
           Append(~List,deg);
       end for;
       maxdeg := Max(List);
       DegList := [];
       for i in [1..maxdeg] do
           DegList[i] := 0;
       end for;
       for i in [1..#List] do
           deg := List[i];
           DegList[deg] := DegList[deg]+1;
       end for;
       rank := #Generators(F);
       dim := 1; codim:=1;
       for j in [1..maxdeg-1] do
           dim := dim*(2*rank - f(j)) - DegList[j];
           codim := codim + dim;
       end for;
       dim := dim*(2*rank - f(maxdeg)) - DegList[maxdeg];
       if dim eq 0 then
           return codim;
       else 
           return 0;
       end if;
end function;

function FGRank(F,H)
/*
          Input: a finitely generated free group F and a finitely generated
                 subgroup H.
          Output: the rank of H.
*/
       SB := SchreierBasis(F,H);
       return #SB;
end function;

function LetterToIndex(letter)
/*
          Input: a letter which is a generator or an inverse of a generator
                 of a group G.
          Output: an integer, between 1 and twice the number of generators
                  of G, which corresponds to letter.
*/
       G := Parent(letter);
       n := #Generators(G);
       i := 1;
       while i le n do
           if letter eq G.i then
               return 2*i-1;
           elif letter eq G.i^-1 then
               return 2*i;
           end if;
           i +:= 1;
       end while;
end function;

function IndexToLetter(G,index)
/*
          Input: a group G and an integer index which is between 1 and twice 
                 the number of generators of G.
          Output: a letter which is a generator or an inverse of a generator
                 of G, which corresponds to index.
*/
       n := #Generators(G);
       assert index le 2*n;
       i := (index + 1) div 2;
       if IsOdd(index) then
           return G.i;
       else
           return G.i^-1;
       end if;
end function;

function Pos(CG,w);
/*
          Input: a coset graph CG and a word w.
          Output: the position in CG of the vertex whose label is w. 
                  If w is not in CG then #CG+1 is returned.
*/
       pos := 1;
       while pos le #CG and w ne CG[pos]`label do
           pos +:= 1;
       end while;
       return pos;
end function;

procedure AddVertex(~CG,w)
/*
          Input: a coset graph CG and a word w.  
          Output: the coset graph after a new entry, with vertex label w,
                  is appended at the end of it.
*/
       n := #Generators(Parent(w));
       Zeros := [ 0 : j in [1..2*n]];
       vertex := recformat<label,neighbours>;
       entry := rec<vertex | label := w, neighbours := Zeros>;
       Append(~CG,entry);
end procedure;

procedure AddV(~CG,~pos,w)
/*
          Input: a coset graph CG and a word w.  
          Output: the coset graph and the position in it of the vertex with
                  label w. If such a vertex does not exist in CG then it is
                  appended at the end of it.
*/
       pos := Pos(CG,w);
       if pos gt #CG then
           AddVertex(~CG,w);
       end if;
end procedure;

procedure UpdateGraph(~CG,pos1,pos2,let);
/*
          Input: a coset graph CG, two indexes pos1 and pos2, and a letter
                 let.
          Output: updating CG so that the edge in direction let goes from
                  the vertex in position pos1 to the vertex in position
                  pos2, and the edge let^{-1} goes in the opposite direction.
*/
       ind1 := LetterToIndex(let);
       CG[pos1]`neighbours[ind1] := pos2;
       ind2 := LetterToIndex(let^-1);
       CG[pos2]`neighbours[ind2] := pos1;
end procedure;

procedure MultiUpdateGraph(~CG,w);
/*
          Input: a coset graph CG and a word w.
          Output: updating CG by adding (if necessary) all the prefixes of w
                  as vertices of CG with the corresponding edges.
*/
       if w ne Parent(w)!1 then
           u := Subword(w,1,#w-1);
           AddV(~CG,~posu,u);
           posw := Pos(CG,w);
           let := Subword(w,#w,1);
           ind := LetterToIndex(let);
           if IsZero(CG[posu]`neighbours[ind]) then
               UpdateGraph(~CG,posu,posw,let);
               MultiUpdateGraph(~CG,u);
           end if;
       end if;
end procedure;

function CosetGraph(F,H)
/*
          Input: a finitely generated free group F and a finitely generated
                 subgroup H.
          Output: the coset graph CG of H with respect to the generators of F.
                  CG is in the form of a sequence, where each entry contains an
                  element of F, which is the label of a vertex v, and
                  2*#Generators(F) integers which give the indices of the
                  vertices adjacent to v. The labels of the vertices form
                  a Schreier transversal for H (relative to a ShortLex
                  ordering). If an edge e adjoins the vertex v to a full
                  (infinite) Schreier subtree then the corresponding integer
                  in the coset graph gets the value 0, and the whole subtree
                  is omitted. Thus, even when H is of infinite index we get
                  all the information about its coset table.
*/
       I := RightIdeal(F,H);
       FSB := FreeSchreierBasis(I); // if H is trivial FSB is empty
       CG := [];
       AddVertex(~CG,F!1);
       for poly in FSB do 
           supp := Support(poly);
           w := supp[2];
           letter := Subword(w,#w,1);
           v1 := Subword(w,1,#w-1);
           v2 := supp[1];
           AddV(~CG,~pos1,v1);
           AddV(~CG,~pos2,v2);
           UpdateGraph(~CG,pos1,pos2,letter);
           MultiUpdateGraph(~CG,v1);
           MultiUpdateGraph(~CG,v2);
       end for;
       return CG;
end function;
    
function CosetGraphToGens(F,CG)
/*
          Input: a finitely generated free group F and a coset graph CG of
                 a finitely generated subgroup H.
          Output: a set of generators of H.
*/
       if IsEmpty(CG) then
           print "Error: empty coset graph";
           assert false;
       end if;
       n := #Generators(F);
       Gens := {F!1};
       for v in CG do
           for i in [1..n] do
               pos := v`neighbours[2*i-1];
               if pos ne 0 then
                   g1 := v`label * F.i;
                   g2 := CG[pos]`label;
                   g := g1 * g2^-1;
                   Gens := Include(Gens,g);
               end if;
           end for;
       end for;
       if #Gens gt 1 then
           Gens := Exclude(Gens,F!1);
       end if;
       return Gens;
end function;

procedure AddVertexPair(~CG,w,Pair)
/*
          Input: a coset graph CG and a word w.  
          Output: the coset graph after a new entry, with vertex label w
                  and label pair Pair, is appended at the end of it.
*/
       n := #Generators(Parent(w));
       Zeros := [ 0 : j in [1..2*n]];
       vertex := recformat<label,labelpair,neighbours>;
       entry := rec<vertex | label:=w,labelpair:=Pair,neighbours:=Zeros>;
       Append(~CG,entry);
end procedure;

procedure CGraphIntersect(F,~CG,~STPairs,CG1,CG2,w,Pair)
/*
          Input: a finitely generated free group F, two cosets graphs CG1
                 and CG2 of two finitely generated subgroups of F, a label w
                 and a pair Pair=<w1,w2> of labels of vertices of CG1,CG2
                 respectively.
          Output: the component CG of the graph CG1xCG2, which includes the
                  vertex with label pair <w1,w2> (which is also labelled
                  with w), and the sequence STPairs of the pairs of vertices
                  of CG1 and CG2 which form the vertices of CG. The graph CG
                  is formed by a simultaneous bredth-first travel on CG1 and
                  CG2, starting at <w1,w2>.
*/
       n := #Generators(F);
       pos1 := Pos(CG1,Pair[1]); pos2 := Pos(CG2,Pair[2]);
       assert (pos1 le #CG1) and (pos2 le #CG2);
       CG := [];
       AddVertexPair(~CG,w,Pair);
       STPairs := []; STPairs[1] := <pos1,pos2>;
       FrontBegin := 1; FrontEnd := 1;
       while FrontBegin le FrontEnd do
           for i in [FrontBegin..FrontEnd] do
               p1 := STPairs[i][1]; p2 := STPairs[i][2];
               ns1 := CG1[p1]`neighbours; ns2 := CG2[p2]`neighbours;
               for j in [1..2*n] do
                   v1 := ns1[j]; v2 := ns2[j];
                   if v1 ne 0 and v2 ne 0 then
                       pos := Position(STPairs,<v1,v2>);
                       if IsZero(pos) then
                           pos := #STPairs+1;
                           STPairs[pos] := <v1,v2>;
                           let := IndexToLetter(F,j);
                           v := CG[i]`label *let;
                           pair := <CG1[v1]`label,CG2[v2]`label>;
                           AddVertexPair(~CG,v,pair);
                       end if;
                       CG[i]`neighbours[j] := pos;
                   end if;
               end for;
           end for;
           FrontBegin := FrontEnd+1; FrontEnd := #STPairs;
       end while;
end procedure;

intrinsic CosetGraphIntersect(F::GrpFP, H1::GrpFP, H2::GrpFP) -> .
{Input: a finitely generated free group F and two finitely
generated subgroups H1 and H2;
Output: a coset graph CG for the intersection of H1 and H2.
This graph is the component of the graph CG1xCG2 which
includes the vertex (1,1) (where CG1, CG2 are the
coset graphs of H1, H2 respectively). The vertex labels
of CG are minimal with respect to the Shortlex ordering
with regard to the generators of F
}
       CG1 := CosetGraph(F,H1);
       CG2 := CosetGraph(F,H2);
       CG := [];
       CGraphIntersect(F,~CG,~STPairs,CG1,CG2,F!1,<F!1,F!1>);
       return CG;
end intrinsic;

intrinsic FGIntersect(F::GrpFP, H1::GrpFP, H2::GrpFP) -> GrpFP
{Input: a finitely generated free group F and two finitely
generated subgroups H1 and H2;
Output: the subgroup of F which is the intersection of H1 and H2
}
       CG := CosetGraphIntersect(F,H1,H2);
       Gens := CosetGraphToGens(F,CG);
       return  sub< F | Gens >;
end intrinsic;

function CosetGraphCarProduct(F,H1,H2)
/*
          Input: a finitely generated free group F and two finitely
                 generated subgroups H1 and H2.
          Output: part of the graph CG = CG1xCG2 which contains all
                  the cycles of CG, where CG1, CG2 are the coset
                  graphs of H1, H2 respectively.
*/
       CG1 := CosetGraph(F,H1); CG2 := CosetGraph(F,H2);
       vers := [ <i,j> : i in [1..#CG1], j in [1..#CG2] ];
       CarProd := []; comp := 0;
       while not IsEmpty(vers) do
           comp +:= 1;
           w := F!1;
           pair := vers[1];
           w1 := CG1[pair[1]]`label; w2 := CG2[pair[2]]`label;
           CarProd[comp] := [];
           CGraphIntersect(F,~CarProd[comp],~STPairs,CG1,CG2,w,<w1,w2>);
           for p in STPairs do
               vers := Exclude(vers,p);
           end for;
       end while;
       return CarProd;
end function;

intrinsic MultiRank(F::GrpFP, H1::GrpFP, H2::GrpFP) -> .
{Input: a finitely generated free group F and two finitely
     generated subgroups H1 and H2;
Output: the expression computed for the generalized Hanna
      Neumann conjecture
}
       MRank := 0;
       CGCP := CosetGraphCarProduct(F,H1,H2);
       for i in [1..#CGCP] do 
           Gens := CosetGraphToGens(F,CGCP[i]);
           H := sub< F | Gens >;    
           rank := FGRank(F,H);
           if rank gt 1 then
               MRank +:= rank-1;
           end if;
       end for;
       return MRank;
end intrinsic;
