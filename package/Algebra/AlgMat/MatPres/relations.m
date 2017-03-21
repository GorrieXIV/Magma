freeze;

import "show.m"     : show_time;
import "word.m"     : filtered_basis_radical;
import "word.m"     : filtered_basis_field_generators;

//*********************************************************************

flatten := func<J, f | [f(x) : x in J[i][j], i, j in [1 ..#J]]>;

//*********************************************************************

function map(J, f)

        r := #J;
        T := Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]);
        for i := 1 to r do
                for j := 1 to r do
                        T[i][j] := [f(x) : x in J[i][j]];
                end for;
        end for;

        return T;
end function;

//**********************************************************************

function condense(A)

     uu := CondensationMatrices(A);
     c_l := uu[1];
     c_r := uu[2];
     dd := [Rank(x): x in PrimitiveIdempotents(A)];
     dim_c := &+dd;

        return func< m | c_l * m * c_r >, dim_c, dd;

end function;

//*******************************************************************

function basic(A, beta, g, J)

        K := CoefficientRing(A);
        f, dim_c, dd := condense(A);
        beta_c := [f(x): x in beta];
        J_gens_c := flatten(J, f);
        B := MatrixAlgebra<K, dim_c | [x : x in beta_c cat J_gens_c]>;
        BG := Generic(B);
        return B, [BG!x : x in beta_c], map(J, func<x | BG!f(x)>), dd;

end function;

//*******************************************************************

graph := func< f | [<x, f(x)> : x in Domain(f) ]>;

//*********************************************************************

rel_seq := func< rels | [LHS(x) - RHS(x) : x in rels] >;

//**********************************************************************

procedure R(~rels, new)
	
	for r in new do
		if LHS(r) ne RHS(r) then
				vprint Presentation: "Adding relation", r;
			Append(~rels, r);
		end if;
	end for;

end procedure;

//*********************************************************************

procedure semisimple_relations(
	isB, r, h_prime, n, q, B, T, ~rels)

	//	relations for each matrix component in the semisimple part

	if not isB then

		R(~rels, [T[i]^n[i] * B[i] = B[i] : i in [1..r]]);
		R(~rels, [B[i] * T[i]^n[i] = B[i] : i in [1..r]]);
		R(~rels, [T[i]^n[i] * T[i] = T[i] : i in [1..r]]);
		R(~rels, [T[i] * T[i]^n[i] = T[i] : i in [1..r]]);
		R(~rels, 
		[B[i] * T[i]^k * B[i] = 0 : k in [1..n[i]-1], i in [1..r]]);
	end if;

	if isB then
		R(~rels, [ B[i]^(q[i]-1) * B[i] = B[i] : i in [1..r]]);
	else
		R(~rels, [
		&+[T[i]^(n[i]-j) * B[i]^(q[i]-1) * T[i]^j : j in [1..n[i]]] 
					= T[i]^n[i] : i in [1..r] ]);
	end if;

	R(~rels, [Evaluate(h_prime[i], B[i]) = 0 : i in [1..r]]);

	//	orthogonality relations in the semisimple part

	R(~rels, [B[i] * B[j] = 0 : i, j in [1..r] | i ne j]);

	if not isB then
		R(~rels, [T[i] * T[j] = 0 : i, j in [1..r] | i ne j]);
		R(~rels, [B[i] * T[j] = 0 : i, j in [1..r] | i ne j]);
		R(~rels, [T[i] * B[j] = 0 : i, j in [1..r] | i ne j]);
	end if;

        // identity relation

	if not isB then 
          Append(~rels, 
                 &+[
                    &+[
                       (T[i]^j)*(B[i]^(q[i]-1))*(T[i]^(n[i]-j)): 
		              j in [ 1 .. n[i]]] : 
                                  i in [1 .. r]] 
                                 - Parent(B[1])!1 = 0);
	else 
          Append(~rels, &+[B[i]^(q[i]-1): i in [1 .. r]] - Parent(B[1])!1 = 0);
	end if;

end procedure;

procedure cross_relations(isB, r, G, n, q, B, T, 
			J_gen, CV, CF, backmap, basis, ~rels, d)

	//	identity relations between the semisimple part and J(A)

	for i := 1 to r do
		for j := 1 to r do

		R(~rels,
			[B[i]^(q[i]-1) * G(y) = G(y)	: y in J_gen[i][j]]);
			R(~rels,
			[G(y) * B[j]^(q[j]-1) = G(y)	: y in J_gen[i][j]]);

			if not isB then
				R(~rels, 
			[T[i]^n[i] * G(y) = G(y)	: y in J_gen[i][j]]);
				R(~rels, 
			[G(y) * T[j]^n[j] = G(y)	: y in J_gen[i][j]]);
			end if;

		end for;
	end for;

	//	orthogonality relations between the semisimple part and J(A)

	for i := 1 to r do
		for j := 1 to r do

			R(~rels, 
		[B[k]*G(y) = 0 : k in [1..r], y in J_gen[i][j] | k ne i]);
			R(~rels, 
		[G(y) * B[k] = 0 : k in [1..r], y in J_gen[i][j] | k ne j]);

			if not isB then	
				R(~rels, 
		[T[k]*G(y) = 0 : k in [1..r], y in J_gen[i][j] | k ne i]);
				R(~rels, 
		[G(y)*T[k] = 0 : k in [1..r], y in J_gen[i][j] | k ne j]);
			end if;

		end for;
	end for;

	//	scaling relations from semisimple part on J(A)

	P := Domain(CF);
	J := KMatrixSpaceWithBasis(basis);
	for i := 1 to r do
		for j := 1 to r do
			for x in J_gen[i][j] do
                            if d[i] eq 1 then 
				lhs := P.i * G(x);
                                a := exists(t){s:s in BaseRing(CV)| 
                                       CV!CF(lhs) eq s*CV!CF(G(x)) };
                                R(~rels, [lhs = t*G(x)]);
                            else
                               lhs := P.i * G(x);
                                C := Coordinates(J, CV!CF(lhs));
                        w := &+[C[i] * backmap(basis[i]) : i in [1..#C]];
                                R(~rels, [lhs = w]);
                            end if;
                            if d[j] eq 1 then 
                                lhs := G(x) * P.j;
                                a := exists(t){s: s in BaseRing(CV)| 
                                        CV!CF(lhs) eq s*CV!CF(G(x))};
				R(~rels, [lhs = t*G(x)]);
                            else
                                lhs := G(x) * P.j;
                                C := Coordinates(J, CV!CF(lhs));
                        w := &+[C[i] * backmap(basis[i]) : i in [1..#C]];
                                R(~rels, [lhs = w]);
                            end if;
			end for;
		end for;
	end for;

end procedure;


//*****************************************************************

MatrixToVector := function(M);

ZM := KMatrixSpace(BaseRing(M),1, Nrows(M)*Ncols(M))!0;
for i := 1 to Nrows(M) do
InsertBlock(~ZM,M[i], 1, (i-1)*Ncols(M)+1);
end for;

return ZM[1];

end function;

//*****************************************************************

Generators_Relations := function(L);

// L is a list of matrices or elements which can be added and 
// multiplied. The elements in L must be nilpotent. Indeed, the 
// monoid they generate must be nilpotent. 

ff := BaseRing(L[1]);
ll := Nrows(L[1])^2;
F := FreeAlgebra(ff, #L);
phi := hom<F -> Parent(L[1])| L>;
I := ideal<F|>;      // the ideal of leading monomials
S := [];             // the list of relations
LM := [];            // the leading monomials of the relations
                                                 //print "B";
GG := [F.i: i in [1 .. Rank(F)]];
MM := [];           // the monomials and matrices that don't go to zero
UU := [];           // the monomials that go to zero
n := 0;
flag := true;
KM := KMatrixSpace(BaseRing(L[1]), Nrows(L[1]), Nrows(L[1]));
NMM := [];          // the list of monomials that will be modified and 
                    // altered for each step
while flag do 
   n := n+1;
   if n eq 1 then 
      NMM := [<GG[i],L[i],MatrixToVector(L[i])>: i in [1 .. #L]]; 
                                        // the degree 1 list of mons and mats
      MM1 := NMM;
      MATminus := KMatrixSpace(ff,#MM1,ll)!0;
      for i := 1 to #MM1 do
	 MATminus[i] := MM1[i][3];
      end for;
      MM := MM1;
      NMM := MM1;
      NGG := GG;
   else 
      flag := false;
      MMn := [];  // degree n mons and mats to be weeded out
      for x in NMM do
         for y in MM1 do
            z := x[1]*y[1];
            if z notin I then 
               w := x[2]*y[2];
               if w ne 0 then 
                  Append(~MMn, <z,w, MatrixToVector(w)>);
               else 
                  Append(~LM,z);
                  Append(~S,z);
               end if;
            end if;
         end for;
      end for;
      if #MMn ne 0 then
         NGG := [x[1]: x in MMn] cat NGG;
         MATn := KMatrixSpace(ff,#MMn,ll)!0;
         for i := 1 to #MMn do
	    MATn[i] := MMn[i][3];
         end for;
         MAT := VerticalJoin(MATn, MATminus);
         NS := NullSpace(MAT);
         if Dimension(NS) ne 0 then
            B := Basis(NS);
            RM := [];
            for x in B do
               h := &+[x[j]*NGG[j]: j in [1 .. #NGG]];
               k := LeadingMonomial(h);
               c := Index(NGG,k);
               Append(~RM,c);
               Append(~S,h);
               Append(~LM,k);
            end for;
            Sort(~RM);
            for i := #RM to 1 by -1 do
               Remove(~NGG,RM[i]);
               Remove(~MMn,RM[i]);
            end for;
         end if;
         NMM := MMn;
         MATn := KMatrixSpace(ff,#MMn,ll)!0;
         for i := 1 to #MMn do
            MATn[i] := MMn[i][3];
         end for;
         MATminus := VerticalJoin(MATn,MATminus);
         I := ideal<F|LM>;
         MM := NMM cat MM;
      end if;
      if #MMn ne 0 then 
         flag := true;
      end if;
   end if;
end while;
J := ideal<F|S>;

         return F, J, phi, MM;

end function;

//*********************************************************************

procedure K_basis(A, offset, V, FF, gens_J, 
	      	~rels, ~backmap, ~basis)

	P := Domain(FF);
	Q, J := Generators_Relations(gens_J);
	P_embed := hom< Q -> P | [P.(i+offset) : i in [1..#gens_J]]>;
	rels := rels cat [P_embed(x) = 0:x in Basis(J)];  
	S := Q/J;
	S_embed := hom< S -> P | [P.(i+offset) : i in [1..#gens_J]]>;
	mb := MonomialBasis(S) diff {1};
	emb := [S_embed(w) : w in mb];
	basis := [ V!FF(w) : w in emb];	

	if 1 eq 1 then
	    lhs := {@ V!FF(w): w in emb @};
	    assert #lhs eq #emb;
	    backmap := map<Universe(basis) -> P | x :-> emb[Index(lhs, x)]>;
	else
	    ibasis := {@ x: x in basis @};
	    im := [<V!FF(w), w> : w in emb];
	    backmap := map<ibasis -> P | im>;
	end if;

end procedure;

//*******************************************************************

function relations(A, beta, tau, g, J_gen, h_prime, n, d, q)

	r := #n;
	K := CoefficientRing(A);
	V := KMatrixSpace(K, Degree(A), Degree(A));
	gens_J := flatten(J_gen, func<x | V!x>);
	isB := &and[n[i] eq 1 : i in [1..r]];
	
	if isB then
		P := FreeAlgebra(K, r + #gens_J);
		AssignNames(~P, 
			["b_" cat IntegerToString(i) : i in [1..r]] cat
			["z_" cat IntegerToString(i) : i in [1..#gens_J]]);
		B := [P.i : i in [1..r]];
                T := [];
		J := [P.i : i in [r+1..r+#gens_J]];
	else
		P := FreeAlgebra(K, 2*r + #gens_J);
		AssignNames(~P, 
			["b_" cat IntegerToString(i) : i in [1..r]] cat
			["t_" cat IntegerToString(i) : i in [1..r]] cat
			["z_" cat IntegerToString(i) : i in [1..#gens_J]]);
		B := [P.i : i in [1..r]];
		T := [P.i : i in [r+1..2*r]];
		J := [P.i : i in [2*r+1..2*r+#gens_J]];
	end if;

	beta := [Matrix(x): x in beta];
	tau := [Matrix(x): x in tau];
	F := hom< P -> Generic(A) | [beta[i] : i in [1..#B]] cat   
                    [tau[i] : i in [1..#T]] cat gens_J>;
	G := map< Seqset(gens_J) -> P | 
		[<gens_J[i], P.(#B+#T+i)> : i in [1..#gens_J]]>;

	rels := [];

	t := Cputime();
	semisimple_relations(isB, r, h_prime, n, q, B, T, ~rels);
	show_time("SemiSimple", Cputime(t));

		vprint Presentation: "Number of semisimple relations", #rels;

	l := #rels;
	t := Cputime();
 	CA, cB, x, dd := basic(A, beta, g, J_gen);
	GCA := Generic(CA);
	//vprint Presentation: "degree CA", Degree(CA);
	cJg := flatten(x, func<x|x>);
	CV := KMatrixSpace(K, Degree(CA), Degree(CA));
	CF := hom< P -> GCA | [GCA!x : x in cB] cat 
		[0:x in T] cat [GCA!x : x in cJg]>;
        if #gens_J eq 0 then 
          return P, rel_seq(rels), 
                      Seqlist([Seqlist([[] : i in [1..r]]) : j in [1..r]]), 
                      filtered_basis_field_generators(dd, cB);
        end if;

	K_basis(CA, #cB+#T, CV, CF, cJg, ~rels, ~backmap, ~basis);
	show_time("K-basis", Cputime(t));

		vprint Presentation: "Number of K-Basis relations", #rels - l;

	if isB then
		A_prime := sub< GCA | cB >;

/*
"CA gens DiagonalBlocksStructure:",
    [DiagonalBlocksStructure(CA.i): i in [1..Ngens(CA)]];
"cJg DiagonalBlocksStructure:", [DiagonalBlocksStructure(x): x in cJg];
"Get ideal basis"; time
*/

		I := ideal< CA | cJg >;
			vprint Presentation: "Dim A", Dimension(CA);
			vprint Presentation: "Dim A'", Dimension(A_prime);
			vprint Presentation: "Dim J(A)", Dimension(I);
			vprint Presentation: "Dim A' meet J(A)", 
				Dimension(A_prime meet I);
		error if Dimension(A_prime) + Dimension(I) 
					ne Dimension(CA), "sum dim";
		error if Dimension(A_prime meet I) ne 0, "meet";
	end if;

	l := #rels;
	t := Cputime();
	cross_relations(isB, r, G, n, q, B, T, J_gen, 
		CV, CF, backmap, basis, ~rels, d);
	show_time("Cross", Cputime(t));
		vprint Presentation: "Number of cross relations", #rels-l;
		vprint Presentation: "Total number of relations", #rels;

           return P, rel_seq(rels), filtered_basis_radical(dd, basis, backmap),
                          filtered_basis_field_generators(dd, cB);
					
end function;

