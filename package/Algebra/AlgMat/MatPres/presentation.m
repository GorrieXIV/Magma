freeze;

import "radical.m"    : ChangeOfBasisMatrixA,ChangeOfBasisMatrixB,
       NeededIndices,NormalFormA,BasisForRadical_i_ne_j ,PowersOfBetaBar ,
       PowersOfBeta,BasisForRadical_i_i,RadicalSquared,nprune,
       radical_generators;

import "relations.m"  : R,graph,rel_seq,semisimple_relations,
       cross_relations,MatrixToVector,Generators_Relations,K_basis,
       relations;



import "show.m"       : show_time;

//********************************************************************

function generators(A)

   t0 := Cputime(0);
        pi_I := PrimitiveIdempotentData(A);
   vprintf Presentation: "In generators, time for PrimitiveIdempotentData(A) is %o seconds.\n", Cputime(t0);
   t0 := Cputime(0);
        ss_I := SemisimpleGeneratorData(A);
   vprintf Presentation: "In generators time for SemisimpleGeneratorData(A) is %o seconds.\n", Cputime(t0);
	mm := SimpleQuotientAlgebras(A);
        s_A := mm`SimpleQuotients;
	n := mm`DegreesOverCenters;
	d := mm`DegreesOfCenters;
	q := mm`OrdersOfCenters;
        r := #ss_I;
	vprint Presentation: "A"; 
	//	show_time("Generators", Cputime(t));

		vprint Presentation: "Number of generators =", r * 2;

	beta := [x`FieldGenerator : x in ss_I];
	tau := [x`Permutation : x in ss_I];
	g := [x`PrimitiveIdempotent : x in ss_I];
	h_prime := [x`GeneratingPolForCenter : x in ss_I];
 
	t := Cputime();
   t0 := Cputime(0);
	J_gens, JS_gens, JC_gens, bmats := radical_generators(A, s_A, 
			g, tau, beta, n, ss_I);
   vprintf Presentation: "In generators time for radical_generators(A) is %o seconds.\n", 
           Cputime(t0);
	show_time("Radical", Cputime(t));

  	vprint Presentation: "Number of generators for J(A) =", 
			&+[#J_gens[i][j] : i, j in [1..#J_gens]];

  	vprint Presentation: "Number of generators for J(A)/J(A)^2 =", 
			&+[#J_gens[i][j] : i, j in [1..#J_gens]];

	return beta, tau, g, J_gens, JS_gens, 
			h_prime, n, d, q, ss_I, s_A, bmats;

end function;

//**********************************************************************

intrinsic AlgebraGenerators(A::AlgMat) -> Rec
{The standard generators of the matrix algebra A}

if assigned A`AlgebraGenerators then 
     return A`AlgebraGenerators;
end if;

AlgebraGens := recformat<
           FieldGenerators : SeqEnum,
           PermutationMatrices : SeqEnum,
           PrimitiveIdempotents :SeqEnum,
           RadicalGenerators : List,
	   SequenceRadicalGenerators : SeqEnum,
           GeneratingPolynomialsForCenters :SeqEnum,
           StandardFormConjugationMatrices : Tup>;

beta, tau, g, J_gens, JS_gens, h_prime, n, d, q, ss_I, sA, bmats :=
                              generators(A);

Recc := rec< AlgebraGens |
           FieldGenerators:= beta,
           PermutationMatrices := tau,
           PrimitiveIdempotents := g,
           RadicalGenerators := J_gens,
	   SequenceRadicalGenerators := JS_gens,
           GeneratingPolynomialsForCenters := h_prime,
           StandardFormConjugationMatrices := bmats
           >;
A`AlgebraGenerators := Recc;

       return Recc;

end intrinsic;

//**********************************************************************

function presentation(A)

	t := Cputime();
	RR := AlgebraGenerators(A);
	beta := RR`FieldGenerators;
	tau := RR`PermutationMatrices;
	g := RR`PrimitiveIdempotents;
	J_gens := RR`RadicalGenerators;
	JS_gens := RR`SequenceRadicalGenerators;
	h_prime := RR`GeneratingPolynomialsForCenters;
	mats := RR`StandardFormConjugationMatrices;
   
	RA := SimpleQuotientAlgebras(A);
	ai := RA`SimpleQuotients;
	n := RA`DegreesOverCenters;
	d := RA`DegreesOfCenters;
	q := RA`OrdersOfCenters;
	show_time("Generators", Cputime(t));
	t := Cputime();
	P, rels, JC_gens, B_gens := 
		relations(A, beta, tau, g, J_gens, h_prime, n, d, q);
	show_time("Relations", Cputime(t));

        beta := [Matrix(x): x in beta];
        tau := [Matrix(x): x in tau];

	t := Cputime();
	I := ideal< P | rels >;
        n := SimpleQuotientAlgebras(A)`DegreesOverCenters;
        if #n eq &+n then 
            theta := hom<P -> Generic(A) | beta cat JS_gens >;
        else 
            theta := hom<P -> Generic(A) | beta cat tau cat JS_gens >;
        end if;

// "I:",I; "Reduce I2:";
  	vprint Presentation: "Reduce ideal relations";
  	vtime Presentation: I := Ideal(Reduce(Basis(I)));

  	vprint Presentation: "Get GB";
  	vtime Presentation: GB := GroebnerBasis(I);

	show_time("GB", Cputime(t));

  	// vprint Presentation: "GB =";
        // vprint Presentation: GB;
	   vprint Presentation: "Number of GB relations =", #GB;

           return  P , I , theta, beta, tau, g, J_gens, JC_gens, B_gens,
		h_prime, n, d, q, ai, mats;

end function;

//*********************************************************************

intrinsic AlgebraStructure(A::AlgMat) -> Rec
{The structure of the matrix algebra A.}

if assigned A`AlgebraStructure then
   aaa := A`AlgebraStructure;
else

P , I , Xi, B, T, G, J, JC, BG, FP, N, D, Q , AI, cmats := presentation(A);

AlgStruct := recformat
<  FreeAlgebra,
  RelationsIdeal,
  StandardFreeAlgebraCover,
  FieldGenerators,
  PermutationMatrices,
  PrimitiveIdempotents,
  RadicalGenerators,
  CondensedRadicalBasis,
  CondensedFieldGenerators,
  FieldPolynomials,
  DegreesOfSimpleModules,
  DegreeOfFieldExtensions,
  SimpleQuotientAlgebras,
  StandardFormConjugationMatrices>;


// want also radical generators small matrices. Need these for the
// word problem.

aaa := rec<AlgStruct |
                FreeAlgebra := P,
                RelationsIdeal := I,
		StandardFreeAlgebraCover := Xi,
                FieldGenerators := B,
                PermutationMatrices := T,
                PrimitiveIdempotents := G,
                RadicalGenerators := J,
                CondensedRadicalBasis := JC,
                CondensedFieldGenerators := BG,
                FieldPolynomials := FP,
                DegreesOfSimpleModules := N,
                DegreeOfFieldExtensions := D,
                SimpleQuotientAlgebras := AI,
                StandardFormConjugationMatrices := cmats>;


end if;

A`AlgebraStructure := aaa;

    return aaa;

end intrinsic;

//******************************************************************

intrinsic Presentation(A:: AlgMat) -> AlgFr, AlgFr, Map
{The presentation in generators and relations of the matrix algebra A.}

algs := AlgebraStructure(A);

   return algs`FreeAlgebra, algs`RelationsIdeal, algs`StandardFreeAlgebraCover;

end intrinsic;

//*******************************************************************

intrinsic StandardFormConjugationMatrices(A::AlgMat) -> Tup
{The matrices that conjugate the matrix algebra A into standard form
   with respect to a chosen set of primitive idempotents.}

algs := AlgebraGenerators(A);

   return algs`StandardFormConjugationMatrices;


end intrinsic;

//*******************************************************************

intrinsic DimensionOfAlgebra(A::AlgMat) -> RngIntElt
{The dimension of the algebra A}

if assigned A`DimensionOfAlgebra then 
return A`DimensionOfAlgebra;
end if;

P,I := Presentation(A);
n := #MonomialBasis(P/I);
A`DimensionOfAlgebra := n;

    return n;

end intrinsic;

//**************************************************************

intrinsic CondensationMatrices(A::AlgMat) -> Tup
{The matrices, conjugating by which, gives the condensation of A.}

if assigned A`CondensationMatrices then
return A`CondensationMatrices;
end if;

ff := CoefficientRing(A);
tt := StandardFormConjugationMatrices(A);
n := SimpleQuotientAlgebras(A)`DegreesOverCenters;
if #n eq &+n then 
    return tt;
end if;
s := [Rank(x) : x in PrimitiveIdempotents(A)];
u := [n[i]*s[i]: i in [1 .. #n]];
mat := KMatrixSpace(ff, &+s, Nrows(A.1))!0;
uu := [0] cat [&+[u[j]: j in [1 .. i]]: i in [1 .. #u]];
ss := [0] cat [&+[s[j]: j in [1 .. i]]: i in [1 .. #u]];
for i := 1 to #s do 
InsertBlock(~mat, IdentityMatrix(ff, s[i]), ss[i]+1, uu[i]+1); 
end for;
uu := <mat*tt[1],tt[2]*Transpose(mat)>;
A`CondensationMatrices := uu;

return uu;

end intrinsic;

//*******************************************************************

intrinsic SequenceOfRadicalGenerators(A::AlgMat) -> SeqEnum
{The sequence of generators of the radical of A.}

return AlgebraGenerators(A)`SequenceRadicalGenerators;

end intrinsic;

//********************************************************************

intrinsic CartanMatrix(A::AlgMat) -> ModMatRngElt
{The Cartan Matrix of the algebra A.}

d := SimpleQuotientAlgebras(A)`DegreesOfCenters;
T := AlgebraStructure(A)`CondensedRadicalBasis;
r := #T;
if r eq 0 then 
   mat := RMatrixSpace(Integers(),#d,#d)!0;
   for i := 1 to #d do
      mat[i][i] := 1;
   end for;
else
   mat := RMatrixSpace(Integers(),r,r)!0;
   for i := 1 to r do
      for j := 1 to r do 
         if i eq j then 
            mat[i][j] := 1 +  (#T[i][j] div d[j]);
         else 
            mat[i][j] := #T[i][j] div d[j];
         end if;
      end for;
   end for;
end if;

           return mat;

end intrinsic;
 
