freeze;

/* GeneralizedAGCode.m
  
   v1.0 23.05.2002

   Markus Grassl
   IAKS
   Univeritaet Karlsruhe
   Germany
   e-mail: grassl@ira.uka.de
 
*/   


intrinsic GeneralizedAGCode(S::[PlcCrvElt],D::DivCrvElt,L::[Code]) -> Code
{}
  return GeneralizedAlgebraicGeometricCode(S,D,L);
end intrinsic;

intrinsic GeneralizedAlgebraicGeometricCode(S::[PlcCrvElt],D::DivCrvElt,L::[Code]) -> Code
{The generalized algebraic-geometric code build by evaluating
functions of the Riemann-Roch space of D at the places in S of degrees
i. Then each coordinate is encoded using the code L[i].}

/* see:

   Chaoping Xing, Harald Niederreiter, and Kwok Yan Lam
   "A Generalization of Algebraic-Geometry Codes"
   IEEE Transactions on Information Theory, vol. 45, no. 7, November 1999,
   pp. 2498-2501
   
   and

   Cunsheng Ding, Harald Niederreiter, and Chaoping Xing
   "Some New Codes from Algebraic Curves"
   IEEE Transactions on Information Theory, vol. 46, no. 7, November 2000,
   pp. 2638-2642

*/
   C := Curve(D);
   require Curve(Universe(S)) eq C:
      "Arguments must be defined with respect to the same curve";

   K:=BaseRing(C);

   F:=Alphabet(Rep(L));

   require &and{Alphabet(c) cmpeq F:c in L}:
      "All codes must be defined over the same alphabet";
 
   require &and{IsCoercible(K,Alphabet(c).1):c in L}:
      "The alphabet of the codes does not match the curve";


   degrees:={Degree(P): P in S};

   ext_deg:=Degree(K,F);
   dims:={Dimension(c) div ext_deg:c in L};

   require degrees subset dims:
      "The dimension of the codes and the degrees of the places do not match";
   suppD := Support(D);

   L_c:=[exists(c){c:c in L|Dimension(c) div ext_deg eq k} select c 
               else ZeroCode(K,1):
           k in [1..Maximum(degrees)]];

   if F ne K then
     _,l:=MatrixAlgebra(K,F);
     L_enc:=[func<x|HorizontalJoin([l(h(x)[i]):i in [1..Degree(V)]])*GeneratorMatrix(L_c[d]) where V,h:=VectorSpace(Parent(x),K)>: d in [1..#L_c]];

   else
     L_enc:=[func<x|h(x)*GeneratorMatrix(L_c[d]) where _,h:=VectorSpace(Parent(x),F)>: d in [1..#L_c]];
   end if;

   require &and [ P notin suppD : P in S ] : 
      "Support of argument 2 must be disjoint from argument 1.";
   total_tyme := Cputime();
   vprintf AGCode : "Generalized algebraic-geometric code:\n";
   IndentPush();


   tyme := Cputime();
   g := GeometricGenus(C);
   vprintf AGCode : "Genus computation time: %o\n", Cputime(tyme);

   tyme := Cputime();
   vprintf AGCode, 2 : "Riemann-Roch divisor, support:\n%o\n", suppD;
   VD, mD := RiemannRochSpace(D);
   LD := [ mD(x) : x in Basis(VD) ];
   vprint AGCode : "Riemann-Roch dimension:", Dimension(VD);
   vprint AGCode : "Riemann-Roch space time: ", Cputime(tyme);


   tyme := Cputime();

   if K eq F then
     G := Matrix([ Vector(&cat[ Eltseq(L_enc[Degree(P)](Evaluate(f,P))) : P in S ]) : f in LD ]);
   else
     for f in LD do
       for P in S do
         if assigned G0 then
           G0:=HorizontalJoin(G0,L_enc[Degree(P)](Evaluate(f,P)));
         else
           G0:=L_enc[Degree(P)](Evaluate(f,P));
         end if;
       end for;
       if assigned G then
         G:=VerticalJoin(G,G0);
       else 
         G:=G0;
       end if;
       delete G0;
     end for;
   end if;

   vprintf AGCode : "Evaluation time: %o\n", Cputime(tyme);

   C := LinearCode(G);
   C`IsWeaklyAG := false;
   C`GeometricSupport := S;
   C`Divisor := D;
   C`RiemannRochBasis := LD;

// compute the lower bound

// check condition of Lemma3.1/Theorem 3.2
   if Degree(D) lt &+[Degree(P):P in S] then
     lb:=&+[Minimum(MinimumWeight(L_c[Degree(P)]),ext_deg*Degree(P)):P in S]-ext_deg*Degree(D);
     vprintf AGCode, 1:"Lower bound: d=%o\n",lb;    
     C`MinimumWeightLowerBound:=lb;
   end if;
   IndentPop();
   vprintf AGCode, 1 : 
      "Algebraic-geometric code time: %o\n", Cputime(total_tyme);
   return C;
end intrinsic;
