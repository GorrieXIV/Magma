freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: tests.m

   (WAS and SRD)

   $Header: /home/was/magma/packages/modform/code/RCS/tests.m,v 1.4 2002/04/13 07:27:10 was Exp $

   $Log: tests.m,v $
   Revision 1.4  2002/04/13 07:27:10  was
   *** empty log message ***

   Revision 1.3  2001/05/30 18:57:44  was
   Created.

   Revision 1.2  2001/05/16 04:00:52  was
   initial code entry.

 ****************************************************************************

   TO RUN TESTS: 

   > SetVerbose("ModularForms",2);  
   > SetVerbose("ModularSymbols",2);  
   > load"/magma/donnelly/package/Geometry/ModSym/tests.m";
   > DoTests(100);
   > Attach("/magma/donnelly/package/Geometry/ModFrm/tests.m");
   > BugHunter([1..100], 1, 0.5);

 ****************************************************************************/

forward RandomBasisG1, 
        NewformsG1, 
        NewSubspaceG1,
        TestModpG1, 
        TestpAdicG1, 
        TestComplexG1, 
        TestCharpoly,
        TestProducts,
        TestProductsWeight1,
        TestProductsWeightHalf,
        TestLinAlg;

NS := NewSubspace;
CS := CuspidalSubspace;
ES := EisensteinSubspace;


intrinsic BugHunter(tests::[RngIntElt], rep::RngIntElt, how_hard::FldReElt : quiet:=false)
{}
   if #tests eq 0 then
      tests := [1..100];
   end if;
   for n in [1..rep] do
      if 1 in tests then
           "BG -- RandomBasisG1 -- ", n;
            RandomBasisG1(how_hard : quiet:=quiet);
      end if;
      if 2 in tests then
           "BG -- NewformsG1 -- ", n;
            NewformsG1(how_hard : quiet:=quiet);
      end if;
      if 3 in tests then
           "BG -- NewSubspaceG1 -- ", n;
            NewSubspaceG1(how_hard : quiet:=quiet);
      end if;
      if 4 in tests then
           "BG -- TestModpG1 -- ", n;
            TestModpG1(how_hard : quiet:=quiet);
      end if;
      if 5 in tests then
           "BG -- TestpAdicG1 -- ", n;
            TestpAdicG1(how_hard : quiet:=quiet);
      end if;
      if 6 in tests then
           "BG -- TestComplexG1 -- ", n;
            TestComplexG1(how_hard : quiet:=quiet);
      end if;
      if 7 in tests then
           "BG -- charpoly test -- ", n;
            TestCharpoly(how_hard : quiet:=quiet);
      end if;
      if 8 in tests then
           "BG -- test products of forms -- ", n;
            TestProducts(how_hard);
      end if;
      if 9 in tests then
           "BG -- test products of weight 1 forms -- ", n;
            TestProductsWeight1(how_hard);
      end if;
      if 10 in tests then
           "BG -- test products of weight 1 forms -- ", n;
            TestProductsWeightHalf(how_hard);
      end if;
      if 11 in tests then
           "BG -- check the linear algebra -- ", n;
            TestLinAlg(how_hard : quiet:=quiet);
      end if;
      if 12 in tests then
           "BG -- test products of weight 1 forms -- ", n;
            TestHecke(how_hard);
      end if;
   end for;
end intrinsic


function G1(how_hard)

   N := Random([1] cat [1..Round(how_hard*100)]);
   k := Random([2] cat [2..Round(how_hard*20)+2]);
   return  ModularForms(Gamma1(N),k);
end function;

function RandomSpace(how_hard)
   N := Random([1] cat [1..Round(how_hard*100)]);
   k := Random([2] cat [2..Round(how_hard*20)+2]);
   if Random([1..2]) eq 1 then
      M := ModularForms(Gamma0(N),Max(k,2));
   else
      N := (N div 2)+1;
      k := k div 2;
      M := ModularForms(Gamma1(N),Max(k,2));
   end if; 
   if Random([1..3]) ne 1 then
      if Random([1..2]) eq 1 then
         p := NextPrime(Random([1..10]));
      else
         p := NextPrime(Random([1..1000]));
      end if;
   else
      p := 0;
   end if;
   printf "Gamma_%o, N=%o, k=%o, p=%o\n", (IsGamma0(M) select 0 else 1), N,k,p;
   return M, p;
end function;


procedure RandomBasisG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   M := G1(how_hard); M;
   print "qExpansionBasis(M);";
   [PowerSeries(f,20) : f in Basis(M)];
   print "qExpansionBasis(EisensteinSubspace(M));";
   [PowerSeries(f,20) : f in Basis(ES(M))];
   print "qExpansionBasis(CuspidalSubspace(M));";
   [PowerSeries(f,20) : f in Basis(CS(M))];
end procedure;

procedure NewformsG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   M := G1(how_hard); M;
   print "N := Newforms(M);";
   N := Newforms(M);
   if how_hard le 0.2 then N; end if;
   print "q-expansions";
   for orb in N do
      "-------------------------";
      for f in orb do
         f_qexp := PowerSeries(f,10);
         if not quiet and how_hard le 0.2 then f_qexp; end if;
         Degree(f);
      end for;
   end for;
end procedure;

procedure NewSubspaceG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   M := G1(3/4*how_hard); M;
   print "NS(M) := ", NS(M);
   print "NS(ES(M)) := ", NS(ES(M));
   print "ES(NS(M)) := ", NS(ES(M));
   assert Dimension(NS(ES(M))) eq Dimension(NS(ES(M)));
   print "CS(NS(M)) := ", CS(NS(M));
   print "NS(CS(M)) := ", NS(CS(M));
   qexp := [PowerSeries(f,20) : f in Basis(NS(CS(M)))];  #[f : f in qexp | not IsWeaklyZero(f)];
   if not quiet then print "qexp(NS(CS(M))) := ", qexp; end if;
   qexp := [PowerSeries(f,20) : f in Basis(ES(NS(M)))];  #[f : f in qexp | not IsWeaklyZero(f)];
   if not quiet then print "qexp(ES(NS(M))) := ", qexp; end if;
end procedure;

procedure TestModpG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   p := 0;
   while p eq 0 do
      M, p := RandomSpace(how_hard);
   end while;
  
   M;
   N := Newforms(M);
   if not quiet then print N; end if;
   print "q-expansions";
   for orb in N do
      it := Reductions(orb[1], p);
      if not quiet then print it; end if;
   end for;   
   
end procedure;


procedure TestpAdicG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   p := 0;
   while p eq 0 do
      M, p := RandomSpace(how_hard);
   end while;
   M;
   N := Newforms(M);
   if not quiet then print N; end if;
   print "q-expansions";
   for orb in N do
      it := pAdicEmbeddings(orb[1], p);
      if not quiet then print it; end if;
   end for;
   
end procedure;

procedure TestComplexG1(how_hard : quiet:=false)
   assert Type(how_hard) eq FldReElt;

   M := RandomSpace(how_hard);
   M;
   N := Newforms(M);N;
   print "q-expansions";
   for orb in N do
      ComplexEmbeddings(orb[1]);
   end for;
end procedure;

procedure TestCharpoly(how_hard : quiet:=false)
   M := RandomSpace(how_hard);
   M;
   n := Round(Random([1..100])*how_hard)+1;
   while GCD(Level(M),n) gt 1 do
      n := Round(Random([1..100])*how_hard)+1;   
   end while;
   printf "n = %o\n", n;
   h := HeckePolynomial(CS(M), n);
   if not quiet then printf "f_%o on CS(M) := %o\n", n, h; end if;
   h := HeckePolynomial(NS(CS(M)), n);
   if not quiet then printf "f_%o on NS(CS(M)) := %o\n", n, h; end if;
end procedure;


// STEVE'S TESTS START HERE 

intrinsic DoTestProducts(input::. : skip_wt3:=false, weight:=0) -> BoolElt
{Run Steve's test (checking products of modular forms lie where they should) 
for the given level, character or congruence subgroup.}
   if weight eq 1/2 then TestProductsWeightHalf(0.5 : N:=input);
   elif weight eq 1 then TestProductsWeight1(0.5 : chi:=input, cusp:=true); 
   else TestProducts(0.5 : arg:=input, no_wt3:=skip_wt3); end if;
   return true;
end intrinsic;

procedure TestProducts(how_hard : arg:=0, no_wt3:=false)
   chi_given := Type(arg) eq GrpDrchElt;
   if arg cmpeq 0 then
      h := Round(40*(how_hard)^0.8);
      N := Random([5..10+h]);
      G := 0;
      chi := 0;
   elif Type(arg) eq RngIntElt then
      N := arg;
      G := 0;
      chi := 0;
   elif Type(arg) eq GrpDrchElt then
      chi := arg;
      N := Conductor(chi);
      G := 0;
   elif Type(arg) eq GrpPSL2 then
      G := arg;
      N := Level(G);
      chi := 0;
   end if;
   assert N gt 0;
   if G cmpeq 0 and chi cmpeq 0 then
      // randomly pick a G or a chi at level N
      rr := Random([0..3]);
      if rr in {0,1} then
         G := (rr eq 0) select Gamma0(N) else Gamma1(N);
      elif rr eq 2 then 
         repeat chi := Random(DirichletGroup(4*N));
         until chi(-1) eq 1 and DimensionByFormula(ModularForms(chi)) gt 0;
      elif rr eq 3 then 
         repeat chi := Random(FullDirichletGroup(4*N));
         until chi(-1) eq 1 and DimensionByFormula(ModularForms(chi)) gt 0;
      end if;
   end if;
   if G cmpne 0 then
      printf "%o", G;
      M2:=ModularForms(G); M3:=ModularForms(G,3); M4:=ModularForms(G,4); M6:=ModularForms(G,6);
   else 
      assert chi cmpne 0;
      printf "chi = %o in %o\n", chi, Parent(chi);
      M2 := ModularForms(chi);
      chi_conjs := [chi^k : k in [1..e-1] | GCD(e,k) eq 1] where e is Max(2, Order(chi));
      chi_prods := GaloisConjugacyRepresentatives([chi1*chi2 : chi1, chi2 in chi_conjs]);
      M4 := ModularForms(chi_prods, 4);
      
      chi_odd := IsOdd(chi) select chi 
                             else  KroneckerCharacter(-4) * chi;   
      assert IsOdd(chi_odd);
      M3 := ModularForms(chi_odd, 3);
      chi_odd_conjs := [chi_odd^k : k in [1..e-1] | GCD(e,k) eq 1] where e is Max(2, Order(chi_odd));
      chi_odd_prods := GaloisConjugacyRepresentatives([chi1*chi2 : chi1, chi2 in chi_odd_conjs]);
      M6 := ModularForms(chi_odd_prods, 6);
   end if;
   
   qq := PowerSeriesRing(BaseRing(M4)).1;
   
   if Dimension(M2) gt 0 then
     printf "Comparing weight 2 and weight 4:\n";
     n := 5 + PrecisionBound(M4);
     printf "  getting weight 2 forms ... "; time
     qexps2 := qExpansionBasis(M2, n);
     printf "  getting weight 4 forms (dimension %o) ... ",Dimension(M4); time 
     qexps4 := qExpansionBasis(M4, n);
     printf "  trying products ... "; time
     for k := 1 to Ceiling(200*how_hard) do 
        i := Random([1..#qexps2]);  j := Random([1..#qexps2]);
        prodf := M4!( qexps2[i] * qexps2[j] + O(qq^(n)) );  // runtime error if wrong
     end for; 
   end if;
  
   DeleteAllAssociatedData(M2);  DeleteAllAssociatedData(M4);

   if no_wt3 or Dimension(M3) eq 0 then 
      print "No weight 3 forms, sadly"; return; end if;
   printf "Comparing weight 3 (dimension %o) and weight 6:\n", Dimension(M3);
   n := 5 + PrecisionBound(M6);
   printf "  getting weight 3 forms ... "; time
   qexps3 := qExpansionBasis(M3, n);
   printf "  getting weight 6 forms (dimension %o) ... ",Dimension(M6); time
   qexps6 := qExpansionBasis(M6, n);
   printf "  trying products ... "; time
   for k := 1 to Ceiling(200*how_hard) do 
      i := Random([1..#qexps3]);  j := Random([1..#qexps3]);
      prodf := M6!( qexps3[i] * qexps3[j] + O(qq^(n)) ); end for;
   
   DeleteAllAssociatedData(M3);  DeleteAllAssociatedData(M6);
   if not chi_given and Type(chi) eq GrpDrchElt then 
      DeleteAllAssociatedData(Parent(chi)); end if;
end procedure;

procedure TestProductsWeight1(how_hard : chi:=0, cusp:=false) 
   chi_given := chi cmpne 0;
   if chi_given then
     if IsEven(chi) then return; end if;
   else
     N := Random([23..24+Round(120*how_hard)]); 
     chis := Elements(FullDirichletGroup(N)); 
     repeat chi := Random(chis); until IsOdd(chi);
   end if;
   chi_conjs := [chi^k : k in [1..e-1] | GCD(e,k) eq 1] where e is Max(2, Order(chi));
   chi_prods := GaloisConjugacyRepresentatives([chi1*chi2 : chi1, chi2 in chi_conjs]);
   M1 := cusp select CuspForms(chi,1)
               else  ModularForms(chi,1); 
   M2 := cusp select CuspForms(chi_prods, 2)
               else  ModularForms(chi_prods, 2);
   print M1;
   if Dimension(M1) gt 0 then
     qq := PowerSeriesRing(BaseRing(M1)).1;
     printf "Comparing weight 1, level %o (dimension %o) with weight 2 (dimension %o)\n", 
                                 Level(M1), Dimension(M1), Dimension(M2);
     n := 5 + PrecisionBound(M2); // Magma computes M2 up to the prec bound anyway
     printf "Using precision %o ... getting weight 1 forms\n", n;
     qexps1 := qExpansionBasis(M1, n);
     printf "  ... getting weight 2 forms\n";
     qexps2 := qExpansionBasis(M2, n);
     printf "  ... trying products -- "; time
     for k := 1 to Ceiling(100*how_hard) do 
        i := Random([1..#qexps1]);  j := Random([1..#qexps1]);
        prodf := M2!( qexps1[i] * qexps1[j] + O(qq^n) );  // runtime error if wrong
     end for; 
     if cusp then 
        printf "  ... trying Eisenstein products -- "; time
        for es in Basis(EisensteinSubspace(AmbientSpace(M1))) do 
           prode := M2!( qExpansion(es,n)*Random(qexps1) + O(qq^n) ); end for; end if;
   end if;
   printf "\n";
   // Clean up by hand:
   DeleteAllAssociatedData(M1);  DeleteAllAssociatedData(M2);
   if not chi_given then DeleteAllAssociatedData(Parent(chi)); end if;
end procedure;

procedure TestProductsWeightHalf(how_hard : N:=0)
   if N eq 0 then N := 4*Random([1..Ceiling(100*how_hard)]); end if;
   Mhalf := ModularForms(Gamma1(N), 1/2);
   Mone := ModularForms(Gamma1(N), 1);
   prec := PrecisionBound(Mone);
   printf "Testing products of pairs of weight 1/2 forms on Gamma1(%o), using precision %o\n",N,prec;
   for i := 1 to Dimension(Mhalf) do for j := 1 to i do 
     _ := Mone!( qExpansion(Mhalf.i,prec) * qExpansion(Mhalf.j, prec) );  
   end for; end for;
   DeleteAllAssociatedData(Mone);  DeleteAllAssociatedData(Mhalf);
end procedure;


procedure TestLinAlg(how_hard : quiet:=false)
   // Check that the echelonizing/saturation done in ModFrm
   // agrees with the corresponding stuff in ModSym
   M := RandomSpace(how_hard); 
   S := CuspidalSubspace(M);
   while DimensionByFormula(S) eq 0 do
     M := RandomSpace(how_hard);
     S := CuspidalSubspace(M);
   end while;
   MS := ModularSymbols(M,1);
   SS := CuspidalSubspace(MS);
   prec := PrecisionBound(M);
   if Random(1) eq 1 then prec +:= Random(Round(100*how_hard)); end if;
   print "prec = ", prec;
   qexps1 := qExpansionBasis(S, prec);
   qexps2 := qIntegralBasis(SS, prec);
   R1 := Universe(qexps1);
   q := R1.1;
   assert R1 eq Universe(qexps2); 
   assert qexps1 eq qexps2;
   "okay";
   DeleteAllAssociatedData(M);
end procedure;


intrinsic TestHecke(how_hard::RngElt : N:=0, k:=0, chars:=0) 
{Check that some Hecke operators seems to be working correctly on a random ModFrm}
   if N eq 0 then N := Random([2..Round(how_hard*150)]); end if;
   if k eq 0 then k := Random([1,2] cat [1..Round(how_hard*10)+2]); end if;
   chars_given := chars cmpne 0;
   if not chars_given then
     chars := [eps: eps in Elements(DirichletGroup(N)) | IsEven(eps) eq IsEven(k)];
   end if;
   if IsEmpty(chars) then return; end if;
   
   ns := [n : n in [2,3,4,5,6,7] | GCD(n,N) eq 1];
   //if GCD(N,30) gt 5 and N mod 7 ne 0 then Append(~ns,7); end if;
   for eps in chars do 
     M := ModularForms(eps,k);
     for MM in [MM: MM in [EisensteinSubspace(M), CuspidalSubspace(M)] | Dimension(MM) gt 0] do
       printf "Computing T_n for n = %o on %o\n", ns, MM;
       mats := [HeckeOperator(MM,n) : n in ns]; // runtime error if result is not in MM
       assert &and[ m1*m2 eq m2*m1 : m1, m2 in mats ]; 
       if k eq 2 and IsCuspidal(MM) and IsGamma0(MM) then
         assert &and[ #Roots(f, RealField()) eq Degree(f) where f is fact[1] 
                    : fact in Factorization(CharacteristicPolynomial(mm)), mm in mats]; 
       end if; 
     end for;
     DeleteAllAssociatedData(M); delete M; 
   end for;
   if not chars_given then DeleteAllAssociatedData(Universe(chars)); end if;
end intrinsic;

// TO DO ... also test whether atkin-lehners commute with Heckes
