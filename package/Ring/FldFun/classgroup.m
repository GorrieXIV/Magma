
freeze;

////////////////////////////////////////////////////////////////////////////// 
/*  
  
  classgroup.m:  Divisor class group computations for global 
                 function fields
  FH 01/01
  
*/  
////////////////////////////////////////////////////////////////////////////// 
 
  
intrinsic NumberOfSmoothDivisors(n::RngIntElt, m::RngIntElt, P::[RngElt]) 
                                                                   -> RngElt
{The number of effective divisors of degree less equal n who consist
 of places of degree less equal m only. P[i] contains the (generic) number of
 places of degree 1 <= i <= min(n, m)};

   require #P ge Minimum(n, m) :
     "Sequence of number of places too short";
   assert ISA(Type(Universe(P)), Rng);
   
   if not IsUnit(Universe(P)!Factorial(n)) then
      require IsUnit(FieldOfFractions(Universe(P))!Factorial(n)) :
        "Factorial of first argument must be invertible";
      PP := [ FieldOfFractions(Universe(P)) | x : x in P ];
   else
      PP := P;
   end if;
   
   if n eq 0 or m eq 0 then
      return 1;
   end if;
   
   N := [ &+ [ Universe(PP) | d * PP[d] : d in Divisors(i) | d le m ] 
          : i in [1..n] ];
   Psi := [ Universe(PP) | ];
   
   for i in [1..n] do
      Psi[i] := &+ [ Universe(PP) | (1 + N[i-j]) * 
                     (j eq 0 select 1 else Psi[j]) : j in [0..i-1] ] 
                       / Universe(PP)!i;
   end for;
   
   if Type(Universe(P)) eq RngInt then
      return Integers()!Psi[n];
   else
      return Psi[n];
   end if;
   
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// alff_abs: maps zum schluss hinkriegen ... ok
// nach doku bringen ok
// alff_class_group.c etc aufr"aumen ??  
  
// Used reduction strategies: 
//   Preimages of f2 module image of f1 (principal divisor gens mod s units)
//   Preimages of f3 mod image of f2 (class group generators are reduced mod
//     principal divisors and A1 by divisor reduction, s-class group gens as 
//     divisors are only reduced mod S)  
  
RR := RealField(30);  
//qbound := 5000;
qbound := Infinity();  // may lead to other errors in the program,
                       // too big lists, matrices etc.

declare verbose     ClassGroup,  2;

declare attributes  FldFunG:      S,       // empty set of places
                                  cld;     // class group data 

declare attributes  RngFunOrd:   S,       // set of places at infinity 
                                 UToF,    // map U(O) -> F*
                                 FToId,   // map F^* -> Ideals(O)
                                 IdToCl;  // map Ideals -> Cl(O)

declare attributes  SetEnum:   S,         // the set as sequence
                               fS,        // f(S`S) for the class group map f 
                               SReg,      // the S-regulator 
                               USToF,     // map U(S) -> F^*
                               FToDivS,   // map F^* -> Div(S)
                               DivSToClS; // map Div(S) -> Cl(S)

declare attributes  Map: PreimageTest;
                          // " Map`PreimageTest(x) = HasPreimage(x, Map) " 
                          // (only HasPreimage() doesn't work for maps 
                          //  given by rules that way)
                                   
forward ClassGroupProfile;
  
cld_fmt := recformat<    // class group data
           userbound,    // user given degree bound for places in 
                         // fb (except A1, S) 
           P,            // P[i]: (Approximate) number of places of degree i 
           n,            // Reduced divisors have degree <= n
           A1,           // Divisor of degree one
           fb,           // Factor basis
           fbbound,      // used degree bound for places in fb (except A1, S)
           sizebound,    // create/enlarge fb in steps of at most sizebound 
                         // places
           fbmaxdeg,     // largest degree in fb
           fbpols,       // prime polynomials in k[x] of finite places in fb
           happrox,      // approximate number of degree zero divisor classes
           smoothprob,   // Expected smoothness probablity
           rels,         // Set of relation vectors on fb
           eldiv,        // Elementary divisor of Cl^0
           xinfty,       // Pole divisor of x in F
           xinftyvec,    // its factorization over fb
           A,            // Reduction divisor
           Avec,         // its factorization over fb
           Cl,           // The divisor class group as abelian group
           ZnToCl,       // The map Zn -> Cl (Zn corresponds to fb)
           ClToDivHigh,  // Lift to divisors with large exponents
           DivToClFlat,  // lift to divisor with small exponent (but 
                         // larger support)
           DivToClHigh,  // Map DivisorGroup -> Classgroup (with high preimage)
           Clabelinv,    // Abelian invariants of Cl
           proven,       // Whether Cl is proven
           profile,      // Profile information
           a,            // For debug
           fbp,          // For debug
           S             // Empty set of places for exact sequence
           >;  

fbp_fmt := recformat<    // Factor basis entry 
           place,        // Place
           i,            // Position in fb
           n,            // Random weight for relation search
           divisor,      // Random divisor for relation search
           basis,        // Basis of divisor but reduced
           countermap,   // Enumeration map for span(basis)
           counter       // Current position in span(basis)
           >;

stat_fmt := recformat<    // Statistics
            LDs,          // Current number of Riemann-Roch calculations
            reltries,     // Current number of attempts to find a relation
            reltrieslast, // reltries of last measurement
            rels,         // Current number of found relations
            relslast,     // rels at last measurement 
            rank,         // Current rank
            ranklast,     // rank at last measurent
            rankeq,       // rank stayed equal for rankeq relations 
            det,          // Current det
            detlast,      // det at last measurement
            deteq,        // det stayed equal for deteq relations
            reltriesnew,  // do reltriesnew new reltries for next measurement
            relsnew,      // find relsnew new relations for next measurement
            rankrelratio, // ratio of rank per relation
            smoothness,   // ratio of relations per reltries
            relfound      // Whether last rel try resulted in a relation 
            >;

profile_fmt := recformat<  // Profile information
               name,       // sequence of function names
               cputime,    // used cputime including descendants
               calls       // number of calls
               >;
   
// Remark: The profile functions seem to make up about maximally 3 percent 
// of the whole running time
   
   
////////////////////////////////////////////////////////////////////////////
  
  
pTorsionSubgroup := function(G, p)
//
// The group of p-torsion points of G
//
   Gp := pPrimaryComponent(G, p);
   Gp1 := sub< G | [ G | (v[i] div p)*Gp.i 
                  : i in [1..NumberOfGenerators(Gp)] ] > 
          where v is pPrimaryInvariants(Gp, p);
   return Gp1;
end function;
  
  
////////////////////////////////////////////////////////////////////////////

   
ProjectiveNumberingMap := function(B, k)
//
//  A set {1..n} and map: f: {1..n} -> Universe(B) with image
//  " ProjectiveHull( Span_k(B) ) "
//
   k := SetToSequence(Set(k));
   len := #k;
   NumToElt := function(n)
      if n eq -1 then
         return B[1];
      end if;
      p := len;
      i := 2;
      while n - p ge 0 do
         n -:= p;
         p *:= len;
         i +:= 1; 
      end while;
      b := Zero(Universe(B));
      j := 1;
      repeat
         n, r := Quotrem(n, len);
         b := b + k[r+1]*B[j];
         j +:= 1;
      until n eq 0;
      b := b + B[i];
      return b;
   end function;
   return map< { 1..(len^#B-1) div (len-1) } -> Universe(B) 
                  | n :-> NumToElt(n-2) >;
end function;
   
   
////////////////////////////////////////////////////////////////////////////
  
FactorBasisCreate := procedure(F, S, deg, num)
   
   timeon := Cputime();                  
   vprint ClassGroup : 
     "creating factor basis for deg", deg, "and num", num;
   
   A1 := DivisorOfDegreeOne(F);
   fb := &cat [ Places(F, ecfdim * i) : i in [1..deg] ]
         where ecfdim := DimensionOfExactConstantField(F);
   if #fb gt num then
     fb := [ fb[i] : i in [1..num] ];
      deg := Maximum( [ Degree(P) div ecfdim : P in fb ] )
             where ecfdim := DimensionOfExactConstantField(F);
     full := false;
   else
     full := true;
   end if;
   fb := fb cat Support(A1) cat S;
   fb := SetToSequence(SequenceToSet(fb));
   Sort( ~fb, function(a, b) return Degree(a) - Degree(b); end function );
      
   F`cld`A1 := A1;
   F`cld`fb := [ rec< fbp_fmt | place := fb[j], i := j > : j in [1..#fb] ];
   F`cld`fbbound := deg;                       
   F`cld`fbmaxdeg := Maximum( [ Degree(P) div ecfdim : P in fb ] )
                     where ecfdim := DimensionOfExactConstantField(F);
   if not full or deg lt F`cld`fbmaxdeg then
      F`cld`fbpols := { Minimum(place) : place in fb | IsFinite(place) };
   else
      delete F`cld`fbpols;
   end if;
   delete F`cld`rels;
   F`cld`happrox := ClassNumberApproximation(F, Sqrt(2) - 0.999);   
   F`cld`xinfty := Denominator(Divisor(F!BaseRing(F).1));
   
   vprint ClassGroup :
     "Size of factor basis is", #F`cld`fb;
   ClassGroupProfile(F, "FactorBasisCreate", timeon);
   
end procedure;


FactorBasisEnlarge := procedure(F, deg, num)
                      
   timeon := Cputime();                   
   vprint ClassGroup :
     "enlarging factor basis for deg", deg, "and num", num;

   if deg lt F`cld`fbbound or num le #F`cld`fb then
      return;
   end if;

   fb1 := [ P : P in fb1 | not P in fb ]
          where fb := [ fbp`place : fbp in F`cld`fb ]
          where fb1 := &cat [ Places(F, ecfdim * i) 
                            : i in [F`cld`fbbound..deg] ]
          where ecfdim := DimensionOfExactConstantField(F);
   if #F`cld`fb + #fb1 gt num then
     num := num - #F`cld`fb;
     fb1 := [ fb1[i] : i in [1..num] ];
     deg := Maximum( [ Degree(P) div ecfdim : P in fb1 ] )
            where ecfdim := DimensionOfExactConstantField(F);
     full := false;   
   else
     full := true;
   end if;
   
   F`cld`fb := F`cld`fb cat 
               [ rec< fbp_fmt | place := fb1[j], i := j+r > : j in [1..#fb1] ]
               where r := #F`cld`fb;        
   F`cld`fbbound := deg;
   F`cld`fbmaxdeg := Maximum( [ F`cld`fbmaxdeg ] cat 
                              [ Degree(P) div ecfdim : P in fb1 ] )
                     where ecfdim := DimensionOfExactConstantField(F);
   if not full or deg lt F`cld`fbmaxdeg then
      F`cld`fbpols := { Minimum(fbp`place) : fbp in F`cld`fb | 
                        IsFinite(fbp`place) };
   else
      delete F`cld`fbpols;
   end if;
   if assigned F`cld`rels then
      zero := [ 0 : i in [1..#fb1] ];
      V := RModule(Integers(), #F`cld`fb);
      F`cld`rels := { V | Eltseq(v) cat zero : v in F`cld`rels };
   end if;
   
   F`cld`smoothprob := RR!1 * 
                       NumberOfSmoothDivisors(F`cld`n, deg, F`cld`P) / 
                       NumberOfSmoothDivisors(F`cld`n, F`cld`n, F`cld`P);
   vprint ClassGroup : "new expected smoothness prob", F`cld`smoothprob; 
   ClassGroupProfile(F, "FactorBasisEnlarge", timeon);
   
end procedure;


/////////////////////////////////////////////////////////////////////////////

EnumEnvDivisorLBasisReduced := function(F, D)
   
  // simple strategy. for larger expos divisor reduction should be used
  if not assigned F`cld`A then  // max infty reduction
     basis, expo := ShortBasis(D : Reduction := false);
     return [ basis[i] : i in [1..#basis] | expo[i] eq m ] 
                    where m is Maximum(expo);
  else
     r := Floor( (Degree(D) - DimensionOfExactConstantField(F) * Genus(F)) 
                 / Degree(F`cld`A) );
     return Basis( D - r*F`cld`A: Reduction := false, 
                   Simplification := "None");
     //basis, expo := ShortBasis(D - r*F`cld`A : Reduction := false);
     //return [ basis[i] : i in [1..#basis] | expo[i] ge 0 ];
     //     return [ x^j*basis[i] : j in [0..expo[i]], i in [1..#basis] ]
     //   where x := F!BaseRing(F).1;
  end if;
   
end function;


EnumEnvInit := procedure(F, ~stat, ~fbp, n)
      
   D := - fbp`place;

   //n := Minimum( [n, #F`cld`fb, 10] );
   for i in [1..n] do
      fbp1 := Random(F`cld`fb);
      D := D + Random([1..n])*fbp1`place;
   end for;
   
   fbp`n := n;
   fbp`divisor := D;
   fbp`basis := EnumEnvDivisorLBasisReduced(F, D);
   
   // vprint ClassGroup : "new enum space of dim ", #fbp`basis;
   // vprint ClassGroup : "expo size is ", fbp`n;
   
   fbp`countermap := ProjectiveNumberingMap(fbp`basis, ConstantField(F)); 
   fbp`counter := 0;
   stat`LDs := stat`LDs + 1;

end procedure;
   
   
EnumEnvNext := procedure(F, ~stat, ~fbp)
   
   timeon := Cputime();            
   stat`reltries +:= 1;
   fbp`counter +:= 1;
   if not fbp`counter le Maximum(Domain(fbp`countermap)) then
      EnumEnvInit(F, ~stat, ~fbp, fbp`n);
      fbp`counter := 1;
   end if;
   ClassGroupProfile(F, "EnumEnvNext", timeon);
   
end procedure; 
   

EnumEnvElt := function(F, fbp)
   return fbp`countermap(fbp`counter);
end function;
   
   
/////////////////////////////////////////////////////////////////////////////
  
  
RelCheck := procedure(F, a, fbp, wo)
   return;         
   if not &or [ not P in fb : P in Support(Divisor(a)) ]
         where fb := [ fbp`place : fbp in F`cld`fb ] then
   F`cld`a := a;
   F`cld`fbp := fbp;
     error "error in rel add in", wo;
   end if;
end procedure;
  

RelAdd := procedure(F, ~stat, fbp, a)
          
   timeon := Cputime();
   flst := Factorisation(Minimum(a, MaximalOrderFinite(F)));
   flst := { p[1] : p in flst };   
   if not &and [ Degree(p) le fbmaxdeg : p in flst ]
      where fbmaxdeg := DimensionOfExactConstantField(F) * F`cld`fbmaxdeg then
      stat`relfound := false;
      RelCheck(F, a, fbp, 1);
      ClassGroupProfile(F, "RelAdd", timeon); 
      return;
   end if;
   if assigned F`cld`fbpols then
      if not flst subset F`cld`fbpols then
         stat`relfound := false;
         RelCheck(F, a, fbp, 2);
         ClassGroupProfile(F, "RelAdd", timeon); 
         return;
      end if;
   end if;
   v := Universe(F`cld`rels)!0;
   dens := Support(fbp`divisor);
   if assigned F`cld`A then
      dens := dens cat Support(F`cld`A);
   else
      dens := dens cat Support(F`cld`xinfty);
   end if;
   dens := SequenceToSet(dens);
   tmp := [ fbp`place : fbp in F`cld`fb ];
   deg := 0;
   for place in dens do
      i := Index(tmp, place);
      v[i] := Valuation(a, place);
      deg := deg + v[i] * Degree(place) div 
             DimensionOfExactConstantField(F);
   end for;
   tmp := [ fbp : fbp in F`cld`fb | not fbp`place in dens ];
   nums := [ fbp : fbp in tmp | not IsFinite(fbp`place) ];
   for fbp1 in nums do
      i := fbp1`i;
      v[i] := Valuation(a, fbp1`place);
      deg := deg + v[i] * Degree(fbp1`place) div 
             DimensionOfExactConstantField(F);
   end for;
   for p in flst do
      nums := [ fbp : fbp in tmp | Minimum(fbp`place) cmpeq p ];
      for fbp1 in nums do
         i := fbp1`i;
         v[i] := Valuation(a, fbp1`place);
         deg := deg + v[i] * Degree(fbp1`place) div 
                DimensionOfExactConstantField(F);
      end for;
   end for;
   if deg eq 0 then
      if not v in F`cld`rels then
         Include(~F`cld`rels, v);
      end if;
      stat`relfound := true;
      stat`rels +:= 1;
      ClassGroupProfile(F, "RelAdd", timeon); 
      return;
   else
      stat`relfound := false;
      RelCheck(F, a, fbp, 3);
      ClassGroupProfile(F, "RelAdd", timeon); 
      return;
   end if;
   
end procedure;


CheckRelmat := procedure(F, ~stat)
   
    timeon := Cputime();           
    vprint ClassGroup : 
        "####### checking value of rels ...";
    if stat`rank eq #F`cld`fb-1 then
      eldiv := ElementaryDivisors(Matrix(SetToSequence(F`cld`rels)));
      det := &* eldiv;       
      vprint ClassGroup :
        "the determinant is", det;
      stat`detlast := stat`det;
      stat`det := det;
      F`cld`eldiv := eldiv;   
   else 
      rank := Rank(Matrix(SetToSequence(F`cld`rels)));            
      vprint ClassGroup :
        "the rank is", rank;
      stat`ranklast := stat`rank;
      stat`rank := rank;
   end if;
   ClassGroupProfile(F, "CheckRelmat", timeon);
   
end procedure;


///////////////////////////////////////////////////////////////////////////
  
RelSearchEnlargeInterval := procedure(F, ~stat)
                            
  timeon := Cputime();                          
  vprint ClassGroup :
     "independence is bad, enlarging search intervals";
  vprint ClassGroup : 
     "initializing enum envs ...";
  for i in [1..#F`cld`fb] do
     EnumEnvInit(F, ~stat, ~F`cld`fb[i], F`cld`fb[i]`n + 1);
  end for;                            
  vprint ClassGroup :
    "average search interval is", 
    RR!1 * &+ [ Integers() | fbp`n : fbp in F`cld`fb ] / #F`cld`fb;
  ClassGroupProfile(F, "RelSearchEnlargeInterval", timeon);
    
end procedure;
  

RelSearchEnlargeFactorBasis := procedure(F, ~stat, deg, num)
                               
   timeon := Cputime();                            
   FactorBasisEnlarge(F, deg, num);
   vprint ClassGroup : "initializing enum envs ...";
   for i in [1..#F`cld`fb] do
      if not assigned F`cld`fb[i]`countermap then
        EnumEnvInit(F, ~stat, ~F`cld`fb[i], 1);
      end if;   
   end for;
   ClassGroupProfile(F, "RelSearchEnlargeFactorBasis", timeon);
   
end procedure;


RelSearch := procedure(F)
             
  timeon0 := Cputime();           

  stat := rec< stat_fmt | LDs := 0,
             reltrieslast := 0, reltries := 0, 
             relslast := 0, rels := 0,
             ranklast := 0, rank := 0, rankeq := 0,
             detlast := 0, det := 0, deteq := 0,
             reltriesnew := Ceiling(Maximum(10 * 
                     Ceiling(1/F`cld`smoothprob), 20)),
             relsnew := Ceiling(Maximum(#F`cld`fb / 10, 10)),
             rankrelratio := 1,
             smoothness := 1 >;

   F`cld`rels := { RModule(Integers(), #F`cld`fb) | };
                         
   vprint ClassGroup: 
    "initializing enum envs ...";
   for i in [1..#F`cld`fb] do
     EnumEnvInit(F, ~stat, ~F`cld`fb[i], 1);
   end for;
                         
   vprint ClassGroup : 
     "starting relation search ...";
   
   i := 1;
   vprint ClassGroup : 
     "******* at place ", i;
   
   while true do
      
      timeon := Cputime();
      EnumEnvNext(F, ~stat, ~F`cld`fb[i]);
      RelAdd(F, ~stat, F`cld`fb[i], EnumEnvElt(F, F`cld`fb[i]));
      ClassGroupProfile(F, "RelSearch (Relations)", timeon);
      
      if stat`reltries - stat`reltrieslast ge stat`reltriesnew then
         
         vprint ClassGroup: 
           "%%%%%%% checking smoothness of reltries ...";
         stat`smoothness := RR!1 * stat`rels / stat`reltries; 
         vprint ClassGroup : "smoothness is", stat`smoothness;
         vprint ClassGroup : "reltries are", stat`reltries;
         
         if stat`smoothness le F`cld`smoothprob / 100 then
            if assigned F`cld`userbound then
               vprint ClassGroup :
                 "bound low but user bound given, no enlargement";
            else
               vprint ClassGroup :
                 "%%%% smoothness is bad, enlarging factorbasis";
               RelSearchEnlargeFactorBasis(F, ~stat, F`cld`fbbound + 1,
                                           #F`cld`fb + F`cld`sizebound);
               stat`reltriesnew := Ceiling(Maximum(10 * 
                                           Ceiling(1/F`cld`smoothprob), 
                                           20));
            end if;
         else
            stat`reltriesnew := Ceiling(Maximum(10 * 
                                        Ceiling(1/stat`smoothness), 
                                        20));
         end if;
         
         vprint ClassGroup : 
           "redoing smoothness check after", stat`reltriesnew, "new reltries";
         stat`reltrieslast := stat`reltries;
         
      end if;
      
      if stat`rels - stat`relslast ge stat`relsnew then
         
         CheckRelmat(F, ~stat);
         
         if stat`det ne 0 then
            if stat`det le Sqrt(0.5) * F`cld`happrox then
               error "approximation error !!!";
            end if;
            if stat`det lt Sqrt(2.0) * F`cld`happrox - 0.1 then
               vprint ClassGroup :
                 "total number of tried rels is", stat`reltries;
               ClassGroupProfile(F, "RelSearch", timeon0);
               return;
            end if;
            
            if stat`det eq stat`detlast then
               stat`deteq := stat`deteq + stat`relsnew;
            else
               stat`deteq := 0;
            end if;
            
            if stat`deteq ge Maximum(#F`cld`fb / 10, 10) then
               RelSearchEnlargeInterval(F, ~stat);
               stat`deteq := 0;
            end if;
            
            stat`relsnew := Ceiling(Maximum(stat`smoothness * 2 * #F`cld`fb / 
                                    Degree(F), 1));
         else
            
            stat`rankrelratio := RR!1 * (
                 (stat`rank - stat`ranklast) / (stat`rels - stat`relslast) +
                                        stat`rankrelratio ) / 2;
            
            if stat`rank eq stat`ranklast then
               stat`rankeq := stat`rankeq + stat`relsnew;
            else 
               stat`rankeq := 0;
            end if;
            
            vprint ClassGroup : "rankrelratio is", stat`rankrelratio;
            
            if stat`rankrelratio lt 0.2 and 
               stat`rankeq ge Maximum(#F`cld`fb / 10, 10) then
              RelSearchEnlargeInterval(F, ~stat);
              stat`rankeq := 0;
              stat`relsnew := Ceiling(Maximum(#F`cld`fb / 10, 10));
            else
              stat`relsnew := Ceiling(Minimum(3 * stat`rankrelratio 
                                      * stat`relsnew + 0.001, 
                                      ( #F`cld`fb - 0.999 - stat`rank) 
                                      / stat`rankrelratio * 
                                      stat`smoothness * 2 * #F`cld`fb / 
                                      Degree(F)));
            end if;   
         end if;
         
         vprint ClassGroup : 
           "redoing check of relations after", stat`relsnew, "new relations";
         stat`relslast := stat`rels;
         
      end if;
      
      if stat`relfound then
         i := i + 1;
         if i gt #F`cld`fb then
            i := 1;
         end if;
         vprint ClassGroup :
           "******* at place ", i;
      end if;
      
   end while;
             
end procedure;


/////////////////////////////////////////////////////////////////////////////


EvalDataAbelianInvariants := procedure(F)
                             
   timeon := Cputime();                             
   if assigned F`cld`eldiv then
     eldiv := F`cld`eldiv;
     delete F`cld`eldiv;  
   else
     M := Matrix(SetToSequence(F`cld`rels));   
     eldiv := ElementaryDivisors(M);                
   end if;
   if #eldiv ne NumberOfColumns(Representative(F`cld`rels))-1 then
     error "Error in package EvalDataAbelianInvariants : Corrupt data";
   end if;
   F`cld`Clabelinv := [ x : x in eldiv | x ne 1 ] cat [ 0 ];
   ClassGroupProfile(F, "EvalDataAbelianInvariants", timeon);
   
end procedure;


EvalDataGenerators := procedure(F)
                      
   // The cyclic generators should
   // 1) consist of small degree places and         
   // 2) have small exponents.
   // 3) The infinite cyclic generator should be the standard 
   //    divisor of degree one.
            
   timeon := Cputime();                      
   vprint ClassGroup : "evaluating abelian group data ...";

   // reverse the fb and rels because then the generators
   // get nicer in the following (is done below as well)

   fb := Reverse( [ fbp`place : fbp in F`cld`fb] );
   Zn := FreeAbelianGroup(#fb);
   N :=  sub< Zn | [ Zn!Reverse(Eltseq(v)) : v in F`cld`rels ] >;
   Cl, g := quo< Zn | N >;
   A1rep := g( Zn![ Valuation(F`cld`A1, P) : P in fb ] );
   h := hom< Cl -> Cl | [ Cl.i : i in [1..NumberOfGenerators(Cl)-1] ] 
                        cat [ A1rep ] >;
   f := hom< Zn -> Cl | g( [ Zn.i : i in [1..NumberOfGenerators(Zn)] ] )@@h >;
   
   genshigh := [ &+ [ DivisorGroup(F) | v[j]*fb[j] : j in [1..#fb] ] 
                       where v is Eltseq(Cl.i@@f) 
               : i in [1..NumberOfGenerators(Cl)-1] ];
   Append(~genshigh, F`cld`A1);                       
                       
   ClToDivHigh := function(a)
      return &+ [ DivisorGroup(F) | v[j] * genshigh[j] : j in [1..#genshigh] ] 
                     where v is Eltseq(a);
   end function;
      
   F`cld`Cl := Cl;   
   F`cld`ZnToCl := f;
   F`cld`ClToDivHigh := ClToDivHigh;
   F`cld`Clabelinv := AbelianInvariants(Cl);
   
   vprint ClassGroup : "done.";
   ClassGroupProfile(F, "EvalDataGenerators", timeon);
   
end procedure;


EvalDataMaps := procedure(F)
            
   timeon := Cputime();             

   f := F`cld`ZnToCl;
   Zn := Domain(f);             
   Cl := Codomain(f);
   ClToDivHigh := F`cld`ClToDivHigh;
   fb := Reverse( [ fbp`place : fbp in F`cld`fb] );
   A1 := F`cld`A1;             
   
   vprint ClassGroup : "reducing generators ...";
   gensflat := [ Dt + r*A1 where Dt, r := Reduction(D, A1) 
                 where D := ClToDivHigh(Cl.i)
               : i in [1..NumberOfGenerators(Cl)] ];
   vprint ClassGroup : "done.";
   
   ClToDivFlat := function(a)
      return &+ [ DivisorGroup(F) | v[j] * gensflat[j] : j in [1..#gensflat] ] 
                     where v is Eltseq(a);
   end function;
    
   ClgDivisorFactorFb := function(F, D)
      // only apply this to reduced (small) divisors!
      I, _ := Ideals(D); // rem: does a superflous ideal inversion
      N := Factorisation(Minimum(I));
      ecfdim := DimensionOfExactConstantField(F);
      if #N gt 0 and
         Maximum([ Degree(x[1]) : x in N ]) gt F`cld`fbmaxdeg * ecfdim then
         return false;
      end if;
      places, expos := Support(D);
      v := Universe(F`cld`rels)!0;
      for i in [1..#places] do
         j := Index(fb, places[i]);
         if j eq 0 then
            return false;
         end if;
         v[F`cld`fb[j]`i] := expos[i];
      end for;
      return v;
   end function;
      
   DivToCl := function(D)
      
      F := FunctionField(D);
       
      if assigned F`cld`A and not assigned F`cld`Avec then
         F`cld`Avec := ClgDivisorFactorFb(F, F`cld`A);
         assert F`cld`Avec cmpne false;
      end if;
      
      places, expos := Support(D);
      v := Universe(F`cld`rels)!0;
      for i in [1..#places] do
         j := Index(fb, places[i]);
         if j eq 0 then
            v := false;
            break;
         end if;
         v[F`cld`fb[j]`i] := expos[i];
      end for;
      
      if v cmpne false then
         vprint ClassGroup :
           "is smooth";
      else
         
         Dred1, r1, xinfty := Reduction(D);
         v := ClgDivisorFactorFb(F, Dred1);
      
         if not assigned F`cld`xinftyvec or F`cld`xinfty ne xinfty then
            F`cld`xinfty := xinfty;
            // is smooth or something is wrong
            F`cld`xinftyvec := ClgDivisorFactorFb(F, xinfty);
         end if;
      
         if v cmpne false then
            vprint ClassGroup : 
              "first reduction ok";
            v := v + r1*F`cld`xinftyvec;
         else
            vprint ClassGroup : 
              "try several random reductions ...";
            tries := 0;
            n := 1;
            while v cmpeq false do
               tries +:= 1;
               n := Minimum( [n, #F`cld`fb, 10] );
               Drand := &+ [ DivisorGroup(F) | 
                             Random([1..n]) * Random(F`cld`fb)`place 
                           : i in [1..n] ];
               if assigned F`cld`A then
                  Dred2, r2 := Reduction(Dred1 + Drand, F`cld`A);
               else
                  Dred2, r2, xinfty2 := Reduction(Dred1 + Drand);
                  // should be the case otherwise we have to factor xinfty2
                  assert xinfty2 eq F`cld`xinfty;
               end if;
               N := ProjectiveNumberingMap(Basis(Dred2), ConstantField(F));
               s := Domain(N);
               vprint ClassGroup :
                 "enum number", Maximum(s), "at weight", n;
               i := 1;
               while v cmpeq false and i in s do
                  v := ClgDivisorFactorFb(F, Dred2 + Divisor(N(i)));
                  i := i + 1;
               end while;
               if tries gt Maximum([ #F`cld`fb / 10, 10 ]) then
                  tries := 0;
                  n +:= 1;
               end if;
            end while;
            Drandvec := ClgDivisorFactorFb(F, Drand);
            if assigned F`cld`A then
               v := v - Drandvec + r2*F`cld`Avec + r1*F`cld`xinftyvec;
            else
               v := v - Drandvec + (r1 + r2)*F`cld`xinftyvec;
            end if;
            
         end if;
      end if;
      
      return f(Zn!Eltseq(v));
      
   end function;
      
   F`cld`DivToClFlat := hom< DivisorGroup(F) -> Cl |
                             x :-> DivToCl(x), y :-> ClToDivFlat(y) >;
   F`cld`DivToClHigh := hom< DivisorGroup(F) -> Cl |
                             x :-> DivToCl(x), y :-> ClToDivHigh(y) >
                        where ClToDivHigh := F`cld`ClToDivHigh;
   
   //delete F`cld`ZnToCl;
   
   ClassGroupProfile(F, "EvalDataMaps", timeon);
   
end procedure;


OverLatticeCheck := procedure(F)
                    
    timeon := Cputime();                
    Cl := F`cld`Cl;
    ClToDiv := F`cld`ClToDivHigh;
    
    l := [ x[1] : x in Factorisation( &* Prune(F`cld`Clabelinv) ) ];
    vprint ClassGroup :
      "number of expo vectors to test", 
      &+ [ Integers() | (p^#pPrimaryInvariants(Cl, p)-1) div (p-1) : p in l ];
              
    for p in l do
       G := pTorsionSubgroup(Cl, p);
       f := ProjectiveNumberingMap(SetToSequence(Generators(G)), {0..p-1});
       for i in Domain(f) do
          D := ClToDiv(Cl!f(i));
          vprint ClassGroup :
             "testing exponent vector ", expos where _, expos := Support(D);
          if Dimension(D) ne 0 then
             error "Error in package OverLatticeCheck: Corrupt data";
          end if;
       end for;
    end for;
    
    ClassGroupProfile(F, "OverLatticeCheck", timeon);
    
end procedure;


////////////////////////////////////////////////////////////////////////////
  
  
SmoothnessRatio := function(n, m, P)
//
// The approximate number of rel tries to complete a fb
//
   return RR!1 * NumberOfSmoothDivisors(n, n, P) / 
          NumberOfSmoothDivisors(n, m, P) * 
          &+ [ Universe(P) | P[i] : i in [1..m] ];
end function;
  
  
HeuristicBound := procedure(F, proof)
                  
   timeon := Cputime();
                  
   CostEstimation := function(F, n, b, P)
      return RR!1 * Degree(F)^5 * Genus(F)^2 * 
             NumberOfSmoothDivisors(n, n, P) / 
             NumberOfSmoothDivisors(n, b, P) * 
             (&+ [ Universe(P) | P[i] : i in [1..b] ])
             + (&+ [ Universe(P) | P[i] : i in [1..b] ])^3 + 1;
   end function;
      
   if not assigned F`cld then
      F`cld := rec< cld_fmt | >;
   end if;
      
   g := Genus(F);
   g1 := g eq 0 select 1 else g;
   q := #ConstantField(F)^DimensionOfExactConstantField(F);
   if assigned F`cld`A then
      c := RR!1 + (Degree(F`cld`A)/DimensionOfExactConstantField(F) - 1) / g1;
   else
      c := RR!1 + (Degree(F)/DimensionOfExactConstantField(F) - 1) / g1;
   end if;
   vprint ClassGroup : "computing heuristic bound ...";
   vprint ClassGroup : "const field size is", q;
   vprint ClassGroup : "genus is", g;
   vprint ClassGroup : "weak gen bound is", 
     ClassGroupGenerationBound(q, g);
   vprint ClassGroup : "prod bound for 2 is", 
     ClassNumberApproximationBound(q, g, Sqrt(2) - 1.001);
   n := Floor(c*g1);
   maxbound := Ceiling(n^0.7);
   gbound := Maximum(ClassGroupGenerationBound(q, g), 
                     ClassNumberApproximationBound(q, g, Sqrt(2) - 1.001));
   vprint ClassGroup :
     "computing number of places up to degree", gbound, "...";
   P := [ NumberOfPlacesDegECF(F, i) : i in [1..gbound] ];
   P := P cat [ (1/i)*q^i : i in [gbound+1..n] ];
   gbound := ClassGroupGenerationBound(F);
   vprint ClassGroup : "strong gen bound is", gbound;
   L := [ CostEstimation(F, n, i, P) : i in [1..maxbound] ];
   bound := Index([ x gt 1 : x in L], true);
   if bound eq 0 then
      bound := #L+1;
   else
      L1 := [ L[i] : i in [bound..#L] ];
      bound := Index(L1, Minimum(L1)) + bound - 1;              
   end if;
   L := [ Round(10*Log(x))/10.0 : x in L ];
   vprint ClassGroup : "expected log costs are", L;
   vprint ClassGroup : "heuristic bound", bound;
   if proof then
      bound := Maximum(gbound, bound);
   end if;
   if assigned F`cld`userbound then
      F`cld`userbound := Minimum(F`cld`userbound, g1);
      bound := F`cld`userbound;
   end if;
   F`cld`fbbound := bound;
   F`cld`P := P;
   F`cld`n := n;
   F`cld`smoothprob := RR!1 * NumberOfSmoothDivisors(n, bound, P) / 
                       NumberOfSmoothDivisors(n, n, P);
   vprint ClassGroup : "taking bound", bound;
   vprint ClassGroup : "expected reltries for this are",
     SmoothnessRatio(n, bound, P);
   vprint ClassGroup : "expected smooth prob is", F`cld`smoothprob;
      
   ClassGroupProfile(F, "HeuristicBound", timeon);
   
end procedure;   
  
  
  
////////////////////////////////////////////////////////////////////////////
  
  
ClassGroupInitialize := procedure(F)
   delete F`cld;
   F`cld := rec< cld_fmt | >;
   if GetVerbose("ClassGroup") gt 1 then
      F`cld`profile := rec<profile_fmt | name := [], cputime := [], 
                                         calls := [] >;
   end if;
end procedure;
  
  
ClassGroupProfile := procedure(F, name, cputime)
   if assigned F`cld`profile then
     i := Index(F`cld`profile`name, name);
     if i eq 0 then
        Append(~F`cld`profile`name, name);
        Append(~F`cld`profile`cputime, Cputime() - cputime);
        Append(~F`cld`profile`calls, 1);
     else     
        F`cld`profile`cputime[i] +:= Cputime() - cputime;   
        F`cld`profile`calls[i] +:= 1;   
     end if;
  end if;   
end procedure;
  

ClassGroupProfilePrint := procedure(F)
   if assigned F`cld`profile then   
     name := F`cld`profile`name;
     cputime := [ Sprint(Round(x)) : x in F`cld`profile`cputime ];
     calls := [ Sprint(x) : x in F`cld`profile`calls ];
     max1 := - Maximum([ #x : x in name ] cat [5]) - 3;
     max2 := Maximum([ #x : x in cputime ] cat [7]) + 3;
     max3 := Maximum([ #x : x in calls ] cat [5]) + 3;                        
     printf " %*o%*o%*o\n", max1, " Name", max2, "Cputime", max3, "Calls";
     for i in [1..#name] do
        printf " %*o%*o%*o\n", max1, name[i],  max2, cputime[i], 
                               max3, calls[i];     
     end for;
   end if;
end procedure;


ClassGroupArgumentChecks := function(F, DegreeBound, SizeBound, 
                                     ReductionDivisor, Proof)
   if not IsGlobal(F) then
      return false, "Function field is not global";
   end if;
/*
   if AbsoluteDegree(F) ne Degree(F) then
    return false, "Function field is relative";
    end if;
*/

   if #ExactConstantField(F) gt qbound then
     return false, "Size of exact constant field is (likely to be) too large for the employed algorithm";
   end if;
//   if Degree(F) cmpeq Infinity() then
//      return false, "Function field currently needs to be a finite extension of a rational function field";
//   end if;
   if not DegreeBound cmpeq false and 
      ( Type(DegreeBound) ne RngIntElt or DegreeBound lt 1 ) then
      return false, 
        "Parameter 'DegreeBound' must be a rational integer greater equal 1";
   end if;
   if not SizeBound cmpeq Infinity() and 
      ( Type(SizeBound) ne RngIntElt or SizeBound lt 1 ) then
      return false, 
         "Parameter 'SizeBound' must be a rational integer greater equal 1";
   end if;
   if not ReductionDivisor cmpeq false and 
      ( Type(ReductionDivisor) ne DivFunElt or Degree(ReductionDivisor) lt 1 )
      then
      return false, 
   "Parameter 'ReductionDivisor' must be a divisor of degree greater equal 1";
   end if;
   if not Proof cmpeq "current" and 
      Type(Proof) ne BoolElt then
      return false, "Parameter 'Proof' must be a boolean";
   end if;
   return true, "all ok"; 
end function;
  
  
ClassGroupMain := procedure(F, userbound, sizebound, A, proof)
                  
    timeon := Cputime();              
    ClassGroupInitialize(F);
   
    if not userbound cmpeq false then
       F`cld`userbound := userbound;
       vprint ClassGroup :
         "Userbound is", userbound; 
    end if;
    
    F`cld`sizebound := sizebound;
    
    if A cmpeq false then
       A := Denominator(Divisor(F!BaseRing(F).1));
       vprint ClassGroup :
         "Reduction divisor is (x)_infty";
    else
       F`cld`A := A;
       vprint ClassGroup :
         "Reduction divisor is", A;
    end if;
                    
    HeuristicBound(F, proof);
    FactorBasisCreate(F, Support(A), F`cld`fbbound, sizebound);
    
    while #F`cld`fb eq 0 do
      FactorBasisEnlarge(F, #F`cld`fbbound + 1, sizebound);
    end while;
       
    RelSearch(F);   
    
    if F`cld`fbbound lt ClassGroupGenerationBound(F) then
       if proof then
          EvalDataGenerators(F);
          OverLatticeCheck(F);
          vprint ClassGroup : "result proven by lattice check";
          F`cld`proven := true;
       else
          F`cld`proven := false;   
       end if;
    else
       vprint ClassGroup : "result proven by bounds";
       F`cld`proven := true;
    end if;
       
    ClassGroupProfile(F, "ClassGroupMain", timeon);
    ClassGroupProfilePrint(F);
    
end procedure;
  

//////////////////////////////////////////////////////////////////////////////
  
ClassGroupStandardRepresentation := function(F, D)
   
   F := RationalExtensionRepresentation(F);
   if D cmpne false then
      D := DivisorGroup(F)!D;
   end if;
   return F, D;
   
end function;

//////////////////////////////////////////////////////////////////////////////
  
  
intrinsic ClassGroupAbelianInvariants(F::FldFunG: 
                                      DegreeBound := false, 
                                      SizeBound := Infinity(),               
                                      ReductionDivisor := false,
                                      Proof := "current" ) -> SeqEnum
{The Abelian invariants of the divisor class group of F};  

   ok, mess := ClassGroupArgumentChecks(F, DegreeBound, SizeBound,
                                        ReductionDivisor, Proof);
   require ok : mess;
   
   F, ReductionDivisor := 
     ClassGroupStandardRepresentation(F, ReductionDivisor);
      
   if not assigned F`cld then
      ClassGroupMain(F, DegreeBound, SizeBound, ReductionDivisor, 
                     Proof cmpeq false select false else true);
   end if;
      
   require not Proof cmpeq true or F`cld`proven eq true :
     "Class group data is already computed, but unproven";
   
   if not assigned F`cld`Clabelinv then
      EvalDataAbelianInvariants(F);
   end if;
      
   return F`cld`Clabelinv;
   
end intrinsic;
   
   
intrinsic ClassGroup(F::FldFunG: 
                     DegreeBound := false, 
                     SizeBound := Infinity(),               
                     ReductionDivisor := false,
                     Proof := "current" ) -> GrpAb, Map, Map
{The divisor class group of F as an Abelian group, a map of representatives from the class group to the divisor group and the homomorphism from the divisor group onto the divisor class group};  

   ok, mess := ClassGroupArgumentChecks(F, DegreeBound, SizeBound,
                                        ReductionDivisor, Proof);
   require ok : mess;
      
   Fre, ReductionDivisor := 
     ClassGroupStandardRepresentation(F, ReductionDivisor);
   
   if not assigned Fre`cld then
      ClassGroupMain(Fre, DegreeBound, SizeBound, ReductionDivisor, 
                     Proof cmpeq false select false else true);
   end if;
      
   require not Proof cmpeq true or Fre`cld`proven eq true :
     "Class group data is already computed, but unproven";
   
   if not assigned Fre`cld`DivToClFlat then
      EvalDataGenerators(Fre);
      EvalDataMaps(Fre);   
   end if;
   
   if not assigned F`cld then
      F`cld := rec< cld_fmt | >;
   end if;
   
   if not assigned F`cld`DivToClFlat then
      F`cld`Cl := Codomain(Fre`cld`DivToClFlat);
      F`cld`DivToClFlat := hom< DivisorGroup(F) -> F`cld`Cl | 
                              x :-> DivToClFlat(DivisorGroup(Fre)!x), 
                              y :-> DivisorGroup(F)!(y@@DivToClFlat) >
                           where DivToClFlat := Fre`cld`DivToClFlat;
   end if;
   
   return F`cld`Cl, Inverse(F`cld`DivToClFlat), F`cld`DivToClFlat; //FHmap
   
end intrinsic;


intrinsic ClassNumber(F::FldFunG) -> RngIntElt
{The order of the group of divisor classes of degree zero of F};  

   ok, mess := ClassGroupArgumentChecks(F, false, Infinity(),
                                        false, "current");
   require ok : mess;
   return &* Prune(ClassGroupAbelianInvariants(F));
   
end intrinsic;



intrinsic GlobalUnitGroup(F::FldFunG) -> GrpAb, Map
{The group of global units of F, i.e. the multiplicative group of the exact constant field, as an Abelian group together with the map into F};

   ok, mess := ClassGroupArgumentChecks(F, false, Infinity(),
                                        false, "current");
   require ok : mess;

   if not assigned F`S then
      F`S := { Places(F) | };
   end if;
   
   return SUnitGroup(F`S);
   
end intrinsic;


intrinsic IsGlobalUnit(a::FldFunElt) -> BoolElt
{Whether a is a global unit, i.e. a constant};

   return res where res, _ := IsConstant(a);

end intrinsic;


intrinsic IsGlobalUnitWithPreimage(a::FldFunElt) -> BoolElt, GrpAbElt
{True and the preimage of a in the global unit group, false otherwise};

    F := Parent(a);
    ok, mess := ClassGroupArgumentChecks(F, false, Infinity(),
                                         false, "current");
    require ok : mess;

    if not assigned F`S then
       F`S := { Places(F) | };
    end if;
    
    return IsSUnitWithPreimage(a, F`S);
    
end intrinsic;


intrinsic PrincipalDivisorMap(F::FldFunG) -> Map
{The map from the multiplicative group of the function field to the group of divisors};
   
   if not assigned F`S then
      F`S := { Places(F) | };
   end if;
   
   return SPrincipalDivisorMap(F`S);
   
end intrinsic;   


intrinsic ClassGroupExactSequence(F::FldFunG) -> Map, Map, Map
{Returns the three maps in the center of the exact sequence 0 -> k -> F -> Div -> Cl -> 0 where k is the global unit group of the function field, F is the multiplicative group of the function field, Div is the divisor group and Cl is the divisor class group}
  
   ok, mess := ClassGroupArgumentChecks(F, false, Infinity(),
                                        false, "current");
   require ok : mess;
   
   if not assigned F`S then
      F`S := { Places(F) | };
   end if;
   
   return SClassGroupExactSequence(F`S);
      
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
  
/*  
intrinsic HasPreimageNew(x::., f::Map) -> BoolElt, .
{True and the preimage of x under f iff it exists, false otherwise};  

   if assigned f`PreimageTest then
      return f`PreimageTest(x);
   end if;
   
   return HasPreimage(x, f);
   
end intrinsic;
*/

  
LogBase := function(b, a)
//
//  Return true and r if r exists such that b = a^r, false otherwise. 
//     (a, b finite field elements).           
//
   k := Log(a);
   l := Log(b);
   n := #Parent(a)-1;
     
   n1 := Gcd(n, k);
   
   if l mod n1 ne 0 then
      return false, _;
   end if;
   
   n2 := n div n1;
   k2 := k div n1;
   l2 := l div n1;
   
   // invert k2 mod n2 and mult with l2
   res := (l2 * inv) mod n2 where _, inv, _ := XGCD(k2, n2);  
   
   return true, res;
   
end function;
  
   
SUnitGroupSubTrivial1 := function(S)
   
   // Return f1: U(S) -> F^*
   
   assert #S lt 2;
     
   F := FunctionField(Universe(S));  
   k := ExactConstantField(F);
   US := AbelianGroup( [#k-1] );
                 
   FToUS := function(a)
      if IsZero(a) then
         print "";
         error "Runtime error: Element is zero";
      end if;
      ok, b := IsConstant(a);
      if not ok then
         print "";
         error"Runtime error: Element has no preimage";
      end if;
      return US![ Log(b) ];
   end function;
      
   FToUSTest := function(a) // copy paste from above
      if IsZero(a) then
         return false, _;
      end if;
      ok, b := IsConstant(a);
      if not ok then
         return false, _;
      end if;
      return true, US![ Log(b) ];
   end function;
      
   a := F!PrimitiveElement(k);  
   f1 := map< US -> F | x :-> a^Eltseq(x)[1], y :-> FToUS(y) >;
   f1`PreimageTest := FToUSTest; 
   
   return f1;
   
end function;
   
   
SUnitGroupSubTrivial2 := function(S)   
   
   // Return f2: F^* -> Div(S)
   
   assert #S lt 2;
   
   F := FunctionField(Universe(S));  
   if #S eq 0 then
     FToDivS := function(a)
        if IsZero(a) then
           print "";
           error "Runtime error: Element is zero";
        end if;   
        return Divisor(a);
     end function;
     DivSToFTest := IsPrincipal;   
     DivSToF := function(D)
        ok, a := IsPrincipal(D);
        if not ok then
           print "";
           error"Runtime error: Element has no preimage";
        end if;
        return a;
     end function;         
   else
      P := Representative(S);
      FToDivS := function(a)
        if IsZero(a) then
           print "";
           error "Runtime error: Element is zero";
        end if;   
        return D - Valuation(D, P)*P where D := Divisor(a);
      end function;
      DivSToFTest := function(D)
         d, r := Quotrem(Degree(D), Degree(P));
         if r ne 0 then
            return false, _;
         end if;
         ok, a := IsPrincipal(D - d*P);
         if not ok then
            return false, _;
         end if;
         return true, a;
      end function;         
      DivSToF := function(D) 
         ok, a := DivSToFTest(D);
         if not ok then
            print "";
            error"Runtime error: Element has no preimage";
         end if;
         return a;
      end function;
   end if;
        
   f2 := map< F -> DivisorGroup(F) | x :-> FToDivS(x), y :-> DivSToF(y) >;   
   f2`PreimageTest := DivSToFTest;

   return f2;
   
end function;
   
   
SUnitGroupSub := function(S, fS, f)
   
   // Returns f1 : U(S) -> F^* and f2 : F^* -> Div / <S>
   
   assert #S gt 1;  
     
   F := FunctionField(Universe(S));
   Cl := Universe(fS);
   
   P := Representative( [ P : P in L | Degree(P) eq min ] ) 
        where min := Minimum( [ Degree(P) : P in L ] )
        where L := Support(DivisorOfDegreeOne(F));
   t := LocalUniformizer(P);
     
   ZS := FreeAbelianGroup(#S);
   g := hom< ZS -> Cl | fS >;
   M := LLL(Matrix( Integers(), NumberOfGenerators(U), #S, 
                [ Eltseq(ZS!a) : a in Generators(U) ] ))
        where U := Kernel(g);
   if NumberOfRows(M) ne #S-1 then
      error "Error in package SUnitGroupSub : Corrupt data I";
   end if;
   B := [ - &+ [ DivisorGroup(F) | M[i][j] * S[j] 
                 : j in [1..#S] ] : i in [1..#S-1] ];
   if not &and [ Degree(D) eq 0 and Dimension(D) eq ecfdim : D in B ] 
                where ecfdim := DimensionOfExactConstantField(F) then
      error "Error in package SUnitGroupSub : Corrupt data II";
   end if;
   B := [ Basis(D)[1] : D in B ];
   Bev := [ ResidueClassField(P) | 
            Evaluate(ProductRepresentation([b, t], [1, -Valuation(b, P)]), P) 
            : b in B ];
   if #ExactConstantField(F) eq 2 then
     // the direct sum below kills the additional trivial generator
     // hence this case
     US := FreeAbelianGroup(#S-1); 
     rf_prim := F!PrimitiveElement(ExactConstantField(F));                   
     rf_prim_ev := Evaluate(rf_prim, P);   
     US_gens := [ Identity(US) ] cat [ US.i : i in [1..#S-1] ];
  else
     US := DirectSum(AbelianGroup([#ExactConstantField(F)-1]),
                     FreeAbelianGroup(#S-1));
     rf_prim := F!PrimitiveElement(ExactConstantField(F));                   
     rf_prim_ev := Evaluate(rf_prim, P);   
     B := [ rf_prim ] cat B;
     US_gens := [ US.i : i in [1..#S] ];
  end if;
     
     
   USToF := function(a)
      // FH -> Nicole:
      // print "using prod rep for", B, Eltseq(a);
      return ProductRepresentation(B, v) where v := Eltseq(a);
   end function;
   
   FToUS := function(a)
      if IsZero(a) then
         print "";
         error "Runtime error: Element is zero";
      end if;
      D := Divisor(a);
      if not &and [ P in S : P in Support(D) ] then
         print "";
         error "Runtime error: Element has no preimage";
      end if;
      v := Solution(M, Matrix(#S, [ Valuation(D, P) : P in S ]))[1];
      ok, w := LogBase( Evaluate(ProductRepresentation([a, t], 
                                 [1, -Valuation(a, P)]), P) / 
                        &* [ ResidueClassField(P) | Bev[i]^v[i] : 
                             i in [1..#S-1] ], rf_prim_ev );
      assert ok;
      b := w * US_gens[1] + &+ [ US | v[i] * US_gens[i+1] : i in [1..#S-1] ];
      // assert USToF(b) eq a;  // temporarily switched on             
      return b;
   end function;
      
   FToUSTest := function(a)  // copy paste from above
      if IsZero(a) then
          return false, _;
      end if;
      D := Divisor(a);
      if not &and [ P in S : P in Support(D) ] then
          return false, _;
      end if;
      v := Solution(M, Matrix(#S, [ Valuation(D, P) : P in S ]))[1];
      ok, w := LogBase( Evaluate(ProductRepresentation([a, t],
                                 [1, -Valuation(a, P)]), P) /
                        &* [ ResidueClassField(P) | Bev[i]^v[i] : 
                             i in [1..#S-1] ], rf_prim_ev );
      assert ok;
      b := w * US_gens[1] + &+ [ US | v[i] * US_gens[i+1] : i in [1..#S-1] ];
      // assert USToF(b) eq a;  // temporarily switched on             
      return true, b;
   end function;
            
   FToDivS := function(a)
      if IsZero(a) then
        print "";
        error "Runtime error: Element is zero";
      end if;   
      return &+ [ DivisorGroup(F) | Valuation(D, P)*P : 
                  P in Support(D) | not P in S ] where D := Divisor(a);
   end function;
      
   DivSToF := function(D)
      D := &+ [ DivisorGroup(F) | Valuation(D, P) * P : P in Support(D) 
                | not P in S ];
      ok, a := HasPreimage(f(D), g);
      if not ok then
         print "";
         error "Runtime error: Element has no preimage";
      end if;
      if not IsIdentity(a) then
         M1 := Matrix( Integers(), #S, #S, 
                       [ Eltseq(M[i]) : i in [1..#S-1] ] cat [ Eltseq(a) ] );
         // take small representative in Eltseq(a) mod rows(M)
         D := D - &+ [ DivisorGroup(F) | v[i]*S[i] : i in [1..#S] ]
                       where v := GramSchmidtReduce(M1, #S-1)[#S];
      end if;
      ok, a := IsPrincipal(D);
      assert ok;
      return a;
   end function;
         
   DivSToFTest := function(D)   // copy paste from above
      D := &+ [ DivisorGroup(F) | Valuation(D, P) * P : P in Support(D) 
                | not P in S ];
      ok, a := HasPreimage(f(D), g);
      if not ok then
         return false, _;
      end if;
      if not IsIdentity(a) then
         M1 := Matrix( Integers(), #S, #S, 
                       [ Eltseq(M[i]) : i in [1..#S-1] ] cat [ Eltseq(a) ] );
         // take small representative in Eltseq(a) mod rows(M)
         D := D - &+ [ DivisorGroup(F) | v[i]*S[i] : i in [1..#S] ]
                       where v := GramSchmidtReduce(M1, #S-1)[#S];
      end if;
      ok, a := IsPrincipal(D);
      assert ok;
      return true, a;
   end function;
         
   f1 := map< US -> F | x :-> USToF(x), y :-> FToUS(y) >;
   f1`PreimageTest := FToUSTest;
   f2 := map< F -> DivisorGroup(F) | x :-> FToDivS(x), y :-> DivSToF(y) >;
   f2`PreimageTest := DivSToFTest;
   
   return f1, f2;   
                          
end function;

   
   
SClassGroupSub := function(S, fS, f)
      
   // Returns f3 : Div -> Cl(S)  (resp. Div / <S> -> Cl(S) )
   
   assert #S gt 0;  
     
   F := FunctionField(Universe(S));
   Cl := Universe(fS);
   ClS, p := quo< Cl | fS >;
   h := f*p;
   ClSToDiv := function(a)
      // maybe apply further reductions to the preimages of the generators
      return &+ [ Domain(f) | expos[i]*places[i] : i in [1..#places] | 
                     not places[i] in S ]
                  where places, expos := Support(a@@h);
   end function;
      
   f3 := hom< DivisorGroup(F) -> ClS | x :-> h(x), y :-> ClSToDiv(y) >;
   return f3;
   
end function;

   
////////////////////////////////////////////////////////////////////////////
  
  
SClassGroupArgumentChecks := function(S)
   if Parent(S) cmpeq Parent({}) then
      return false, "Set has no universe";
   end if;
   Pl := Universe(S);
   if Type(Pl) ne PlcFun then
      return false, "Given set must be a set of places of an algebraic function field";
   end if;
   F := FunctionField(Pl);
   if not IsGlobal(F) then
      return false, "Function field is not global";
   end if;
//   if Degree(F) cmpeq Infinity() then
//      return false, "Function field currently needs to be a finite extension of a rational function field";
//   end if;
   return true, "all ok";   
end function;
  
   
   
intrinsic SUnitGroup(S::{PlcFunElt}) -> GrpAb, Map
{The group of S-units as an Abelian group and the map into the function field};  

   if assigned S`USToF then
      return Domain(f1), f1 where f1 := S`USToF;
   end if;
   
   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;
   
   if #S lt 2 then
      f1 := SUnitGroupSubTrivial1(S);
      f2 := SUnitGroupSubTrivial2(S);
   else
      _, _, f := ClassGroup(FunctionField(Universe(S))); //FHmap
      if not assigned S`fS then
         S`S := SetToSequence(S);
         S`fS := f( [ 1*P : P in S`S ] );
      end if;
      f1, f2 := SUnitGroupSub(S`S, S`fS, f);
   end if;
         
   S`USToF := f1;
   S`FToDivS := f2;
   // small remark: no cyclic ref to S here because f1,f2 ref S`S not S 
   
   return Domain(f1), f1;   
   
end intrinsic;
   


intrinsic IsSUnit(a::FldFunElt, S::{PlcFunElt}) -> BoolElt
{True if a is an S-unit, false otherwise};

   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;
   
   if IsZero(a) then
      return false;
   end if;
   
   return SequenceToSet(Support(Divisor(a))) subset S;

end intrinsic;


intrinsic IsSUnitWithPreimage(a::FldFunElt, S::{PlcFunElt}) -> BoolElt, GrpAbElt
{True and the preimage of a in the S-unit group if a is an S-unit, false otherwise};
  
   // This intrinsic we need because HasPreimage(a, f1) doesn't work
   // neither we can check for two return values in IsSUnit()  
     
   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;
   
   if IsZero(a) then
      return false, _;
   end if;
   
   return f1`PreimageTest(a) where _, f1 := SUnitGroup(S);   
   
end intrinsic;



intrinsic SRegulator(S::{PlcFunElt}) -> RngIntElt
{The S-Regulator};

   if assigned S`SReg then
      return S`SReg;
   end if;
   
   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;

   if #S lt 2 then
      S`SReg := 1;
   else   
      Cl, _, f := ClassGroup(FunctionField(Universe(S))); //FHmap
      if not assigned S`fS then
         S`S := SetToSequence(S);
         S`fS := f( [ 1*P : P in S`S ] );
      end if;
      S`SReg := #TorsionSubgroup( sub< Cl | S`fS > );
   end if;
      
   return S`SReg;
   
end intrinsic;


intrinsic SPrincipalDivisorMap(S::{PlcFunElt}) -> Map
{The map from the multiplicative group of the function field to the
group of divisors (mod places in S)};

   if assigned S`FToDivS then
      return S`FToDivS;
   end if;
   
   if #S lt 2 then  // makes it work in the non global case as well
     f2 := SUnitGroupSubTrivial2(S);
     S`FToDivS := f2;
   else
      ok, mess := SClassGroupArgumentChecks(S);
      require ok : mess;
      _, _ := SUnitGroup(S);
      f2 := S`FToDivS;
   end if;
   
   return f2;   
   
end intrinsic;
      

intrinsic IsSPrincipal(D::DivFunElt, S::{PlcFunElt}) -> BoolElt, FldFunElt
{True and a generator if D is principal modulo places in S, false otherwise};

   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;

   return SPrincipalDivisorMap(S)`PreimageTest(D);
   
end intrinsic;


intrinsic SClassGroup(S::{PlcFunElt}) -> GrpAb, Map, Map
{The S-class group as an Abelian group, a map of representatives from the S-class group to the group of divisors (mod places in S) and the homomorphism from the group of divisors (mod places in S) onto the S-class group}
  
   if assigned S`DivSToClS then
      return Codomain(f3), Inverse(f3), f3 where f3 := S`DivSToClS;
   end if;
   
   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;
   
   F := FunctionField(Universe(S));
   if #S eq 0 then
      _, _, f3 := ClassGroup(F); //FHmap
   else 
      _, _, f := ClassGroup(F);  //FHmap
      if not assigned S`fS then
         S`S := SetToSequence(S);
         S`fS := f( [ 1*P : P in S`S ] );
      end if;
      f3 := SClassGroupSub(S`S, S`fS, f);
   end if;
      
   S`DivSToClS := f3;
   
   return Codomain(f3), Inverse(f3), f3; //FHmap
    
end intrinsic;



intrinsic SClassGroupExactSequence(S::{PlcFunElt}) -> Map, Map, Map
{Returns the three maps in the center of the exact sequence 0 -> U -> F -> Div -> Cl -> 0 where U is the S-unit group, F is the multiplicative group of the function field, Div is the group of divisors (mod places in S) and Cl is the S-class group}
  
   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;
   
   _, f1 := SUnitGroup(S);
   f2 := SPrincipalDivisorMap(S);
   _, _, f3 := SClassGroup(S);  //FHmap
   
   return f1, f2, f3;
   
end intrinsic;
   

intrinsic SClassGroupAbelianInvariants(S::{PlcFunElt}) -> SeqEnum
{The Abelian invariants of the S-class group};

   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;

   // Remark: the Abelian invariants we could have a little cheaper
   // as done for the full class group (avoid computing generators)
     
   return AbelianInvariants(SClassGroup(S));      
   
end intrinsic;
   
   
intrinsic SClassNumber(S::{PlcFunElt}) -> RngIntElt
{The order of the torsion part of the S-class group};

   ok, mess := SClassGroupArgumentChecks(S);
   require ok : mess;

   // See above remark
   return #TorsionSubgroup(SClassGroup(S));
     
end intrinsic;

   
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
  
  
ClassGroupCheckOrder := function(O)

   if not IsGlobal(FunctionField(O)) then
      return false, "Function field of given order must be global";
   end if;

/*
    if AbsoluteDegree(O) ne Degree(O) then
	return false, "Order is relative";
    end if;
*/

   if not IsMaximal(O) then
      return false, "Order must be maximal";
   end if;
   if not IsFiniteOrder(O) then
      return false, "Order must be finite";
   end if;
   if #ExactConstantField(FunctionField(O)) gt qbound then
     return false, "Size of exact constant field is (likely to be) too large for the employed algorithm";
   end if;
   return true, "all ok";
end function;
  
   
   
intrinsic UnitGroup(O::RngFunOrd) -> GrpAb, Map
{The unit group of a finite maximal order O as an Abelian group and the map from the unit group into O};

   F := FunctionField(O);
   
   // Remark: Because the codomain is O computing images involves 
   // checking the result to lie in O which involves multiplying 
   // (huge) power products out!
        
   if assigned O`UToF then
      f1 := O`UToF;
      U := Domain(f1);
      f1O := map< U -> O | x :-> O!f1(x), y :-> (F!y)@@f1 >;
      f1O`PreimageTest := function(y)
         return f1`PreimageTest(F!y);
      end function;
      return U, f1O;   
   end if;
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;

   if not assigned O`S then
      S := SequenceToSet(Poles(F!BaseRing(F).1));
      ok, mess := SClassGroupArgumentChecks(S);
      require ok : mess;
      O`S := S;
   end if;
   
   U, f1 := SUnitGroup(O`S); 
   O`UToF := f1;
   
   f1O := map< U -> O | x :-> O!f1(x), y :-> (F!y)@@f1 >;
   f1O`PreimageTest := function(y)
      return f1`PreimageTest(F!y);
   end function;
   
   return U, f1O;
      
end intrinsic;



intrinsic IsUnitWithPreimage(a::RngFunOrdElt) -> BoolElt, GrpAbElt
{True and the preimage of a in the unit group of O if a is a unit, false otherwise};

   // This intrinsic we need because HasPreimage(a, f1) doesn't work
   // neither we can check for two return values in IsUnit()  
     
   ok, mess := ClassGroupCheckOrder(Parent(a));
   require ok : mess;
   
   if IsZero(a) then
      return false, _;
   end if;
   
   return f1`PreimageTest(a) where _, f1 := UnitGroup(Parent(a));

end intrinsic;



intrinsic Regulator(O::RngFunOrd) -> RngIntElt
{The regulator of the unit group of the finite maximal order O};
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   if not assigned O`S then
      F := FunctionField(O);
      S := SequenceToSet(Poles(F!BaseRing(F).1));
      ok, mess := SClassGroupArgumentChecks(S);
      require ok : mess;
      O`S := S;
   end if;

   return SRegulator(O`S);
     
end intrinsic;



intrinsic PrincipalIdealMap(O::RngFunOrd) -> Map
{The map from the multiplicative group of the field of fractions of O to the group of fractional ideals of O where O is a finite maximal order};  

   if assigned O`FToId then
      return O`FToId;
   end if;
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   F := FunctionField(O);
   
   if not assigned O`S then
      S := SequenceToSet(Poles(F!BaseRing(F).1));
      ok, mess := SClassGroupArgumentChecks(S);
      require ok : mess;
      O`S := S;
   end if;
   
   f2 := SPrincipalDivisorMap(O`S);
   
   FToId := function(a)
      if IsZero(a) then
         print "";
         error "Runtime error: Argument is zero";
      end if;
      return a*O;
   end function;
    
   IdToF := function(I)
      if IsZero(I) then
         print "";
         error "Runtime error: Argument is zero";
      end if;
      ok, a := f2`PreimageTest(Divisor(I));
      if not ok then
         print "";
         error "Runtime error: Element has no preimage";
      end if;   
      return a;
   end function;
       
   IdToFTest := function(I)
      if IsZero(I) then
         return false, _;
      end if;
      ok, a := f2`PreimageTest(Divisor(I));
      if not ok then
         return false, _;
      end if;   
      return true, a;
   end function;
      
   f2 := map< F -> Id | x :-> FToId(x), y :-> IdToF(y) >
         where Id := Parent(1*O);
   f2`PreimageTest := IdToFTest;
   
   O`FToId := f2;
   
   return f2;
   
end intrinsic;


intrinsic IsPrincipal(I::RngFunOrdIdl) -> BoolElt, FldFunElt
{True and a generator if the fractional ideal I is principal, false otherwise};

   ok, mess := ClassGroupCheckOrder(Order(I));
   require ok : mess;
   
   if IsZero(I) then
      return true, FunctionField(Order(I))!0;
   end if;
   
   return PrincipalIdealMap(Order(I))`PreimageTest(I);

end intrinsic;


intrinsic ClassGroup(O::RngFunOrd) -> GrpAb, Map, Map
{The ideal class group of the finite maximal order O as an Abelian group, a map of representatives from the ideal class group to the group of fractional ideals and the homomorphism from the group of fractional ideals onto the ideal class group};  

   if assigned O`IdToCl then
      return Codomain(f3), Inverse(f3), f3 where f3 := O`IdToCl;
   end if;
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   F := FunctionField(O);
   
   if not assigned O`S then
      S := SequenceToSet(Poles(F!BaseRing(F).1));
      ok, mess := SClassGroupArgumentChecks(S);
      require ok : mess;
      O`S := S;
   end if;
   
   ClS, _, f3 := SClassGroup(O`S); //FHmap
   
   IdToClS := function(I)
      if IsZero(I) then
         error "Runtime error: Argument is zero";
      end if;
      return f3(Divisor(I));
   end function;
       
   Id := Parent(1*O);
   f3 := hom< Id -> ClS | x :-> IdToClS(x), 
                          y :-> I where I := Ideals(y@@f3) >;
   O`IdToCl := f3;
   
   return ClS, Inverse(f3), f3; //FHmap
   
end intrinsic;


intrinsic ClassGroupExactSequence(O::RngFunOrd) -> Map, Map, Map
{Returns the maps in the center of the exact sequence 0 -> U -> F -> Id -> Cl -> 0 where U is the unit group of O, F is the multiplicative group of the field of fractions of O, Id is the group of fractional ideals of O and Cl is the class group of O for a finite maximal order O} 

   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;

    _, _ := UnitGroup(O);
    f1 := O`UToF;
    f2 := PrincipalIdealMap(O);
    _, _, f3 := ClassGroup(O); //FHmap

    return f1, f2, f3;
    
end intrinsic;



intrinsic ClassGroupAbelianInvariants(O::RngFunOrd) -> SeqEnum
{The Abelian invariants of the ideal class group of the finite maximal order O};

   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
     
   return AbelianInvariants(ClassGroup(O));      
   
end intrinsic;
   
   
intrinsic ClassNumber(O::RngFunOrd) -> RngIntElt
{The order of the ideal class group of the finite maximal order O};

   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   return #ClassGroup(O);
     
end intrinsic;

   
intrinsic FundamentalUnits(O::RngFunOrd) -> SeqEnum
{A sequence of fundamental units of the finite maximal order O};
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   U, f := UnitGroup(O);
   return [ O | f(U!x) : x in Generators(TorsionFreeSubgroup(U)) ];
   
end intrinsic;


intrinsic IndependentUnits(O::RngFunOrd) -> SeqEnum
{A sequence of independent units of the finite maximal order O};
   
   ok, mess := ClassGroupCheckOrder(O);
   require ok : mess;
   
   return FundamentalUnits(O);
   
end intrinsic;


////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
     
  
intrinsic DeleteAttributes(R::Rng)
{Remove all attributes from R};

    DeleteS := procedure(R)
       delete R`S`S;
       delete R`S`fS;
       delete R`S`SReg;
       delete R`S`USToF;
       delete R`S`FToDivS;
       delete R`S`DivSToClS;              
    end procedure;

    if Type(R) eq FldFun then
       if assigned R`S then
          DeleteS(R);
       end if;
       O := MaximalOrderFinite(R);
       if assigned O`S then
          DeleteS(O);
       end if;
       delete O`S;
       delete O`UToF;
       delete O`FToId;
       delete O`IdToCl;
       delete R`S;
       delete R`cld;
    elif Type(R) eq RngFunOrd then   
       if assigned R`S then
          DeleteS(R);
       end if;
       F := FunctionField(R);
       if assigned F`S then
          DeleteS(F);
       end if;
       delete F`S;
       delete F`cld;
       delete R`S;
       delete R`UToF;
       delete R`FToId;
       delete R`IdToCl;
    else
       require false : 
         "Ring must be function field or function field order";   
    end if;
    
end intrinsic;


////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////

  
ClassGroupChecksSub := procedure(f1, f2, f3, R, S, IsZe, IsU, IsPrinc, op)  
     
   F := FunctionField(R);              
   gens := [ SU.i : i in [1..NumberOfGenerators(SU)] ]
           where SU := Domain(f1);
   assert [ x@@f1 : x in f1(gens) ] eq gens; 
   assert [ x@@f1 : x in f1(l) ] eq l 
         where l := [ 123456789876543214711 * g : g in gens ];
   assert &and [ IsZe(f2(f1(g))) : g in gens ]; 
   assert &and [ IsZe(f2(f1(g))) : g in l ]
        where l := [ 123456789876543214711 * g : g in gens ];
   if Type(R) ne RngFunOrd then
      d := 1;
      ecfdim := DimensionOfExactConstantField(F);
      while true do
         ok1, P1 := HasPlace(F, d*ecfdim);
         ok2, P2 := HasPlace(F, (d+1)*ecfdim);
         if ok1 and ok2 and not P1 in S and not P2 in S then
            break;
         end if;
         d := d + 1;
      end while;
      D := - &+ [ DivisorGroup(F) | 1*P : P in S ] - P1;
      while (Degree(D) div ecfdim) lt Genus(F)+3 do
         D := D + P2;
      end while;
      B := Basis(D);
      for a in B do
         assert f1`PreimageTest(a) eq false and IsU(a) eq false;
         assert f1`PreimageTest(f2(a)@@f2 div a) and IsU(f2(a)@@f2 div a); 
         assert IsIdentity(f3(f2(a)));
      end for;   
   else
      // should always work but could theoretically be wrong tests here
      a := R!Domain(f2).1 + BaseRing(R).1;   
      assert f1`PreimageTest(a) eq false and IsU(a) eq false;
      assert f1`PreimageTest(f2(a)@@f2 div a) and IsU(f2(a)@@f2 div a);
      assert IsIdentity(f3(f2(a)));
      a := (a^11 + a + 1)*(a + 1)*a; 
      assert f1`PreimageTest(a) eq false and IsU(a) eq false;
      assert f1`PreimageTest(f2(a)@@f2 div a) and IsU(f2(a)@@f2 div a);
      assert IsIdentity(f3(f2(a)));
   end if;
   gens := [ Cl.i : i in [1..NumberOfGenerators(Cl)] ]
           where Cl := Codomain(f3);
   assert f3([ x@@f3 : x in gens]) eq gens;
   assert f3( [ op(gens[i]@@f3, -h+1) : i in [1..#l] ] ) eq 
           [ gens[i] : i in [1..#l] ]
          where h := &* l where l := TorsionInvariants(Codomain(f3));
   assert not &or [ f2`PreimageTest(gens[i]@@f3) : i in [1..#gens] ];
   assert not &or [ IsPrinc(gens[i]@@f3) : i in [1..#gens] ];
   assert &and [ f2`PreimageTest(op(gens[i]@@f3, l[i])) : i in [1..#l] ]
          where l := TorsionInvariants(Codomain(f3));
   assert &and [ IsPrinc(op(gens[i]@@f3, l[i])) : i in [1..#l] ]
          where l := TorsionInvariants(Codomain(f3));
   assert &and [ f2(g@@f2) eq g : 
           g in [ op(gens[i]@@f3, l[i]) : i in [1..#l] ] ]
           where l := TorsionInvariants(Codomain(f3));
   deg := #S gt 0 select Gcd( [ Degree(P) div 
     DimensionOfExactConstantField(F) : P in S ] ) else 1;
   sreg := Type(R) eq RngFunOrd select Regulator(R) else SRegulator(S);
   sclnum := Type(R) eq RngFunOrd select ClassNumber(R) 
             else SClassNumber(S);
   assert sreg * sclnum eq deg * ClassNumber(F);
   
end procedure;              
   
   
intrinsic ClassGroupChecks(F::FldFunG, all::BoolElt)
{Do some checks of the class group functionality. If all is true check the functions for the finite maximal order as well};

   f1, f2, f3 := ClassGroupExactSequence(F);         
   S := F`S;
   R := F;
   IsZe := IsZero;
   IsU := IsConstant;
   IsPrinc := IsPrincipal;
   op := function(D, k) return k*D; end function;
   ClassGroupChecksSub(f1, f2, f3, F, F`S, IsZe, IsU, IsPrinc, op);
        
   if all then
      O := MaximalOrderFinite(F);
      f1, f2, f3 := ClassGroupExactSequence(O);         
      S := O`S;
      R := O;
      IsZe := IsOne;
      IsU := IsUnit;
      IsPrinc := IsPrincipal;
      op := function(D, k) return D^k; end function;
      ClassGroupChecksSub(f1, f2, f3, O, O`S, IsZe, IsU, IsPrinc, op);
   else  /* avoids integrality check of units ... */
      S := SequenceToSet(Poles(F!BaseRing(F).1));   
      f1, f2, f3 := SClassGroupExactSequence(S);         
      R := F;           
      IsZe := IsZero;
      IsU := function(a) return IsSUnit(a, S); end function;
      IsPrinc := function(a) return IsSPrincipal(a, S); end function;
      op := function(D, k) return k*D; end function;              
   end if;
      
   d := 2;
   while #Places(F, d) lt 2 do
     d := d + 1;
   end while;
        
   S := { Places(F, d)[1] };
   f1, f2, f3 := SClassGroupExactSequence(S);         
   R := F;           
   IsZe := IsZero;
   IsU := function(a) return IsSUnit(a, S); end function;
   IsPrinc := function(a) return IsSPrincipal(a, S); end function;
   op := function(D, k) return k*D; end function;              
   ClassGroupChecksSub(f1, f2, f3, F, S, IsZe, IsU, IsPrinc, op);
        
   S := { S[1], S[2] } where S := Places(F, d);
   f1, f2, f3 := SClassGroupExactSequence(S);         
   R := F;           
   IsZe := IsZero;
   IsU := function(a) return IsSUnit(a, S); end function;
   IsPrinc := function(a) return IsSPrincipal(a, S); end function;
   op := function(D, k) return k*D; end function;              
   ClassGroupChecksSub(f1, f2, f3, F, S, IsZe, IsU, IsPrinc, op);
        
   S := SequenceToSet(Places(F, d));   
   f1, f2, f3 := SClassGroupExactSequence(S);         
   R := F;           
   IsZe := IsZero;
   IsU := function(a) return IsSUnit(a, S); end function;
   IsPrinc := function(a) return IsSPrincipal(a, S); end function;
   op := function(D, k) return k*D; end function;              
   ClassGroupChecksSub(f1, f2, f3, F, S, IsZe, IsU, IsPrinc, op);
   
end intrinsic;
