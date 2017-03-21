freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: mestre.m (Mestre-Oesterle "method of graphs")                      

   2004-10-24: (was) commented out an exported intrinsic that began xxx_

   09/10/03: Fixed slight bug in FindSupersingularJ where it 
   would return the j but forget to coerce it into a quadratic
   extension of GF(p).  
   Also, I improved FindSupersingularJ so it succeeds in 
   all cases.

   Revision 1.1  2001/04/20 04:46:59  was
   Initial revision

   Revision 1.4  2001/01/16 11:01:57  was
   *** empty log message ***

   Revision 1.3  2000/06/24 09:39:33  was
   added a function BasisX0.

   Revision 1.2  2000/06/24 09:33:51  was
   fix the way too slow at high level bug!

   Revision 1.1  2000/05/02 08:02:59  was
   Initial revision
                                                                 

 ***************************************************************************/


/**********************************************************
   IMPORTANT NOTE: None of the functions in this file are
   exported in the current version of HECKE. The reason is that
   we don't yet have a nice interface via Hack objects. 
   For this reason these functions are imported by compgrp.m.
   In the future, this will change to a stand-alone package with
   intrinsics, and then compgrp.m will be suitably modified. 
 ************************************************************/


import "calc.m" :   EigenvectorOfMatrixWithCharpoly ;

import "linalg.m" : MyCharpoly,
                    Restrict;


forward             FindSupersingularJ,
                    TpSS,
                    Mestre,
                    TpD,
                    MestreEisensteinFactor,
                    MonodromyWeights,
                    SupersingularBasis,
                    Decomposition,
                    MestreEigenvector;


/**********************************************************************

              METHOD OF GRAPHS                                         

   Based on requests of Loic Merel, I implemented this system using    
   various tricks I learned from several distinct sources.  The most   
   important is Mestre's paper:   

     Mestre, J.-F.,  La m\'ethode des graphes. Exemples et applications 
     Proceedings of the international conference on class  numbers      
     and fundamental units of algebraic number fields (Katata)          
     217--242, Nagoya Univ., Nagoya, 1986.                              
                                                                      
   However, this paper contains errors, especially in the formulas
   for the isogeny polynomials at the end.  These errors have been 
   corrected in this implementation.
 
**********************************************************************/



SSTABLE := [  
// If negative, uses Kronecker test, if positive then a supersingular
// p is given by the second entry. 
    [-1,1728],  [-2,8000], [-3,0], 
    [-7,255^3], [-11,(-32)^3], [-19,-884736],
    [-43,-884736000], [-67, (-5280)^3], [-163, -262537412640768000],

// The exceptions for p<10^6.
    [15073,5797], [18313,10629], [38833,16622],
    [69337,2840], [71593,33119], [242713,87914],
    [448177,18081], [708481,79970], [716857, 389681],
    [882289,589416], [886537, 212553],
    [1000393, 7464], [1011697, 1728],
    [1045081, 64], [1049833, 29114],
    [1060777, 15070], [1072537, 2476],
    [1084297, 8507], [1020457,63], [1097209,8325], [1109761,10167], 
    [1110817,10386], [1120849,3192], [1123873,353], [1124209,666], 
    [1125793,11999], [1127281,2721], [1134193,13804], [1137313,26926], 
    [1152937,9843], [1155169,1005], [1157641,1901], [1175497,527], 
    [1175617,1359], [1198033,14317], [1198201,9510], [1204681,3253], 
    [1213921,9169], [1233409,452], [1238521,5593], [1239529,3424], 
    [1255081,4656], [1270537,331], [1271953,1047], [1277761,4720], 
    [1313761,212], [1326889,5544], [1332433,5336], [1358809,794], 
    [1359913,7897], [1369201,13421], [1373761,2163], [1377601,2334], 
    [1381153,1416], [1384993,17581], [1386361,7832], [1397257,16025], 
    [1406617,2850], [1408873,31690], [1411369,3299], [1420057,2293], 
    [1427281,1281], [1430521,8186], [1433833,11499], [1438537,1960], 
    [1440961,2131], [1447009,7565], [1451041,4913], [1451521,13445], 
    [1453897,3663], [1490833,16549], [1497049,617], [1497577,388],
    [1501921,8996], [1508929,3737], [1517569,1834], [1522249,5320],
    [1524433,3265], [1526977,2125], [1532017,4682], [1545553,7606],
    [1554529,5923], [1583233,2300], [1588777,13156], [1591969,592],
    [1616113,4853], [1621657,5315], [1647097,575], [1648441,15964],
    [1661137,14756], [1662697,20057], [1666729,11832], [1670953,39874],
    [1679833,3138], [1707577,3339], [1753249,1480], [1774777,1645],
    [1774921,12124], [1775041,21338], [1778473,2352], [1790713,10638],
    [1797097,337], [1802641,301], [1810153,4641], [1812721,4084],
    [1846177,26819], [1856233,5291], [1865161,6363], [1881961,323],
    [1884481,8216]
];


function FindSupersingularJ(p) 
// Returns a supersingular j-invariant in characteristic p < 10^6.
   k := FiniteField(p,2 : Optimize := false);

   // When we do this, it leaks memory like crazy!!!!
   //   k := FiniteField(p,2 : Optimize := true);

   for s in SSTABLE do
      if (s[1] lt 0 and KroneckerSymbol(s[1],p) eq -1)
        or s[1] eq p then
         return k!s[2];
      end if;
   end for;
   function IsSS(j) 
      return IsSupersingular(EllipticCurveFromjInvariant(j));
   end function;
   for j in GF(p) do 
      if IsSS(j) then
         return k!j;
      end if;
   end for;
end function;


///////////////////////////////////////////////////////////////////
// MODULAR POLYNOMIALS Phi_{ell} for ell=2,3,5,7.                //
///////////////////////////////////////////////////////////////////

R<x,j> := PolynomialRing(Integers(),2);
PHI := [0,
// Phi2:
       x^3 + j^3 - x^2*j^2 + 1488 * x * j * (x + j)
         - 162000 * (j^2 + x^2) + 40773375 * j * x 
         + 8748000000 * (x + j) - 157464000000000,
// Phi3:
       x*(x+2^15*3*5^3)^3+j*(j+2^15*3*5^3)^3-x^3*j^3
         +2^3*3^2*31*x^2*j^2*(x+j)-2^2*3^3*9907*x*j*(x^2+j^2)
         +2*3^4*13*193*6367*x^2*j^2 
         +2^16*3^5*5^3*17*263*x*j*(x+j)-2^31*5^6*22973*x*j,
        0, 
// Phi5:
      x^6 + (-j^5 + 3720*j^4 - 4550940*j^3 + 2028551200*j^2 - 246683410950*j + 1963211489280)*x^5 + (3720*j^5 + 1665999364600*j^4 + 107878928185336800*j^3 + 383083609779811215375*j^2 + 128541798906828816384000*j + 1284733132841424456253440)*x^4 + (-4550940*j^5 + 107878928185336800*j^4 - 441206965512914835246100*j^3 + 26898488858380731577417728000*j^2 - 192457934618928299655108231168000*j + 280244777828439527804321565297868800)*x^3 + (2028551200*j^5 + 383083609779811215375*j^4 + 26898488858380731577417728000*j^3 + 5110941777552418083110765199360000*j^2 + 36554736583949629295706472332656640000*j + 6692500042627997708487149415015068467200)*x^2 + (-246683410950*j^5 + 128541798906828816384000*j^4 - 192457934618928299655108231168000*j^3 + 36554736583949629295706472332656640000*j^2 - 264073457076620596259715790247978782949376*j + 53274330803424425450420160273356509151232000)*x + (j^6 + 1963211489280*j^5 + 1284733132841424456253440*j^4 + 280244777828439527804321565297868800*j^3 + 6692500042627997708487149415015068467200*j^2 + 53274330803424425450420160273356509151232000*j + 141359947154721358697753474691071362751004672000),
       0,
// Phi7:  
       x^8 + (-j^7 + 5208*j^6 - 10246068*j^5 + 9437674400*j^4 - 4079701128594*j^3 + 720168419610864*j^2 - 34993297342013192*j + 104545516658688000)*x^7 + (5208*j^7 + 312598931380281*j^6 + 177089350028475373552*j^5 + 4460942463213898353207432*j^4 + 16125487429368412743622133040*j^3 + 10685207605419433304631062899228*j^2 + 1038063543615451121419229773824000*j + 3643255017844740441130401792000000)*x^6 + (-10246068*j^7 + 177089350028475373552*j^6 - 18300817137706889881369818348*j^5 + 14066810691825882583305340438456800*j^4 - 901645312135695263877115693740562092344*j^3 + 11269804827778129625111322263056523132928000*j^2 - 40689839325168186578698294668599003971584000000*j + 42320664241971721884753245384947305283584000000000)*x^5 + (9437674400*j^7 + 4460942463213898353207432*j^6 + 14066810691825882583305340438456800*j^5 + 88037255060655710247136461896264828390470*j^4 + 17972351380696034759035751584170427941396480000*j^3 + 308718989330868920558541707287296140145328128000000*j^2 + 553293497305121712634517214392820316998991872000000000*j + 41375720005635744770247248526572116368162816000000000000)*x^4 + (-4079701128594*j^7 + 16125487429368412743622133040*j^6 - 901645312135695263877115693740562092344*j^5 + 17972351380696034759035751584170427941396480000*j^4 - 5397554444336630396660447092290576395211374592000000*j^3 + 72269669689202948469186346100000679630099972096000000000*j^2 - 129686683986501811181602978946723823397619367936000000000000*j + 13483958224762213714698012883865296529472356352000000000000000)*x^3 + (720168419610864*j^7 + 10685207605419433304631062899228*j^6 + 11269804827778129625111322263056523132928000*j^5 + 308718989330868920558541707287296140145328128000000*j^4 + 72269669689202948469186346100000679630099972096000000000*j^3 - 46666007311089950798495647194817495401448341504000000000000*j^2 - 838538082798149465723818021032241603179964268544000000000000000*j + 1464765079488386840337633731737402825128271675392000000000000000000)*x^2 + (-34993297342013192*j^7 + 1038063543615451121419229773824000*j^6 - 40689839325168186578698294668599003971584000000*j^5 + 553293497305121712634517214392820316998991872000000000*j^4 - 129686683986501811181602978946723823397619367936000000000000*j^3 - 838538082798149465723818021032241603179964268544000000000000000*j^2 + 1221349308261453750252370983314569119494710493184000000000000000000*j)*x + (j^8 + 104545516658688000*j^7 + 3643255017844740441130401792000000*j^6 + 42320664241971721884753245384947305283584000000000*j^5 + 41375720005635744770247248526572116368162816000000000000*j^4 + 13483958224762213714698012883865296529472356352000000000000000*j^3 + 1464765079488386840337633731737402825128271675392000000000000000000*j^2)
];


function TpSS(p, j) 
   F   := Parent(j);
   R   := PolynomialRing(F,2);
   S   := PolynomialRing(F);
   h   := hom <R -> S | S.1, j>;
   phi := h(R!PHI[p]);
// use roots instead.
   fac := Factorization(phi);
   if Max([Degree(a[1]) : a in fac]) gt 1 then
      print "Char = ",Characteristic(F);
      print "p = ",p;
      print "j = ",j;
      print "fac = ",fac;
   end if;
   assert Max([Degree(a[1]) : a in fac]) eq 1;
   return &cat[[-Evaluate(a[1],0) : i in [1..a[2]]] : a in fac];
end function;


// Mestre class.
declare attributes ModTupRng:
        p,          
        M,
        ssbasis,   
        weights,
        T,
        decomp,
        eisen;



function Mestre(p, M) 
//Returns the Mestre method of graphs module.
   assert Type(p) eq RngIntElt;
   assert Type(M) eq RngIntElt;
   assert Gcd(p,M) eq 1 ;//: "Argument 1 and argument 2 must be coprime.";
   assert IsPrime(p) ;//: "Argument 1 must be prime.";
   assert M eq 1; 
   V:=RSpace(Integers(),DimensionCuspFormsGamma0(p,2)+1);
   B:=Basis(V);
   X:=RSpaceWithBasis(Basis(V));
   X`p := p;
   X`M := M;
   X`T := [* 0,0,0,0,0,0,0 *];
   if assigned X`ssbasis then delete X`ssbasis; end if;
   if assigned X`weights then delete X`weights; end if;
   if assigned X`decomp then delete X`decomp; end if;
   if assigned X`eisen then delete X`eisen; end if;

   return X;
end function;


function BasisX0(X)
   B := Basis(X);
   return [B[i]-B[#B] : i in [1..#B-1]];
end function;


function TpD(X, p)
/* Computes Tp on the Mestre graphs module. 
 Here p must be a prime between 2 and 7. */
   assert p ge 2 and p le 7;
   assert p in {2,3,5,7}; // : "Argument 2 must lie in the set {2,3,5,7}.";
   if Type(X`T[p]) eq RngIntElt then
      if not assigned X`ssbasis then
         d         := Degree(X);
         X`ssbasis := {@ FindSupersingularJ(X`p) @};
      else
         d         := #X`ssbasis;
      end if;
      V         := RSpace(Integers(),d);
      T         := MatrixAlgebra(Integers(),d)!0;
      for i in [1..d] do
         S := TpSS(p, X`ssbasis[i]);
         for j in S do
            Include(~X`ssbasis, j);
            T[i,Index(X`ssbasis,j)] +:= 1;
         end for; 
      end for;
      X`T[p] := T;
   end if;
   return X`T[p];
end function;


function MestreEisensteinFactor(X)
// Computes the Eisenstein factor of the Mestre module X.
   if not assigned X`eisen then
      p := 2;
      T := TpD(X,p)-(p+1);
      V := Kernel(T);
      while Dimension(V) gt 1 and p lt 7 do
         p := NextPrime(p); 
         T := TpD(X,p)-(p+1);
         V := V meet Kernel(T);
      end while;
      if Dimension(V) gt 1 then
         error "Not enough Hecke operators are known for us to find Eisenstein series.";
      end if;
      X`eisen := V;
   end if;
   return X`eisen;
end function;


function MonodromyWeights(X) 
// Returns the monodromy weights.
   if not assigned X`weights then
      eis       := Eltseq(Basis(MestreEisensteinFactor(X))[1]);
      n         := Lcm([Integers()|e : e in eis]);
      X`weights := [Integers()|Abs(Numerator(n/e)) : e in eis];
   end if;
   return X`weights;
end function;


function SupersingularBasis(X) 
// Returns the basis for D of supersingular j-invariants.
   if not assigned X`ssbasis then
      dummy:=TpD(X,2);
   end if;
   return X`ssbasis;      
end function;


function Decomposition(X : Proof := true)
/* Returns the decomposition of X into Hecke stable submodules
 under T2,T3,T5,T7. */
   if not assigned X`decomp then
      p := 2;
      Decomp := [ RSpace(Integers(),Degree(X)) ];
      Irred := [ false ];
      while p le 7 and not &and Irred do
         T := TpD(X,p);
         for V in [ V : V in Decomp | not Irred[Index(Decomp,V)] ] do
            fact := Factorization(MyCharpoly(Restrict(T,V),Proof));
            if #fact gt 1 then
               Remove(~Irred,Index(Decomp,V));
               Exclude(~Decomp,V);
               for f in fact do
                  Append(~Decomp,V meet Kernel(Evaluate(f[1],T)));
                  if f[2] eq 1 then
                     Append(~Irred,true);
                  else
                     Append(~Irred,false);
                  end if;
               end for;
            elif fact[1][2] eq 1 then
               Irred[Index(Decomp,V)] := true;
            end if;
         end for;
         p := NextPrime(p);                          
      end while;
      X`decomp := Decomp;
   end if;
   return X`decomp;
end function;


function MestreEigenvector(X, V) 
   p := 2;
   T := Restrict(TpD(X,p),V);
   f := MyCharpoly(T,true);
   while not IsIrreducible(f) do
      p := NextPrime(p);
      if p gt 7 then
         error "MestreEigenvector: Could not verify that second argument is irreducible.";
      end if;
      T +:= Random(1,10)*Restrict(TpD(X,p),V);
      f := MyCharpoly(T,true);
   end while;
   e := EigenvectorOfMatrixWithCharpoly(
               MatrixAlgebra(Rationals(),Ncols(T))!T,f);
   F := Parent(e[1]);
   W := VectorSpace(F,Degree(V));
   B := [W!b : b in Basis(V)];
   return &+[e[i]*B[i] : i in [1..#B]];
end function;



procedure DeleteAttributes(X)
   assert Type(X) eq ModTupRng;
   if assigned X`p then delete X`p; end if;
   if assigned X`M then delete X`M; end if;
   if assigned X`ssbasis then delete X`ssbasis; end if;
   if assigned X`weights then delete X`weights; end if;
   if assigned X`T then delete X`T; end if;
   if assigned X`decomp then delete X`decomp; end if;
   if assigned X`eisen then delete X`eisen; end if;
end procedure;

function phi2(j)
   R := PolynomialRing(Parent(j)); x := R.1;
   return x^3 + j^3 - x^2*j^2 + 1488 * x * j * (x + j)
         - 162000 * (j^2 + x^2) + 40773375 * j * x 
         + 8748000000 * (x + j) - 157464000000000;
end function;

/*
intrinsic XXX_SupersingularInvariants(p::RngIntElt) -> SetEnum
   {The supersingular j-invariants in GF(p^2).}
   require IsPrime(p) : "Argument 1 must be prime.";
   J := [FindSupersingularJ(p)];
   n := DimensionCuspFormsGamma0(p,2) + 1;

   i := 1;
   while #J lt n do
      assert i le #J;
      phi := phi2(J[i]);
      for j in Roots(phi) do
         if not (j[1] in J) then
            Append(~J,j[1]);
         end if;
      end for;
      i := i + 1;
   end while;
   return J;
end intrinsic;
*/

intrinsic SupersingularInvariants(p::RngIntElt) -> SetEnum, MtrxSprs
{The supersingular j-invariants in GF(p^2) and a sparse matrix that 
represents T2 acting on the j-invariants.}
   require IsPrime(p) : "Argument 1 must be prime.";
   J := {@ FindSupersingularJ(p) @};
   n := DimensionCuspFormsGamma0(p,2) + 1;
   T2 := SparseMatrix(Integers(),n,n);

   i := 1;
   while i le n do
      if i mod 100 eq 0 then
         vprintf SupersingularModule : "%o percent\n ", Round(100*#J/n*1.0);
      end if;
      phi := phi2(J[i]);
      for j in Roots(phi) do
         Include(~J,j[1]);
         ind := Index(J,j[1]);
         T2[i,ind] := T2[i,ind] + j[2];
      end for;
      i := i + 1;
   end while;
   return [x : x in J], T2;
end intrinsic;

intrinsic YYY_SupersingularInvariants(p::RngIntElt) -> SetEnum
   {The supersingular j-invariants in GF(p^2).}
   require IsPrime(p) : "Argument 1 must be prime.";
   J := {@ FindSupersingularJ(p) @};
   n := DimensionCuspFormsGamma0(p,2) + 1;
   R := PolynomialRing(Parent(J[1]));
   x := R.1;

   i := 1;
   while #J lt n do
      assert i le #J;
      phi := phi2(J[i]);
      for a in J do 
         if Evaluate(phi, a) eq 0 then
            phi := phi div (x-a);
            break;
         end if;
      end for;
      b := Coefficient(phi,1);
      c := Coefficient(phi,0);
      rad := Sqrt(b^2-4*c);
      for j in [(-b+rad)/2, (-b-rad)/2] do
         if not (j in J) then
            Include(~J,j);
         end if;
      end for;
        
/*      for j in Roots(phi) do
         if not (j[1] in J) then
            Append(~J,j[1]);
         end if;
      end for;
*/
      i := i + 1;
   end while;
   return J;
end intrinsic;
