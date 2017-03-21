/******************************************************************************
 *
 *    sporadic.m Composition Tree Sporadic Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3134                                           $:
 *    Date      : $Date:: 2015-08-09 15:13:35 +1000 (Sun, 09 Aug 2015)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: sporadic.m 3134 2015-08-09 05:13:35Z eobr007                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "leaf.m" : LeafError, MembershipTesting, BuiltinMembership,
    MaxBSGSVerifyPermDegree, C9Presentation,
    C9CenterMembership, C9Membership;
import "present.m" : SporadicGroupPresentations,
    SporadicMaximalWords, SporadicMultiplicators;
import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "comp-series.m" : PullbackCompFactors;
import "centre.m" : C9Centre, CyclicGenerator;
import "sporadics.m" : SporadicGoldCopy;
import "standard-sporadics.m" : SporadicStandardPresentationSLP;
import "../../reduce/reduce.m" : Reduction;

forward MatrixSchreierSims, PermSchreierSims;

// Ryba or RandomSchreier?
RybaMembershipInfo := recformat<
    Verify                 : BoolElt,
    Projective             : BoolElt,
    LieRank                : RngIntElt,
    CentraliserGenerators  : RngIntElt,
    InvolutionSelections   : RngIntElt,
    InvolutionConjugations : RngIntElt,
    CentraliserMembership  : MonStgElt>;

RybaMembershipData := AssociativeArray();
RybaMembershipData["J4"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["Ly"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["HN"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["ON"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 50,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["Th"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["F24"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["B"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["F42"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 25,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["E62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["TE62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["TD43"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["S82"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 5,
    CentraliserGenerators  := 100, // revised from 20
    InvolutionSelections   := 500, // revised from 100
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;


RybaMembershipData["S102"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 5,
    CentraliserGenerators  := 100, // revised from 20 
    InvolutionSelections   := 500, // revised from 100 
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["U316"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 2,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["U313"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 2,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

RybaMembershipData["U63"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 5,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2U63"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 0,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["O8p3"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2O8p3"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["O8m3"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2O8m3"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["L43"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 3,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2L43"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 3,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["U82"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 3,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

/* 
RybaMembershipData["O8p2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2O8p2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2^2O8p2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;
*/


/* 
RybaMembershipData["U52"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["U62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["3U62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;
*/

RybaMembershipData["U72"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["U92"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 20,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;


/* 
RybaMembershipData["S62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2S62"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 3,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;
*/

RybaMembershipData["O8m2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["2O8m2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 100,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

RybaMembershipData["O10m2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 250,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;

/* 
RybaMembershipData["O10p2"] := rec<RybaMembershipInfo |
    Verify                 := false,
    Projective             := false,
    LieRank                := 4,
    CentraliserGenerators  := 1000,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "BSGS">;
*/


// We call SchreierSims in different ways for each group type
SporadicSchreierSetup := AssociativeArray();

// We call SchreierSims in different ways for each group type
SporadicSchreierSetup := AssociativeArray();
SporadicSchreierSetup[GrpMat] := MatrixSchreierSims;
SporadicSchreierSetup[GrpPerm] := PermSchreierSims;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

/* G is the automorphism group of the sporadic group having 
   name <str>; construct the sporadic group S as a subgroup of G; 
   return S and the SLPs for its corresponding generators 
   in the generators of G */

function SporadicSubgroupOfAutomorphismGroup(G, str) 
    assert IsDefined(SporadicMaximalWords, str);
    f := SporadicMaximalWords[str];
    
    try
	flag, X, Y := StandardGenerators(G, str : AutomorphismGroup := true,
	Projective := true);
        if not flag then
	    return false, _, _;
	end if;
	
	U := f(X);
	W := f(Y);
	S := sub<Generic(G) | U>;
	return true, S, W;
    catch err
	error Error(rec<LeafError | Family := "18", Error :=
	"Failed to construct simple sporadic">);
    end try;
end function;

function SporadicAlmostSimple(G, nameTuple)
    name := nameTuple[3];

    // Check if there is an automorphism group
    if not IsDefined(SporadicMaximalWords, name) then
	return false, _, _;
    end if;
    
    // Try to find standard generators of the sporadic as a maximal subgroup
    // of its automorphism group
    return SporadicSubgroupOfAutomorphismGroup(G, name);
end function;

/* from Type 1 standard gens X, W for J4, construct and return  Type 2 */
function J4Type1ToType2(X, W)
    a  := X[1];
    b  := X[2];
    aw := W[1];
    bw := W[2];
    
    x  := ((a * b * a * b^2)^5)^((a * b)^4);
    xw := ((aw * bw * aw * bw^2)^5)^((aw * bw)^4);
    y  := ((a * b^2)^4)^((a * b)^2 * (b * a)^18);
    yw := ((aw * bw^2)^4)^((aw * bw)^2 * (bw * aw)^18);
    z  := (x * y)^2 * (x * y^2)^2 * (x * y)^3;
    zw := (xw * yw)^2 * (xw * yw^2)^2 * (xw * yw)^3;
    c  := a^(a * b * a * b^3 * (a * b * a * b^2)^3);
    cw := aw^(aw * bw * aw * bw^3 * (aw * bw * aw * bw^2)^3);
    t  := (c * z)^15;
    tw := (cw * zw)^15;
    
    return [x, y, t], [xw, yw, tw];
end function;

ThompsonStandardToPresentation := function (X) 
   /*
   Words for going from Type I standard generators of Th (x,y) to Type II
   standard generators (a,b,c,d,e,s,t,u) 
   Type II sgens are the Havas--Soicher--Wilson presentation. */

   assert #X eq 2;
   x := X[1]; y := X[2];

   z1:=(x,x*y*x*y*x*y*x*y^2*x*y^2)*x*y*x*y^2;
   z2:=x^(x*y*x*y*x*y*x*y^2*x*y^2)*x*y*x*y^2;
   z:=z1;
   // x*z1 = z2, x*z2 = z1.
   // <x,z> = 3D4(2):3.
   // z = z1 has order 21.
   
   d:=x;
   c:=(x*z)^3;
   a:=(c*d)^4;
   // oe:=x^(z^2*x*z^-2*x*z^2);
   // oe:=x*(x,z^2)^3;
   e:=x^(z*x*z^11*x*z^2*x*z^20);
   b:=z^2*a*z^-2;
   t:=(z^14)^(x*z*x*z^11*x*z*x*z^2);
   // os:=(x*z*x*z^8)^((z^2*x)^4*z^-1);
   s:=(z*x*z^8*x)^((x*z^2)^4*z*x*z);
   
   h1:=(a,y)^6;
   // C_G(a) = <a,c,d,e,s,t,h1>;
   h2:=d*e*c*d*e*c*d;
   h3:=h1*e*t*s*e*h1;
   // C_G(a,c) = <a,c,e,s,t,h2,h3>; // Index 270 in C_G(a).
   h4:=s^4*h3;
   h5:=h2*h4*h2;
   h6:=s*e*s^-1;
   // C_G(a,c,e) = <a,c,e,t,h4,h5,h6> = <a,c,e,t,h4,h5*h6>; 
   // Index 112 in C_G(a,c).
   u:=a*c*h4*t^2*h4*t*h4;
   // At last! The final generator.
   
   return [a,b,c,d,e,s,t,u];
   
end function;

/* Bray recipe to convert standard generators for Thompson 
   to those used by Havas, Soicher, Wilson in presentation */

function ThType1ToType2 (X, W)

   return ThompsonStandardToPresentation (X),
          ThompsonStandardToPresentation (W);
end function;

/* receipe to convert standard generators for Lyons 
   to those used by Parker in his presentation; extracted from  
   "Generators and relations for the Lyons sporadic simple group"
    Christopher Parker, Arch. Math. 78 (2002) 97-103
*/

LyStandardToParker := function (X, W)
   ConvertGenerators := function (X)
      A := X[1]; B := X[2];
      C:=(A*B*A*B*A*B*B)^15*A*(A*B*A*B*A*B*B)^-15;
      D:=(B*A*B*A*B^2)^-12*(A*B*A*B*A*B*B*A*B)^3*(B*A*B*A*B*B)^12;
      
      b7 := C; E := D^C; F:= (D*E*E*D*E*E*D*E*D*E)^15; H := (C*F^D)^4;
      J := (C*F^E)^3; b3 := H^J; K := (C*F^(D*E))^6; L:= b3*b3^((C*F)^5);
      M := b3^K; b4 := M^(L^2*M*L*M); b1 := (b4*H)^3; b2 := b1^(L*b3); 
      b6 := b1^(K*J)*b1; N:= (b4*b4^(C*D*C*D*C*D*D))^3; P := (b7*N)^4;
      O := (b4*b4^(C*D*D*C*D*C*D*D*C*D))^3; b5 := O^(P*O*P); 
      
      a2 := b3*b6*b7;
      a3 := b3*b6*((b3*b6)^b4)*b7;
      a1 := a3^((b1*b5)^2);
      a4 := (b4*a1*a3)^(a2*(a2^b4))*a1;
      a5 := a2^((b1*b5)^2*b4*b3);
      a6 := a1^b6;
      a7 := ((b1*b2)^(b5*b2*b3*b1*b5*b1*b3*b5), a1);
      a8 := (b3*b5*b6)^7;
      a10 := a2^((b5*b1*b2*b3)^4);  
      
      Q := a4^2; R := A*B^4*A*B^3*A; S := R*(Q,R)^15; 
      T := S^5*a4*S^13*a4*S^8*a4^2; T := T*(a4,T)^2;
      U := S*a4*S^5*a4*S^11*a4^3; U := (a4,U)^3;
      W:= U *Q*U*a4*U*a4; W := W*(a1*a6,W);
      V := T^15*U^2*T^5*U^3*T^23*U^3; V := V*(a1*a6,V);
      a9 := (W*V)^7;
       
      return [b1, b2, b3, b4, b5, b6, b7,
              a1, a2, a3, a4, a5, a6, a7, a8, a9, a10];
   end function;
   return ConvertGenerators (X), ConvertGenerators (W);
end function;

function SporadicStandardGenerators(G, name)
    // Find standard generators using ATLAS black box algorithms
    nmr := 5;
    flag := false;
    repeat 
       if name eq "L43" then 
         flag, gens, slps := StandardGenerators(G, name : Projective := false);
         if not flag then 
            flag, gens, slps := StandardGenerators(G, "2L43": Projective := false);
         end if;
       elif name eq "2L43" then 
          flag, gens, slps := StandardGenerators(G, name : Projective := false);
       else
          flag, gens, slps := StandardGenerators(G, name : Projective := true);
       end if;
       // flag, gens, slps := StandardGenerators(G, name : Projective := true);
       nmr -:= 1;
    until flag or nmr eq 0;

    if not flag then
	error ERROR_RECOGNITION;
    end if;

    vprint CompositionTree, 2 :
	"Standard generators obtained:", name;

    // Special treatment of J4, convert to gens where there is a presentation
    if name eq "J4" then
	gens, slps := J4Type1ToType2(gens, slps);
    end if;

    // Special treatment of Ly, convert to gens where there is a presentation
    if name eq "Ly" then
	gens, slps := LyStandardToParker(gens, slps);
    end if;

    // Special treatment of Th, convert to gens where there is a presentation
    if name eq "Th" then
	gens, slps := ThType1ToType2(gens, slps);
    end if;
    
    return gens, slps;
end function;

procedure MatrixSchreierSims(G, name, order, verify, maxOrder)
    /* the sporadic group is defined on its standard generators,
       which occur as the first two in the extended group G */
    flag, base := GoodBasePoints(G, name : 
      Generators := [G.i: i in [1..2]], Projective := true);
    
    if flag and not HasAttribute(G, "Base") and #base gt 0 then
	AssertAttribute(G, "Base", base);
    end if;

    if not HasAttribute(G, "Order")  then
	AssertAttribute(G, "Order", order);
    end if;
    
    // Fire in the hole
    RandomSchreier(G);
    if verify or #G le maxOrder then
	Verify(G);
    end if;
end procedure;

procedure PermSchreierSims(G, name, order, verify, maxOrder)
    if not HasAttribute(G, "Order")  then
	AssertAttribute(G, "Order", order);
    end if;

    // Fire in the hole
    RandomSchreier(G);

    if verify or #G le maxOrder or Degree(G) le MaxBSGSVerifyPermDegree then
	Verify(G);
    end if;
end procedure;

// Fischer groups are called F in ATLAS but Fi elsewhere
// Exceptional groups can be handled as ATLAS groups
function SimpleGroupNameToATLAS(node)
    if Category(Retrieve(node`LeafData`DefiningField)) eq RngIntElt then
	family := Retrieve(node`LeafData`Family);
	assert #family in {1, 2};

	if family eq "A" then
	    family := "L";
	    rank := IntegerToString(node`LeafData`LieRank + 1);
	elif family eq "C" then
	    family := "S";
	    rank := IntegerToString(node`LeafData`LieRank * 2);
	elif family eq "2A" then
	    family := "U";
	    rank := IntegerToString(node`LeafData`LieRank + 1);
	elif family eq "B" then
	    family := "O";
	    rank := IntegerToString(node`LeafData`LieRank * 2 + 1);
	elif family eq "D" then
	    family := "O";
	    rank := IntegerToString(node`LeafData`LieRank * 2) cat "p";
	elif family eq "2D" then
	    family := "O";
	    rank := IntegerToString(node`LeafData`LieRank * 2) cat "m";
	else
	    rank := IntegerToString(node`LeafData`LieRank);
	end if;
	
	if #family eq 2 then
	    twist := StringToInteger(Substring(family, 1, 1));
	    family := "T" cat Substring(family, 2, 1);
	    q := IntegerToString(Iroot(Retrieve(node`LeafData`DefiningField),
		twist));
	else
	    q := IntegerToString(Retrieve(node`LeafData`DefiningField));
	end if;
	
	return family cat rank cat q;
    else
	if Retrieve(node`LeafData`Family) cmpeq 17 then
	    return "A" cat IntegerToString(node`LeafData`LieRank);
	else
	    name := Retrieve(node`LeafData`DefiningField);
	    if Substring(name, 1, 2) eq "Fi" then
		return "F" cat Substring(name, 3, 2);
	    else
		return name;
	    end if;
	end if;
    end if;
end function;

procedure SporadicPresentation(~node, name, center, centerToSLP)    
    // We do not always have a short presentation
    if IsDefined(SporadicGroupPresentations, name) then
	pres := SporadicGroupPresentations[name];

	relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
	
	if not IsTrivial(center) then
	    // Convert words to SLPs
	    wordToSLP := hom<pres -> node`NiceData`WordGroup |
	    Prune(UserGenerators(node`NiceData`WordGroup))>;
	    
	    slps := wordToSLP(relators);
	else 
	    
	    // Convert words to SLPs
	    wordToSLP := hom<pres -> node`NiceData`WordGroup |
	    UserGenerators(node`NiceData`WordGroup)>;
	    
	    slps := wordToSLP(relators);
	end if;
    elif IsDefined(SporadicStandardPresentationSLP, name) then
	slps := SporadicStandardPresentationSLP[name]();
    else
	SporadicSchreierSetup[Category(node`LeafData`GoldCopy)](
	    node`LeafData`GoldCopy, name, FactoredOrder(node`LeafData`GoldCopy),
	    node`Verify, node`MaxBSGSVerifyOrder);
	
	vprint CompositionTree, 5 :
	    "Obtain presentation on strong generators for sporadic:", name;
	pres, pres2G := FPGroupStrong(node`LeafData`GoldCopy);
	assert NumberOfGenerators(pres) eq
	    NumberOfStrongGenerators(node`LeafData`GoldCopy);
	assert IndexedSetToSequence(StrongGenerators(node`LeafData`GoldCopy))
	    eq pres2G(UserGenerators(pres));
	
	vprint CompositionTree, 5 : "Rewrite relations on nice generators";
	relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
	
	// Convert words to SLPs
	wordToSLP := hom<pres -> node`NiceData`WordGroup |
	node`SLPMaps`EltToSLPBatch(node`LeafData`FromGoldBatch(
	    pres2G(UserGenerators(pres))))>;
	
	slps := wordToSLP(relators);
    end if;

    if not IsTrivial(center) then
	// Center generator is at the end
	slps := C9Presentation(node`NiceData`Group, node`NiceData`WordGroup,
	    slps, NumberOfGenerators(node`NiceData`Group), centerToSLP,
	    node`Scalar);
    end if;
    
    node`PresentationData := rec<PresentationInfo | SLPRelators := slps>;
end procedure;

function RybaMembership(G, name, verify)
    return func<h | Reduction(G, h :
	Verify := verify or RybaMembershipData[name]`Verify,
	Central := RybaMembershipData[name]`Projective,
	LieRank := RybaMembershipData[name]`LieRank,
	CentraliserMethod := RybaMembershipData[name]`CentraliserMembership,
	ConjugationTries  := RybaMembershipData[name]`InvolutionConjugations,
	MaxTries          := RybaMembershipData[name]`InvolutionSelections,
	CentraliserCompletionCheck := func<G, C, g, l | NumberOfGenerators(C)
	ge RybaMembershipData[name]`CentraliserGenerators>)>;
end function;

procedure SporadicFactorData(~node, center, g2slpGold)
    // Take centre projectively
    centerPC, phi := AbelianGroup(sub<Generic(node`Group) |
	center, node`Scalar>);
    centerProj, proj := quo<centerPC | phi(node`Scalar)>;
    
    series := CompositionSeries(centerProj);
    
    centerFactors := PullbackCompFactors(node`NiceData`Group,		               node`SLPMaps`EltToSLPBatch, phi * proj, series, #centerPC + 1);
    
    if not IsTrivial(centerProj) then
	slps := Append(centerFactors`FactorSLPs,
	    Prune(UserGenerators(node`NiceData`WordGroup)));
	factors := Append(centerFactors`ToFactor, node`LeafData`ToGold);
	factor2slp := Append(centerFactors`FactorToSLP, g2slpGold);
    else
	factors := [* node`LeafData`ToGold *];
	factor2slp := [* g2slpGold *];
	
	if IsTrivial(centerPC) then
	    slps := [UserGenerators(node`NiceData`WordGroup)];
	else
	    slps := [Prune(UserGenerators(node`NiceData`WordGroup))];
	end if;
    end if;
    
    node`FactorData := rec<FactorInfo |
	FactorSLPs := slps,
	ToFactor := factors,
	FactorToSLP := factor2slp,
	Refined := true,
	FactorLeaves := [node : i in [1 .. #centerFactors`ToFactor + 1]]>;
end procedure;

function SporadicGoldCopyOrder(name)    
    case name:
        when "2^2O8p2" : return #ATLASGroup("O8p2") * 4;
        when "2O8p2" : return #ATLASGroup("O8p2") * 2;
        when "2O8p3" : return #ATLASGroup("O8p3") * 2;
        when "2O8m3" : return #ATLASGroup("O8m3") * 2;
	when "2U63"  : return #ATLASGroup("U63") * 2;
	when "2L43"  : return #ATLASGroup("L43") * 2;
	when "2S62"  : return #ATLASGroup("S62") * 2;
	when "3U62"  : return #ATLASGroup("U62") * 3;
        when "U92"   : return 3 * 325473292721108444774400;
        when "3U92"   : return 3 * 325473292721108444774400;
	else return #ATLASGroup(name);
    end case;
end function;

function SporadicGoldCopyName(name)
    case name:
        when "2^2O8p2" : return "O8p2";
        when "2O8p2" : return "O8p2";
        when "O8p3" : return "2O8p3";
	when "U63"  : return "2U63";
	when "L43"  : return "2L43";
	when "U62"  : return "3U62";
	else return name;
    end case;
end function;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

procedure BlackBoxSporadic(~node)
    try
	name := SimpleGroupNameToATLAS(node);
        goldName := SporadicGoldCopyName(name);

	if not IsDefined(SporadicGoldCopy, name) then
	    error Error(rec<LeafError |
		Description := "Sporadic black box",
		Error := "No black box algorithm for this sporadic">);
	end if;
	
	stdCopy := SporadicGoldCopy[goldName];
	
	stdSLPs := [* *];
	niceGroups := [* *];
	names := [name, goldName];
	groups := [* node`Group, stdCopy *];

	// Setup input and standard copy
	for i in [1 .. #names] do
	    G := groups[i];
	    atlasName := names[i];

	    vprint CompositionTree, 2 :
		"Find standard generators for sporadic:", atlasName;

	    // Find standard generators
	    gens, slps := SporadicStandardGenerators(G, atlasName);

	    // Nice generators are the standard generators
	    niceGroup := sub<Generic(G) | gens>;
	    
	    // Save standard generators
	    Append(~stdSLPs, slps);
	    Append(~niceGroups, niceGroup);
	end for;

	assert NumberOfGenerators(niceGroups[1]) eq #stdSLPs[1];

	center, centerSLP := C9Centre(node`Group);

	if not IsTrivial(center) then
	    assert NumberOfGenerators(center) eq 1;
	    assert Parent(centerSLP) eq WordGroup(node`Group);
	
	    // Save nice group
	    niceGroup := sub<Generic(node`Group) | niceGroups[1], center>;
	    niceSLPs := Append(stdSLPs[1], centerSLP);
	else
	    niceGroup := niceGroups[1];
	    niceSLPs := stdSLPs[1];
	end if;
	
	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
	NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

	assert NumberOfGenerators(Universe(node`NiceData`NiceSLPs)) eq
	    NumberOfGenerators(node`Group);
	
	goldCopy := niceGroups[2];
	centerGold, centerGoldSLP := C9Centre(goldCopy);
//	if not IsTrivial(centerGold) then
//	    node`LeafData`GoldCopy := sub<Generic(goldCopy) | goldCopy, centerGold>;
//	else
        node`LeafData`GoldCopy := goldCopy;
//	end if;

        AssertAttribute(node`LeafData`GoldCopy, "Order", 
			Factorisation(SporadicGoldCopyOrder(goldName)));

	
	slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>;

	H := sub<Generic(node`NiceData`Group) | node`NiceData`Group,
	    node`Scalar>;
	C := sub<Generic(node`NiceData`Group) | center, node`Scalar>;

	W := node`NiceData`WordGroup;
	numScalars := NumberOfGenerators(H) - 
		      NumberOfGenerators(node`NiceData`Group);
	G := node`LeafData`GoldCopy;
	WG := WordGroup(G);

	if not IsTrivial(center) then	    
	    assert NumberOfGenerators(node`NiceData`Group) eq NumberOfGenerators(G) + 1;
	    niceGens := [g : g in Prune(UserGenerators(node`NiceData`Group))];
	    if not IsTrivial(centerGold) then
		goldGens := [g : g in UserGenerators(G)] cat [centerGold.1] cat [Identity(G) : i in [1 .. numScalars]];
	    else
		goldGens := [g : g in UserGenerators(G)] cat [Identity(G) : i in [1 .. NumberOfGenerators(C)]];
	    end if;
	else
	    assert NumberOfGenerators(node`NiceData`Group) eq NumberOfGenerators(G);
	    niceGens := [g : g in UserGenerators(node`NiceData`Group)];
	    goldGens := [g : g in UserGenerators(G)] cat [Identity(G) : i in [1 .. numScalars]];
	end if;
	
	// Now setup mappings using built-in machinery or Ryba
	// Always use RandomSchreier if we want verification and we don't have
	// an immediate presentation
	if (IsDefined(RybaMembershipData, name) and
	    (IsDefined(SporadicGroupPresentations, name) or
	     not node`Verify)) then
	    vprint CompositionTree, 2 :
		"Use Ryba for sporadic membership:", name;
	    
	    // Ryba needs random processes
	    H`RandomProcess :=
		RandomProcessWithWords(H : WordGroup := WordGroup(H));

	    // Projective constructive membership testing
	    //if not IsTrivial(center) then
//		slpGens := [g : g in Prune(UserGenerators(W))] cat [Identity(W) : i in [1 .. NumberOfGenerators(C)]];
//	    else
//		slpGens := UserGenerators(W) cat [Identity(W) : i in [1 .. numScalars]];
//	    end if;
	    slpGens := UserGenerators(W) cat [Identity(W) : i in [1 .. numScalars]];

	    g2slpProj := hom<H -> W | g :-> 
		Evaluate(MembershipTesting(node, RybaMembership(H, name, node`Verify), g), slpGens)>;

	    // Ryba needs random processes
	    G`RandomProcess := RandomProcessWithWords(G : WordGroup := WG);
	    
	    // Constructive membership testing with exception handling
	    g2slpGold := hom<G -> WG | g :-> MembershipTesting(node,
	    RybaMembership(G, goldName, node`Verify), g)>;

	    node`LeafData`ToGold := hom<H -> G | g :->
		 Evaluate(Function(g2slpProj)(g), goldGens)>;

	    node`LeafData`FromGold := hom<G -> node`NiceData`Group | g :->
		Evaluate(Function(g2slpGold)(g), niceGens)>;
	else
	    vprint CompositionTree, 2 :
		"A Find BSGS for sporadic:", name;
	    
            if name eq "U92" then 
               A := PSU(9, 2);
            elif name eq "3U92" then
               A := SU(9, 2);
            else 
         	A := ATLASGroup(name);
            end if;

	    SporadicSchreierSetup[Category(H)](H, name, #A * #C,
		node`Verify, node`MaxBSGSVerifyOrder);
	    
	    // Projective constructive membership testing
	    g2slpProj := hom<H -> W | g :->
	    Evaluate(MembershipTesting(node, func<h |
		BuiltinMembership(H, h)>, g), UserGenerators(W) cat
		[Identity(W) : i in [1 .. NumberOfGenerators(C)]])>;
	    
	    SporadicSchreierSetup[Category(G)](G, goldName, #G, node`Verify,
		node`MaxBSGSVerifyOrder);
	    
	    iso := hom<H -> G | goldGens>;	    
	    inv := hom<G -> node`NiceData`Group | niceGens>;
	    
	    node`LeafData`ToGold :=
		hom<node`NiceData`Group -> G | g :-> iso(g)>;
	    node`LeafData`FromGold :=
		hom<G -> node`NiceData`Group | g :-> inv(g)>;

	    // Constructive membership testing with exception handling
	    g2slpGold := hom<node`LeafData`GoldCopy -> WG | g :-> 
                MembershipTesting(node,
		func<h | BuiltinMembership(node`LeafData`GoldCopy, h)>, g)>;
	end if;
	    
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	n := NumberOfGenerators(node`NiceData`WordGroup);
	centerMembership := hom<center -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node, func<h | C9CenterMembership(center,
	    node`Scalar, h)>, g), [node`NiceData`WordGroup.n])>;

	// Constructive membership testing with exception handling
	g2slp := hom<H -> node`NiceData`WordGroup | g :->
	C9Membership(node`NiceData`Group, g2slpProj, centerMembership, g)>;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := slp2g,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;
		
	// We have immediate presentations for some sporadics
	node`FastVerify := IsDefined(SporadicGroupPresentations, name);
	node`FindFactors := proc< ~node |
	    SporadicFactorData(~node, center, g2slpGold)>;
	
	vprint CompositionTree, 2 : "Obtain sporadic presentation:", name;
	node`FindPresentation := proc< ~node |
	    SporadicPresentation(~node, name, center, centerMembership)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;
	
	error Error(rec<LeafError | Description := "18", Error := err>);
    end try;
end procedure;
