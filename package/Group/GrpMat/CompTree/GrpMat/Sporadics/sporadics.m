freeze;

import "standardgens.m": StandardGens;


import "Code/BlackBoxes/L43.m":StandardGeneratorsL43;
import "Code/BlackBoxes/2O8p3.m":StandardGenerators2O8p3;
import "Code/BlackBoxes/O8p3.m":StandardGeneratorsO8p3;
import "Code/BlackBoxes/A7.m":StandardGeneratorsA7;
import "Code/BlackBoxes/S102.m":StandardGeneratorsS102;
import "Code/BlackBoxes/O73.m":StandardGeneratorsO73;
import "Code/BlackBoxes/O10p2.m":StandardGeneratorsO10p2;
import "Code/BlackBoxes/U37.m":StandardGeneratorsU37;
import "Code/BlackBoxes/U39.m":StandardGeneratorsU39;
import "Code/BlackBoxes/U311.m":StandardGeneratorsU311;
import "Code/BlackBoxes/U313.m":StandardGeneratorsU313;
import "Code/BlackBoxes/U316.m":StandardGeneratorsU316;
import "Code/BlackBoxes/U44.m":StandardGeneratorsU44;
import "Code/BlackBoxes/U45.m":StandardGeneratorsU45;
import "Code/BlackBoxes/U54.m":StandardGeneratorsU54;
import "Code/BlackBoxes/2U63.m":StandardGenerators2U63;
import "Code/BlackBoxes/U63.m":StandardGeneratorsU63;
import "Code/BlackBoxes/U82.m":StandardGeneratorsU82;
import "Code/BlackBoxes/E62.m":StandardGeneratorsE62;
import "Code/BlackBoxes/TE62.m":StandardGeneratorsTE62;
import "Code/BlackBoxes/TD43.m":StandardGeneratorsTD43;
import "Code/BlackBoxes/TD42.m":StandardGeneratorsTD42;
import "Code/BlackBoxes/G23.m":StandardGeneratorsG23;
import "Code/BlackBoxes/G24.m":StandardGeneratorsG24;
import "Code/BlackBoxes/G25.m":StandardGeneratorsG25;
import "Code/BlackBoxes/F42.m":StandardGeneratorsF42;
import "Code/BlackBoxes/M11.m":StandardGeneratorsM11;
import "Code/BlackBoxes/M12.m":StandardGeneratorsM12;
import "Code/BlackBoxes/M22.m":StandardGeneratorsM22;
import "Code/BlackBoxes/M23.m":StandardGeneratorsM23;
import "Code/BlackBoxes/M24.m":StandardGeneratorsM24;
import "Code/BlackBoxes/McL.m":StandardGeneratorsMcL;
import "Code/BlackBoxes/Co1.m":StandardGeneratorsCo1;
import "Code/BlackBoxes/Co2.m":StandardGeneratorsCo2;
import "Code/BlackBoxes/Co3.m":StandardGeneratorsCo3;
import "Code/BlackBoxes/Fi22.m":StandardGeneratorsFi22;
import "Code/BlackBoxes/Fi23.m":StandardGeneratorsFi23;
import "Code/BlackBoxes/Fi24.m":StandardGeneratorsFi24;
import "Code/BlackBoxes/J1.m":StandardGeneratorsJ1;
import "Code/BlackBoxes/J2.m":StandardGeneratorsJ2;
import "Code/BlackBoxes/J3.m":StandardGeneratorsJ3;
import "Code/BlackBoxes/J4.m":StandardGeneratorsJ4;
import "Code/BlackBoxes/He.m":StandardGeneratorsHe;
import "Code/BlackBoxes/HN.m":StandardGeneratorsHN;
import "Code/BlackBoxes/HS.m":StandardGeneratorsHS;
import "Code/BlackBoxes/Ly.m":StandardGeneratorsLy;
import "Code/BlackBoxes/ON.m":StandardGeneratorsON;
import "Code/BlackBoxes/Ru.m":StandardGeneratorsRu;
import "Code/BlackBoxes/Suz.m":StandardGeneratorsSuz;
import "Code/BlackBoxes/TF42.m":StandardGeneratorsTF42;
import "Code/BlackBoxes/Th.m":StandardGeneratorsTh;
import "Code/BlackBoxes/B.m":StandardGeneratorsB;
import "Code/BlackBoxes/M.m":StandardGeneratorsM;

import "Code/BlackBoxes/Autm/G24.m":StandardGeneratorsG24Autm;
import "Code/BlackBoxes/Autm/F42.m":StandardGeneratorsF42Autm;
import "Code/BlackBoxes/Autm/Fi22.m":StandardGeneratorsFi22Autm;
import "Code/BlackBoxes/Autm/Fi24.m":StandardGeneratorsFi24Autm;
import "Code/BlackBoxes/Autm/He.m":StandardGeneratorsHeAutm;
import "Code/BlackBoxes/Autm/HN.m":StandardGeneratorsHNAutm;
import "Code/BlackBoxes/Autm/HS.m":StandardGeneratorsHSAutm;
import "Code/BlackBoxes/Autm/J2.m":StandardGeneratorsJ2Autm;
import "Code/BlackBoxes/Autm/J3.m":StandardGeneratorsJ3Autm;
import "Code/BlackBoxes/Autm/M12.m":StandardGeneratorsM12Autm;
import "Code/BlackBoxes/Autm/M22.m":StandardGeneratorsM22Autm;
import "Code/BlackBoxes/Autm/McL.m":StandardGeneratorsMcLAutm;
import "Code/BlackBoxes/Autm/ON.m":StandardGeneratorsONAutm;
import "Code/BlackBoxes/Autm/Suz.m":StandardGeneratorsSuzAutm;
import "Code/BlackBoxes/Autm/TF42.m":StandardGeneratorsTF42Autm;

import "Code/Presentations/2Sz8.m":Presentation2Sz8;
import "Code/Presentations/Sz8.m":PresentationSz8;
import "Code/Presentations/L43.m":PresentationL43;
import "Code/Presentations/2O8p3.m":Presentation2O8p3;
import "Code/Presentations/O8p3.m":PresentationO8p3;
import "Code/Presentations/A7.m":PresentationA7;
import "Code/Presentations/S102.m":PresentationS102;
import "Code/Presentations/O73.m":PresentationO73;
import "Code/Presentations/O10p2.m":PresentationO10p2;
import "Code/Presentations/U37.m":PresentationU37;
import "Code/Presentations/U39.m":PresentationU39;
import "Code/Presentations/U311.m":PresentationU311;
import "Code/Presentations/U313.m":PresentationU313;
import "Code/Presentations/U316.m":PresentationU316;
import "Code/Presentations/U44.m":PresentationU44;
import "Code/Presentations/U45.m":PresentationU45;
import "Code/Presentations/U54.m":PresentationU54;
import "Code/Presentations/U63.m":PresentationU63;
import "Code/Presentations/2U63.m":Presentation2U63;
import "Code/Presentations/U82.m":PresentationU82;
import "Code/Presentations/E62.m":PresentationE62;
import "Code/Presentations/TD43.m":PresentationTD43;
import "Code/Presentations/TE62.m":PresentationTE62;
import "Code/Presentations/TD42.m":PresentationTD42;
import "Code/Presentations/G23.m":PresentationG23;
import "Code/Presentations/G24.m":PresentationG24;
import "Code/Presentations/G25.m":PresentationG25;
import "Code/Presentations/F42.m":PresentationF42;
import "Code/Presentations/M11.m":PresentationM11;
import "Code/Presentations/M12.m":PresentationM12;
import "Code/Presentations/M22.m":PresentationM22;
import "Code/Presentations/M23.m":PresentationM23;
import "Code/Presentations/M24.m":PresentationM24;
import "Code/Presentations/McL.m":PresentationMcL;
import "Code/Presentations/Co1.m":PresentationCo1;
import "Code/Presentations/Co2.m":PresentationCo2;
import "Code/Presentations/Co3.m":PresentationCo3;
import "Code/Presentations/Fi22.m":PresentationFi22;
import "Code/Presentations/Fi23.m":PresentationFi23;
import "Code/Presentations/Fi24.m":PresentationFi24;
import "Code/Presentations/J1.m":PresentationJ1;
import "Code/Presentations/J2.m":PresentationJ2;
import "Code/Presentations/J3.m":PresentationJ3;
import "Code/Presentations/J4.m":PresentationJ4;
import "Code/Presentations/He.m":PresentationHe;
import "Code/Presentations/HN.m":PresentationHN;
import "Code/Presentations/HS.m":PresentationHS;
import "Code/Presentations/Ly.m":PresentationLy;
import "Code/Presentations/ON.m":PresentationON;
import "Code/Presentations/Ru.m":PresentationRu;
import "Code/Presentations/Suz.m":PresentationSuz;
import "Code/Presentations/TF42.m":PresentationTF42;
import "Code/Presentations/Th.m":PresentationTh;
import "Code/Presentations/B.m":PresentationB;
import "Code/Presentations/M.m":PresentationM;

import "Code/Presentations/Autm/G24.m":PresentationG24Autm;
import "Code/Presentations/Autm/F42.m":PresentationF42Autm;
import "Code/Presentations/Autm/Fi22.m":PresentationFi22Autm;
import "Code/Presentations/Autm/Fi24.m":PresentationFi24Autm;
import "Code/Presentations/Autm/He.m":PresentationHeAutm;
import "Code/Presentations/Autm/HN.m":PresentationHNAutm;
import "Code/Presentations/Autm/HS.m":PresentationHSAutm;
import "Code/Presentations/Autm/J2.m":PresentationJ2Autm;
import "Code/Presentations/Autm/J3.m":PresentationJ3Autm;
import "Code/Presentations/Autm/M12.m":PresentationM12Autm;
import "Code/Presentations/Autm/M22.m":PresentationM22Autm;
import "Code/Presentations/Autm/McL.m":PresentationMcLAutm;
import "Code/Presentations/Autm/ON.m":PresentationONAutm;
import "Code/Presentations/Autm/Suz.m":PresentationSuzAutm;
import "Code/Presentations/Autm/TF42.m":PresentationTF42Autm;

import "Code/Maximal-Subgroups/Sz8.m":DataSz8;
import "Code/Maximal-Subgroups/2O8p3.m":Data2O8p3;
import "Code/Maximal-Subgroups/O8p3.m":DataO8p3;
import "Code/Maximal-Subgroups/O10p2.m":DataO10p2;
import "Code/Maximal-Subgroups/S82.m":DataS82;
import "Code/Maximal-Subgroups/A7.m":DataA7;
import "Code/Maximal-Subgroups/U37.m":DataU37;
import "Code/Maximal-Subgroups/U63.m":DataU63;
import "Code/Maximal-Subgroups/2U63.m":Data2U63;
import "Code/Maximal-Subgroups/U311.m":DataU311;
import "Code/Maximal-Subgroups/TE62.m":DataTE62;
import "Code/Maximal-Subgroups/TD43.m":DataTD43;
import "Code/Maximal-Subgroups/TD42.m":DataTD42;
import "Code/Maximal-Subgroups/G23.m":DataG23;
import "Code/Maximal-Subgroups/G24.m":DataG24;
import "Code/Maximal-Subgroups/G25.m":DataG25;
import "Code/Maximal-Subgroups/F42.m":DataF42;
import "Code/Maximal-Subgroups/M11.m":DataM11;
import "Code/Maximal-Subgroups/M12.m":DataM12;
import "Code/Maximal-Subgroups/M22.m":DataM22;
import "Code/Maximal-Subgroups/M23.m":DataM23;
import "Code/Maximal-Subgroups/M24.m":DataM24;
import "Code/Maximal-Subgroups/McL.m":DataMcL;
import "Code/Maximal-Subgroups/Co1.m":DataCo1;
import "Code/Maximal-Subgroups/Co2.m":DataCo2;
import "Code/Maximal-Subgroups/Co3.m":DataCo3;
import "Code/Maximal-Subgroups/Fi22.m":DataFi22;
import "Code/Maximal-Subgroups/Fi23.m":DataFi23;
import "Code/Maximal-Subgroups/Fi24.m":DataFi24;
import "Code/Maximal-Subgroups/J1.m":DataJ1;
import "Code/Maximal-Subgroups/J2.m":DataJ2;
import "Code/Maximal-Subgroups/J3.m":DataJ3;
import "Code/Maximal-Subgroups/J4.m":DataJ4;
import "Code/Maximal-Subgroups/He.m":DataHe;
import "Code/Maximal-Subgroups/HN.m":DataHN;
import "Code/Maximal-Subgroups/HS.m":DataHS;
import "Code/Maximal-Subgroups/Ly.m":DataLy;
import "Code/Maximal-Subgroups/ON.m":DataON;
import "Code/Maximal-Subgroups/Ru.m":DataRu;
import "Code/Maximal-Subgroups/Suz.m":DataSuz;
import "Code/Maximal-Subgroups/TF42.m":DataTF42;
import "Code/Maximal-Subgroups/Th.m":DataTh;
import "Code/Maximal-Subgroups/B.m":DataB;
import "Code/Maximal-Subgroups/M.m":DataM;

import "Code/Maximal-Subgroups/Autm/M12.m":DataM12Autm;
import "Code/Maximal-Subgroups/Autm/M22.m":DataM22Autm;
import "Code/Maximal-Subgroups/Autm/Fi22.m":DataFi22Autm;
import "Code/Maximal-Subgroups/Autm/Fi24.m":DataFi24Autm;
import "Code/Maximal-Subgroups/Autm/McL.m":DataMcLAutm;
import "Code/Maximal-Subgroups/Autm/Suz.m":DataSuzAutm;
import "Code/Maximal-Subgroups/Autm/TF42.m":DataTF42Autm;
import "Code/Maximal-Subgroups/Autm/J2.m":DataJ2Autm;
import "Code/Maximal-Subgroups/Autm/J3.m":DataJ3Autm;
import "Code/Maximal-Subgroups/Autm/He.m":DataHeAutm;
import "Code/Maximal-Subgroups/Autm/HN.m":DataHNAutm;
import "Code/Maximal-Subgroups/Autm/HS.m":DataHSAutm;
import "Code/Maximal-Subgroups/Autm/ON.m":DataONAutm;

import "Code/Chains/chains.m":SubgroupChainsSz8;
import "Code/Chains/chains.m":SubgroupChains2O8p3;
import "Code/Chains/chains.m":SubgroupChainsO8p3;
import "Code/Chains/chains.m":SubgroupChainsO10p2;
import "Code/Chains/chains.m":SubgroupChainsA7;
import "Code/Chains/chains.m":SubgroupChainsU37;
import "Code/Chains/chains.m":SubgroupChainsU63;
import "Code/Chains/chains.m":SubgroupChains2U63;
import "Code/Chains/chains.m":SubgroupChainsU311;
import "Code/Chains/chains.m":SubgroupChainsTE62;
import "Code/Chains/chains.m":SubgroupChainsTD43;
import "Code/Chains/chains.m":SubgroupChainsG23;
import "Code/Chains/chains.m":SubgroupChainsG24;
import "Code/Chains/chains.m":SubgroupChainsG25;
import "Code/Chains/chains.m":SubgroupChainsTD42;
import "Code/Chains/chains.m":SubgroupChainsF42;
import "Code/Chains/chains.m":SubgroupChainsM11;
import "Code/Chains/chains.m":SubgroupChainsM12;
import "Code/Chains/chains.m":SubgroupChainsM22;
import "Code/Chains/chains.m":SubgroupChainsM23;
import "Code/Chains/chains.m":SubgroupChainsM24;
import "Code/Chains/chains.m":SubgroupChainsMcL;
import "Code/Chains/chains.m":SubgroupChainsCo1;
import "Code/Chains/chains.m":SubgroupChainsCo2;
import "Code/Chains/chains.m":SubgroupChainsCo3;
import "Code/Chains/chains.m":SubgroupChainsFi22;
import "Code/Chains/chains.m":SubgroupChainsFi23;
import "Code/Chains/chains.m":SubgroupChainsFi24;
import "Code/Chains/chains.m":SubgroupChainsJ1;
import "Code/Chains/chains.m":SubgroupChainsJ2;
import "Code/Chains/chains.m":SubgroupChainsJ3;
import "Code/Chains/chains.m":SubgroupChainsJ4;
import "Code/Chains/chains.m":SubgroupChainsHe;
import "Code/Chains/chains.m":SubgroupChainsHN;
import "Code/Chains/chains.m":SubgroupChainsHS;
import "Code/Chains/chains.m":SubgroupChainsLy;
import "Code/Chains/chains.m":SubgroupChainsON;
import "Code/Chains/chains.m":SubgroupChainsRu;
import "Code/Chains/chains.m":SubgroupChainsSuz;
import "Code/Chains/chains.m":SubgroupChainsTh;
import "Code/Chains/chains.m":SubgroupChainsTF42;
// import "Code/Chains/chains.m":SubgroupChainsB;
// import "Code/Chains/chains.m":SubgroupChainsM;

import "Code/Chains/base.m": NextStep;
import "Code/List.m": ListMaximals, ListAll;

ValidGenerators := function (G, X)

   if Type (G) eq GrpPerm and Type (Rep (X)) eq GrpPermElt then
      return Degree (Parent (Rep (X))) eq Degree (G);
   elif Type (G) eq GrpMat and Type (Rep (X)) eq GrpMatElt then 
      return Nrows (Rep(X)) eq Degree (G) and 
             #BaseRing (Parent (Rep (X))) eq #BaseRing (G);
   else 
      return false;
   end if;

end function;

/* set up hom from B -> G where U is the list of images of
   generators of B; do it in this way to  ensure that it
   does not force membership testing in G */

MyHom := function (G, B, U)
   d := Degree (G);
   if Type (G) eq GrpMat then
      F := BaseRing (G);
      P := GL (d, F);
   elif Type (G) eq GrpPerm then
      P := Sym (d);
   end if;
   gens := [P ! G.i : i in [1..Ngens (G)]];
   pos := [Position (gens, U[i]) : i in [1..#U]];
   return hom <B -> G | [G.i : i in pos]>;

end function;

intrinsic ElementOfOrder (P :: GrpRandProc, RequiredOrder, Limit :: 
                          RngIntElt : Word := true, Fct := Order) 
                      -> GrpElt, GrpSLPElt 
{Fct can be Order or ProjectiveOrder; search at most Limit times for 
 element of (projective) order RequiredOrder; if found return element 
 and possibly word, else return false} 

   // if Type (Random (P)) ne GrpMatElt then Fct := Order; end if;

   if Type (RequiredOrder) eq RngIntElt then 
      RequiredOrder := {RequiredOrder};
   end if;

   NmrTries := Limit;
   repeat
      if Word then 
         g, w := Random (P);
      else 
         g := Random (P);
      end if;
      o := Fct (g);
      NmrTries -:= 1;
      rem := exists (x) {x : x in RequiredOrder | (o mod x eq 0)};
   until rem or (NmrTries eq 0);

   if rem then o := o div x; 
      if Word then return g^o, w^o; else return g^o, _; end if; 
   end if;

   return false, _; 

end intrinsic;

intrinsic StandardPresentation (G:: Grp, str :: MonStgElt : 
           AutomorphismGroup := false, 
           Generators := [], Projective := false) -> BoolElt
{return true if standard presentation is satisfied by generators 
 of sporadic group G having name str, else false; 
 if AutomorphismGroup is true, assume G is automorphism group 
 of sporadic group having name str;
 standard generators can be supplied, otherwise defining generators are
 assumed to be standard; if G is absolutely irreducible matrix group and 
 Projective is true, then verify presentation possibly modulo centre of G}

   if AutomorphismGroup eq true then 
      case str:
         when "F22", "Fi22": A := PresentationFi22Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "F24", "Fi24": A := PresentationFi24Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "He": A := PresentationHeAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "HN": A := PresentationHNAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "HS": A := PresentationHSAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "J2": A := PresentationJ2Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "J3": A := PresentationJ3Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "M12": A := PresentationM12Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "M22": A := PresentationM22Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "McL": A := PresentationMcLAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "ON": A := PresentationONAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "Suz": A := PresentationSuzAutm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "TF42": A := PresentationTF42Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "F42": A := PresentationF42Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         when "G24": A := PresentationG24Autm (G : 
             UserGenerators := Generators, Projective := Projective);
         else return false;
      end case;
      return A;
   end if;

   case str:
      when "B": A := PresentationB (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Co1": A := PresentationCo1 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Co2": A := PresentationCo2 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Co3": A := PresentationCo3 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "F22", "Fi22": A := PresentationFi22 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "F23", "Fi23": A := PresentationFi23 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "F24", "Fi24": A := PresentationFi24 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "He": A := PresentationHe (G: 
                UserGenerators := Generators, Projective := Projective);
      when "HN": A := PresentationHN (G: 
                UserGenerators := Generators, Projective := Projective);
      when "HS": A := PresentationHS (G: 
                UserGenerators := Generators, Projective := Projective);
      when "J1": A := PresentationJ1 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "J2": A := PresentationJ2 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "J3": A := PresentationJ3 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "J4": A := PresentationJ4 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Ly": A := PresentationLy (G: 
                UserGenerators := Generators, Projective := Projective);
      when "M11": A := PresentationM11 (G:
                UserGenerators := Generators, Projective := Projective);
      when "M12": A := PresentationM12 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "M22": A := PresentationM22 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "M23": A := PresentationM23 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "M24": A := PresentationM24 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "McL": A := PresentationMcL (G: 
                UserGenerators := Generators, Projective := Projective);
      when "M": A := PresentationM (G: 
                UserGenerators := Generators, Projective := Projective);
      when "ON": A := PresentationON (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Ru": A := PresentationRu (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Suz": A := PresentationSuz (G: 
                UserGenerators := Generators, Projective := Projective);
      when "TF42": A := PresentationTF42 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "F42": A := PresentationF42 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Th": A := PresentationTh (G: 
                UserGenerators := Generators, Projective := Projective);
      when "G23": A := PresentationG23 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "G24": A := PresentationG24 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "G25": A := PresentationG25 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "TD42": A := PresentationTD42 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "TD43": A := PresentationTD43 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "TE62": A := PresentationTE62 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "E62": A := PresentationE62 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "S102": A := PresentationS102 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "O73": A := PresentationO73 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "O10p2": A := PresentationO10p2 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U37": A := PresentationU37 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U39": A := PresentationU39 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U311": A := PresentationU311 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U313": A := PresentationU313 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U316": A := PresentationU316 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U44": A := PresentationU44 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U45": A := PresentationU45 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U54": A := PresentationU54 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U63": A := PresentationU63 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "2U63": A := Presentation2U63 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "U82": A := PresentationU82 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "A7": A := PresentationA7 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "O8p3": A := PresentationO8p3 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "2O8p3": A := Presentation2O8p3 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "L43": A := PresentationL43 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "2L43": A := PresentationL43 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "Sz8": A := PresentationSz8 (G: 
                UserGenerators := Generators, Projective := Projective);
      when "2Sz8": A := Presentation2Sz8 (G: 
                UserGenerators := Generators, Projective := Projective);
      else return false;
   end case;
   return A;
end intrinsic;

/* 
procedure InitialiseGroup (G)
   if assigned G`SLPGroup then return; end if;
   U := [G.i: i in [1..Ngens (G)]];
   G`UserGenerators := U;
   n := #U;
   B := SLPGroup (n);
   G`SLPGroup := B;
   G`SLPGroupHom := MyHom (G, B, U);
end procedure;
*/

intrinsic StandardGenerators (G:: Grp, str :: MonStgElt : 
          AutomorphismGroup := false, 
             MaxTries:=2000,
          Projective := false) -> BoolElt, SeqEnum, SeqEnum
{construct standard generators for sporadic group G having name str; 
 words in SLP group defined on the defining generators of G 
 are also obtained for the standard generators; if AutomorphismGroup is 
 true, assume G is automorphism group of sporadic group having name str;
 if standard generators found, return true and sequences of
 generators and words, else false; if Projective is true, 
 then construct standard generators possibly modulo centre of G}

   if AutomorphismGroup eq true then 
   case str:
      when "F22", "Fi22": A, B := StandardGeneratorsFi22Autm (G : Projective := Projective);
      when "F24", "Fi24": A, B := StandardGeneratorsFi24Autm (G : Projective := Projective);
      when "He": A, B := StandardGeneratorsHeAutm (G : Projective := Projective);
      when "HN": A, B := StandardGeneratorsHNAutm (G : Projective := Projective);
      when "HS": A, B := StandardGeneratorsHSAutm (G : Projective := Projective);
      when "J2": A, B := StandardGeneratorsJ2Autm (G : Projective := Projective);
      when "J3": A, B := StandardGeneratorsJ3Autm (G : Projective := Projective);
      when "M12": A, B := StandardGeneratorsM12Autm (G : Projective := Projective);
      when "M22": A, B := StandardGeneratorsM22Autm (G : Projective := Projective);
      when "McL": A, B := StandardGeneratorsMcLAutm (G : Projective := Projective);
      when "ON": A, B := StandardGeneratorsONAutm (G : Projective := Projective);
      when "Suz": A, B := StandardGeneratorsSuzAutm (G : Projective := Projective);
      when "TF42": A, B := StandardGeneratorsTF42Autm (G : Projective := Projective);
      when "F42": A, B := StandardGeneratorsF42Autm (G : Projective := Projective);
      when "G24": A, B := StandardGeneratorsG24Autm (G : Projective := Projective);
      else "<str> is not valid identifier for sporadic group having outer automorphisms"; 
           return false, _, _;
   end case;
   if Type (A) eq BoolElt then return false, _, _; end if;
   return true, A, B;
   end if;

   case str:
      when "B": A, B := StandardGeneratorsB (G : Projective := Projective);
      when "Co1": A, B := StandardGeneratorsCo1 (G : Projective := Projective);
      when "Co2": A, B := StandardGeneratorsCo2 (G : Projective := Projective);
      when "Co3": A, B := StandardGeneratorsCo3 (G : Projective := Projective);
      when "F22", "Fi22": A, B := StandardGeneratorsFi22 (G : Projective := Projective);
      when "F23", "Fi23": A, B := StandardGeneratorsFi23 (G : Projective := Projective);
      when "F24", "Fi24": A, B := StandardGeneratorsFi24 (G : Projective := Projective);
      when "He": A, B := StandardGeneratorsHe (G : Projective := Projective);
      when "HN": A, B := StandardGeneratorsHN (G : Projective := Projective);
      when "HS": A, B := StandardGeneratorsHS (G : Projective := Projective);
      when "J1": A, B := StandardGeneratorsJ1 (G : Projective := Projective);
      when "J2": A, B := StandardGeneratorsJ2 (G : Projective := Projective);
      when "J3": A, B := StandardGeneratorsJ3 (G : Projective := Projective);
      when "J4": A, B := StandardGeneratorsJ4 (G : Projective := Projective);
      when "Ly": A, B := StandardGeneratorsLy (G : Projective := Projective);
      when "M11": A, B := StandardGeneratorsM11 (G : Projective := Projective);
      when "M12": A, B := StandardGeneratorsM12 (G : Projective := Projective);
      when "M22": A, B := StandardGeneratorsM22 (G : Projective := Projective);
      when "M23": A, B := StandardGeneratorsM23 (G : Projective := Projective);
      when "M24": A, B := StandardGeneratorsM24 (G : Projective := Projective);
      when "McL": A, B := StandardGeneratorsMcL (G : Projective := Projective);
      when "M": A, B := StandardGeneratorsM (G : Projective := Projective);
      when "ON": A, B := StandardGeneratorsON (G : Projective := Projective);
      when "Ru": A, B := StandardGeneratorsRu (G : Projective := Projective);
      when "Suz": A, B := StandardGeneratorsSuz (G : Projective := Projective);
      when "TF42": A, B := StandardGeneratorsTF42 (G : Projective := Projective);
      when "F42": A, B := StandardGeneratorsF42 (G : Projective := Projective);
      when "Th": A, B := StandardGeneratorsTh (G : Projective := Projective);
      when "G23": A, B := StandardGeneratorsG23 (G : Projective := Projective);
      when "G24": A, B := StandardGeneratorsG24 (G : Projective := Projective);
      when "G25": A, B := StandardGeneratorsG25 (G : Projective := Projective);
      when "TD42": A, B := StandardGeneratorsTD42 (G : Projective := Projective);
      when "TD43": A, B := StandardGeneratorsTD43 (G : Projective := Projective);
      when "TE62": A, B := StandardGeneratorsTE62 (G : Projective := Projective);
      when "E62": A, B := StandardGeneratorsE62 (G : Projective := Projective);
      when "S102": A, B := StandardGeneratorsS102 (G : Projective := Projective);
      when "O73": A, B := StandardGeneratorsO73 (G : Projective := Projective);
      when "O10p2": A, B := StandardGeneratorsO10p2 (G : Projective := Projective);
      when "U37": A, B := StandardGeneratorsU37 (G : Projective := Projective);
      when "U39": A, B := StandardGeneratorsU39 (G : Projective := Projective);
      when "U311": A, B := StandardGeneratorsU311 (G : Projective := Projective);
      when "U313": A, B := StandardGeneratorsU313 (G : Projective := Projective);
      when "U316": A, B := StandardGeneratorsU316 (G : Projective := Projective);
      when "U44": A, B := StandardGeneratorsU44 (G : Projective := Projective);
      when "U45": A, B := StandardGeneratorsU45 (G : Projective := Projective);
      when "U54": A, B := StandardGeneratorsU54 (G : Projective := Projective);
      when "U63": A, B := StandardGeneratorsU63 (G : Projective := Projective);
      when "2U63": A, B := StandardGenerators2U63 (G : Projective := Projective);
      when "U82": A, B := StandardGeneratorsU82 (G : Projective := Projective);
      when "A7": A, B := StandardGeneratorsA7 (G : Projective := Projective);
      when "O8p3": A, B := StandardGeneratorsO8p3 (G : Projective := Projective);
      when "2O8p3": A, B := StandardGenerators2O8p3 (G : Projective := Projective);
      when "U62": f, A, B := StandardGens(G, str: Projective := Projective, MaxTries := MaxTries); 
      when "3U62": f, A, B := StandardGens(G, str: MaxTries := MaxTries);
      when "Sz8": f, A, B := StandardGens(G, str: Projective := Projective, MaxTries := MaxTries); 
      when "2Sz8": f, A, B := StandardGens(G, str: Projective := Projective, MaxTries := MaxTries); 
      else
          f, A, B := StandardGens(G, str: Projective := Projective, MaxTries := MaxTries);
          if not f then return false, _, _;  end if;
      end case;
   if Type (A) eq BoolElt then return false, _, _; end if;
   return true, A, B;
end intrinsic;

intrinsic MaximalSubgroupsData (str :: MonStgElt: AutomorphismGroup :=
false) -> BoolElt, SeqEnum
{Stored data for maximal subgroups of sporadic group having name str; if 
 AutomorphismGroup is true, then return data for its automorphism group} 

   if AutomorphismGroup eq true then 
   case str:
      when "F22", "Fi22": A := DataFi22Autm ();
      when "F24", "Fi24": A := DataFi24Autm ();
      when "ON": A := DataONAutm ();
      when "Suz": A := DataSuzAutm ();
      when "TF42": A := DataTF42Autm ();
      when "He": A := DataHeAutm ();
      when "HN": A := DataHNAutm ();
      when "HS": A := DataHSAutm ();
      when "J2": A := DataJ2Autm ();
      when "J3": A := DataJ3Autm ();
      when "M12": A := DataM12Autm ();
      when "M22": A := DataM22Autm ();
      when "McL": A := DataMcLAutm ();
      else 
         "<str> is not valid identifier for sporadic group having outer automorphisms"; 
        return false;
   end case;
   return [A[i]: i in [2..#A]];
   end if;

   case str:
      when "B": A := DataB ();
      when "Co1": A := DataCo1 ();
      when "Co2": A := DataCo2 ();
      when "Co3": A := DataCo3 ();
      when "F22", "Fi22": A := DataFi22 ();
      when "F23", "Fi23": A := DataFi23 ();
      when "F24", "Fi24": A := DataFi24 ();
      when "He": A := DataHe ();
      when "HN": A := DataHN ();
      when "HS": A := DataHS ();
      when "J1": A := DataJ1 ();
      when "J2": A := DataJ2 ();
      when "J3": A := DataJ3 ();
      when "J4": A := DataJ4 ();
      when "Ly": A := DataLy ();
      when "M11": A := DataM11 ();
      when "M12": A := DataM12 ();
      when "M22": A := DataM22 ();
      when "M23": A := DataM23 ();
      when "M24": A := DataM24 ();
      when "McL": A := DataMcL ();
      when "M": A := DataM ();
      when "ON": A := DataON ();
      when "Ru": A := DataRu ();
      when "Suz": A := DataSuz ();
      when "TF42": A := DataTF42 ();
      when "F42": A := DataF42 ();
      when "Th": A := DataTh ();
      when "G23": A := DataG23 ();
      when "G24": A := DataG24 ();
      when "G25": A := DataG25 ();
      when "TD42": A := DataTD42 ();
      when "TD43": A := DataTD43 ();
      when "TE62": A := DataTE62 ();
      when "U37": A := DataU37 ();
      when "U63": A := DataU63 ();
      when "2U63": A := Data2U63 ();
      when "U311": A := DataU311 ();
      when "A7": A := DataA7 ();
      when "O10p2": A := DataO10p2 ();
      when "S82": A := DataS82 ();
      when "O8p3": A := DataO8p3 ();
      when "2O8p3": A := Data2O8p3 ();
      when "Sz8": A := DataSz8 ();
      else return false;
   end case;
   return [A[i]: i in [2..#A]];
end intrinsic;

intrinsic MaximalSubgroups (G :: Grp, str :: MonStgElt : 
                            Generators := [], AutomorphismGroup := false, 
                            Projective := false) -> BoolElt, SeqEnum
{certain maximal subgroups of sporadic group G having name str;
 if AutomorphismGroup is true, then G is automorphism 
 group of sporadic and return certain maximals of G;
 if standard generators supplied or found for G, then return true 
 and list, else return false; if Projective is true, then construct 
 standard generators and so subgroups possibly modulo centre of G}

   if AutomorphismGroup eq true then 
      if Generators eq [] then 
         flag, X := StandardGenerators (G, str : 
            AutomorphismGroup := true, Projective := Projective);
         if not flag then "No standard generators found"; end if;
      else 
         X := Generators;
         // flag := ValidGenerators (G, X) and StandardPresentation (G, str: 
         // AutomorphismGroup := true, Generators := X, Projective := Projective);
         flag := ValidGenerators (G, X);
         if not flag then "Supplied generators are not standard"; end if;
      end if;
      if not flag then return false, _; end if;
      return true, ListMaximals (G, str cat ":2", 
         MaximalSubgroupsData (str : AutomorphismGroup := true): 
         UserGenerators := X);
   end if;

   if Generators eq [] then 
      flag, X := StandardGenerators (G, str : Projective := Projective);
      if not flag then "No standard generators found"; end if;
   else 
      X := Generators;
      // flag := ValidGenerators (G, X) and StandardPresentation (G, str: 
      //                 Generators := X, Projective := Projective);
      flag := ValidGenerators (G, X);
      if not flag then "Supplied generators are not standard"; end if;
   end if;
   if not flag then return false, _; end if;
   return true, ListMaximals (G, str, MaximalSubgroupsData (str): 
                        UserGenerators := X);

end intrinsic;

intrinsic SubgroupsData (str :: MonStgElt ) -> SeqEnum
{Stored subgroup data for sporadic group having name str}
   case str:
      when "Co1": L := SubgroupChainsCo1 ();
      when "Co2": L := SubgroupChainsCo2 ();
      when "Co3": L := SubgroupChainsCo3 ();
      when "F22", "Fi22": L := SubgroupChainsFi22 ();
      when "F23", "Fi23": L := SubgroupChainsFi23 ();
      when "F24", "Fi24": L := SubgroupChainsFi24 ();
      when "He": L := SubgroupChainsHe ();
      when "HN": L := SubgroupChainsHN ();
      when "HS": L := SubgroupChainsHS ();
      when "J1": L := SubgroupChainsJ1 ();
      when "J2": L := SubgroupChainsJ2 ();
      when "J3": L := SubgroupChainsJ3 ();
      when "J4": L := SubgroupChainsJ4 ();
      when "Ly": L := SubgroupChainsLy ();
      when "M11": L := SubgroupChainsM11 ();
      when "M12": L := SubgroupChainsM12 ();
      when "M22": L := SubgroupChainsM22 ();
      when "M23": L := SubgroupChainsM23 ();
      when "M24": L := SubgroupChainsM24 ();
      when "McL": L := SubgroupChainsMcL ();
      when "ON": L := SubgroupChainsON ();
      when "Ru": L := SubgroupChainsRu ();
      when "Suz": L := SubgroupChainsSuz ();
      when "Th": L := SubgroupChainsTh ();
//      when "B": L := SubgroupChainsB ();
//      when "M": L := SubgroupChainsM ();
      when "TF42": L := SubgroupChainsTF42 ();
      when "F42": L := SubgroupChainsF42 ();
      when "G23": L := SubgroupChainsG23 ();
      when "G24": L := SubgroupChainsG24 ();
      when "G25": L := SubgroupChainsG25 ();
      when "TD42": L := SubgroupChainsTD42 ();
      when "TD43": L := SubgroupChainsTD43 ();
      when "TE62": L := SubgroupChainsTE62 ();
      when "U37": L := SubgroupChainsU37 ();
      when "U63": L := SubgroupChainsU63 ();
      when "2U63": L := SubgroupChains2U63 ();
      when "U311": L := SubgroupChainsU311 ();
      when "A7": L := SubgroupChainsA7 ();
      when "O10p2": L := SubgroupChainsO10p2 ();
      when "O8p3": L := SubgroupChainsO8p3 ();
      when "2O8p3": L := SubgroupChains2O8p3 ();
      when "Sz8": L := SubgroupChainsSz8 ();
      else return false;
   end case;
   return L;
end intrinsic;

intrinsic Subgroups (G :: Grp, str :: MonStgElt:
          Generators := [], Projective := false) -> BoolElt, SeqEnum
{Certain subgroups for sporadic group G having name str;
 if standard generators supplied or found for G then 
 return true and list of subgroups, else return false; 
 if Projective is true, then construct standard generators 
 possibly modulo centre of G}

   if Generators eq [] then 
      flag, X := StandardGenerators (G, str: Projective := Projective); 
      if not flag then "No standard generators found"; end if;
   else 
      X := Generators;
      // flag := ValidGenerators (G, X) and StandardPresentation (G, str: 
      //                 Generators := X, Projective := Projective);
      flag := ValidGenerators (G, X);
      if not flag then "Supplied generators are not standard"; end if;
   end if;

   if not flag then return false, _; end if;

   L := SubgroupsData (str);
   if Type (L) eq BoolElt then return false, _; end if;

   GroupName := L[1]`name;

   if Type (G) eq GrpMat then 
      H := sub <GL (Degree (G), BaseRing (G)) | X>;
   else
      H := sub <G | X>;
   end if;

   S := ListAll (H, GroupName, L);
   return true, S;
end intrinsic;

intrinsic GoodBasePoints (G :: GrpMat, str :: MonStgElt: 
             Generators := [], Projective := false) -> BoolElt, SeqEnum
{if standard generators supplied or found for sporadic group G having 
 name str, then return true and list of base points for G, else 
 return false; if Projective is true, then standard generators are 
 possibly modulo centre of G, and base points are correspondingly adjusted}

   if str eq "F22" then str := "Fi22"; end if;
   if str eq "F23" then str := "Fi23"; end if;
   if str eq "F24" then str := "Fi24"; end if;
   if str eq "T" then str := "TF24"; end if;
   if str eq "O10p2" and Degree (G) le 200 then return false, _; end if;

   if Generators eq [] then 
      flag, X := StandardGenerators (G, str: Projective := Projective); 
      if not flag then "No standard generators found"; end if;
   else 
      X := Generators;
      // flag := ValidGenerators (G, X) and StandardPresentation (G, str: 
      //                 Generators := X, Projective := Projective);
      flag := ValidGenerators (G, X);
      if not flag then "Supplied generators are not standard"; end if;
   end if;

   if not flag then return false, _; end if;

   L := SubgroupsData (str);
   if Type (L) eq BoolElt then return false, _; end if;

   H := sub <GL (Degree (G), BaseRing (G)) | X>;
   points := [**]; flag := false;
   NextStep (H, L, str, 1, ~points, ~flag);
   return true, points;

end intrinsic;

intrinsic BSGS (G:: GrpMat, str :: MonStgElt)
{Make sure there is a known base and strong generating set for G,
 which is the sporadic group having name str}
   if not assigned G`Base then 
       fl, B := GoodBasePoints (G, str);
       if fl then G`Base := B; end if;
   end if;
   BSGS (G);
end intrinsic;

intrinsic RandomSchreier (G:: GrpMat, str:: MonStgElt : Run := 40)
{Apply RandomSchreier to G, which is the sporadic group having name str}
   if not assigned G`Base then 
       fl, B := GoodBasePoints (G, str);
       if fl then G`Base := B; end if;
   end if;
   RandomSchreier (G: Run := Run);
end intrinsic

