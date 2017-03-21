freeze;

import "reds.m": SLStabOfNSpaceMeetDual, SLStabOfNSpaceMissDual,
                 SLStabOfNSpace, GLStabOfNSpace;
import "sympreds.m": PointStabSp, IsotropicStabSp, SymplecticStab;
import "unitreds.m": IsotropKStab, NonisotropKStab;
import "orthreds.m": NonDegenStabOmega, IsotropicStabOmega, NSPointStabOmega;
import "sp4novelties.m": NoveltyReduct, NoveltySemilin, NoveltyImprims;
import "imp_and_gamma.m": ImprimsMeetSL, GammaL, GammaLMeetSL;
import "sympimprims.m": GetSympImprimsD4, GetWreathProd, GetStabOfHalf;
import "unitimps.m": StandardUnitImps, UnitImpHalfDim;
import "orthimprims.m": OrthImprim, OrthStabOfHalfTS, OrthStabOfHalfND;
import "superfield.m": GammaSp, GammaUMeetSp, GammaSU, GammaOdimEven,
                       GammaOdimOdd, GammaUMeetOmega, GammaOsOdd;
import "tensor.m": SLTensor, SpTensors, SUTensor, OrthSpTensor,
                   OrthTensorOddOdd, OrthTensorEvenOdd, OrthTensorEvenEven;
import "subfield.m": SubfieldSL, SubfieldSp, SubfieldSU, SpInSU, OrthsInSU,
                     SubfieldOdimOdd, SubfieldOdimEven;
import "normes.m": NormaliserOfExtraSpecialGroup,
              NormaliserOfSymplecticGroup, NormaliserOfExtraSpecialGroupMinus;
import "tensorind.m": SUTensorInd, SLTensorInd, SpTensorInd, OrthogSpTensorInd,
                      OrthogTensorInd;
import "classicals.m": GLMinusSL, GUMinusSU, NormSpMinusSp, SOMinusOmega,
                       GOMinusSO, NormGOMinusGO, NormOfSU, NormOfSp, NormOfO;
import "construct.m": ReduceOverFiniteField;
import "o8plussubs.m": TwoOminus8, TwoO7, TwoOminus82, TwoO72,
        KlLine4, KlLine7, KlLine15, KlLine22, KlLine26, KlLine51, KlLine61;
import "generics.m": SymplecticSL2, OrthogSL2, l3qdim6, u3qdim6, l2q3dim8,
        l3qdim8, u3qdim8, l2q2dim9, l3q2dim9l, l3q2dim9u, sp4qdim10,
        l3qdim10, l4qdim10, l5qdim10, u3qdim10, u4qdim10, u5qdim10;

GConjugates := function(S,C,r)
//S is a maximal subgroup of a classical group.
//The list of r conjugates of S under GL/GU/GSp that are not
//conjugates under SL/SU/Sp is returned.
  return [ S^(C^i) : i in [0..r-1] ];
end function;

intrinsic
 ClassicalMaximals(type::MonStgElt, d::RngIntElt, q::RngIntElt :
         classes := {1..9}, all := true, novelties:=false,
      special:=false, general:=false, normaliser:=false) -> SeqEnum
{ Maximal subgroups of quasisimple classical group of "type"(d,q). }
/* Maximal subgroups of quasisimple classical groups in the Aschbacher classes.
 * type must currently be "L", "S", "U", "O+" or "O-" (d even), or "O" (d odd) 
 * classes must be a nonempty subset of {1..9} and signifies the
 * Aschbacher classes required as follows:
 * 1 = reducibles
 * 2 = imprimitives
 * 3 = semiliear (superfield)
 * 4 = tensor product
 * 5 = subfield
 * 6 = normalizer of symplectic-types/extraspecials
 * 7 = tensor induced
 * 8 = classicals
 * 9 = non-classical almost simples
 *
 * Class 9 only works up to dimension 11 at present 
 *
 * if `novelties' is true, then only the Novelty subgroups (see ATLAS for
 * definition) under the appropriate outer automorphisms are returned.
 *
 * if `all' is true, then conjugacy class representatives in the perfect
 * classical group are returned - otherwise, representatives up to
 * conjugacy in the automorphism group are returned.
 *
 * By default, the subgroup of the relevant quasisimple group is returned.
 * If special is true (case O only), normaliser in SO is returned.
 * If general is true (cases L/U/O), normaliser in GL, GU, GO is returned.
 * If normaliser is true (cases Sp/U/O) normaliser in GL is returned. 
 */

 if type cmpne "L" and type cmpne "S" and type cmpne "U" and
    type cmpne "O+" and type cmpne "O-" and type cmpne "O" then
     print
      "<type> must be \"L\" (linear), \"S\" (symplectic), \"U\" (unitary),";
      print "               \"O+\", \"O-\", or \"O\" (orthogonal).";
     error "";
 end if;

 if (type eq "L" and d lt 2) or (type ne "L" and d lt 3) then
   error "dimension <d> is too small";
 end if;

 if (type eq "L" and d eq 2 and q le 3) then
   error "L(2,2) and L(2,3) are solvable";
 end if;

 if (type eq "O" and d eq 3 and q le 3) then
   error "O(3,2) and O(3,3) are solvable";
 end if;

 if (type eq "U" and d eq 3 and q eq 2) then
   error "U(3,2) is solvable";
 end if;

 if type eq "S" and d eq 4 and q eq 2 then
   error "Sp(4,2) is not quasisimple";
 end if;

 if type eq "O" then
   if IsEven(d) then
     error "Degree must be odd for type \"O\"";
   end if;
   sign := 0;
 end if;

 if type eq "O+" or type eq "O-" then
   if IsOdd(d) then
     error "Degree must be even for type \"O+\" or \"O-\"";
   end if;
   if type eq "O+" then
     if d eq 4 then error "O^+(4,q) is not quasisimple"; end if;
     sign := 1;
   else sign := -1;
   end if;
   type := "O";
 end if;

 if Universe(classes) cmpne Integers() or not classes subset {1..9} then
   error "<classes> must be a subset of {1..9}";
 end if;
 if 9 in classes and d gt 12 then
   "*WARNING*: Aschbacher Class 9 subgroups are not returned for dimensions";
   "           greater than 12. List of subgroups will be incomplete.";
 end if;

 if normaliser or general and type eq "L" then
   general := true; normaliser := true;
   // avoids a few problems e.g. SL2 fixes symplectic form.
 end if;

 if #Factorisation(q) ne 1 then
   error "<q> must be a prime power";
 end if;

 qq := type eq "U" select q^2 else q; //makes life easier!
 z := PrimitiveElement(GF(qq));
 fac:=Factorisation(q);
 p:=fac[1][1]; e:=fac[1][2];
 ee := type eq "U" select 2*e else e;
 //Make matrix C form making conjugates of subgroups under GL/GU/GSp
 if type eq "L" then
   C := GLMinusSL(d, qq);
 elif type eq "U" then
   C := GUMinusSU(d,q);
 elif type eq "S" then
  C := NormSpMinusSp(d, qq);
 else
   CS := SOMinusOmega(d, qq, sign);
   if IsOdd(q) then
     CG := GOMinusSO(d, qq, sign);
     if IsEven(d) then
       CN := NormGOMinusGO(d, qq, sign);
     end if;
   end if;
 end if;
 asmax := [];

 c9lib := GetLibraryRoot() cat "/c9lattices/";

 for cl in classes do
   if cl eq 1 then
     if type eq "L" then
       if novelties then
         for i in [1 .. (d-1) div 2] do
           Append(~asmax,SLStabOfNSpaceMeetDual(d, q, i : general:=general));
           Append(~asmax,SLStabOfNSpaceMissDual(d, q, i : general:=general));
         end for;
       else
         lim := all select d-1 else d div 2;
         for i in [1..lim] do
           if general then Append(~asmax, GLStabOfNSpace(d, q, i));
           else Append(~asmax, SLStabOfNSpace(d, q, i));
           end if;
         end for;
       end if;
     elif type eq "S" then
        if d eq 4 and IsEven(q) and novelties then
          asmax cat:= [NoveltyReduct(q : normaliser:=normaliser)];
        elif not novelties then
          if d eq 4 and IsEven(q) and not all then
            Append(~asmax, PointStabSp(d, q :normaliser:=normaliser));
            //for d=4, q even, PointStabSp(d, q) and IsotropicStabSp(d, q, 2)
            //are conjugate under the graph automorphism
          else
            Append(~asmax, PointStabSp(d, q :normaliser:=normaliser));
            half:= d div 2;
            for i in [2..half] do
              Append(~asmax, IsotropicStabSp(d, q, i:normaliser:=normaliser));
            end for;
            for i in [2..half-1] do
              if IsEven(i) then
                Append(~asmax, SymplecticStab(d, q, i:normaliser:=normaliser));
              end if;
            end for;
          end if;
        end if;
     elif type eq "U" and not novelties then
       for i in [1.. d div 2] do
         Append(~asmax, IsotropKStab(d, q, i :
                         general:=general, normaliser:=normaliser) );
       end for;
       for i in [1.. (d-1) div 2] do
         Append(~asmax, NonisotropKStab(d, q, i :
                         general:=general, normaliser:=normaliser) );
       end for;
     elif type eq "O" then
       half := d div 2;
       if novelties then
         if d eq 3 and q in {7,9,11} then
           Append(~asmax,
               NonDegenStabOmega(d, q, sign, 2, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
           if q ne 11 then
             Append(~asmax, NonDegenStabOmega(d, q, sign, 2, -1 :
              special:=special, general:=general, normaliser:=normaliser) );
           end if;
         end if;
         if IsEven(d) then
           if sign eq 1 then
             Append(~asmax, IsotropicStabOmega(d, q, half-1, sign :
               special:=special, general:=general, normaliser:=normaliser) );
           end if;
           if q eq 3 then
             Append(~asmax, NonDegenStabOmega(d, q, sign, 2, 1 :
               special:=special, general:=general, normaliser:=normaliser) );
           end if;
         end if;
         if d eq 8 and sign eq 1 then
            Append(~asmax, KlLine4(q:
               special:=special, general:=general, normaliser:=normaliser) );
            S := KlLine7(q:
               special:=special, general:=general, normaliser:=normaliser);
            if all then
              if IsOdd(q) then asmax cat:= [S, S^CG];
              else asmax cat:= [S, S^CS];
              end if;
            else Append(~asmax, S);
            end if;
            S := KlLine15(q:
               special:=special, general:=general, normaliser:=normaliser);
            if all and IsOdd(q) then
               asmax cat:= [S, S^CS, S^CN, S^(CS*CN)];
            else Append(~asmax, S);
            end if;
            Append(~asmax, KlLine22(q:
               special:=special, general:=general, normaliser:=normaliser) );
            Append(~asmax, KlLine26(q:
               special:=special, general:=general, normaliser:=normaliser) );
         end if;
         continue;
       end if;
       for i in [1..half] do
         if (i eq half-1 and sign eq 1) or //KL <= P_{n/2}
            (i eq half and sign eq -1) then
           continue;
         end if;
         S := IsotropicStabOmega(d, q, i, sign :
              special:=special, general:=general, normaliser:=normaliser);
         Append(~asmax, S);
         if sign eq 1 and i eq half and all then //c=2
           if IsEven(q) then Append(~asmax, S^CS); 
           else Append(~asmax, S^CG);
           end if;
         end if;
       end for;
       if IsOdd(d) then
         for i in [2..d-1 by 2] do
           if i gt 2 or q gt 3 then
             if d gt 3 or q gt 11 then
               Append(~asmax, NonDegenStabOmega(d, q, sign, i, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
             end if;
           end if;
           if (d gt 3 or not q in {7,9}) and (d ne 5 or i ne 2 or q ne 3) then
             Append(~asmax, NonDegenStabOmega(d, q, sign, i, -1 :
              special:=special, general:=general, normaliser:=normaliser) );
           end if;
         end for;
       else //d even
         for i in [1..half] do
           if IsEven(i) then
             if sign eq 1 then
               if i ne half then //else in imprimitive group
                 if i gt 2 or q gt 3 then
                   Append(~asmax, NonDegenStabOmega(d, q, sign, i, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
                 end if;
                 if d ne 8 or i ne 2 or all then
                   //conj to IsotropicStabOmega(8, q, 4, 1) when d=8, i=2
                   //under graph automorphism
                   Append(~asmax, NonDegenStabOmega(d, q, sign, i, -1 :
              special:=special, general:=general, normaliser:=normaliser) );
                 end if;
               end if;
             else //sign = -1
               if i gt 2 or q gt 3 or (d eq 4 and q eq 2) then
                 Append(~asmax, NonDegenStabOmega(d, q, sign, i, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
               end if;
               if i ne half then
                 if d ne 6 or q ne 2 then
                   Append(~asmax, NonDegenStabOmega(d, q, sign, d-i, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
                 end if;
               end if;
             end if;
           else //i odd
             if IsOdd(q) and i ne half  then
               S := NonDegenStabOmega(d, q, sign, d-i, 0 :
              special:=special, general:=general, normaliser:=normaliser);
               Append(~asmax, S);
               if all then Append(~asmax, S^CN); end if;
             end if;
           end if;
         end for;
       end if;
       if IsEven(d) and IsEven(q) then
         Append(~asmax, NSPointStabOmega(d, q, sign :
                            special:=special, normaliser:=normaliser) );
       end if;
     end if;
   elif cl eq 2 then
     if type eq "L" then
        if novelties then
          if (d eq 2 and q in {7,9,11}) then
            Append(~asmax,ImprimsMeetSL(d, q, d : general:=general ));
          end if;
          if d eq 4 and q eq 3 then
            Append(~asmax,ImprimsMeetSL(d, q, 2 : general:=general ));
          end if;
          if d eq 4 and q eq 5 then
            Append(~asmax,ImprimsMeetSL(d, q, 4 : general:=general ));
          end if;
          continue;
        end if;
        divs := Divisors(d);
        Exclude(~divs,1);
        for t in divs do
          if (t eq d and q le 4) or (t eq d div 2 and q le 2) then
            continue; //not maximal - in C1 or C8 group - KL
            //For SL(3,3) - C2 group = C8 group
          end if;
          if (d eq 2 and q in {5,7,9,11}) or (d eq 3 and q in {2,4}) or
     (d eq 4 and t eq 2 and q eq 3) or (d eq 4 and t eq 4 and q eq 5) then
            continue; //small exceptions
          end if;
          Append(~asmax,ImprimsMeetSL(d, q, t : general:=general ));
        end for;
     elif type eq "S" then
        if d eq 4 and q mod 2 eq 0 then
          if novelties then
             S1, S2 := NoveltyImprims(q : normaliser:=normaliser);
             if q ne 4 then Append(~asmax, S1); end if;
             Append(~asmax, S2);
          else
             Append(~asmax,GetSympImprimsD4(q));
          end if;
        elif d eq 4 then
          if novelties then continue; end if;
          S1, S2:= GetSympImprimsD4(q);
          Append(~asmax, S1);
          if q eq 3 then continue; end if; //small exception
          Append(~asmax, S2);
        else 
          divs:= [x : x in Divisors(d) | x gt 1 and IsEven(d div x)];
          for n in divs do
            if q eq 2 and d div n eq 2 then //otherwise orthogonal (KL)
              continue;
            end if;
            Append(~asmax, GetWreathProd(d, q, n));
          end for;
          if IsOdd(q) then //Colva and KL have this - o.w. group is orthogonal
            Append(~asmax, GetStabOfHalf(d, q));
          end if;
        end if;
     elif type eq "U" then
        if novelties then
          if (d eq 4 and q eq 3)  then
            Append(~asmax, StandardUnitImps(d, q, 1 :
                         general:=general, normaliser:=normaliser) );
            Append(~asmax, UnitImpHalfDim(d, q));
          elif (d eq 6 and q eq 2) or (d eq 3 and q eq 5) then
            Append(~asmax, StandardUnitImps(d, q, 1 :
                         general:=general, normaliser:=normaliser) );
          end if;
          continue;
        end if;
        divs := Divisors(d);
        Exclude(~divs,1);
        for t in divs do
          if t eq d div 2 and q eq 2 then
            continue; //not maximal - in C2 group with t=d  - KL
          end if;
          if (d eq 3 and d eq t and q eq 5) or
             (d eq 4 and d eq t and q eq 3) or
             (d eq 6 and d eq t and q eq 2) then
            continue; //small exceptions
          end if;
          Append(~asmax, StandardUnitImps(d, q, d div t :
                         general:=general, normaliser:=normaliser) );
        end for;
        if d mod 2 eq 0 then
          if (d eq 4 and q le 3) then
            continue; //small exception
          end if;
          Append(~asmax, UnitImpHalfDim(d, q :
                         general:=general, normaliser:=normaliser) );
        end if;
     elif type eq "O" then
       if novelties then
         if sign eq (-1)^(d div 2) and q eq 3 then
           Append(~asmax, OrthImprim(d, q, sign, 2, -1 :
              special:=special, general:=general, normaliser:=normaliser) );
         elif sign eq 1 and q eq 5 then
           Append(~asmax, OrthImprim(d, q, sign, 2, 1 :
              special:=special, general:=general, normaliser:=normaliser) );
         end if;
         if sign eq 1 and d mod 4 eq 2 then
           Append(~asmax, OrthStabOfHalfTS(d, q :
              special:=special, general:=general, normaliser:=normaliser) );
         end if;
         if d eq 3 and p mod 5 in {1,4} and p mod 8 in {3,5} then
           Append(~asmax, OrthImprim(d, q, 0, 1, 0 :
              special:=special, general:=general, normaliser:=normaliser) );
         end if;
         if sign eq 1 and d eq 8 then
           if q eq 3 then
             S :=  OrthStabOfHalfTS(d, q :
              special:=special, general:=general, normaliser:=normaliser);
              if all then
                asmax cat:= [S, S^CG];
              else Append(~asmax, S);
              end if;
           end if;
           if IsOdd(q) and e eq 1 then
             if p mod 8 in {3,5} then
               S := OrthImprim(d, q, sign, 1, 0 :
                  special:=special, general:=general, normaliser:=normaliser);
               if all then
                 asmax cat:= [S, S^CN];
               else Append(~asmax, S);
               end if;
             end if;
             S := KlLine51(q:
               special:=special, general:=general, normaliser:=normaliser);
             if all then
               asmax cat:= [S, S^CS, S^CN, S^(CS*CN)];
             else Append(~asmax, S);
             end if;
           end if;
           Append(~asmax, KlLine61(q:
               special:=special, general:=general, normaliser:=normaliser) );
         end if;
         continue;
       end if;
       divs := Divisors(d);
       Exclude(~divs,1);
       for t in divs do
         k := d div t;
         if IsEven(k) then
           sign1 := 1;
           if sign eq sign1^t then
             if (k ne 2 or q gt 5) and (k ne 4 or q ne 2) then //KL
               Append(~asmax, OrthImprim(d, q, sign, k, sign1 :
              special:=special, general:=general, normaliser:=normaliser) );
             end if;
           end if;
           sign1 := -1;
           if sign eq sign1^t then
             if (k ne 2 or q ne 3) then //KL
               Append(~asmax, OrthImprim(d, q, sign, k, sign1 :
              special:=special, general:=general, normaliser:=normaliser) );
             end if;
           end if;
         else //k odd
           if IsEven(q) then continue; end if;
           if k eq 1 and (e ne 1 or
                     (d eq 3 and p mod 5 in {1,4} and p mod 8 in {3,5})) then
             continue;
           end if;
           if  q eq 3 and k eq 3 then continue; end if; //KL
           if IsEven(t) then
             ex := d mod 4 eq 2 and q mod 4 eq 3; //D non-square
             if (ex and sign eq -1) or (not ex and sign eq 1) then
               S := OrthImprim(d, q, sign, k, 0 :
                  special:=special, general:=general, normaliser:=normaliser);
               if not all then
                 Append(~asmax, S);
               elif k eq 1 then
                 if q mod 8 in {1,7} then //c=4
                   asmax cat:= [S, S^CS, S^CN, S^(CS*CN) ];
                 elif d ne 8 then //q =3,5 mod 8, c=2
                   //in O_8(2) when d=8
                   asmax cat:= [S, S^CN ];
                 end if;
               else
                 if IsEven(t) then
                   asmax cat:= [S, S^CN ];
                 else Append(~asmax, S);
                 end if;
               end if;
             end if;
           else //k, t odd
             S := OrthImprim(d, q, sign, k, 0 :
              special:=special, general:=general, normaliser:=normaliser);
             Append(~asmax, S );
             if all and k eq 1 and q mod 8 in {1,7} then //c=2
               Append(~asmax, S^CS );
             end if;
           end if;
         end if;
       end for;
       if IsEven(d) then
         if sign eq 1 and d mod 4 eq 0 and not (d eq 8 and q eq 3) then
                                                //reducible if d mod 4 eq 2
           S := OrthStabOfHalfTS(d, q :
            special:=special, general:=general, normaliser:=normaliser); //c=2
           Append(~asmax, S );
           if all then
             if IsEven(q) then Append(~asmax, S^CS );
             else Append(~asmax, S^CG );
             end if;
           end if;
         end if;
         if IsOdd(q) and d mod 4 eq 2 then
           if (q mod 4 eq 1 and sign eq -1) or (q mod 4 eq 3 and sign eq 1)
                                                                        then
             Append(~asmax, OrthStabOfHalfND(d, q :
              special:=special, general:=general, normaliser:=normaliser) );
           end if;
         end if;
       end if;
     end if;
   elif cl eq 3 then
     if type eq "L" then
        if novelties then
          if (d eq 2 and q in {7,9}) or (d eq 3 and q eq 4)
            then
              if general then Append(~asmax,GammaL(d, q, d));
              else Append(~asmax,GammaLMeetSL(d, q, d));
              end if;
          end if;
          continue;
        end if;
        primes := [ f[1]: f in Factorisation(d) ];
        if (d eq 2 and q in {7,9}) or (d eq 3 and q eq 4) then
          continue; //small exceptions
        end if;
        for s in primes do
          if general then Append(~asmax,GammaL(d, q, s));
          else Append(~asmax,GammaLMeetSL(d, q, s));
          end if;
        end for;
     elif type eq "S" then
        if d eq 4 and q mod 2 eq 0 and novelties then
            Append(~asmax,NoveltySemilin(q : normaliser:=normaliser));
        else
          if novelties then continue; end if;
          primes := [ f[1]: f in Factorisation(d) ];
          for s in primes do if IsEven(d div s) then
            Append(~asmax,GammaSp(d, q, s : normaliser:=normaliser) );
          end if; end for;
          if d eq 4 and q eq 3 then
            continue; //small exceptions
          end if;
          //KL has q odd here - o.w. group is orthogonal
          if IsOdd(q) then
            Append(~asmax,GammaUMeetSp(d, q : normaliser:=normaliser) );
          end if;
        end if;
     elif type eq "U" then
        if novelties then
          if (d eq 6 and q eq 2) or (d eq 3 and q eq 5) then
            Append(~asmax,GammaSU(d, q, 3 :
                           general:=general, normaliser:=normaliser) );
          end if;
          continue;
        end if;
        if (d eq 3 and q in {3,5}) or (d in {5,6} and q eq 2) then
          continue; //small exceptions
        end if;
        primes := [ f[1]: f in Factorisation(d) ];
        for s in primes do if s ne 2 then //s=2 doesn't give subgroup
          Append(~asmax,GammaSU(d, q, s :
                           general:=general, normaliser:=normaliser) );
        end if; end for;
     elif type eq "O" then
        if novelties then
          if d eq 4 and q eq 3 and sign eq -1 then
             Append(~asmax, GammaOdimEven(d, q, sign :
                  special:=special, general:=general, normaliser:=normaliser) );
          end if;
          continue;
        end if;
        primes := [ f[1]: f in Factorisation(d) ];
        for s in primes do
          dim := d div s;
          if dim le 2 and (d ne 4 or sign ne -1 or q eq 3) then
             continue;
          end if;
          if s eq 2 then
            if IsEven(dim) then
              if d ne 8 or sign ne 1 or all then
 //if d=8, sign=1, then GammaOdimEven(d, q, sign) and GammaUMeetOmega(d, q)
 //are conj to O-(4,q)wr2 and O-(2,q) x O-(6,q) under graph automorphism
                S := GammaOdimEven(d, q, sign :
                  special:=special, general:=general, normaliser:=normaliser);
                Append(~asmax, S );
                if all and sign eq 1 then //c=2
                  if IsEven(q) then Append(~asmax, S^CS );
                  else Append(~asmax, S^CG );
                  end if;
                end if;
                if sign eq 1 then
                  S := GammaUMeetOmega(d, q :
                  special:=special, general:=general, normaliser:=normaliser);
                  Append(~asmax, S );
                  if all then //c=2
                    if IsEven(q) then Append(~asmax, S^CS );
                    else Append(~asmax, S^CG );
                    end if;
                  end if;
                end if;
              end if;
            else
              if IsOdd(q) then //KL - qm odd r=2
                S := GammaOdimOdd(d, q, sign :
                  special:=special, general:=general, normaliser:=normaliser);
                Append(~asmax, S );
                if all then
                  if (sign eq 1 and q mod 4 eq 1) or
                     (sign eq -1 and q mod 4 eq 3) then //c=2
                     Append(~asmax, S^CG );
                  end if;
                end if;
              end if;
              if sign eq -1 then
                Append(~asmax, GammaUMeetOmega(d, q :
                 special:=special, general:=general, normaliser:=normaliser) );
              end if;
            end if;
          else
            Append(~asmax, GammaOsOdd(d, q, s, sign :
                 special:=special, general:=general, normaliser:=normaliser) );
          end if;          
        end for;
     end if;
   elif cl eq 4 then
     if type eq "L" then
       if novelties then continue; end if;
       //t = d div t contained in C7
       divs := [ t : t in Divisors(d) | t ne 1 and t lt d div t ]; 
       //KL excludes d1=q=2. in GL_{n/2}(4)
       if q eq 2 and Position(divs,2) gt 0 then 
         Remove(~divs,Position(divs,2));
       end if;
       if all then
         for t in divs do
           nconj := GCD( [q-1, t, d div t] );
           S := SLTensor(t, d div t, q : general:=general );
           asmax cat:= GConjugates(S,C,nconj);
         end for;
       else asmax cat:=
                  [ SLTensor(t, d div t, q : general:=general ): t in divs];
       end if;
     elif type eq "S" and IsOdd(q) then
       //q even doesn't seem to give a subgroup at all
       if novelties then continue; end if;
       divs := [ t : t in Divisors(d) | IsEven(t) and d div t gt 2]; 
       //KL excludes d2=q=3 imprimitive? always non maximal
       //KL excludes d2=2 - imprimitive or semilinear?
       if q eq 3 and d mod 3 eq 0 and Position(divs,d div 3) gt 0 then
         Remove(~divs,Position(divs,d div 3));
       end if;
       //always c=1
       for t in divs do
         if IsEven(d div t) then
           S1, S2 := SpTensors(t,d div t,q : normaliser:=normaliser );
           //for d=8 SO+(4,q)xSp(2,q) <= C7 group
           if d eq 8 then
             Append(~asmax,S2);
           else asmax cat:= [S1,S2]; end if;
         else Append(~asmax,SpTensors(t,d div t,q : normaliser:=normaliser ));
         end if;
       end for;
     elif type eq "U" then
       if novelties then continue; end if;
       //t = d div t contained in C7
       divs := [ t : t in Divisors(d) | t ne 1 and t lt d div t ]; 
       if q eq 2 and Position(divs,2) gt 0 then //KL- in C2 group 
         Remove(~divs,Position(divs,2));
       end if;
       if all then
         for t in divs do
           nconj := GCD( [q+1, t, d div t] );
           S := SUTensor(t, d div t, q :
                      general:=general, normaliser:=normaliser );
           asmax cat:= GConjugates(S,C,nconj);
         end for;
       else
         asmax cat:= [ SUTensor(t, d div t, q :
                      general:=general, normaliser:=normaliser ): t in divs];
       end if;
     elif type eq "O" then
       if novelties then
         if sign eq 1 and IsOdd(q) and d mod 4 eq 0 and d gt 8 then
           d1 := 4; d2 := d div 4;
           if IsOdd(d2) then
             if d2 ne 3 or q ne 3 then //KL
               Append(~asmax, OrthTensorEvenOdd(d1,d2,q,1 :
                  special:=special, general:=general, normaliser:=normaliser) );
             end if;
           else //c=2
             if q mod 4 eq 3 and d2 mod 4 eq 2 then
               S := OrthTensorEvenEven(d1,d2,q,1,1 :
                  special:=special, general:=general, normaliser:=normaliser);
             else
               S := OrthTensorEvenEven(d1,d2,q,1,-1 :
                  special:=special, general:=general, normaliser:=normaliser);
             end if;
             Append(~asmax, S);
             if all then Append(~asmax, S^CG); end if;
           end if;
         end if;
         continue;
       end if;
       divs := [ t : t in Divisors(d) | t ne 1 and t le d div t ]; 
       for t in divs do
         d1 := t; d2 := d div t;
         if sign eq 1 and IsEven(d1) and IsEven(d2) and d1 lt d2 then
           if q eq 2 and d1 eq 2 then //KL
             continue;
           end if;
           if d1 eq 2 and d2 eq 4 and (not all or IsEven(q)) then
//if d=8, OrthSpTensor(2, 4, q) conjugate to O(3,q)xO(5,q) under graph auto
//if q even OrthSpTensor(2, 4, q) <= irrecucible Sp(6,q)
             continue;
           end if;
           S := OrthSpTensor(d1, d2, q :
                  special:=special, general:=general, normaliser:=normaliser);
           if not all then
               Append(~asmax, S);
           elif IsOdd(q) and d mod 8 eq 0 then //c=4
               asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
           else //c=2
               if IsEven(q) then asmax cat:= [S, S^CS];
               else asmax cat:= [S, S^CG];
               end if;
           end if;
         end if;
         if IsEven(q) or d1 le 2 then
           continue;
         end if;
         if IsOdd(d1) and IsOdd(d2) and d1 lt d2 then
           if d1 eq 3 and q eq 3 then continue; end if; //KL
           Append(~asmax, OrthTensorOddOdd(d1,d2,q :
                  special:=special, general:=general, normaliser:=normaliser) );
         elif IsOdd(d1) and IsEven(d2) then
           if d1 eq 3 and q eq 3 then continue; end if; //KL
           if d2 eq 4 and sign eq 1 then continue; end if; //KL
           Append(~asmax, OrthTensorEvenOdd(d2,d1,q,sign :
                  special:=special, general:=general, normaliser:=normaliser) );
         elif IsEven(d1) and IsOdd(d2) then
           if d1 eq 4 and sign eq 1 then continue; end if; //KL
           Append(~asmax, OrthTensorEvenOdd(d1,d2,q,sign :
                  special:=special, general:=general, normaliser:=normaliser) );
         elif sign eq 1 then //d1, d2 even, sign always 1 
           if d1 lt d2 then
             S := OrthTensorEvenEven(d1,d2,q,-1,-1 :
            special:=special, general:=general, normaliser:=normaliser); //c=2
             Append(~asmax, S);
             if all then Append(~asmax, S^CG); end if;
             S := OrthTensorEvenEven(d1,d2,q,1,1 :
                  special:=special, general:=general, normaliser:=normaliser);
             if (q mod 4 eq 3 and (d1 mod 4 eq 2 or d2 mod 4 eq 2)) or
                  d mod 8 eq 4 then //c=2
               if d1 gt 4 then //KL
                 if all then asmax cat:= [S, S^CG];
                 else Append(~asmax, S);
                 end if;
               end if;
             else //c=4
               if all then asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
               else Append(~asmax, S);
               end if;
             end if;
           end if;
           S := OrthTensorEvenEven(d1,d2,q,1,-1 :
                  special:=special, general:=general, normaliser:=normaliser);
           if q mod 4 eq 3 and d1 mod 4 eq 0 and d2 mod 4 eq 2 then //c=4 
             if all then asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
             else Append(~asmax, S);
             end if;
           else //c=2
             if d1 gt 4 then //KL
               if all then asmax cat:= [S, S^CG];
               else Append(~asmax, S);
               end if;
             end if;
           end if;
           if d1 le d2 then
             S := OrthTensorEvenEven(d2,d1,q,1,-1 :
                  special:=special, general:=general, normaliser:=normaliser);
             if q mod 4 eq 3 and d2 mod 4 eq 0 and d1 mod 4 eq 2 then //c=4 
               if all then asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
               else Append(~asmax, S);
               end if;
             else //c=2
               if all then asmax cat:= [S, S^CG];
               else Append(~asmax, S);
               end if;
             end if;
           end if;
         end if; // d1/d2 odd/even
       end for; //t in divs
     end if;
   elif cl eq 5 then
     if novelties then continue; end if;
     face := Factorisation(ee); //recall q=p^e, ee=2e in type U, ee=e o.w.
     for pf in [f[1] : f in face] do
       f := e div pf;
       if type eq "L" then
         if d eq 2 and p eq 2 and f eq 1 then
           continue; //small exception
         end if;
         S := SubfieldSL(d, p, e, f : general:=general );
         if all then nconj := GCD(d, (q-1) div (p^f-1));
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       elif type eq "S" then
         S := SubfieldSp(d, p, e, f : normaliser:=normaliser );
         if all then nconj := GCD(2, (q-1) div (p^f-1));
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       elif type eq "U" then
         if pf ne 2 then //SU(d,q) is not a subgroup of SU(d,q^2)
            S := SubfieldSU(d, p, e, f
                                 : general:=general, normaliser:=normaliser);
            if all then nconj := GCD(d, (q+1) div (p^f+1));
              asmax cat:= GConjugates(S,C,nconj);
            else Append(~asmax,S);
            end if;
         end if;
         if pf eq 2 then
           if IsOdd(d) then
             if all then nconj := GCD(d,q+1); end if;
             if IsOdd(q) then //o.w. orthogonal group reducible!
               if d eq 3 and q le 5 then
                 continue; //small exceptions
               end if;
               S := OrthsInSU(d, q : general:=general, normaliser:=normaliser);
               if all then
                 asmax cat:= GConjugates(S,C,nconj);
               else Append(~asmax,S);
               end if;
             end if;
           else
             S1, S2 :=
                    OrthsInSU(d, q : general:=general, normaliser:=normaliser);
             if IsOdd(q) then //o.w. <= SpInSU(d, q)
               if all then nconj := GCD(d,q+1) div 2; end if;
               if d eq 4 and q eq 3 then //small exception - don't want S1
                 if all then 
                   asmax cat:= GConjugates(S2,C,nconj);
                 else asmax cat:= [S2];
                 end if;
               elif all then 
                 asmax cat:= GConjugates(S1,C,nconj);
                 asmax cat:= GConjugates(S2,C,nconj);
               else asmax cat:= [S1,S2];
               end if;
             end if;
             S := SpInSU(d, q : general:=general, normaliser:=normaliser);
             if all then
               nconj := GCD(d div 2,q+1);
               asmax cat:= GConjugates(S,C,nconj);
             else Append(~asmax,S);
             end if;
           end if; //if IsOdd(d)
         end if; //pf=2
       elif type eq "O" then
         if IsOdd(d) then
           S :=  SubfieldOdimOdd(d, p, e, f :
                  special:=special, general:=general, normaliser:=normaliser);
           if all and pf eq 2 then
             asmax cat:= [ S, S^CS ];
           else Append(~asmax,S);
           end if;
         else
           if pf eq 2 then
             if sign eq -1 then continue; end if;
             if p eq 2 then
               Append(~asmax, SubfieldOdimEven(d, p, e, f, 1 :
                  special:=special, general:=general, normaliser:=normaliser) );
               Append(~asmax, SubfieldOdimEven(d, p, e, f, -1 :
                  special:=special, general:=general, normaliser:=normaliser) );
             else
               S :=  SubfieldOdimEven(d, p, e, f, 1 :
                  special:=special, general:=general, normaliser:=normaliser);
               if not all then
                  Append(~asmax, S);
               elif (d mod 4 eq 2 and p^f mod 4 eq 1) then //c=2
                 asmax cat:= [ S, S^CN ];
               else //c=4
                 asmax cat:= [ S, S^CS, S^CN, S^(CS*CN) ];
               end if;
               S :=  SubfieldOdimEven(d, p, e, f, -1 :
                  special:=special, general:=general, normaliser:=normaliser);
               if not all then
                  Append(~asmax, S);
               elif d mod 4 eq 0 or (d mod 4 eq 2 and p^f mod 4 eq 3) then //c=2
                 asmax cat:= [ S, S^CN ];
               else //c=4
                 asmax cat:= [ S, S^CS, S^CN, S^(CS*CN) ];
               end if;
             end if; //p eq 2
           else //pf ne 2
             Append(~asmax, SubfieldOdimEven(d, p, e, f, sign :
                  special:=special, general:=general, normaliser:=normaliser) );
           end if; //pf=2
         end if;
       end if; //types
     end for;   // for pf in [f[1] : f in face] do
   elif cl eq 6 then
     fac := Factorisation(d);
     if #fac ne 1 then continue; end if;
     r:=fac[1][1];
     if (qq-1) mod r ne 0 then continue; end if;
     //Let R be the extraspecial or symplectic group normalised.
     //Then these groups are contained in C5 groups and hence not maximal
     //unless qq = p^ee, where ee is minimal subject to |Z(R)| divides qq-1. 
     //Note |Z(R)|= r for r odd and |Z(R)|=2 or 4 for r even.
     if IsOdd(r) and ee ne Order(GF(r)!p) then
       continue;
     end if;
     if type eq "L" then
       if (d eq 2 and q mod 40 in {11,19,21,29} and not novelties) or
          ((d ne 2 or not q mod 40 in {11,19,21,29}) and novelties) then
          continue; //small exceptions
       end if;
       if IsOdd(r) then
         //note that if minimal ee defined above is even, then the group
         //preserves a unitary form, so is not maximal
         if IsEven(ee) then continue; end if;
         S := NormaliserOfExtraSpecialGroup(d,qq : general:=general);
         if all then
           nconj := GCD(d,q-1);
           if d eq 3 and q mod 9 in {4,7} then
              nconj := 1;
           end if;
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       else
         //note that if minimal ee is not equal to 1, then the group
         //preserves a unitary form, so is not maximal
         if ee ne 1 then continue; end if;
         if (qq-1) mod 4 eq 0 and d gt 2 then
           S := NormaliserOfSymplecticGroup(d,qq : general:=general);
           if all then
             nconj := GCD(d,q-1);
             if d eq 4 and q mod 8 eq 5 then nconj := 2; end if;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax,S);
           end if;
         end if;
         if d eq 2 then //whole group if qq=3.
//In fact, we probably want this for larger d whenever q mod 4 eq 2.
           S := NormaliserOfExtraSpecialGroupMinus(d,qq : general:=general);
           if all and (qq mod 8 eq 1 or qq mod 8 eq 7) then
             nconj:=2;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax,S);
           end if;
         end if;
       end if;
     elif type eq "S" then
       if ee ne 1 then continue; end if;
       if novelties then continue; end if;
       if IsEven(d) and IsOdd(qq) then
         S := NormaliserOfExtraSpecialGroupMinus(d,qq :
                symplectic:=true, general:=general, normaliser:=normaliser);
         if all and (qq mod 8 eq 1 or qq mod 8 eq 7) then
           nconj:=2;
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       end if;
     elif type eq "U" then
       if (d eq 3 and q eq 5 and not novelties) or
          ((d ne 3 or q ne 5) and novelties) then
          continue; //small exception
       end if;
       if IsOdd(r) then
         S := NormaliserOfExtraSpecialGroup(d,qq :
                     unitary:=true, general:=general, normaliser:=normaliser);
         if all then
           nconj := GCD(d,q+1);
           if d eq 3 and q mod 9 in {2,5} then
              nconj := 1;
           end if;
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       elif IsEven(r) and p mod 4 eq 3 and ee eq 2 then
         S := NormaliserOfSymplecticGroup(d,qq :
                     unitary:=true, general:=general, normaliser:=normaliser);
         if all then
           nconj := GCD(d,q+1);
           if d eq 4 and q mod 8 eq 3 then nconj := 2; end if;
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax,S);
         end if;
       end if;
     elif type eq "O" then
       if sign eq 1 and r eq 2 and ee eq 1 then
         ex := d eq 8 and q mod 8 in {3,5};
         if (novelties and not ex) or (not novelties and ex) then
           continue;
         end if;
         S := NormaliserOfExtraSpecialGroup(d,q :
                                  orthogonal:=true, normaliser:=normaliser);
         if not all then
           Append(~asmax, S);
         elif q mod 8 in {3,5} then
           asmax cat:= [ S, S^CS, S^CG, S^(CS*CG) ];
         else
           asmax cat:= [ S, S^CS, S^CG, S^(CS*CG),
                         S^CN, S^(CS*CN), S^(CG*CN), S^(CS*CG*CN) ];
         end if;
       end if;
     end if;
   elif cl eq 7 then
     if novelties then continue; end if;
     t:=2;
     while 2^t le d do
       isp, m := IsPower(d,t);
       if isp then
         if type eq "L" then
           //KL excludes m=2 orthogonal?
           if m eq 2 then
             t +:= 1; continue;
           end if;
           S := SLTensorInd(m, t, q : general:=false );
           if all then nconj := GCD(q-1,m^(t-1));
             if (m mod 4 eq 2) and t eq 2 and (q mod 4 eq 3) then
                //in that case odd permutation from Sym(t) increases N_GL.
                nconj := nconj div 2;
             end if;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         elif type eq "S" and IsEven(m)  then
           //group not symplectic for t even, q odd
           //KL insist on tq odd and (m,q) ne (2,3).
           if IsEven(t) or IsEven(q)  or (m eq 2 and q eq 3) then
             t +:= 1; continue;
           end if;
           S := SpTensorInd(m,t,q : normaliser:=normaliser );
           //always one conjugate here - yes!
           Append(~asmax, S);
         elif type eq "U" then
           //KL exclude m=2 (subfield group) and (m,q) = (3,2).
           if m eq 2  or (m eq 3 and q eq 2) then
             t +:= 1; continue;
           end if;
           S := SUTensorInd(m,t,q : general:=general, normaliser:=normaliser );
           if all then nconj := GCD(q+1,m^(t-1));
             if (m mod 4 eq 2) and t eq 2 and (q mod 4 eq 1) then
                //in that case odd permutation from Sym(t) increases N_GL.
                nconj := nconj div 2;
             end if;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         elif type eq "O" then
           if sign eq -1 or (m le 3 and q le 3) then
             t +:= 1; continue;
           end if;
           if IsEven(q*t) and IsEven(m) and (IsOdd(q) or m gt 4) then
              //last condition KL Table 3.5.I
             S := OrthogSpTensorInd(m, t, q :
                  special:=special, general:=general, normaliser:=normaliser );
             if not all or (t eq 2 and m mod 4 eq 2) then
               Append(~asmax, S);
             elif IsEven(q) then //c=2
               asmax cat:= [ S, S^CS ];
             else //c=4
               asmax cat:= [ S, S^CS, S^CG, S^(CS*CG) ];
             end if;
           end if;
           if IsEven(m) and m gt 2 and IsOdd(q) then
             if t eq 2  and m mod 4 eq 2 then //c=1
               Append(~asmax, OrthogTensorInd(m, t, q, 1 :
                special:=special, general:=general, normaliser:=normaliser ) );
               Append(~asmax, OrthogTensorInd(m, t, q, -1:
                special:=special, general:=general, normaliser:=normaliser ) );
             else
               S := OrthogTensorInd(m, t, q, 1 :
                special:=special, general:=general, normaliser:=normaliser );
               if not all then
                 Append(~asmax, S);
               elif t eq 3 and m mod 4 eq 2 and q mod 4 eq 3 then //c=2
                 asmax cat:= [ S, S^CG ];
               else
                 asmax cat:= [ S, S^CS, S^CG, S^(CS*CG) ];
               end if;
               S := OrthogTensorInd(m, t, q, -1 :
                special:=special, general:=general, normaliser:=normaliser );
               if not all then
                 Append(~asmax, S);
               elif (t eq 3 and m mod 4 eq 2 and q mod 4 eq 1) or
                  (t eq 2 and m mod 4 eq 0) then //c=2
                 asmax cat:= [ S, S^CG ];
               else
                 asmax cat:= [ S, S^CS, S^CG, S^(CS*CG) ];
               end if;
             end if;
           end if;
           if IsOdd(m) and IsOdd(q) then
             Append(~asmax, OrthogTensorInd(m, t, q, 0  :
                special:=special, general:=general, normaliser:=normaliser) );
           end if;
         end if;
       end if;
       t +:= 1;
     end while;
   elif cl eq 8 then
     if novelties then continue; end if;
     if type eq "L" then
        if d eq 2 then
          //U(2,sqrt(q)) = L(2,sqrt(2)), subfield
          //Sp(2,q) = L(2,q)
          //O+(2,q) imprimitive, O-(2,q) semilinear
          continue;
        end if;
        fac:=Factorisation(q); p:=fac[1][1]; e:=fac[1][2];
        if IsEven(e) then
          rq := p^(e div 2);
          S := NormOfSU(d,rq : general:=general);
          if all then nconj := GCD(d,rq-1);
             asmax cat:= GConjugates(S,C,nconj);
          else Append(~asmax,S);
          end if;
        end if;
        if IsEven(d) then
          S := NormOfSp(d,q : general:=general);
          if all then nconj := GCD(q-1, d div 2);
             asmax cat:= GConjugates(S,C,nconj);
          else Append(~asmax,S);
          end if;
        end if;
        if IsOdd(q) then
          if IsOdd(d) then
            S := NormOfO(d,q,0 : general:=general);
            if all then nconj := GCD(q-1, d);
              asmax cat:= GConjugates(S,C,nconj);
            else Append(~asmax,S);
            end if;
          else
            if all then
              nconj := GCD(q-1, d) div 2;
            end if;
            S := NormOfO(d,q,1 : general:=general);
            if all then
              asmax cat:= GConjugates(S,C,nconj);
            else Append(~asmax,S);
            end if;
            S := NormOfO(d,q,-1 : general:=general);
            if all then
              asmax cat:= GConjugates(S,C,nconj);
            else Append(~asmax,S);
            end if;
          end if;
        end if;
     elif type eq "S" and IsEven(q) and (d ne 4 or all) then
       Z := GL(d,q)!ScalarMatrix(d, PrimitiveElement(GF(q)) );
       if general then
         Append(~asmax,sub< GL(d,q) | GOPlus(d,q), Z > );
       else
         Append(~asmax,SOPlus(d,q));
       end if;

       isit, form := SymplecticForm(GOMinus(d,q));
       assert isit;
       trans := GL(d,q)!CorrectForm(form,d,q,"symplectic");
       if general then
         Append(~asmax,sub< GL(d,q) | GOMinus(d,q)^trans, Z > );
       else
         Append(~asmax,SOMinus(d,q)^trans);
       end if;
     end if;
   elif cl eq 9 then
     if d eq 2 then //must have type "L"
       if novelties then continue; end if;
       if (e eq 1 and p mod 5 in {1,4}) or
                    (e eq 2 and p ne 2 and p mod 5 in {2,3}) then
          //2.A5
          _LRS := Read(c9lib cat "sl25d2");
          _LR := eval _LRS;
          S := ReduceOverFiniteField(_LR,qq:general:=general);
          if all then nconj := 2;
             asmax cat:= GConjugates(S[1],C,nconj);
          else Append(~asmax, S[1]);
          end if;
       end if;
     elif d eq 3 then
       if type eq "L" then
         if novelties then continue; end if;
         if (e eq 1 and p ne 2 and p mod 7 in {1,2,4}) then
           //L27
           _LRS := Read(c9lib cat "l27d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := GCD(p-1,3);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 3 eq 1 and p mod 5 in {1,4}) or
                    (e eq 2 and p ne 3 and p mod 5 in {2,3}) then
           //3.A6
           _LRS := Read(c9lib cat "3a6d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := 3;
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
       elif type eq "U" then
         if (novelties and q eq 5) or
            (not novelties and e eq 1 and p ne 5 and p mod 7 in {3,5,6}) then
           //L27
           _LRS := Read(c9lib cat "l27d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
           if all then nconj := GCD(p+1,3);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if novelties then continue; end if;
         if (e eq 1 and p mod 3 eq 2 and p mod 5 in {1,4}) then
           //3.A6
           _LRS := Read(c9lib cat "3a6d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
           if all then nconj := 3;
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 5 then
           //3.A7
           _LRS := Read(c9lib cat "3a7d21b");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
           S := [ s: s in S | Degree(s) eq 3 ];
           if all then nconj := 3;
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
           //3.M10
           _LRS := Read(c9lib cat "3a6d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
           if all then nconj := 3;
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
       elif type eq "O" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 5 in {1,4}) or
                    (e eq 2 and p ne 2 and p mod 5 in {2,3}) then
           //A5
           _LRS := Read(c9lib cat "a5d3");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
           if all then asmax cat:= [S[1], S[1]^CS];
           else Append(~asmax, S[1]);
           end if;
         end if;
       end if;
     elif d eq 4 then
       if type eq "L" then
         if (e eq 1 and p ne 2 and p mod 7 in {1,2,4}) then
           if novelties then
             //2.L27
             _LRS := Read(c9lib cat "sl27d4");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:general:=general);
             if all then nconj := GCD(q-1,4);
                asmax cat:= GConjugates(S[1],C,nconj);
             else Append(~asmax, S[1]);
             end if;
           else //2.A7
             _LRS := Read(c9lib cat "2a7d4");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:general:=general);
             if all then nconj := GCD(q-1,4);
                asmax cat:= GConjugates(S[1],C,nconj);
             else Append(~asmax, S[1]);
             end if;
           end if;
         end if;
         if novelties then continue; end if;
         if (e eq 1 and p mod 6 eq 1) then
           //2.U42
           _LRS := Read(c9lib cat "2u42d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := GCD(q-1,4);
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 2 then
           //A7
           _LRS := Read(c9lib cat "2a7d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           Append(~asmax, S[1]);
         end if;
       elif type eq "U" then
         if (e eq 1 and p mod 7 in {3,5,6}) then
           if novelties then
             if p ne 3 then //2.L27
               _LRS := Read(c9lib cat "sl27d4");
               _LR := eval _LRS;
               S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
               if all then nconj := GCD(q+1,4);
                  asmax cat:= GConjugates(S[1],C,nconj);
               else Append(~asmax, S[1]);
               end if;
             end if;
           else //2.A7
             _LRS := Read(c9lib cat "2a7d4");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
             if all then nconj := GCD(q+1,4);
                asmax cat:= GConjugates(S[1],C,nconj);
             else Append(~asmax, S[1]);
             end if;
           end if;
         end if;
         if novelties then continue; end if;
         if (e eq 1 and p mod 6 eq 5) then
           //2.U42
           _LRS := Read(c9lib cat "2u42d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := GCD(q+1,4);
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 3 then
           //4_2.L34
           _LRS := Read(c9lib cat "4bl34d20");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           S := [ s: s in S | Degree(s) eq 4 ];
           if all then nconj := 2;
              asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
       elif type eq "S" then
         if novelties then
           if q eq 7 then //2.L2q
             S := SymplecticSL2(4,q:normaliser:=normaliser);
             Append(~asmax, S);
           end if;
           continue;
         end if;
         if (e eq 1 and p ne 7 and p mod 12 in {1,5,7,11}) then
           //2.A6 (p mod 12 in {5,7}), 2.S6 (p mod 12 in {1,11})
           _LRS := Read(c9lib cat "2a6d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all and p mod 12 in {1,11} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 7 then
           //2.A7
           _LRS := Read(c9lib cat "2a7d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
         if p ge 5 and q gt 7 then
           //2.L2q
           S := SymplecticSL2(4,q:normaliser:=normaliser);
           Append(~asmax, S);
         end if;
         if p eq 2 and IsOdd(e) and e gt 1 then
            //Szq
            if normaliser then
              Append(~asmax, sub< GL(d,q) | Sz(q), ScalarMatrix(d,z) > );
            else Append(~asmax, Sz(q));
            end if;
         end if;
       elif type eq "O" then //must have sign -1
         if novelties then continue; end if;
         if e eq 1 and p ne 2 and p mod 5 in {2,3} then
           //A5
           _LRS := Read(c9lib cat "a5d4");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
           if all then asmax cat:= [S[1], S[1]^CS];
           else Append(~asmax, S[1]);
           end if;
         end if;
       end if;
     elif d eq 5 then
       if type eq "L" then
         if (novelties and q eq 3) or
      (not novelties and e eq 1 and p gt 3 and p mod 11 in {1,3,4,5,9}) then
           //L2_11
           _LRS := Read(c9lib cat "l211d5");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := GCD(q-1,5);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if novelties then continue; end if;
         if (e eq 1 and p mod 6 eq 1) then
           //U42
           _LRS := Read(c9lib cat "u42d5");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := GCD(q-1,5);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 3 then //M11
           _LRS := Read(c9lib cat "m11d11");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           Append(~asmax, S[1]);
           if all then
             Append(~asmax, ActionGroup(Dual(GModule(S[1]))));
           end if;
         end if;
       elif type eq "U" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 11 in {2,6,7,8,10}) then
           //L2_11
           _LRS := Read(c9lib cat "l211d5");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                               general:=general,normaliser:=normaliser);
           if all then nconj := GCD(q+1,5);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 6 eq 5) then
           //U42
           _LRS := Read(c9lib cat "u42d5");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                               general:=general,normaliser:=normaliser);
           if all then nconj := GCD(q+1,5);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
       elif type eq "O" then
         if novelties then
           if q eq 7 then //L2q
             S := OrthogSL2(d,q:
                     special:=special,general:=general,normaliser:=normaliser);
             Append(~asmax, S);
           end if;
           continue;
         end if;
         if (e eq 1 and p ne 7 and p mod 12 in {1,5,7,11}) then
           //A6 (p mod 12 in {5,7}) or S6 (p mod 12 in {1,11})
           _LRS := Read(c9lib cat "a6d5");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
           if all and p mod 12 in {1,11} then
             asmax cat:= [S[1], S[1]^CS];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 7 then //A7
           _LRS := Read(c9lib cat "a7d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
         if p ge 5 and q gt 7 then
           //L2q
           S := OrthogSL2(d,q:
                     special:=special,general:=general,normaliser:=normaliser);
           Append(~asmax, S);
         end if;
       end if;
     elif d eq 6 then
       if type eq "L" then
         if novelties then
           if (e eq 1 and p mod 24 in {7,13}) then
              //6.L3_4
             _LRS := Read(c9lib cat "6l34d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:general:=general);
             if all then nconj := 3;
               asmax cat:= GConjugates(S[1],C,nconj);
             else Append(~asmax, S[1]);
             end if;
           end if;
  	   if (e eq 1 and p mod 24 in {1,7}) or
                                    (e eq 2 and p mod 24 in {5,11,13,19}) then
  	     //6.A6
  	    _LRS := Read(c9lib cat "6a6d6");
  	    _LR := eval _LRS;
  	    S := ReduceOverFiniteField(_LR,qq:general:=general);
  	    if all then nconj := 6;
  	      asmax cat:= GConjugates(S[1],C,nconj);
  	    else Append(~asmax, S[1]);
            end if;
           end if;
  	   if (e eq 1 and p mod 24 in {1,7,13,19}) then
  	     //3.A6
  	    _LRS := Read(c9lib cat "3a6d6");
  	    _LR := eval _LRS;
  	    S := ReduceOverFiniteField(_LR,qq:general:=general);
  	    if all then nconj := p mod 24 in {1,19} select 6 else 3;
  	      asmax cat:= GConjugates(S[1],C,nconj);
  	    else Append(~asmax, S[1]);
            end if;
           end if;
           continue;
         end if;
         if (e eq 1 and p ne 3 and p mod 11 in {1,3,4,5,9}) then
           //2.L2_11 in 2.M12 for p=3
           _LRS := Read(c9lib cat "sl211d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := GCD(q-1,6);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         elif q eq 3 then //2.M12
           _LRS := Read(c9lib cat "2m12d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := 2;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 12 in {1,7}) then
            //6_1.U4_3 (p mod 12 =7) or 6_1.U4_3.2_2 (p mod 12 = 1)
           _LRS := Read(c9lib cat "6au43d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := p mod 12 eq 1 select 6 else 3;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 24 in {1,19}) then
            //6.L3_4.2_1
           _LRS := Read(c9lib cat "6l34d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:general:=general);
           if all then nconj := 6;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
	 if (e eq 1 and p mod 24 in {1,7}) or
                                  (e eq 2 and p mod 24 in {5,11,13,19}) then
	    //6.A7
	   _LRS := Read(c9lib cat "6a7d6");
	   _LR := eval _LRS;
	   S := ReduceOverFiniteField(_LR,qq:general:=general);
	   if all then nconj := 6;
	     asmax cat:= GConjugates(S[1],C,nconj);
	     asmax cat:= GConjugates(S[2],C,nconj);
	   else Append(~asmax, S[1]); Append(~asmax, S[2]);
           end if;
         end if;
         if IsOdd(q) then
           S := l3qdim6(q:general:=general);
           if all then nconj := 2;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
       elif type eq "U" then
         if novelties then
           if (e eq 1 and p mod 24 in {11,17}) then
              //6.L3_4
             _LRS := Read(c9lib cat "6l34d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
             if all then nconj := 3;
               asmax cat:= GConjugates(S[1],C,nconj);
             else Append(~asmax, S[1]);
             end if;
           end if;
  	   if (e eq 1 and p mod 24 in {17,23}) then
  	     //6.A6
  	    _LRS := Read(c9lib cat "6a6d6");
  	    _LR := eval _LRS;
  	    S := ReduceOverFiniteField(_LR,qq:
                                  general:=general, normaliser:=normaliser);
  	    if all then nconj := 6;
  	      asmax cat:= GConjugates(S[1],C,nconj);
  	    else Append(~asmax, S[1]);
            end if;
           end if;
  	   if (e eq 1 and p mod 24 in {5,11,17,23} and p ne 5) then
  	     //3.A6
  	    _LRS := Read(c9lib cat "3a6d6");
  	    _LR := eval _LRS;
  	    S := ReduceOverFiniteField(_LR,qq:
                                  general:=general, normaliser:=normaliser);
  	    if all then nconj := p mod 24 in {5,23} select 6 else 3;
  	      asmax cat:= GConjugates(S[1],C,nconj);
  	    else Append(~asmax, S[1]);
            end if;
           end if;
           continue;
         end if;
         if (e eq 1 and p ne 2 and p mod 11 in {2,6,7,8,10}) then
           //2.L2_11 in 3.M22 for p=2
           _LRS := Read(c9lib cat "sl211d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := GCD(q+1,6);
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         elif q eq 2 then
           //3.M22
           _LRS := Read(c9lib cat "3m22d21");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := 3;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
           //3.U4_3.2_2
           _LRS := Read(c9lib cat "6au43d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := 3;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 12 in {5,11}) then
            //6_1.U4_3 (p mod 12 =5) or 6_1.U4_3.2_2 (p mod 12 = 11)
           _LRS := Read(c9lib cat "6au43d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := p mod 12 eq 11 select 6 else 3;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 24 in {5,23}) then
            //6.L3_4.2_1
           _LRS := Read(c9lib cat "6l34d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
           if all then nconj := 6;
             asmax cat:= GConjugates(S[1],C,nconj);
           else Append(~asmax, S[1]);
           end if;
         end if;
	 if (e eq 1 and p mod 24 in {17,23}) then
	    //6.A7
	   _LRS := Read(c9lib cat "6a7d6");
	   _LR := eval _LRS;
	   S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
	   if all then nconj := 6;
	     asmax cat:= GConjugates(S[1],C,nconj);
	     asmax cat:= GConjugates(S[2],C,nconj);
	   else Append(~asmax, S[1]); Append(~asmax, S[2]);
           end if;
         end if;
         if IsOdd(q) then
           S := u3qdim6(q:general:=general, normaliser:=normaliser);
           if all then nconj := 2;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
       elif type eq "S" then
         if novelties then
           if e eq 1 and p mod 8 in {3,5} and p mod 5 in {1,4} then
              //2.A5
             _LRS := Read(c9lib cat "sl25d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
             Append(~asmax, S[1]);
           end if;
           if q eq 9 then //2.L_2(7)
             _LRS := Read(c9lib cat "sl27d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
             if all then asmax cat:= [S[1], S[1]^C];
             else Append(~asmax, S[1]);
             end if;
           end if;
           if e eq 1 and p mod 60 in {19,29,31,41} then
              //2 x U_3(3)
             _LRS := Read(c9lib cat "u33d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
             Append(~asmax, S[1]);
           end if;
           continue;
         end if;
         if e eq 1 and (p mod 8 in {1,7} or
                          (p mod 8 in {3,5} and p mod 5 in {2,3}) ) then
           //2.S5 (p mod 8 in {1,7}) of 2.A5 o.w. 
           _LRS := Read(c9lib cat "sl25d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all and p mod 8 in {1,7} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 16 in {1,15}) or
            (e eq 1 and p mod 16 in {7,9} and p ne 7) or
            (e eq 2 and p mod 16 in {3,5,11,13} and p ne 3) then
           //2.L2_7.2 (e eq 1 and p mod 16 in {1,15}) or 2.L2_7 o.w.
           _LRS := Read(c9lib cat "sl27d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all and p mod 16 in {1,15} then
              asmax cat:= [S[1], S[1]^C, S[2], S[2]^C];
           else Append(~asmax, S[1]); Append(~asmax, S[2]);
           end if;
         end if;
         if (e eq 1 and p mod 13 in {1,3,4,9,10,12}) or
            (e eq 2 and p mod 13 in {2,5,6,7,8,11} and p ne 2) then
            //2.L2_13
           _LRS := Read(c9lib cat "sl213d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if e eq 1 and
          (p mod 12 in {1,11} or (p mod 12 in {5,7} and p mod 5 in {2,3})) then
           //U33.2 (p mod 12 in {1,11}) or U33 o.w.)
           _LRS := Read(c9lib cat "u33d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all and p mod 12 in {1,11} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 5 in {0,1,4}) or
            (e eq 2 and p mod 5 in {2,3} and p ne 2) then 
         //2.J2
           _LRS := Read(c9lib cat "2j2d6");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq:normaliser:=normaliser);
           if all and p ne 5 then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 9 then //2.A7
           _LRS := Read(c9lib cat "2a7d6f9");
           S := eval _LRS;
           asmax cat:= [S, S^C];
         end if;
         if p ge 7 then
           //2.L2q
           S := SymplecticSL2(6,q:normaliser:=normaliser);
           Append(~asmax, S);
         end if;
         if p eq 2 then //G2q
           C := Constituents(GModule(G2(q)));
           A := ActionGroup([c: c in C | Dimension(c) eq 6][1]);
           A := A^TransformForm(A);
           if normaliser then
             A := sub<GL(d,q) | A, ScalarMatrix(d,z) >;
           end if;
           Append(~asmax, A );
         end if;
       elif type eq "O" then
         if novelties then
           if e eq 1 and
              ( (sign eq 1 and p mod  7 in {1,2,4}) or
               (sign eq -1 and p mod  7 in {3,5,6}) ) then //L_2(7) 
             _LRS := Read(c9lib cat "l27d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
             if all and q mod 4 eq 1 then
                if sign eq -1 then asmax cat:= [S[1], S[1]^CN];
                else asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
                end if;
             elif all and q mod 4 eq 3 then
                if sign eq 1 then asmax cat:= [S[1], S[1]^CN];
                else asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
                end if;
             else Append(~asmax, S[1]);
             end if;
           end if;
           continue;
         end if;
         if sign eq 1 then
           if e eq 1 and p mod 7 in {1,2,4} then
           //A7
             _LRS := Read(c9lib cat "a7d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
             if all and q mod 4 eq 1 then
                asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
             elif all and q mod 4 eq 3 then
                asmax cat:= [S[1], S[1]^CN];
             else Append(~asmax, S[1]);
             end if;
           end if;
           if e eq 1 and p mod 6 eq 1 then
           //U42
             _LRS := Read(c9lib cat "u42d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
             if all and q mod 4 eq 1 then
                asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
             elif all and q mod 4 eq 3 then
                asmax cat:= [S[1], S[1]^CN];
             else Append(~asmax, S[1]);
             end if;
           end if;
         elif sign eq -1 then
           if e eq 1 and p mod 7 in {3,5,6} then
           //A7
             _LRS := Read(c9lib cat "a7d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
             if all and q mod 4 eq 3 then
                asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
             elif all and q mod 4 eq 1 then
                asmax cat:= [S[1], S[1]^CN];
             else Append(~asmax, S[1]);
             end if;
           end if;
           if e eq 1 and p mod 6 eq 5 then
           //U42
             _LRS := Read(c9lib cat "u42d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
             if all and q mod 4 eq 3 then
                asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
             elif all and q mod 4 eq 1 then
                asmax cat:= [S[1], S[1]^CN];
             else Append(~asmax, S[1]);
             end if;
           end if;
           if q eq 3 then //2.L34
             _LRS := Read(c9lib cat "6l34d6");
             _LR := eval _LRS;
             S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
             if all then asmax cat:= [S[1], S[1]^CG];
             else Append(~asmax, S[1]);
             end if;
           end if;
         end if;
       end if;
     elif d eq 7 then
       if novelties then continue; end if;
       if type eq "L" then
         if e eq 1 and p mod 4 eq 1 then //U33
            _LRS := Read(c9lib cat "u33d7b");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj := GCD(q-1,7);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
       elif type eq "U" then
         if e eq 1 and p mod 4 eq 3 and p ne 3 then //U33
            _LRS := Read(c9lib cat "u33d7b");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                    general:=general,normaliser:=normaliser);
            if all then nconj := GCD(q+1,7);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
       elif type eq "O" then
         if e eq 1 then //Sp62
            _LRS := Read(c9lib cat "s62d7");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 3 then //S9
            _LRS := Read(c9lib cat "a9d8");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         S := G2(q);
         S := S^TransformForm(S);
         if normaliser then S := sub<GL(d,q) | S, ScalarMatrix(d,z) >;
         elif general then S := sub<GL(d,q) | S, ScalarMatrix(d,-1) >;
         end if;
         if all then asmax cat:= [S, S^CS];
         else Append(~asmax, S);
         end if;
       end if;
     elif d eq 8 then
       if type eq "L" then
        if novelties then continue; end if;
        if (e eq 1 and p mod 20  in {1,9}) or
           (e eq 2 and p mod 20  in {3,7,13,17}) then
           //4_1.L3_4 if q!=1 mod 16 or 4_1.L34.2_3 if q=1 mod 16
            _LRS := Read(c9lib cat "4al34d8");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj := q mod 16 eq 1 select 8 else GCD(q-1,8) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
         if p eq 5 then //4_1.L3_4 once
             _LRS := Read(c9lib cat "4al34d8");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj := 2;
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
       elif type eq "U" then
        if novelties then continue; end if;
        if (e eq 1 and p mod 20  in {11,19}) then
           //4_1.L3_4 if q!=-1 mod 16 or 4_1.L34.2_3 if q=-1 mod 16
            _LRS := Read(c9lib cat "4al34d8");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                  general:=general, normaliser:=normaliser);
            if all then nconj := q mod 16 eq -1 select 8 else GCD(q+1,8) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
       elif type eq "S" then
         if novelties then continue; end if;
         if e eq 1 and p mod 12 in {1,5,7,11} and p ne 7 then
           //2.L27 if p mod 12 in {5,7}, 2.L27.2 if p mod 12 in {1,11} 
                      _LRS := Read(c9lib cat "sl27d8");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 12 in {1,11} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 20 in {1,9,11,19}) or
            (e eq 2 and p mod 5 in {2,3} and p ne 3) then
           //2.A6.2_2  if p mod 20 in {1,19}, 2.A6 o.w.
           _LRS := Read(c9lib cat "2a6d8");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 20 in {1,19} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 17 in {1,2,4,8,9,13,15,16}) or
            (e eq 2 and p mod 17 in {3,5,6,7,10,11,12,14}) then
           //2.L2_17
           _LRS := Read(c9lib cat "sl217d8");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p ne 2 then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 2 then //S10
           _LRS := Read(c9lib cat "a10d9");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
         if p ge 11 then
           //2.L2q
           S := SymplecticSL2(8,q:normaliser:=normaliser);
           Append(~asmax, S);
         end if;
         if IsOdd(q) then
           Append(~asmax, l2q3dim8(q:normaliser:=normaliser) );
         end if;
       elif type eq "O" then
         if sign eq 1 then
           if novelties then
             continue;
           end if;
           if e eq 1 and p ge 3 then //2.Omega+(8,2)
             _LRS := Read(c9lib cat "2o8+2d8");
             _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                   special:=special, general:=general, normaliser:=normaliser);
              if all then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              else Append(~asmax, S[1]);
              end if;
           end if;
           if q eq 2 then //A9 x3 (all fused under triality)
             _LRS := Read(c9lib cat "a9d8");
             _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                   special:=special, general:=general, normaliser:=normaliser);
              Append(~asmax, S[1]);
             _LRS := Read(c9lib cat "2a9d8");
             _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                   special:=special, general:=general, normaliser:=normaliser);
              if all then asmax cat:= [S[1], S[1]^CS];
              else Append(~asmax, S[1]);
              end if;
           end if;
           if q eq 5 then
             //A10, 2.A10 (all fused under triality)
             _LRS := Read(c9lib cat "a10d9");
             _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
          special:=special, general:=general, normaliser:=normaliser);
              if all then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              else Append(~asmax, S[1]);
              end if;
              _LRS := Read(c9lib cat "2a10d16");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
          special:=special, general:=general, normaliser:=normaliser);
              if all then
                  asmax cat:= [S[1], S[1]^CS, S[1]^CG, S[1]^(CS*CG),
                      S[1]^CN, S[1]^(CS*CN), S[1]^(CG*CN), S[1]^(CS*CG*CN)];
              else Append(~asmax, S[1]);
              end if;
             //2Sz8
             _LRS := Read(c9lib cat "2sz8d8f5");
             S := eval _LRS;
             if normaliser then S := sub<GL(8,5) | S, ScalarMatrix(8,z) >;
             end if;
             if all then
                 asmax cat:= [S, S^CS, S^CG, S^(CS*CG),
                      S^CN, S^(CS*CN), S^(CG*CN), S^(CS*CG*CN)];
             else Append(~asmax,S);
             end if;
           end if;
           if q ne 2 and p ne 3 then //PSL(3,q).3 or PSU(3,q).3
             S := q mod 3 eq 1 select l3qdim8(q:
               special:=special, general:=general, normaliser:=normaliser)
                                 else u3qdim8(q:
               special:=special, general:=general, normaliser:=normaliser);
             if all and IsOdd(q) then
                 asmax cat:= [S, S^CS, S^CN, S^(CS*CN)];
             else Append(~asmax,S);
             end if;
           end if;
           if e mod 3 eq 0 then
             S :=sub< GL(d,q) | ChevalleyGroup("3D",4,GF(q)),ScalarMatrix(8,-1) >;
             S:=S^TransformForm(S);
             if all then
               if p eq 2 then
                 asmax cat:= [S, S^CS];
               else
                 asmax cat:= [S, S^CS, S^CG, S^(CS*CG),
                      S^CN, S^(CS*CN), S^(CG*CN), S^(CS*CG*CN)];
               end if;
             else Append(~asmax,S);
             end if;
           end if;
           //2.O(7,q)
           S := normaliser and p ne 2 select TwoO72(q) else TwoO7(q);
           if normaliser and p eq 2 then
              S := sub< GL(8,q) | S, ScalarMatrix(8,z) >;
           end if;
           if all then
             if p eq 2 then
               asmax cat:= [S, S^CS];
             else
               asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
             end if;
           else Append(~asmax,S);
           end if;
           if IsEven(e) then //2.O^-(8,q^(1/2))
             S := normaliser and p ne 2 select TwoOminus82(p^(e div 2))
                                          else TwoOminus8(p^(e div 2));
             if normaliser and p eq 2 then
                S := sub< GL(8,q) | S, ScalarMatrix(8,z) >;
             end if;
             if all then
               if p eq 2 then
                 asmax cat:= [S, S^CS];
               else
                 asmax cat:= [S, S^CS, S^CG, S^(CS*CG)];
               end if;
             else Append(~asmax,S);
             end if;
           end if;
         elif sign eq -1 then
           if novelties then continue; end if;
           if p ne 3 then //PSL(3,q).3 or PSU(3,q).3
             S := q mod 3 eq 2 select l3qdim8(q:
             special:=special, general:=general, normaliser:=normaliser)
                               else u3qdim8(q:
             special:=special, general:=general, normaliser:=normaliser);
             if all and IsOdd(q) then
               asmax cat:= [S, S^CN];
             else Append(~asmax,S);
             end if;
           end if;
         end if; //signs for O8
       end if; //types for d=8
     elif d eq 9 then
       if type eq "L" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 19  in {1,4,5,6,7,9,11,16,17}) then
           //L2_19
            _LRS := Read(c9lib cat "l219d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,9);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if (e eq 1 and p mod 3 eq 1 and p mod 5 in {2,3}) then
           //3.A6.2_3
            _LRS := Read(c9lib cat "3a6d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,9);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 7 then //3.A7
            _LRS := Read(c9lib cat "3a7d15b");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            S := [s: s in S | Degree(s) eq 9];
            if all then nconj :=  3;
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         //(3.)L3_q^2(.3).2
         S := l3q2dim9l(q: general:=general);
         if all then nconj :=  GCD(q-1,3);
              asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax, S);
         end if;
       elif type eq "U" then
         if novelties then
           if q eq 2 then
             //L2_19
              _LRS := Read(c9lib cat "l219d9");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                                     general:=general, normaliser:=normaliser);
              if all then nconj :=  GCD(q+1,9);
                asmax cat:= GConjugates(S[1],C,nconj);
              else Append(~asmax, S[1]);
              end if;
           end if;
           continue;
         end if;
         if (e eq 1 and p mod 19  in {2,3,8,10,12,13,14,15,18}) and p ne 2 then
           //L2_19
            _LRS := Read(c9lib cat "l219d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,9);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if (e eq 1 and p mod 3 eq 2 and p mod 5 in {2,3} and p gt 2) then
           //3.A6.2_3
            _LRS := Read(c9lib cat "3a6d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q+1,9);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 2 then //3J3
           _LRS := Read(c9lib cat "3j3d9f4");
           S := eval _LRS;
           if normaliser then S := sub<GL(9,4) | S, ScalarMatrix(9,z) >;
           end if;
           if all then nconj := 3;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax,S);
           end if;
         end if;
         //(3.)L3_q^2(.3).2
         S := l3q2dim9u(q: general:=general, normaliser:=normaliser);
         if all then nconj :=  GCD(q+1,3);
              asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax, S);
         end if;
       elif type eq "O" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 7 in {1,6} ) or
           (e eq 3 and p mod 7 in {2,3,4,5}) then
            _LRS := Read(c9lib cat "l28d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if (e eq 1 and p mod 17 in {1,2,4,8,9,13,15,16} ) or
           (e eq 2 and p mod 17 in {3,5,6,7,10,11,12,14}) then
            _LRS := Read(c9lib cat "l217d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p ne 11 and p mod 5 ne 0 then
           //A10 (p mod 5 = 1,4) or A10.2 o.w.
           _LRS := Read(c9lib cat "a10d9");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 5 in {1,4} then
               asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 11 then //A11.2
            _LRS := Read(c9lib cat "a11d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if p ge 11 then
           //L2q
           S := OrthogSL2(d,q:
                   special:=special,general:=general,normaliser:=normaliser);
           if all then asmax cat:= [S, S^CS];
           else Append(~asmax, S);
           end if;
         end if;
         if q ne 3 then
           //L2q^2
           S := l2q2dim9(q:
                 special:=special,general:=general,normaliser:=normaliser);
           Append(~asmax, S);
         end if;
       end if;
     elif d eq 10 then
        if type eq "L" then
         if novelties then
          if e eq 1 and p ne 2 and p mod 28 in {1,2,9,11,15,23,25} then
           //2.l34 (p=11,15,23 mod 28) or 2.l34.2 o.w.
                      _LRS := Read(c9lib cat "2l34d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq: general:=general);
            if all then nconj := p mod 28 in {1,9,25} select GCD(q-1,10)
                                                       else GCD(q-1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              //asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); //Append(~asmax, S[2]);
            end if;
          end if;
          continue;
         end if;
         if (e eq 1 and p mod 19  in {1,4,5,6,7,9,11,16,17}) then
           //SL2_19
            _LRS := Read(c9lib cat "sl219d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,10);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 8 in {1,3} then
           //2.M12 (p=3 mod 8) or 2.M12.2 (p=1 mod 8)
                      _LRS := Read(c9lib cat "2m12d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=
                 p mod 8 eq 1 select GCD(q-1,10) else GCD(q-1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
         if e eq 1 and p mod 28 in {1,2,9,11,15,23,25} then
           //2.M22 (p=11,15,23 mod 28) or 2.M22.2 o.w.
                      _LRS := Read(c9lib cat "2m22d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq: general:=general);
            if all then nconj := p mod 28 in {1,2,9,25} select GCD(q-1,10)
                                                       else GCD(q-1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
         if p ge 5 then
           S := l3qdim10(q:general:=general);
           if all then nconj := GCD(q-1,d);
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
         if p ge 3 then
           S := l4qdim10(q:general:=general);
           if all then nconj := GCD(q-1,5);
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
         S := l5qdim10(q:general:=general);
         if all then nconj := GCD(q-1,2);
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax, S);
         end if;
       elif type eq "U" then
        if novelties then
         if e eq 1 and p mod 28 in {3,5,13,17,19,27} and p ne 3 then
           //2.L34 (p=5,13,17 mod 28) or 2.L34.2 o.w.
                      _LRS := Read(c9lib cat "2l34d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
            if all then nconj := p mod 28 in {3,19,27} select GCD(q+1,10)
                                                        else GCD(q+1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              //asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); //Append(~asmax, S[2]);
            end if;
         end if;
         continue;
        end if;
        if (e eq 1 and p mod 19 in {2,3,8,10,12,13,14,15,18} and not p eq 2)
                                                                         then
           //SL2_19
            _LRS := Read(c9lib cat "sl219d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,10);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 8 in {5,7} then
           //2.M12 (p=5 mod 8) or 2.M12.2 (p=7 mod 8)
                      _LRS := Read(c9lib cat "2m12d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
            if all then nconj :=
                 p mod 8 eq 7 select GCD(q+1,10) else GCD(q+1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
         if e eq 1 and p mod 28 in {3,5,13,17,19,27} then
           //2.M22 (p=5,13,17 mod 28) or 2.M22.2 o.w.
                      _LRS := Read(c9lib cat "2m22d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general, normaliser:=normaliser);
            if all then nconj := p mod 28 in {3,19,27} select GCD(q+1,10)
                                                        else GCD(q+1,10) div 2;
              asmax cat:= GConjugates(S[1],C,nconj);
              asmax cat:= GConjugates(S[2],C,nconj);
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
         end if;
         if p ge 5 then
           S := u3qdim10(q:general:=general, normaliser:=normaliser);
           if all then nconj := GCD(q+1,d);
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
         if p ge 3 then
           S := u4qdim10(q:general:=general, normaliser:=normaliser);
           if all then nconj := GCD(q+1,5);
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax, S);
           end if;
         end if;
         S := u5qdim10(q:general:=general, normaliser:=normaliser);
         if all then nconj := GCD(q+1,2);
           asmax cat:= GConjugates(S,C,nconj);
         else Append(~asmax, S);
         end if;
       elif type eq "S" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 16 in {1,7,9,15}) or
            (e eq 2 and p mod 16 in {3,5,11,13} and p ne 3) then
           //2.A6.2_2 if p mod 16 in {1,15}, 2.A6 o.w.
           _LRS := Read(c9lib cat "2a6d10");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 16 in {1,15} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 8 in {1,3,5,7} and p ne 11) then
           //2.L2_11.2 if p mod 8 in {1,7}, 2.L2_11 o.w.
           _LRS := Read(c9lib cat "sl211d10a");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 8 in {1,7} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if (e eq 1 and p mod 24 in {1,11,13,23} and p ne 11) or
            (e eq 2 and p mod 24 in {5,7,17,19}) then
           //2.L2_11 if p mod 23 in {11,13}, 2.L2_11.2 o.w.
           _LRS := Read(c9lib cat "sl211d10b");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 24 in {1,5,7,17,19,23} then
              asmax cat:= [S[1], S[1]^C];
              asmax cat:= [S[2], S[2]^C];
           else Append(~asmax, S[1]); Append(~asmax, S[2]);
           end if;
         end if;
         if (e eq 1 and p mod 8 in {1,3,5,7}) then
           //U52.2 if p mod 8 in {1,7}, U52 o.w.
           _LRS := Read(c9lib cat "u52d10");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 8 in {1,7} then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if p ge 11 then
           //2.L2q
           S := SymplecticSL2(10,q:normaliser:=normaliser);
           Append(~asmax, S);
         end if;
       elif type eq "O" then
         if sign eq 1 then
          if novelties then
            if e eq 1 and p mod 12 in {1,5} then //A6
             _LRS := Read(c9lib cat "a6d10");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 12 eq 1 then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              elif all and p mod 12 eq 5 then
                 asmax cat:= [S[1], S[1]^CN];
              else Append(~asmax, S[1]);
              end if;
            end if;
            if e eq 1 and p mod 11 in {1,3,4,5,9} and p ne 3 then //L211b
             _LRS := Read(c9lib cat "l211d10b");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 4 eq 1 then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              elif all and p mod 4 eq 3 then
                 asmax cat:= [S[1], S[1]^CN];
              else Append(~asmax, S[1]);
              end if;
            end if;
            continue;
          end if;
          if e eq 1 and p mod 11 in {1,3,4,5,9} and p ne 3 then
           //L2_11a
           _LRS := Read(c9lib cat "l211d10a");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 4 eq 1 then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            elif all and p mod 4 eq 3 then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if e eq 1 and p mod 11 in {1,3,4,5,9} and p ne 3 then
           //A11
           _LRS := Read(c9lib cat "a11d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 4 eq 1 then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            elif all and p mod 4 eq 3 then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if q eq 3 then //A12
            _LRS := Read(c9lib cat "a12d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if q mod 4 eq 1 then //Sp4q
            S := sp4qdim10(qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S, S^CG, S^CN, S^(CG*CN)];
            else Append(~asmax, S);
            end if;
          end if;
         elif sign eq -1 then
          if novelties then
            if e eq 1 and p mod 12 in {7,11} then //A6
              _LRS := Read(c9lib cat "a6d10");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                      special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 12 eq 11 then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              elif all and p mod 12 eq 7 then
                 asmax cat:= [S[1], S[1]^CN];
              else Append(~asmax, S[1]);
              end if;
            end if;
            if e eq 1 and p mod 11 in {2,6,7,8,10} then //L211b
              _LRS := Read(c9lib cat "l211d10b");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                      special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 4 eq 3 then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
              elif all and p mod 4 eq 1 then
                 asmax cat:= [S[1], S[1]^CN];
              else Append(~asmax, S[1]);
              end if;
            end if;
            if q eq 2 then //M12
              _LRS := Read(c9lib cat "m12d11");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                      special:=special,general:=general,normaliser:=normaliser);
              Append(~asmax, S[1]);
            end if;
            if q eq 7 then //2L34d10
              _LRS := Read(c9lib cat "2l34d10");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                      special:=special,general:=general,normaliser:=normaliser);
              if all then
                 asmax cat:= [S[1], S[1]^CN];
              else Append(~asmax, S[1]);
              end if;
            end if;
            continue;
          end if;
          if e eq 1 and p mod 11 in {2,6,7,8,10} and p ne 2 then
           //L2_11
           _LRS := Read(c9lib cat "l211d10a");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 4 eq 3 then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            elif all and p mod 4 eq 1 then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if e eq 1 and p mod 11 in {2,6,7,8,10} and p ne 2 then
           //A11
           _LRS := Read(c9lib cat "a11d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 4 eq 3 then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            elif all and p mod 4 eq 1 then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if q eq 2 then //A12
            _LRS := Read(c9lib cat "a12d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            Append(~asmax, S[1]);
          end if;
          if q eq 7 then //2.M22
            _LRS := Read(c9lib cat "2m22d10");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
              asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if q mod 4 eq 3 then //Sp4q
            S := sp4qdim10(qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S, S^CG, S^CN, S^(CG*CN)];
            else Append(~asmax, S);
            end if;
          end if;
         end if; //sign=-1
       end if; //type = "O"
     elif d eq 11 then
       if novelties then
         if q eq 2 then
            //L2_23
            _LRS := Read(c9lib cat "l223d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            Append(~asmax, S[1]);
         end if;
         continue;
       end if;
       if type eq "L" then
         if e eq 1 and p mod 3 eq 1 then
           //U52
            _LRS := Read(c9lib cat "u52d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,11);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 23 in {1,2,3,4,6,8,9,12,13,16,18} and p ne 2 then
           //L2_23
            _LRS := Read(c9lib cat "l223d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,11);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 2 then //M24
           _LRS := Read(c9lib cat "m24d23");
           _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            Append(~asmax, S[1]); Append(~asmax, S[2]);
         end if;
       elif type eq "U" then
         if e eq 1 and p mod 3 eq 2 and p ne 2 then
           //U52
            _LRS := Read(c9lib cat "u52d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                     general:=general,normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,11);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 23 in {5,7,10,11,14,15,17,19,20,21,22} then
           //L2_23
            _LRS := Read(c9lib cat "l223d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                     general:=general,normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,11);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
       elif type eq "O" then
         if e eq 1 and GCD(p,24) eq 1 and p ne 13 then
           //A12 (p mod 24 = 7,11,13,17) or A12.2 p mod 24 =1,5,19,23
           _LRS := Read(c9lib cat "a12d11");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 24 in {1,5,19,23} then
               asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 13 then
           //A13
           _LRS := Read(c9lib cat "a13d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            Append(~asmax, S[1]);
            //L33.2
            _LRS := Read(c9lib cat "l33d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
         end if;
         if p ge 11 and q ne 11 then
           //L2q
           S := OrthogSL2(d,q:
                   special:=special,general:=general,normaliser:=normaliser);
           Append(~asmax, S);
         end if;
       end if;
     elif d eq 12 then
       if type eq "L" then
          if novelties then
           if (e eq 1 and p mod 3 eq 1 and p mod 5 in {1,4}) or
            (e eq 2 and p mod 5 in {2,3} and p gt 3 )   then
           //6A6
            _LRS := Read(c9lib cat "6a6d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
           end if;
          continue;
         end if;
         if e eq 1 and p mod 23 in {1,2,3,4,6,8,9,12,13,16,18} and p ne 2 then
           //2.L2_23
            _LRS := Read(c9lib cat "sl223d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 3 eq 1 then
           //6.Suz
            _LRS := Read(c9lib cat "6suzd12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:general:=general);
            if all then nconj :=  GCD(q-1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 49 then //12.L3_4
           _LRS := Read(c9lib cat "12bl34d12f49");
           S := eval _LRS;
           if general then S := sub<GL(d,q) | S, ScalarMatrix(d,z) >;
           end if;
           if all then nconj := 12;
             asmax cat:= GConjugates(S,C,nconj);
           else Append(~asmax,S);
           end if;
         end if;
       elif type eq "U" then
         if novelties then
          if e eq 1 and p mod 3 eq 2 and p mod 5 in {1,4} then
           //6A6
            _LRS := Read(c9lib cat "6a6d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
          end if;
          continue;
         end if;
         if e eq 1 and p mod 23 in {5,7,10,11,14,15,17,19,20,21,22} then
           //2.L2_23
            _LRS := Read(c9lib cat "sl223d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if e eq 1 and p mod 3 eq 2 then
           //6.Suz (or 3.Suz of p=2)
            _LRS := Read(c9lib cat "6suzd12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
            if all then nconj :=  GCD(q+1,d);
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
         if q eq 5 then //6A7
            _LRS := Read(c9lib cat "6a7d24");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                                   general:=general,normaliser:=normaliser);
            S := [s: s in S | Degree(s) eq 12];
            if all then nconj :=  6;
              asmax cat:= GConjugates(S[1],C,nconj);
            else Append(~asmax, S[1]);
            end if;
         end if;
       elif type eq "S" then
         if novelties then continue; end if;
         if (e eq 1 and p mod 5 in {1,4}) or
            (e eq 2 and p mod 5 in {2,3} and q ne 4) then
           //2.L2_11.2 (q=1,19 mod 20), 2.L2_11 o.w.
           _LRS := Read(c9lib cat "sl211d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 20 in {1,19} then
              asmax cat:= [S[1], S[1]^C];
              asmax cat:= [S[2], S[2]^C];
           else Append(~asmax, S[1]); Append(~asmax, S[2]);
           end if;
         end if;
         if (e eq 1 and p mod 7 in {1,6} and p ne 13) or
            (e eq 3 and p mod 7 in {2,3,4,5}) then
           //2.L2_13.2 (q=1,27 mod 28), 2.L2_13 o.w.
           _LRS := Read(c9lib cat "sl213d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 28 in {1,27} then
              asmax cat:= [S[1], S[1]^C];
              asmax cat:= [S[2], S[2]^C];
              asmax cat:= [S[3], S[3]^C];
           else
             Append(~asmax, S[1]); Append(~asmax, S[2]); Append(~asmax, S[3]);
           end if;
         end if;
         if e eq 1 and p mod 5 in {2,3} and p ne 3 then
           //2.L2_25 (p!=2), L2_25.2 (p=2)
           _LRS := Read(c9lib cat "sl225d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
         if (e eq 1 and p mod 5 in {0,1,4}) or
            (e eq 2 and p mod 5 in {2,3}) then
           //Sp4_5 (p!=2) or PSp4_5 (p=2)
           _LRS := Read(c9lib cat "sp45d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p ne 2 and p ne 5 then
              asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
/* U34 < G24
         if e eq 1 and p ne 2 then
           //U34.4 (p mod 8 = 1,7), U34.2 o.w.
           _LRS := Read(c9lib cat "u34d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 8 in {1,7} then
             asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
*/
         if e eq 1 and p ne 2 and p ne 3 then
           //2.G24.2 (p mod 8 = 1,7), 2.G24 o.w.
           _LRS := Read(c9lib cat "2g24d12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           if all and p mod 8 in {1,7} then
             asmax cat:= [S[1], S[1]^C];
           else Append(~asmax, S[1]);
           end if;
         end if;
         if q eq 3 then //2.Suz
           _LRS := Read(c9lib cat "6suzd12");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
         if q eq 2 then //S_14
           _LRS := Read(c9lib cat "a14d13");
           _LR := eval _LRS;
           S := ReduceOverFiniteField(_LR,qq: normaliser:=normaliser);
           Append(~asmax, S[1]);
         end if;
        if p ge 13 then
           //2.L2q
           S := SymplecticSL2(d,q:normaliser:=normaliser);
           Append(~asmax, S);
         end if;
       elif type eq "O" then
         if sign eq 1 then
          if novelties then
            if e eq 1 and p mod 13 in {1,3,4,9,10,12} and p ne 3 then
              //L33
              _LRS := Read(c9lib cat "l33d12");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                   special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 12 in {1,11}  then
                 asmax cat:= [S[1], S[1]^CG, S[1]^CN, S[1]^(CG*CN)];
              elif all then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CG, S[1]^(CS*CG)];
              else Append(~asmax, S[1]);
              end if;
            end if;
            if e eq 1 and p ge 5 and p mod 24 in {5,7,11,13,17,19} then
              //2.M12
              _LRS := Read(c9lib cat "2m12d12");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                  special:=special,general:=general,normaliser:=normaliser);
              if all and p mod 24 in {11,13} then
                 asmax cat:= [S[1], S[1]^CG, S[1]^CN, S[1]^(CG*CN)];
              elif all then
                 asmax cat:= [S[1], S[1]^CS, S[1]^CG, S[1]^(CS*CG)];
              else Append(~asmax, S[1]);
              end if;
            end if;
            continue;
          end if;
          if e eq 1 and p mod 55 in {1,16,19,24,26,29,31,36,39,54} then
           //L2_11
           _LRS := Read(c9lib cat "l211d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
               asmax cat:= [S[2], S[2]^CS, S[2]^CN, S[2]^(CS*CN)];
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
          end if;
          if p mod 13 in {1,3,4,9,10,12} and
             ( (e eq 1 and p mod 7 in {1,6}) or
               (e eq 3 and p mod 7 in {2,3,4,5})  ) then
            //L2_13
            _LRS := Read(c9lib cat "l213d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
               asmax cat:= [S[2], S[2]^CS, S[2]^CN, S[2]^(CS*CN)];
               asmax cat:= [S[3], S[3]^CS, S[3]^CN, S[3]^(CS*CN)];
            else
             Append(~asmax, S[1]); Append(~asmax, S[2]); Append(~asmax, S[3]);
            end if;
          end if;
          if e eq 1 and p mod 13 in {1,3,4,9,10,12} then
            //A13
            _LRS := Read(c9lib cat "a13d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CS, S[1]^CN, S[1]^(CS*CN)];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if e eq 1 and p ge 5 and p mod 24 in {1,23} then
            //2.M12.2
            _LRS := Read(c9lib cat "2m12d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CS, S[1]^CG, S[1]^(CS*CG),
                      S[1]^CN, S[1]^(CS*CN), S[1]^(CG*CN), S[1]^(CS*CG*CN)];
            else Append(~asmax, S[1]);
            end if;
          end if;
         elif sign eq -1 then
          if novelties then
            if e eq 1 and p mod 13 in {2,5,6,7,8,11} and p mod 12  in {5,7} then
              //L33
              _LRS := Read(c9lib cat "l33d12");
              _LR := eval _LRS;
              S := ReduceOverFiniteField(_LR,qq:
                    special:=special,general:=general,normaliser:=normaliser);
              if all then
                 asmax cat:= [S[1], S[1]^CG];
              else Append(~asmax, S[1]);
              end if;
            end if;
            continue;
          end if;
          if (e eq 1 and p mod 55 in {4,6,9,14,21,34,41,46,49,51}) or
             (e eq 2 and p mod 5 in {2,3}) then
           //L2_11
           _LRS := Read(c9lib cat "l211d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p ne 2 then
               asmax cat:= [S[1], S[1]^CN];
               asmax cat:= [S[2], S[2]^CN];
            else Append(~asmax, S[1]); Append(~asmax, S[2]);
            end if;
          end if;
          if p mod 13 in {2,5,6,7,8,11} and
             ( (e eq 1 and p mod 7 in {1,6}) or
               (e eq 3 and p mod 7 in {2,3,4,5})  ) then
            //L2_13
            _LRS := Read(c9lib cat "l213d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p ne 2 then
               asmax cat:= [S[1], S[1]^CN];
               asmax cat:= [S[2], S[2]^CN];
               asmax cat:= [S[3], S[3]^CN];
            else
             Append(~asmax, S[1]); Append(~asmax, S[2]); Append(~asmax, S[3]);
            end if;
          end if;
          if e eq 1 and p mod 13 in {2,5,6,7,8,11} and
                                p mod 12 in {1,2,11} then
            //L33.2
            _LRS := Read(c9lib cat "l33d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                   special:=special,general:=general,normaliser:=normaliser);
            if all and p mod 12 in {1,11} then
               asmax cat:= [S[1], S[1]^CG, S[1]^CN, S[1]^(CG*CN)];
            elif all and p eq 2 then
               asmax cat:= [S[1], S[1]^CS];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if e eq 1 and p mod 13 in {2,5,6,7,8,11} and p ne 7 then
            //A13
            _LRS := Read(c9lib cat "a13d12");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all and p ne 2 then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
          if q eq 7 then //A14
            _LRS := Read(c9lib cat "a14d13");
            _LR := eval _LRS;
            S := ReduceOverFiniteField(_LR,qq:
                     special:=special,general:=general,normaliser:=normaliser);
            if all then
               asmax cat:= [S[1], S[1]^CN];
            else Append(~asmax, S[1]);
            end if;
          end if;
         end if; //sign = 1,-1
       end if; //type = "O"
     end if; // if d eq ? loop 
   end if; // if cl eq d loop
 end for; //for cl in classes do

 return asmax;
end intrinsic;
