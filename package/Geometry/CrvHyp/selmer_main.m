freeze;


/************************************************************************

       USER INTERFACE FOR RANK AND SELMER GROUPS 
             OF HYPERELLIPTIC JACOBIANS
  
                (Introduced for V2.13)

                Steve Donnelly, May 2006


  In V2.13, TwoSelmerGroupData is no longer a publicized intrinsic
  (although it will remain available), and the old TwoSelmerGroup
  is renamed TwoSelmerGroupOld and not publicized. The official way 
  to use them is to call TwoSelmerGroup (a new intrinsic as an interface)
  with Al:="TwoSelmerGroupData" or "TwoSelmerGroupOld" (or neither). 

  Notes on the new varargs:
    * By default, Al will be selected (intelligently?) by the program
    * There are no varargs for controlling the class group computation.
      In V2.13 it can more easily be controlled using the global bounds maps.
      Alternatively, precompute class groups and pass in the Fields.
    * There is no Hints. (Was it really useful?) 
      If so, let's make it an attribute instead.
    * There is no Points. Use the attribute Points instead.

     New intrinsic **RankBound** does essentially what the first return value
     in TwoSelmerGroupData always did, plus it will check the cache.
     Also, there is **RankBounds**, where the lower bound will do
     some sort of point search on the curve, and maybe on the Kummer surface.
     (Right now it doesn't do very much).

   *** Still TO DO:
         
         + Use the Points cache in both functions

   *** Updates:
      
    + Feb 2012, BMC
      Modified Rank and RankBounds to incorporate descent on PIC^1
      and to do a better point search (in the higher genus case)

********************************************************************/


declare attributes JacHyp: TwoSelmerGroup;
   // This will be a list of tuples, which can be
   //  < "TwoSelmerGroupOld", S, StoA, toVec, FB > or 
   //  < "TwoSelmerGroupData, S, StoA, fakedata >.
import "../CycCov/rankbounds.m": JacCycCovRankBounds;   

intrinsic RankBounds(J::JacHyp : ReturnGenerators:=false) 
       -> RngIntElt, RngIntElt
{Lower and upper bounds on the Mordell-Weil rank of the given Jacobian
(of some hyperelliptic curve over Q).}

  C := Curve(J);
  if Genus(C) eq 1 then 
     return RankBounds(Jacobian(GenusOneModel(C))); 
  end if;

  require BaseField(J) eq Rationals() :
    "RankBounds is currently only implemented for Jacobians over the rationals.";
    C := IntegralModel(SimplifiedModel(C));
    f,g := HyperellipticPolynomials(C);
    f := MonicModel(f,2);

 // require g cmpeq 0: "Curve must be of the form y^2 = f(x).";
 // if Degree(f) mod 2 eq 1 then
 //   require LeadingCoefficient(f) eq 1 and &and[ IsIntegral(c) : c in Coefficients(f) ]:
 //     "Curve must be of the form y^2 = f(x) with f(x) monic.";
 // else
 //   require &and[ IsIntegral(c) : c in Coefficients(f/LeadingCoefficient(f)) ]:
 //     "Curve must be of the form y^2 = c*f(x) with f(x) monic.";
 // end if;

  r,R,gens,J2 := JacCycCovRankBounds(f,2,false);
  if assigned J`TwoSelmerGroup then
    Als := [ G[1] : G in J`TwoSelmerGroup ];
    if Index(Als,"TwoSelmerGroupNew") eq 0 then
      Append(~J`TwoSelmerGroup,J2`TwoSelmerGroup[1]);
      J`TwoSelmerSet := J2`TwoSelmerSet;
      J`TwoSelmerRank := J2`TwoSelmerRank;
    end if;
  else
    J`TwoSelmerGroup := J2`TwoSelmerGroup;
    J`TwoSelmerSet := J2`TwoSelmerSet;
    J`TwoSelmerRank := J2`TwoSelmerRank;
  end if; 
  C := HyperellipticCurve(f);
  BoundIsProven := Genus(C) eq 2 or HasIndexOneEverywhereLocally(C);
  if not BoundIsProven then
    printf "WARNING: upper bound is only an upper bound for the rank of Pic^0(X)/2*Pic^0(X).\n";
  end if;
  if ReturnGenerators then 
    return r,R,gens;
  else
    return r,R;
  end if;
  
  //Below is the code for genus 2 the old way:
  //JacCycCovRankBounds(f,2,false) gives a sharper
  //bounds in many cases.
  //
  // ptsC := Points(C : Bound:=10^4 );
  //ptsJ := {};
  //if #ptsC gt 0 then 
  //   pt0 := ptsC[1];
  //   ptsJ := { J!(pt-pt0) : pt in ptsC }; 
  //end if;
  //ptsJ join:= {pt : pt in Points(J : Bound:=20)};
  //if assigned J`Points then 
  //   ptsJ join:= {pt : pt in J`Points}; 
  //end if;

  // TO DO: All the time goes in computing the height of all these points.
  //        So, be more intelligent and eliminate a lot of the points 
  //        (by identifying them as torsion or simple combos of other points)
  //        Then turn the Bound in Points(J) back up to 100 or so.
  //basis := ReducedBasis(Setseq(ptsJ));

  //upperbound := RankBound(J);
  //require #basis le upperbound: "Lower bound is larger than upper bound."; 

  //if ReturnGenerators then
  //   return #basis, upperbound, basis;
  //else
  //   return #basis, upperbound;
  //end if;

end intrinsic;


intrinsic RankBound(J::JacHyp) -> RngIntElt
{An upper bound on the Mordell-Weil rank of the given Jacobian
(of some hyperelliptic curve over a number field).}

  C := Curve(J);
  if Genus(C) eq 1 then 
    return RankBound(Jacobian(GenusOneModel(C))); 
  end if;
  
  if BaseField(J) cmpeq Rationals() then
    S := TwoSelmerGroup(J : Al := "TwoSelmerGroupNew");
    r := J`TwoSelmerRank;
    //if IsEven(Genus(C)) and Genus(C) le 6 then
      //if Genus(C) is large, IsOdd(J) may be slow.
    //  if IsOdd(J) then r -:= 1; end if;
    //end if;
      BoundIsProven := Genus(C) eq 2 or HasIndexOneEverywhereLocally(C);
      if not BoundIsProven then
        printf "WARNING: upper bound is only an upper bound for the rank of Pic^0(X)/2*Pic^0(X).\n";
      end if;
    if Degree(C) mod 2 eq 0 then
      SelPic := J`TwoSelmerSet;
      if #SelPic eq 0 and BoundIsProven then
        //PIC1 is not divisible by 2 in Sha
        if IsOdd(J) then
		r -:= 1;
		vprintf Selmer, 1: "Sha is odd ==> Rank(J(k)) le %o.\n", r;
	else
	        r -:= 2;
	end if;
      end if;
    end if;
    return r;
  end if;
  
  // BaseField cmpneq Rationals();
  require IsEven(Genus(C)) or IsOdd(Degree(C)) :
    "For Jacobians over number fields other than Q, TwoSelmerGroup",
    "is only implemented for curves of even genus or of odd degree.";

  G,m := TwoSelmerGroup(J);
  r := Ngens(G);
  r -:= Ngens(TwoTorsionSubgroup(Jacobian(SimplifiedModel(C))) );
  return r;
end intrinsic;



intrinsic TwoSelmerGroup(J::JacHyp : 
                         Al := 0,  // "TwoSelmerGroupData" or "TwoSelmerGroupOld"
                         Fields := {},
                         ReturnFakeSelmerData := false,
                         ReturnRawData := false)
   -> GrpAb, Map, Any, Any 
{The 2-Selmer group of the Jacobian J (of some hyperelliptic curve over a number field).}

  C := Curve(J);
  genus := Genus(C);
  deg := Degree(C);

  bruin := "TwoSelmerGroupOld";
  stoll := "TwoSelmerGroupData";
  creutz := "TwoSelmerGroupNew";

  require Al cmpeq 0 or Al cmpeq bruin or Al cmpeq stoll or Al cmpeq creutz:
          "The optional argument 'Al' must be \"TwoSelmerGroupData\" or \"TwoSelmerGroupOld\" or \"TwoSelmerGroupNew\"";
  
  // Parse the varargs
  if ReturnFakeSelmerData then 
     require Al cmpeq stoll: "Fake Selmer data can only be returned when the optional argument 'Al' is set to \"TwoSelmerGroupData\"";
     Al := stoll;
  elif ReturnRawData then
     require Al cmpne stoll: "Raw data cannot be returned when the optional argument 'Al' is set to \"TwoSelmerGroupData\"";
     //Al := bruin;
  end if;

  // if Al is not specified, choose whichever is cached, if any
  if not assigned J`TwoSelmerGroup then 
     J`TwoSelmerGroup := [* *]; 
  end if;
  cachedAls := [ tup[1] : tup in J`TwoSelmerGroup ];
  if Al cmpeq 0 and #cachedAls ne 0 then 
     Al := cachedAls[1]; 
  end if;
   
  // Choose Al, defaulting to stoll when possible, except for elliptic curves
  if Al cmpeq 0 then
     if BaseField(J) ne Rationals() then 
        Al := bruin;
     elif deg gt 6 then
        Al := creutz;
        // best option for higher genus over Q
        // TwoSelmerGroupData for even degree is only implemented for genus 2
     elif deg lt 5 then
        // TO DO: call TwoSelmerGroup(CrvEll)
        Al := bruin;
     else 
        Al := stoll;
     end if;
  end if;

  idx := Index( cachedAls, Al );

  if Al eq bruin and idx ne 0 then
     _, S, StoA, toVec, FB := Explode(J`TwoSelmerGroup[idx]);
  elif Al eq bruin then
     S, StoA, Hints, toVec, FB := TwoSelmerGroupOld(J : Raw, Fields:=Fields);
     Append( ~J`TwoSelmerGroup, <bruin, S, StoA, toVec, FB> );
  elif Al eq creutz and idx ne 0 then 
     _, S, StoA, toVec, FB := Explode(J`TwoSelmerGroup[idx]);
  elif Al eq creutz then
     S, StoA, toVec, FB := TwoSelmerGroupNew(J : Raw := true, Fields := Fields);
     //Append(~J`TwoSelmerGroup, <creutz, S, StoA, toVec, FB> );
     //data is already appended by TwoSelmerGroupNew
  elif Al eq stoll and idx ne 0 then
     _, S, StoA, fakedata := Explode(J`TwoSelmerGroup[idx]);
  elif Al eq stoll then
     r, s, fakedata, fields, S, StoA := TwoSelmerGroupData(J : Fields:=Fields);
     Append( ~J`TwoSelmerGroup, <stoll, S, StoA, fakedata> );
  end if;

  ans := [* S, StoA *];
  if ReturnFakeSelmerData then 
     ans cat:= [* fakedata *]; 
  end if;
  if ReturnRawData then 
     ans cat:= [* toVec, FB *]; 
  end if;

  // Check whether bruin and stoll agree with eachother:
  //if #J`TwoSelmerGroup eq 2 then 
  //   require #J`TwoSelmerGroup[1][2] eq #J`TwoSelmerGroup[2][2] :
  //      "The two internal algorithms disagree about the Selmer rank.";
  //end if;

  return Explode(ans);

end intrinsic;



intrinsic TwoSelmerGroupTest(J) -> GrpAb, Map
{Test the two implementations of TwoSelmerGroup against eachother}

  printf "Bruin: "; time
  SB := TwoSelmerGroup(J : Al := "TwoSelmerGroupOld");
   
  printf "Creutz: "; time
  SC := TwoSelmerGroup(J : Al := "TwoSelmerGroupNew");  
  
  //printf "Stoll: "; time
  //SS, _, fake := TwoSelmerGroup(J : Al := "TwoSelmerGroupData);
  
  if #SC ne #SB then
     printf "Failed test!\nCreutz says %o\nBruin says %o\n", SC, SB;
  end if;

  return #SC eq #SB, Ilog(2, #SC);
end intrinsic;

