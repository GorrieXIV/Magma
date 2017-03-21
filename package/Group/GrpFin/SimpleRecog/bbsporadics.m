freeze;

import "bbprelims.m": OrderModCentre, BruteForceHomomorphism;

///////////////////////////////////////////////////////////
// We want to redefine certain groups with specific sets //
// of generators. Here are a few global variables.       //
///////////////////////////////////////////////////////////

SU3_3 := sub < GL (3, 9) |  [0,0,2,0,2,0,2,0,0],
                            [2,W^2,W,1,W^5,W^7,W,W,W] >
              where W := GF(3, 2).1;
SU3_3`Order := 6048;
   
//////
SU3_4 := sub < GL (3, 16) | [0,0,1,0,1,0,1,0,0],
                      [W^3,0,W^13,W^8,W^9,W^3,W^14,W^14,W] >
              where W := GF(2, 4).1;
SU3_4`Order := 62400;

//////
SU3_5 := sub < GL (3, 25) | [0,0,3,0,4,3,2,1,1],
                            [4,0,W^15,0,1,0,W^9,0,3] >
              where W := GF(5, 2).1;
SU3_5`Order := 378000;
   
//////
SU3_8 := sub < GL (3, 64) | [0,0,1,0,1,0,1,0,0],
                      [1,W^60,W^4,W^22,W^48,W^29,W^5,W^21,W^19] >
              where W := GF(2, 6).1;
SU3_8`Order := 16547328;
   
//////
SU3_11 := sub < GL (3, 121) | [0,0,10,0,10,0,10,0,0],
                       [W^81,9,W^20,9,W,W^31,W^55,W^57,W^41] >
              where W := GF(11, 2).1;
SU3_11`Order := 212747040;
   
//////
SU3_17 := sub < GL (3, 289) | [0,0,16,0,16,0,16,0,0],
           [W^233,W^182,W^275,W^214,W^154,W^186,W^275,W^154,W^5] >
              where W := GF(17, 2).1;
SU3_17`Order := 6953034816;
   
//////
SU4_2 := sub < GL (4, 4) | [0,0,W,1,W^2,1,1,W^2,0,0,1,0,1,0,W,0],
                       [W,0,W^2,W,W,W^2,W^2,0,W,W^2,0,0,W,0,0,0] >
                          where W := GF(2, 2).1;
SU4_2`Order := 25920;
  
//////
SU4_3 := sub < GL (4, 9) | 
                  [W^5,W^7,W^6,1,2,W,0,W^2,W^6,1,W^3,W^5,0,W^2,2,W^7],
                  [2,0,2,W^6,1,1,W^5,W,0,0,1,0,0,0,1,2] >
                       where W := GF(3, 2).1;
SU4_3`Order := 13063680;
  
//////
SU4_4 := sub < GL (4, 16) |
           [1,0,0,0,1,W^10,W^10,0,W^10,1,W^10,0,W^5,W^10,1,1], 
      [W^14,W^12,W^5,W^8,W^8,W,W^14,W,1,1,W^11,W^11,W^5,W^5,W^8,W^8] >
                 where W := GF(2, 4).1;
SU4_4`Order := 1018368000;
  
//////
SU4_5 := sub < GL (4, 25) |
          [2,2,W^8,3,W^3,W^5,3,W^16,1,1,W,2,0,1,W^15,2], 
     [W^5,W^16,4,W^16,W^23,W^17,W^5,W^11,1,W^3,W^7,1,W^9,4,2,W^11] >
                   where W := GF(5, 2).1;
SU4_5`Order := 29484000000;
  
//////
SU4_7 := sub < GL (4, 49) |
  [W^29,W^42,W^14,0,W^20,W^6,2,W^2,W^31,5,W^42,W^6,5,W^25,W^44,W^11], 
  [W^35,6,W^29,W^11,W^28,W^31,W^28,W^29,W^11,W^5,0,0,W^13,2,W^17,W^47] >
           where W := GF(7, 2).1;
SU4_7`Order := 4662288691200;
  
//////
dSp4_2 := sub < GL (4, 2) | [1,0,1,0,1,1,1,1,0,0,1,0,0,0,1,1],
                            [0,0,1,0,0,0,0,1,1,0,0,1,0,1,0,0] >;
dSp4_2`Order := 360;

//////
Sp4_2 := sub < GL (4, 2) | [1,0,0,0,1,0,1,0,1,1,0,0,1,1,1,1],
                           [0,0,1,0,0,0,1,1,1,0,1,1,1,1,1,0] >;
Sp4_2`Order := 720;
  
           
/////////////////////////////////////////////////////////
/////////////// PSU(3,q) sporadic cases /////////////////
/////////////////////////////////////////////////////////

//////////////////////// PSU(3,3) ///////////////////////

RECOGNIZE_U3_3 := function (G, limit)
     proc := RandomProcess (G);
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 6 eq 0) then
             found := true;
             found := true;
             b0 := g^(o div 6);
             a := g^(o div 2);
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i := i + 1;
         b := b0^Random (proc);
         if Order (a*b) eq 7 then
         found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     
return true, true, [a, b];
end function;


////////////////////// PSU(3,4) ////////////////////////

RECOGNIZE_U3_4 := function (G, limit)
     proc := RandomProcess (G);
     founda := false;
     foundb := false;
     found := founda and foundb;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 2 eq 0) then
             founda := true;
             a := g^(o div 2);
         end if;
         if (o mod 3 eq 0) then
             foundb := true;
             b0 := g^(o div 3);
         end if;
         found := founda and foundb;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i := i + 1;
         b := b0^Random (proc);
         if Order (a*b) eq 13 then
         found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;    
return true, true, [a, b];
end function;


////////////////////////// PSU(3,5) /////////////////////////

RECOGNIZE_U3_5 := function (G, limit)
     isSimple := true;
     proc := RandomProcess (G);
     founda := false;
     foundb := false;
     found := founda and foundb;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 3 eq 0) then
             a0 := g^(o div 3);
             if not forall
               { i : i in [1..Ngens (G)] | (a0, G.i) eq Identity (G) } then
                 a := a0;
                 founda := true;
             else
                 isSimple := false;
             end if;
         end if;
         if (o mod 10 eq 0) then
             foundb := true;
             b0 := g^(o div 5);
         end if;
         if (o eq 24) then
             isSimple := false;
         end if;
         found := founda and foundb;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         if Order (g) eq 24 then
             isSimple := false;
         end if;
         b := b0^g;
         if Order (a*b) eq 7 then
         found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, isSimple, [a, b];
end function;


////////////////////////// PSU(3,8) //////////////////////////

RECOGNIZE_U3_8 := function (G, limit)
     isSimple := true;
     proc := RandomProcess (G);
     founda := false;
     foundb := false;
     found := founda and foundb;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 2 eq 0) then
             a := g^(o div 2);
             founda := true;
         end if;
         if (o mod 19 eq 0) then
             foundb := true;
             b0 := g^(o div 19);
         end if;
         if (o eq 63) then
             isSimple := false;
         end if;
         found := founda and foundb;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         if Order (g) eq 63 then
             isSimple := false;
         end if;
         b := b0^g;
         if Order (a*b) eq 3 then
         found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
/*
XX := sub < Generic (G) | [a, a*b] >;
RandomSchreier (XX);
#XX;
if #XX ne 16547328 then "ALERT!"; end if;
*/
return true, isSimple, [a, a*b];
end function;


/////////////////////// PSU(3,11) //////////////////////

RECOGNIZE_U3_11 := function (G, limit)
     isSimple := true;
     proc := RandomProcess (G);
     founda := false;
     foundb := false;
     found := founda and foundb;
     i := 0;
     repeat
         i +:= 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 2 eq 0) then
             founda := true;
             a := g^(o div 2);
         end if;
         if (o mod 3 eq 0) then
             b1 := g^(o div 3);
             if not forall { i : i in [1..Ngens (G)] | 
                          (b1, G.i) eq Identity (G) } then
                 b0 := b1;
                 foundb := true;
             else
                 isSimple := false;
             end if;
         end if;
         if (o eq 120) then
             isSimple := false;
         end if;
         found := founda and foundb;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i +:= 1; 
         g := Random (proc);
         if Order (g) eq 120 then
             isSimple := false;
         end if;
         b := b0^g;
         if Order (a*b) eq 37 and Order (a*b*a*b^2) eq 4 then
           found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, isSimple, [a, b];
end function;


//////////////////// PSU(3,17) ///////////////////////

RECOGNIZE_U3_17 := function (G, limit)
     isSimple := true;
     proc := RandomProcess (G);
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 4 eq 0) then
             found := true;
             a := g^(o div 2);
             b0 := g^(o div 4);
         end if;
         if (o eq 288) then
             isSimple := false;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
     found := false;
     i := 0;
     repeat
         i := i + 1; 
         g := Random (proc);
         if Order (g) eq 288 then
             isSimple := false;
         end if;
         b := b0^g;
         if Order (a*b^2) eq 6 then
             if isSimple then
                 if Order (a*b) eq 13 then
                     found := true;
                 end if;
             else
                 if Order (a*b) eq 39 then
                     found := true;
                 end if;
             end if;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, isSimple, [a, b];
end function;


//////////////////////////////////////////////////////
//
// Given: a homomorphic image G of SU(3,q) 
//          where q is in {3,4,5,8,11,17}
// Constructively recognize G
//
///////////////////////////////////////////////////////

SporadicSU3 := function (G, q)

     if (q eq 3) then
         isit, simple, Y := RECOGNIZE_U3_3 (G, 200);
         good := isit;
         I := SU3_3;
     elif (q eq 4) then
         isit, simple, Y := RECOGNIZE_U3_4 (G, 200);
         good := isit;
         I := SU3_4;
     else  // <G> could have a center
         sanity := [];
         good := false;
         for i in [1..5] do
            if (q eq 5) then
               isit, simple, Z := RECOGNIZE_U3_5 (G, 200);
               I := SU3_5;
            elif (q eq 8) then
               isit, simple, Z := RECOGNIZE_U3_8 (G, 200);
               I := SU3_8;
            elif (q eq 11) then
               isit, simple, Z := RECOGNIZE_U3_11 (G, 200);
               I := SU3_11;
            elif (q eq 17) then
               isit, simple, Z := RECOGNIZE_U3_17 (G, 500);
               I := SU3_17;
            end if; 
            if isit then 
               Append (~sanity, simple); 
               Y := Z;
               good := true;
            end if;
        end for;
        simple := #{i : i in [1..#sanity] | sanity[i]} ge #sanity - 1;
     end if;

     if not good then
         return false, _, _, _, _;
     end if;

     RandomSchreier (I);

     H := sub < Generic (G) | Y >;
     if simple then
        H`Order := I`Order div Gcd (q+1, 3);
     else
        H`Order := I`Order;
     end if; 

     // addition by EOB -- otherwise STCS invoked later by WordMap 
     RSBound := 500000;
     if Type (H) eq GrpMat then 
        repeat 
           flag := RandomSchreierBounded (H, RSBound);
        until flag;
        // "Basic orbit lengths are ", BasicOrbitLengths (H);
     else
        RandomSchreier (H);
     end if;

     RandomSchreier (H);

     // addition by EOB -- otherwise STCS invoked when gammaRule evaluated   
     if Type (H) eq GrpMat then 
        G`Base := H`Base;
     end if;
     G`Order := H`Order;
     RandomSchreier (G);
     
     // added 12/08/2010 after correspondence with D. Holt and J. Cannon
     flag := forall { i : i in [1..Ngens (G)] | G.i in H };
     if (not flag) then return
         false, _, _, _, _;
     end if;
       
     phi := BruteForceHomomorphism (H, I);

     W, delta := WordGroup (G);
     gamma := InverseWordMap (G);

     phiRule := hom < Generic (H) -> I | h :-> h @ phi >;
     tauRule := hom < Generic (I) -> H | i :-> i @@ phi >;
     gammaRule := hom < Generic (G) -> W | g :-> gamma (g) >;
     
     rf := recformat < Generators, Images >;
     data := rec < rf | Generators := Y,
                        Images := [ I.j : j in [1..Ngens (I)] ] >;
     G`SU3DataStructure := data;

     G`RecognitionMaps := < phiRule , tauRule , gammaRule , delta >;

return true, phiRule, tauRule, gammaRule, delta;
end function;


/////////////////////////////////////////////////////////
/////////////// PSU(4,q) sporadic cases /////////////////
/////////////////////////////////////////////////////////

////////////////////// PSU(4,2) ///////////////////////

RECOGNIZE_U4_2 := function (G, limit)
     proc := RandomProcess (G);
     found := false;
     i := 0;
        // first find <b> of order 5
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if (o mod 5 eq 0) then
            found := true;
            b := g^(o div 5);
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
        // next find suitable <a> of order 2
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (proc);
         o := Order (g);
         if o mod 2 eq 0 then
             a := g^(o div 2);
             if Order (a*b) eq 9 and Order ((a, b)) eq 3 then
                 found := true;
             end if;
         end if;       
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, true, [a, b];
end function;

/////////////////////// PSU(4,3) //////////////////////

RECOGNIZE_U4_3 := function (G, limit)
     procG := RandomProcess (G);
     founda := false;
     foundb := false;
     found := founda and foundb;
     isSimple := true;
     i := 0;
     repeat
         i := i + 1;
         g := Random (procG);
         o := OrderModCentre (g, G, [4]);
         if o ne Order (g) then isSimple := false; end if;
         if (o mod 2 eq 0) then
            founda := true;
            a := g^(o div 2);
            if (o mod 12 eq 0) then
               foundb := true;
               b0 := g^(o div 6);
            end if;
         end if;
         found := founda and foundb;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
//"found a and b0";
        // next find a suitable conjugate of <b0>
     found := false;
     i := 0;
     repeat
         i := i + 1;
         g := Random (procG);
         b := b0^g;
         c := a*b;
         o1 := OrderModCentre (c, G, [4]);
         if o1 ne Order (c) then isSimple := false; end if;
         o2 := OrderModCentre (c^3*b*c^2*b, G, [4]);
         if o2 ne Order (c^3*b*c^2*b) then isSimple := false; end if;
         if o1 eq 7 and o2 eq 5 then
             found := true;
         end if;       
     until (found or (i gt limit));
     if (not found) then
         return false, _, _, _;
     end if;
return true, isSimple, [a, b];
end function;


//////////////////////////// PSU(4,4) ///////////////////////

RECOGNIZE_U4_4 := function (G, limit)
     procG := RandomProcess (G);
        // first find suitable <a>
     found := false;
     i := 0;
     repeat
         i +:= 1;
         g := Random (procG);
         o := Order (g);
         if (o in [20, 30]) then
            found := true;
            a := g^(o div 2);
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
        // next find suitable <b>
     found := false;
     i := 0;
     repeat
         i +:= 1;
         g := Random (procG);
         if Order (g) eq 4 then
             j := 0;
             repeat
                 j +:= 1;
                 b := g^Random (procG);
                 if Order (a*b) eq 20 then
                     found := true;
                 end if;   
             until (found) or (j gt 20); 
         end if;   
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, true, [a, b];
end function;


///////////////////////// PSU(4,5)//////////////////////

RECOGNIZE_U4_5 := function (G, limit)
     procG := RandomProcess (G);
     isSimple := true;
     found := false;
     i := 0;
     repeat
         i +:= 1;
         g := Random (procG);
         o := OrderModCentre (g, G, [2]);
         if o ne Order (g) then isSimple := false; end if;
         if o in [8, 24, 60] then
             found := true;
             a := g^(o div 2);
             b0 := g^(o div 4);
         end if;
     until (found) or (i gt limit);
     if not found then 
         return false, _, _, _;
     end if;
        // find a suitable conjugate of <b0>
     found := false;
     i := 0;
     repeat
         i +:= 1;
         b := b0^Random (procG);
         o := OrderModCentre (a*b, G, [2]);
         if o ne Order (a*b) then isSimple := false; end if;
         if o eq 9 then
             found := true;
         end if;
     until (found) or (i gt limit);
     if not found then
         return false, _, _, _;
     end if;
return true, isSimple, [a, b];
end function;


//////////////////////////// PSU(4,7) ///////////////////////////

RECOGNIZE_U4_7 := function (G, limit)
//"limit =", limit;
     procG := RandomProcess (G);
     found := false;
     isSimple := true;
     i := 0;
     repeat
         i +:= 1;
         g := Random (procG);
         o := OrderModCentre (g, G, [4]);
         if o ne Order (g) then 
            isSimple := false; 
         end if;
         if o in [48, 56] then
             found := true;
             a := g^(o div 2);
             b0 := g^(o div 4);
         end if;
     until (found) or (i gt limit);
     if not found then 
         return false, _, _, _;
     end if;
//"found a and b0";
        // find a suitable conjugate of <b0>
     found := false;
     i := 0;
     repeat
         i +:= 1;
         b := b0^Random (procG);
         o1 := OrderModCentre (a*b, G, [4]);
         o2 := OrderModCentre ((a, b), G, [4]);
         if o1 ne Order (a*b) or o2 ne Order((a, b)) then 
               isSimple := false; 
         end if;
         if (o1 eq 15 and o2 eq 24) then
            found := true;
         end if;
     until (found) or (i gt limit);
     // "Generators found in U4_7? ", found;
     if not found then
         return false, _, _, _;
     end if;     
return true, isSimple, [a, b];
end function;

////////// main sporadic recognition function for SU(4,q) ///////////

SporadicSU4 := function (G, q)
     // conjugacy class issues for q = 3 and 7 
     Bad_class_limit := 10;

     if (q eq 2) then
         isit, simple, Y := RECOGNIZE_U4_2 (G, 300);
         I := SU4_2;
     elif (q eq 3) then
         // added by PAB on 18/1/2011
         i := 0;
         repeat
            i +:= 1;
            isit, simple, Y := RECOGNIZE_U4_3 (G, 300);
         until (isit) or (i eq Bad_class_limit);
         // end: handles conjugacy class issues
         I := SU4_3; 
     elif (q eq 4) then
         isit, simple, Y := RECOGNIZE_U4_4 (G, 500);
         I := SU4_4; 
     elif (q eq 5) then
         isit, simple, Y := RECOGNIZE_U4_5 (G, 400);
         I := SU4_5; 
     elif (q eq 7) then
         // added by PAB on 18/1/2011
         i := 0;
         repeat
            i +:= 1;
            isit, simple, Y := RECOGNIZE_U4_7 (G, 400);
         until (isit) or (i eq Bad_class_limit);
         // end: handles conjugacy class issues
         I := SU4_7; 
     end if;

     // "Identified the group as SU4? ", isit;
     if (not isit) then
         return false, _, _, _, _;
     end if;

     // addition by EOB -- otherwise STCS invoked later by WordMap 
     RSBound := 5000000; Nmr := 100;
     if Type (G) eq GrpMat then 
        repeat 
           flag := RandomSchreierBounded (G, RSBound);
            // "Flag is ", flag;
           Nmr -:= 1;
        until flag or Nmr eq 0;
        if Nmr eq 0 then error "RandomSchreierBounded failed"; end if;
        // "Basic orbit lengths are ", BasicOrbitLengths (G);
     else
        RandomSchreier (G);
     end if;

     RandomSchreier (I);
     H := sub < Generic (G) | Y >;
     // H = G, so use good base from calculation of BSGS for G 
     if Type (G) eq GrpMat then 
        H`Base := G`Base;
     end if;
     RandomSchreier (H);
     
     // added 12/08/2010 after correspondence with D. Holt and J. Cannon
     flag := forall { i : i in [1..Ngens (G)] | G.i in H };
     if (not flag) then return
         false, _, _, _, _;
     end if;
     
     phi := BruteForceHomomorphism (H, I);
     W, delta := WordGroup (G);
     gamma := InverseWordMap (G);
     phiRule := hom < H -> I | h :-> h @ phi >;
     tauRule := hom < I -> H | i :-> i @@ phi >;
     gammaRule := hom < G -> W | g :-> gamma (g) >;
     
     rf := recformat < Generators, Images >;
     data := rec < rf | Generators := Y,
                        Images := [ I.j : j in [1..Ngens (I)] ] >;
     G`SU4DataStructure := data;

     G`RecognitionMaps := < phiRule , tauRule , gammaRule , delta >;

return true, phiRule, tauRule, gammaRule, delta;
end function;


/////////////////////////////////////////////////////////
/////////////// PSp(4,q) sporadic cases /////////////////
/////////////////////////////////////////////////////////

RECOGNIZE_DS4_2 := function (G, limit)
     procG := RandomProcess (G);
     i := 0;
     found := false;
     repeat
         i +:= 1;
         y := Random (procG);
         if (Order (y) eq 4) then
             found := true;
         end if;
     until (found) or (i gt limit);
     if (not found) then 
         return false, _, _;
     end if;
     a := y^2;
        // now find a suitable conjugate of <y0>
     i := 0;
     found := false;
     repeat
         i +:= 1;
         b := y^Random (procG);
         if (Order (a*b) eq 5) then
             found := true;
         end if;
     until (found) or (i gt 4 * limit);
     if (not found) then
         return false, _, _;
     end if;
return true, [a, b];
end function;


RECOGNIZE_S4_2 := function (G, limit)
     procG := RandomProcess (G);
     i := 0;
     found := false;
     repeat
         i +:= 1;
         b := Random (procG);
         if (Order (b) eq 5) then
             found := true;
         end if;
     until (found) or (i gt limit);
     if (not found) then 
         return false, _, _;
     end if;
       // next find an involution
     i := 0;
     found := false;
     repeat
         i +:= 1;
         y := Random (procG);
         if (Order (y) mod 2 eq 0) then
             a0 := y^(Order (y) div 2);
             found := true;
         end if;
     until (found) or (i gt limit);
       // find a suitable conjugate of <a0>
     i := 0;
     found := false;
     repeat
        i +:= 1;
        y := Random (procG);
        a := a0 ^ y;
        if (Order (a*b) eq 6 and Order (a*b^2) eq 6) then
           found := true;
        end if;
     until (found) or (i gt 4 * limit);
     if (not found) then
         return false, _, _;
     end if;
return true, [a, b];
end function;


// modified by PAB on 7/10/2010
// function now recognises Sp(4,2) not the quasisimple Sp(4,2)'

SporadicSp4 := function (G, q)

     if (q eq 2) then
         j := 0;
         repeat
            j +:= 1;
            flag, Y := RECOGNIZE_S4_2 (G, 50);
         until flag or (j eq 20);
         I := Sp4_2;
     end if;

     if (not flag) then
         return false, _, _, _, _;
     end if;

     // addition by EOB -- otherwise STCS invoked later by WordMap 
     RandomSchreier (G);
     RandomSchreier (I);
     H := sub < Generic (G) | Y >;
     RandomSchreier (H);
     
     // added 12/08/2010 after correspondence with D. Holt and J. Cannon
     flag := forall { i : i in [1..Ngens (G)] | G.i in H };
     if (not flag) then return
         false, _, _, _, _;
     end if;

     phi := BruteForceHomomorphism (H, I);
     W, delta := WordGroup (G);
     gamma := InverseWordMap (G);
     phiRule := hom < H -> I | h :-> h @ phi >;
     tauRule := hom < I -> H | i :-> i @@ phi >;
     gammaRule := hom < Generic (G) -> W | g :-> gamma (g) >;
     
     rf := recformat < Generators, 
                       Images >;
     data := rec < rf | Generators := Y,
                        Images := [ I.j : j in [1..Ngens (I)] ] >;
     G`Sp4DataStructure := data;

     G`RecognitionMaps := < phiRule , tauRule , gammaRule , delta >;
     
return true, phiRule, tauRule, gammaRule, delta;  
end function;
