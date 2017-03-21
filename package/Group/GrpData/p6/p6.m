freeze;
 
/* GroupsOfOrderp6 (p) returns corrected list of 
   Easterfield presentations for given prime p > 5 */

import "Phi1.m":Phi1;
import "Phi2.m":EasterfieldPhi2;
import "Phi3.m":EasterfieldPhi3;
import "Phi4.m":EasterfieldPhi4;
import "Phi5.m":EasterfieldPhi5;
import "Phi6.m":EasterfieldPhi6;
import "Phi7.m":EasterfieldPhi7;
import "Phi8.m":EasterfieldPhi8;
import "Phi9.m":EasterfieldPhi9;
import "Phi10.m":EasterfieldPhi10;
import "Phi11.m":EasterfieldPhi11;
import "Phi12.m":EasterfieldPhi12;
import "Phi13.m":EasterfieldPhi13;
import "Phi14.m":EasterfieldPhi14;
import "Phi15.m":EasterfieldPhi15;
import "Phi16.m":EasterfieldPhi16;
import "Phi17.m":EasterfieldPhi17;
import "Phi18.m":EasterfieldPhi18;
import "Phi19.m":JamesPhi19;
import "Phi20.m":EasterfieldPhi20;
import "Phi21.m":EasterfieldPhi21;
import "Phi22.m":EasterfieldPhi22;
import "Phi23.m":EasterfieldPhi23;
import "Phi24.m":EasterfieldPhi24;
import "Phi25.m":EasterfieldPhi25;
import "Phi26.m":EasterfieldPhi26;
import "Phi27.m":EasterfieldPhi27;
import "Phi28.m":EasterfieldPhi28;
import "Phi29.m":EasterfieldPhi29;
import "Phi30.m":EasterfieldPhi30;
import "Phi31.m":EasterfieldPhi31;
import "Phi32.m":EasterfieldPhi32;
import "Phi33.m":EasterfieldPhi33;
import "Phi34.m":EasterfieldPhi34;
import "Phi35.m":EasterfieldPhi35;
import "Phi36.m":EasterfieldPhi36;
import "Phi37.m":EasterfieldPhi37;
import "Phi38.m":EasterfieldPhi38;
import "Phi39.m":EasterfieldPhi39;
import "Phi40.m":EasterfieldPhi40;
import "Phi41.m":EasterfieldPhi41;
import "Phi42.m":EasterfieldPhi42;
import "Phi43.m":EasterfieldPhi43;
import "misc.m":NonQuadraticResidue, EasterfieldPair;

GroupsOfOrderp6 := function (p)

if not IsPrime (p) or p lt 5 then 
   "p must be at least 5";
   return false;
end if;

X := [];
X cat:= Phi1 (p);
X cat:= EasterfieldPhi2 (p);
X cat:= EasterfieldPhi3 (p);
X cat:= EasterfieldPhi4 (p);
X cat:= EasterfieldPhi5 (p);
X cat:= EasterfieldPhi6 (p);
X cat:= EasterfieldPhi7 (p);
X cat:= EasterfieldPhi8 (p);
X cat:= EasterfieldPhi9 (p);
X cat:= EasterfieldPhi10 (p);
X cat:= EasterfieldPhi11 (p);
X cat:= EasterfieldPhi12 (p);
X cat:= EasterfieldPhi13 (p);
X cat:= EasterfieldPhi14 (p);
X cat:= EasterfieldPhi15 (p);
X cat:= EasterfieldPhi16 (p);
X cat:= EasterfieldPhi17 (p);
X cat:= EasterfieldPhi18 (p);
X cat:= JamesPhi19 (p);
X cat:= EasterfieldPhi20 (p);
X cat:= EasterfieldPhi21 (p);
X cat:= EasterfieldPhi22 (p);
X cat:= EasterfieldPhi23 (p);
X cat:= EasterfieldPhi24 (p);
X cat:= EasterfieldPhi25 (p);
X cat:= EasterfieldPhi26 (p);
X cat:= EasterfieldPhi27 (p);
X cat:= EasterfieldPhi28 (p);
X cat:= EasterfieldPhi29 (p);
X cat:= EasterfieldPhi30 (p);
X cat:= EasterfieldPhi31 (p);
X cat:= EasterfieldPhi32 (p);
X cat:= EasterfieldPhi33 (p);
X cat:= EasterfieldPhi34 (p);
X cat:= EasterfieldPhi35 (p);
X cat:= EasterfieldPhi36 (p);
X cat:= EasterfieldPhi37 (p);
X cat:= EasterfieldPhi38 (p);
X cat:= EasterfieldPhi39 (p);
X cat:= EasterfieldPhi40 (p);
X cat:= EasterfieldPhi41 (p);
X cat:= EasterfieldPhi42 (p);
X cat:= EasterfieldPhi43 (p);

expected := 3*p^2+39*p+344+24*Gcd(p-1,3)+11*Gcd(p-1,4)+2*Gcd(p-1,5);
assert #X eq expected;

return X;

end function;


intrinsic Internal_p6_list(p::RngIntElt) -> SeqEnum
{For internal use}
    return GroupsOfOrderp6(p);
end intrinsic;

