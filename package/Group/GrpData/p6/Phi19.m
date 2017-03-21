freeze;
 
/* James list for Phi19 */

import "misc.m": NonQuadraticResidue, EasterfieldPair;



JamesPhi19 := function(p)

   Z := Integers ();

   K := GF(p);
 
   nu := Z ! (NonQuadraticResidue (p)); 

   g := PrimitiveRoot(p);

   F<al, al1, al2, be, be1, be2> := Group<
      al, al1, al2, be, be1, be2 |
      (al1,al2) = be,
      (be,al1) = be1,
      (be,al2) = be2,
      (al,al1) = be1,
      (al,al2) 
   >;

   E := [];
   labels := [];

   count := 0;
   lcount := 0;
   countvec := [];

   label := "(2211)a";
   llabel := [1]; //hack
   Append(~E, [0,0,1,0,0,1]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)br";

   for r in [1..(p-1) div 2] do
      llabel := [r];
      Append(~E, [0,0,1,0,0,(g^r mod p)]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)crs";

   for r in [1,nu] do
      for s in [2..(p-1)] do
         llabel := [r,s];
         Append(~E, [0,0,1,r,0,s]);
         count := count+1;
         lcount := lcount+1;
         Append (~labels, <label, llabel, lcount, count>);
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)d000";
   llabel := [];
   Append(~E, [0,0,0,nu,-nu,0]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)dr0t";

   for r in [1,nu] do
      for t in [1..(p-1)] do
         if (1+4*r*t) mod p ne 0 and IsPower(K!(1+4*r*t),2) eq true then
            llabel := [r,t];
            Append(~E, [0,0,1,r,t,0]);
            count := count+1;
            lcount := lcount+1;
            Append (~labels, <label, llabel, lcount, count>);
         end if;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)drst";

   for r in [1,nu] do
      for s in [1..p-1] do
         for t in [0..(p-1) div 2] do
            k := g^t mod p;
            flag := false;
            if (k mod p) ne (r*s) mod p and ((1-k)^2+4*r*s) mod p ne 0 
               and IsPower(K!((1-k)^2+4*r*s),2) eq true then
               flag := true;
               if r eq nu and k in [1,p-1] and IsPower(K!(-s),2) then
                  flag := false;
               end if;
            end if;
            if flag eq true then
               llabel := [r,s,t];
               Append(~E, [0,0,1,r,s,k]);
               count := count+1;
               lcount := lcount+1;
               Append (~labels, <label, llabel, lcount, count>);
            end if;
         end for;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)er";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [0,0,1,r,0,1]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)fr0"; // cf. dr0t

   for r in [1,nu] do
      for t in [0..(p-1)] do
         if (1+4*r*t) mod p eq 0 then
            llabel := [r,t];
            Append(~E, [0,0,1,r,t,0]);
            count := count+1;
            lcount := lcount+1;
            Append (~labels, <label, llabel, lcount, count>);
         end if;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)frs";

   for r in [1,nu] do
      for s in [1..(p-3) div 2] do
         for t in [0..(p-1) ] do
            k := g^s mod p;
            if (4*r*t + (1-k)^2) mod p eq 0 then
               llabel := [r,s,t];
               Append(~E, [0,0,1,r,t,k]);
               count := count+1;
               lcount := lcount+1;
               Append (~labels, <label, llabel, lcount, count>);
            end if;
         end for;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)gr00";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [0,0,0,1,r,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
    end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)gr0t";

   for r in [1,nu] do
      for t in [1..(p-1)] do
         if IsPower(K!(1+4*r*t),2) eq false then
            llabel := [r,t];
            Append(~E, [0,0,1,r,t,0]);
            count := count+1;
            lcount := lcount+1;
            Append (~labels, <label, llabel, lcount, count>);
         end if;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)grst";

   for r in [1,nu] do
      for s in [1..p-1] do
         for t in [0..(p-1) div 2] do
            k := g^t mod p;
            flag := false;
            if (k mod p) ne (r*s) mod p and
               IsPower(K!((1-k)^2+4*r*s),2) eq false then
               flag := true;
               if r eq nu and k in [1,p-1] and IsPower(K!(-s) ,2) then
                  flag := false;
               end if;
            end if;
            if flag eq true then
               llabel := [r,s,t];
               Append(~E, [0,0,1,r,s,k]);
               count := count+1;
               lcount := lcount+1;
               Append (~labels, <label, llabel, lcount, count>);
            end if;
         end for;
       end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)hr";

   for r in [1..(p-1) ] do
      llabel := [r];
      Append(~E, [1,0,0,r,0,1]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)i";

   llabel := [1];
   Append(~E, [1,0,0,0,0,1]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)jr";

   for r in [1..(p-1) div 2] do
      llabel := [r];
      Append(~E, [1,1,r,0,0,r]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)krs";

   for r in [1..p-1] do
      for s in [0..(p-1) div 2] do
         if (s-r) mod p ne 0 and (2*r-s) mod p ne 0 then
            llabel := [r,s];
            Append(~E, [1,1,r,0,0,s-r]);
            count := count+1;
            lcount := lcount+1;
            Append (~labels, <label, llabel, lcount, count>);
         end if;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)lr";

   for r in [1..(p-1) ] do
      llabel := [r];
      Append(~E, [1,1,r,0,0,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(2211)mr";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [1,0,0,r,0,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)a";

   llabel := [1];
   Append(~E, [0,0,1,0,0,0]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)br";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [0,0,1,r,0,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)cr";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [0,0,1,0,r,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)drs";

   for r in [1,nu] do
      for s in [0..(p-3) div 2] do
         gg := g^s mod p;
         for u in [1..p-1] do
            if (r*u) mod p eq 1 then
               if not (p mod 4 eq 3 and r eq nu and s eq 0) then 
                  llabel := [r,s];
                  Append(~E, [0,0,1,r,(u*gg mod p),gg]);
                  count := count+1;
                  lcount := lcount+1;
                  Append (~labels, <label, llabel, lcount, count>);
               end if;
            end if;
         end for;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)er";

   for r in [1,nu] do
      llabel := [r];
      Append(~E, [0,0,0,r,0,0]);
      count := count+1;
      lcount := lcount+1;
      Append (~labels, <label, llabel, lcount, count>);
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)fr";

   for r in [1,nu] do
      for u in [1..p-1] do
         if (r*u) mod p eq 1 then
            llabel := [r];
            Append(~E, [0,0,1,r,-u,-1]);
            count := count+1;
            lcount := lcount+1;
            Append (~labels, <label, llabel, lcount, count>);
         end if;
      end for;
   end for;

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)g";

   llabel := [1];
   Append(~E, [1,0,0,0,0,0]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(21111)h";

   llabel := [1];
   Append(~E, [1,1,0,0,0,0]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   label := "(1^6)";

   llabel := [];
   Append(~E, [0,0,0,0,0,0]);
   count := count+1;
   lcount := lcount+1;
   Append (~labels, <label, llabel, lcount, count>);

   Append (~countvec, lcount);
   lcount := 0;

   Pres := [];

   for i in [1..count] do
      // if i mod 100 eq 0 then "setup ", i; end if;
      e := E[i];
      G := quo<F|
      al^p = be1^e[1]*be2^e[2],
      al1^p = be1^e[3]*be2^e[4],
      al2^p = be1^e[5]*be2^e[6]>;
      Append(~Pres, pQuotient(G,p,3));
   end for;

   return Pres, labels, count, countvec;
end function;
