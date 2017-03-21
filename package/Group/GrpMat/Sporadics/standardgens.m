freeze;

digits := {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9" };

parse_L2p := function(str)
    if #str gt 2 and
	str[1..2] eq "L2" and forall{i:i in [3..#str] | str[i] in digits}
    then
	p := StringToInteger(str[3..#str]);
	if p ge 7 and p le 10000 and IsPrime(p) then
	    return true, "L2", p;
	else
	    return false, _, _;
	end if;
    elif #str gt 3 and
	str[1..3] eq "2L2" and forall{i:i in [4..#str] | str[i] in digits}
    then
	p := StringToInteger(str[4..#str]);
	if p ge 7 and p le 10000 and IsPrime(p) then
	    return true, "2L2", p;
	else
	    return false, _, _;
	end if;
    else
	return false, _, _;
    end if;
end function;

StandardGens := function(G, gpname : Projective:=false, MaxTries:=2000 )
/* Return standard generators a,b, as defined in the online ATLAS
 * http://brauer.maths.qmul.ac.uk/Atlas/v3/
 * of the (permutation or matrix) group G known to be isomorphic to
 * the nearly simple group with name "gpname".
 * the names are as returned by the Magma command ATLASGroupNames();
 * For matrix groups, if Projective is true, then work modulo scalars.
 * It works in the same way as StandardGenerators and
 * returns true/false, [a,b], [wa,wb],
 * where wa,wb are SLPs for a,b.
 */
  local O, CO, R, S, P, gens, z, a, b, bb, A, B, BB, c, C, d, D, oa, oA,
        o, seeking, nt, ct, tct, sct;
  nt := MaxTries;
  O := Projective select CentralOrder else Order;
  CO := CentralOrder;
  P := RandomProcessWithWords(G);
  R := function()
    x, X := Random(P);
    return x, X;
  end function;

/*
  S := SLPGroup(Ngens(G));
  gens := [G.i : i in [1..Ngens(G)]];
  P := RandomProcess(S);
  R := function()
       X := Random(P);
       x := Evaluate(X, gens);
       return x, X;
  end function;
*/

  F := function(n) //try to find an element of order n
    local ct;
    ct:=0;
    repeat ct+:=1;  a,A := R(); until O(a) mod n eq 0 or ct eq nt;
    if ct eq nt then return false, _, _; end if; 
    o := O(a) div n; a:=a^o; A:=A^o;
    return true, a, A;
  end function;

  Fb := function(n: nt := MaxTries)
               //try to find an element of order n not using powers
    local ct;
    ct:=0;
    repeat ct+:=1;  a,A := R(); until O(a) eq n or ct eq nt;
    if ct eq nt then return false, _, _; end if; 
    return true, a, A;
  end function;

  FC := function(n,m) //try to find an element of central order n, order m
    local ct, ct2;
    ct2:=0;
    repeat  ct2+:=1 ;
      ct:=0;
      repeat ct+:=1;  a,A := R();
             until O(a) mod m eq 0 and CO(a) mod n eq 0 or ct eq nt;
      if ct eq nt then return false, _, _; end if; 
      o := O(a) div m; a:=a^o; A:=A^o;
      if CO(a) eq n then
        return true, a, A;
      end if;
    until ct2 eq nt;
    if ct2 eq nt then return false, _, _; end if;
  end function;

    //deal with all of the L2p together
    fl, head, p := parse_L2p(gpname);
    if fl then
	if head eq "L2" then
	  z,a,A := F(2);
	  if not z then return false,_,_; end if;
	  z,b,B := F(3);
	  if not z then return false,_,_; end if;
	  bb := b; BB := B;
	  ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
		 until O(a*b) eq p or ct eq nt;
	  if ct eq nt then return false, _, _; end if;
	  return true, [a,b], [A,B];
	elif head eq "2L2" then
	  z,a,A := F(4);
	  if not z then return false,_,_; end if;
	  z,b,B := F(3);
	  if not z then return false,_,_; end if;
	  bb := b; BB := B;
	  ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
		 until O(a*b) eq p or ct eq nt;
	  if ct eq nt then return false, _, _; end if;
	  return true, [a,b], [A,B];
	else
	    error "This cannot happen!!";
	end if;
    end if;

  case gpname:
   when "A5": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 5 or ct eq nt;
   when "2A5": 
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 5 or ct eq nt;
   when "A6": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 5 or ct eq nt;
   when "2A6": 
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(8);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 5 and O(a*b^2) eq 5 or ct eq nt;
   when "3A6": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 5 or ct eq nt;
     assert O(a*b) eq 15;
   when "6A6": 
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(8);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 15 and O(a*b^2) eq 5 or ct eq nt;
   when "L28": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "A7": 
     z,a,A := F(6); //to square into Class 3A
     if not z then return false,_,_; end if;
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "2A7": 
     z,a,A := FC(6,12); //to square into Class 3A
     if not z then return false,_,_; end if;
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "3A7": 
     z,a,A := FC(6,6); //to square into Class 3A
     if not z then return false,_,_; end if;
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "6A7": 
     z,a,A := FC(6,12); //to square into Class 3A
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "L216": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 15 or ct eq nt;
   when "L33": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     //need b in Class 3B, but cannot check that directly!
     seeking:=true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,b,B := Fb(3);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 13 and O(a*b*a*b^2) eq 4 then
           seeking:=false; break;
         end if;
       end for;
     end while;
   when "U33": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(6);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "L225":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,25), a order 2, b order 3, order(ab)=12.
//standard generators for SL(2,25), a order 4, b order 3, order(ab)=24,
//order(abab^-1ab) = 13.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 12 or ct eq nt;
   when "2L225":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 12 and O(a*b) eq 24 and O(a*b*a*b^-1*a*b) eq 13
                  or ct eq nt;
   when "M11": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 and O(a*b*a*b^2*a*b^3) eq 5 or ct eq nt;
   when "L227": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "2L227": 
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "A8": 
     z,a,A := F(15); //to power into 3A
     if not z then return false,_,_; end if;
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 6 and O(a*b^2) eq 15 or ct eq nt;
   when "2A8": 
     z,a,A := F(15); //to power into 3A
     if not z then return false,_,_; end if;
     o := O(a) div 3; a:=a^o; A:=A^o;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 6 and CO(a*b^2) eq 15 or ct eq nt;
     assert O(a*b) eq 6 and O(a*b^2) eq 30;
   when "L34": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and O(a*b^2) eq 5 or ct eq nt;
   when "3L34": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 7 and CO(a*b^2) eq 5 or ct eq nt;
     assert O(a*b) eq 21 and O(a*b^2) eq 5;
   when "2L34": //this one is tricky! 
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 and CO(a*b*a*b*a*b^3) eq 5 then
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 14 then b *:= (a*b)^7; B *:= (A*B)^7; end if;
            if O(a*b*a*b*a*b^3) eq 5 then
              assert O(a*b) eq 7 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5;
              seeking:=false; break;
            end if;
         end if;
       end for;
     end while;
     assert O(a*b) eq 7 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5;
   when "4aL34":
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 then
            if O(a*b^2) eq 20 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 28 then b *:= (a*b)^7; B *:= (A*B)^7; end if;
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 14 then b *:= (a*b)^7; B *:= (A*B)^7; end if;
            assert O(a*b) eq 7 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5;
            seeking:=false; break;
         end if;
         if O(a*b) eq 7 and O(a*b^2) eq 5 then
            seeking:=false; break;
         end if;
       end for;
     end while;
   when "4bL34":
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 then
            if O(a*b^2) eq 20 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 28 then b *:= (a*b)^7; B *:= (A*B)^7; end if;
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 14 then b *:= (a*b)^7; B *:= (A*B)^7; end if;
            assert O(a*b) eq 7 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 10;
            seeking:=false; break;
         end if;
       end for;
     end while;
   when "6L34":
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 and CO(a*b*a*b*a*b^3) eq 5 then
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 42 then b *:= (a*b)^21; B *:= (A*B)^21; end if;
            if O(a*b*a*b*a*b^3) eq 5 then
              assert O(a*b) eq 21 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5;
              seeking:=false; break;
            end if;
         end if;
       end for;
     end while;
     assert O(a) eq 2 and O(b) eq 4 and O(a*b) eq 21 and
            O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5;
   when "12aL34":
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 then
            if O(a*b^2) eq 20 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 84 then b *:= (a*b)^21; B *:= (A*B)^21; end if;
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 42 then b *:= (a*b)^21; B *:= (A*B)^21; end if;
            if O(a*b) eq 21 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 5 then
              seeking:=false; break;
            end if;
         end if;
       end for;
     end while;
   when "12bL34":
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;  
         if CO(a*b) eq 7 and CO(a*b^2) eq 5 then
            if O(a*b^2) eq 20 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 84 then b *:= (a*b)^21; B *:= (A*B)^21; end if;
            if O(a*b^2) eq 10 then a *:= (a*b^2)^5; A *:= (A*B^2)^5; end if;
            if O(a*b) eq 42 then b *:= (a*b)^21; B *:= (A*B)^21; end if;
            if O(a*b) eq 21 and O(a*b^2) eq 5 and O(a*b*a*b*a*b^3) eq 10 then
              seeking:=false; break;
            end if;
         end if;
       end for;
     end while;
   when "U42", "S43":
     z,a,A := F(12); //to power into 2A
     if not z then return false,_,_; end if;
     o := O(a) div 2; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 9 or ct eq nt;
   when "2U42", "2S43":
     z,a,A := FC(12,12); //to power into 2A
     if not z then return false,_,_; end if;
     o := O(a) div 2; a:=a^o; A:=A^o;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 9 or ct eq nt;
   when "Sz8":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,b,B := F(4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 5 and O(a*b^2) eq 7 and O(a*b*a*b^3*a*b^2) eq 7 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "2Sz8":
     z,a,A := FC(2,2);
     if not z then return false,_,_; end if;
     o := O(a) div 2; a:=a^o; A:=A^o;
     seeking := true; ct:=0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false, _, _; end if;
       z,b,B := FC(4,4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 5 and O(a*b^2) eq 7 and O(a*b*a*b^3*a*b^2) eq 7 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "L232": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 31 and O(a*b*a*b^2) eq 11 or ct eq nt;
   when "L249":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 25 and O(a*b*a*b^2) eq 24 or ct eq nt;
   when "2L249":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 25 and O(a*b*a*b^2) eq 48 or ct eq nt;
   when "U34":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 or ct eq nt;
   when "M12":
     z,a,A := F(4); //squares into 2B
     if not z then return false,_,_; end if;
     a:=a^2; A:=A^2;
     //elements b in Class 3B are products of two elements in Class 2A
     z,bb,BB := F(10); //fifth power in 2A
     if not z then return false,_,_; end if;
     bb:=bb^5; BB:=BB^5;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(b*bb) eq 3;
     if ct eq nt then return false,_,_; end if;
     b := b*bb; B := B*BB;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11;
   when "2M12":
     z,a,A := FC(4,4); //squares into 2B
     if not z then return false,_,_; end if;
     a:=a^2; A:=A^2;
     //elements b in Class 3B are products of two elements in Class 2A
     z,bb,BB := FC(10,20); //fifth power in 2A
     if not z then return false,_,_; end if;
     bb:=bb^5; BB:=BB^5;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(b*bb) eq 3 and O(b*bb) eq 6;
     if ct eq nt then return false,_,_; end if;
     b := b*bb; B := B*BB;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11;
   when "U35":
     z,a,A := F(3);
     if not z then return false,_,_; end if;
     z,b,B := F(10); //to power into 5A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "3U35":
     z,a,A := FC(3,3); 
     if not z then return false,_,_; end if;
     z,b,B := F(10); //to power into 5A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "J1":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and Order(a*b*a*b^2) eq 19 or ct eq nt;
   when "A9":
     z,a,A := F(12); //to power into 3A
     a:=a^4; A:=A^4;
     if not z then return false,_,_; end if;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 9 or ct eq nt;
   when "2A9":
     z,a,A := FC(12,24); //to power into 3A
     a:=a^4; A:=A^4;
     if not z then return false,_,_; end if;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 9 or ct eq nt;
   when "L264":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,64), a order 2, b order 3, order(ab)=12,
//order [a,b]=13.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 63 and Order((a,b)) eq 13 or ct eq nt;
   when "L281":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,81), a order 2, b order 3, order(ab)=20.
//standard generators for SL(2,81), a order 4, b order 3, order(ab)=40,
//order(ababab^-1) = 41.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 20 or ct eq nt;
   when "2L281":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 40 and Order(a*b*a*b*a*b^-1) eq 41 or ct eq nt;
   when "L35":
     z,a,A := F(3);
     if not z then return false,_,_; end if;
     z,b,B := F(10); //to power into 5A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 20 or ct eq nt;
   when "M22":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(8); //to power into 4A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 and O(a*b*a*b^2) eq 11 or ct eq nt;
   when "2M22":
     z,a,A := F(8); //to power into class +2A
     if not z then return false,_,_; end if;
     a:=a^4; A:=A^4;
     z,b,B := F(8); //to power into 4A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     //we need to multiply this by the central element, which we
     //get as a power of an element of order 10,14 or 22
     ct:=0; repeat ct+:=1;  c,C := R(); until O(c) in {10,14,22} or ct eq nt;
     if ct eq nt then return false,_,_; end if;
     b := b * c^(Order(c) div 2); B := B * C^(Order(c) div 2);
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 and O(a*b*a*b^2) eq 11 or ct eq nt;
   when "3M22":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(8); //to power into 4A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 11 and CO(a*b*a*b^2) eq 11 or ct eq nt;
   when "6M22":
     z,a,A := F(8); //to power into class +2A
     if not z then return false,_,_; end if;
     a:=a^4; A:=A^4;
     z,b,B := F(8); //to power into 4A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     //we need to multiply this by the central element, which we
     //get as a power of an element of order 10,14,22,30,42,66
     ct:=0; repeat ct+:=1;  c,C := R();
            until O(c) in {10,14,22,30,42,66} or ct eq nt;
     if ct eq nt then return false,_,_; end if;
     b := b * c^(O(c) div 2); B := B * C^(O(c) div 2);
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until CO(a*b) eq 11 and CO(a*b*a*b^2) eq 11 or ct eq nt;
   when "4M22":
     z,a,A := FC(2,2);
     if not z then return false,_,_; end if;
     z,b,B := FC(8,8);
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     //we need to multiply this by a central element of order 4, which we
     //get as a power of an element of order 20,48,44
     ct:=0; repeat ct+:=1;  c,C := R();
            until O(c) in {20,28,44} or ct eq nt;
     if ct eq nt then return false,_,_; end if;
     b := b * c^(O(c) div 4); B := B * C^(O(c) div 4);
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 and O(a*b*a*b^2) eq 11 or ct eq nt;
   when "12M22":
     z,a,A := FC(2,2);
     if not z then return false,_,_; end if;
     z,b,B := FC(8,8);
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     //we need to multiply this by a central element of order 4, which we
     //get as a power of an element of order 20,28,44, 60,84,132
     ct:=0; repeat ct+:=1;  c,C := R();
            until O(c) in {20,28,44,60,84,132} or ct eq nt;
     if ct eq nt then return false,_,_; end if;
     b := b * c^(O(c) div 4); B := B * C^(O(c) div 4);
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 33 and O(a*b*a*b^2) eq 33 or ct eq nt;
   when "J2":
     //2B and 3B elements are hard to find. We use a 2A element to
     //test them
     z,c,C := F(4);
     if not z then return false,_,_; end if;
     c := c^(O(c) div 2); //c in 2A
     seeking := true; ct2 := 0;
     while seeking do
       ct2 +:= 1;
       if ct2 eq nt then return false,_,_; end if;
       ct:=0; repeat ct+:=1; a,A := R(); until O(a) in {2,6,10} or ct eq nt;
       if ct eq nt then return false,_,_; end if;
       o := O(a); a := a^(o div 2); A := A^(o div 2);
       if not O(a*c) in {1,2,3,4,5} then //a is in 2B
          seeking:=false; break;
       end if;
     end while;
     seeking := true; ct2 := 0;
     while seeking do
       ct2 +:= 1;
       if ct2 eq nt then return false,_,_; end if;
       ct:=0; repeat ct+:=1; b,B := R(); until O(b) in {3,6} or ct eq nt;
       if ct eq nt then return false,_,_; end if;
       o := O(b); b := b^(o div 3); B := B^(o div 3);
       if not O(b*c) in {6,12} then //b is in 3B
          seeking:=false; break;
       end if;
     end while;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and O(a*b*a*b^2) eq 12 or ct eq nt;
   when "2J2":
     //projective 3B elements are hard to find. We use a 2A element to
     //test them
     z,c,C := FC(2,2); //c in 2A
     if not z then return false,_,_; end if;
     z,a,A := FC(2,4); //c in 2B
     if not z then return false,_,_; end if;
     seeking := true; ct2 := 0;
     while seeking do
       ct2 +:= 1;
       if ct2 eq nt then return false,_,_; end if;
       ct:=0; repeat ct+:=1; b,B := R(); until CO(b) in {3,6} or ct eq nt;
       if ct eq nt then return false,_,_; end if;
       o := O(b); b := b^(o div 3); B := B^(o div 3);
       if not CO(b*c) in {6,12} then //b is in 3B
          seeking:=false; break;
       end if;
     end while;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and CO(a*b*a*b^2) eq 12 or ct eq nt;
   when "L2121":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(121) are a and b where a has order 2,
//b has order 3, ab has order 15 and abab^-1 has order 61.
//Standard generators of the double cover 2.L2(121) = SL2(121) are preimages
//A and B where B has order 3,  and AB has order 15.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 15 and O(a*b*a*b^2) eq 61 or ct eq nt;
   when "2L2121":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 15 and CO(a*b*a*b^2) eq 61 or ct eq nt;
   when "L2125":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,121), a order 2, b order 3, order(ab)=63
//and Order(abab^2) = 7.
//standard generators for SL(2,121), preimages of a,b,
//a order 4, b order 3, order(ab)=63,
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 63 and O(a*b*a*b^2) eq 7 or ct eq nt;
   when "2L2125":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 63 and CO(a*b*a*b^2) eq 7 or ct eq nt;
   when "S44":
     z,a,A := F(10); //to power into 2A/B
     if not z then return false,_,_; end if;
     a := a^5; A := A^5;
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,b,B := Fb(5); //want it in Class 5E but cannot test this directly
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i in [1..20] do
          c,C := R(); b := bb^c; B := BB^C;
          if O(a*b) eq 17 and O(a*b*a*b^2) eq 15 then
             seeking := false; break;
          end if;
       end for;
     end while;
   when "S62":
     z,a,A := F(10); //to power into 2A
     if not z then return false,_,_; end if;
     a := a^5; A := A^5;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 9 or ct eq nt;
   when "2S62":
     z,a,A := FC(10,20); //to power into 2A
     if not z then return false,_,_; end if;
     a := a^5; A := A^5;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 9 or ct eq nt;
   when "A10":
     z,a,A := Fb(15); //to power into 3A
     a:=a^5; A:=A^5;
     if not z then return false,_,_; end if;
     z,b,B := F(9);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 8 and O(a*b^2) eq 12 or ct eq nt;
   when "2A10":
     z,a,A := FC(15,15); //to power into 3A
     a:=a^5; A:=A^5;
     if not z then return false,_,_; end if;
     z,b,B := F(9);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C; 
            until CO(a*b) eq 8 and CO(a*b^2) eq 12 or ct eq nt;
   when "L37":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 19 and O(a*b*a*b^2) eq 6 or ct eq nt;
   when "3L37":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := FC(3,3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 19 and CO(a*b*a*b^2) eq 6 or ct eq nt;
   when "L2128":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,128), a order 2, b order 3, order(ab)=43,
//order [a,b]=129.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 43 and Order((a,b)) eq 129 or ct eq nt;
   when "L2169":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(169) are a and b where a has order 2,
//b has order 3, ab has order 85 and abab^-1 has order 5.
//Standard generators of the double cover 2.L2(169) = SL2(169) are preimages
//A and B where B has order 3,  and AB has order 85.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 85 and O(a*b*a*b^2) eq 5 or ct eq nt;
   when "2L2169":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 85 and CO(a*b*a*b^2) eq 5 or ct eq nt;
   when "U43":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := Fb(12); //to power into 6A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 5 or ct eq nt;
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := FC(12,12); //to power into 6A
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 5 or ct eq nt;
   when "2U43":
     //not in ATLAS - standard generators are preimages A,B of a,b where
     //ABAB^2 has order 7 and AB^3 has order 5
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
          c,C := R(); b := bb^c; B := BB^C;
          if CO(a*b) eq 7 and CO((a*b)^3*(b*a)^2*b^2) eq 5
            and O(a*b*a*b^2) eq 7 and O(a*b^3) eq 5 then
             seeking := false; break;
          end if;
       end for;
     end while;
   when "3aU43":
     //not in ATLAS standard generators are A,B, preimages of a and b where
     //A,B,AB,ABABABBABABB,ABBABBBAB^-1 have orders 2, 6, 7, 5 and 5
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 5
              and O(a*b^2*a*b^3*a*b^-1) eq 5 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "3bU43":
     //not in ATLAS standard generators are A,B, preimages of a and b where
     //A,B,AB,ABABABBABABB,ABABBB have orders 2, 6, 7, 5 and 7
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 5
              and O(a*b*a*b^3) eq 7 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "4U43":
     //not in ATLAS - standard generators are preimages A,B of a,b where
     //ABAB^2 has order 7 and AB^3 has order 5
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := FC(2,2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
          c,C := R(); b := bb^c; B := BB^C;
          if CO(a*b) eq 7 and CO((a*b)^3*(b*a)^2*b^2) eq 5
            and O(a*b*a*b^2) eq 7 and O(a*b^3) eq 5 then
             seeking := false; break;
          end if;
       end for;
     end while;
   when "6aU43":
     //not in ATLAS standard generators are A,B, preimages of a and b where
     //A,B,AB,ABABABBABABB,ABBABBBAB^-1 have orders 2, 6, 7, 5 and 10
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 5
              and O(a*b^2*a*b^3*a*b^-1) eq 10 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "6bU43":
     //not in ATLAS standard generators are A,B, preimages of a and b where
     //A,B,AB,ABABABBABABB,ABABBB have orders 2, 6, 14, 10 and 14
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 14 and O((a*b)^3*(b*a)^2*b^2) eq 10
              and O(a*b*a*b^3) eq 14 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "12aU43":
     //not in ATLAS standard generators are A,B, preimages of a and b where
     //A,B,ABABB,ABABABBABABB,ABBABBBAB^-1 have orders 2, 6, 7, 20 and 5
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B := FC(12,12); //to power into 6A
       if not z then return false,_,_; end if;
       b:=b^2; B:=B^2;
       bb := b; BB := B;
       for i in [1..30] do
         c,C := R(); b := bb^c; B := BB^C;
         if  O(a*b*a*b^2) eq 7 and O((a*b)^3*(b*a)^2*b^2) eq 20
              and O(a*b^2*a*b^3*a*b^-1) eq 5 then
            seeking := false; break;
         end if;
       end for;
     end while;
   when "G23":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := Fb(9); //to power into 3C
     if not z then return false,_,_; end if;
     b := b^3; B := B^3;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 or ct eq nt;
   when "3G23":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := FC(9,9); //to power into 3C
     if not z then return false,_,_; end if;
     b := b^3; B := B^3;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 or ct eq nt;
   when "L2243":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(243) are a and b where a has order 2,
//b has order 3, ab has order 61 and abab^-1 has order 11.
//Standard generators of the double cover 2.L2(243) = SL2(243) are preimages
//A and B where B has order 3,  and AB has order 61.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 61 and O(a*b*a*b^2) eq 11 or ct eq nt;
   when "2L2243":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 61 and CO(a*b*a*b^2) eq 11 or ct eq nt;
   when "S45":
     //first get a in Class 2B
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b := F(3);
       if not z then return false,_,_; end if;
       for i in [1..20] do
         c := R();
         if O(a*b^c) in {3,5,13,15,20} then
            seeking := false; break; //a in Class 2B
         end if;
       end for;
     end while;
     //now get b in Class 3B
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,b,B := F(3);
       if not z then return false,_,_; end if;
       for i  in [1..20] do
         c := R();
         if O(a^c*b*a^c*b^2) in {6,15} then
            seeking := false; break; //b in Class 3B
         end if;
       end for;
     end while;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 and O(a*b*a*b^2) eq 12  or ct eq nt;
   when "2S45":
     z,a,A := FC(2,4); //inverse image of class 2B
     if not z then return false,_,_; end if;
     //now get b in Class 3B
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,b,B := FC(3,3);
       if not z then return false,_,_; end if;
       for i  in [1..20] do
         c := R();
         if CO(a^c*b*a^c*b^2) in {6,15} then
            seeking := false; break; //b in Class 3B
         end if;
       end for;
     end while;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 and CO(a*b*a*b^2) eq 12  or ct eq nt;
   when "U38":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,b,B := F(3); //must get in in 3C
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i  in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if CO(a*b) eq 19 then
            seeking := false; break; //b in Class 3B
         end if;
       end for;
     end while;
   when "3U38":
     z,a,A := FC(2,2);
     if not z then return false,_,_; end if;
     seeking := true; ct := 0;
     while seeking do
       ct +:= 1;
       if ct eq nt then return false,_,_; end if;
       z,b,B := FC(3,3); //must get in in 3C
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       for i  in [1..20] do
         c,C := R(); b := bb^c; B := BB^C;
         if O(a*b) eq 19 then
            seeking := false; break; //b in Class 3B
         end if;
       end for;
     end while;
   when "U37": 
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 43 and O(a*b*a*b^2) eq 4 or ct eq nt;
   when "L43":
     z,a,A := F(10); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := Fb(8); //to power into 4B
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 and O(a*b*a*b^2) eq 13 or ct eq nt;
   when "2L43":
     z,a,A := FC(10,20); //to power into 2A
     if not z then return false,_,_; end if;
     o:=CO(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := FC(8,8); //to power into 4B
     if not z then return false,_,_; end if;
     b:=b^2; B:=B^2;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 and O(a*b*a*b^2) eq 13 or ct eq nt;
   when "L52":
     z,a,A := F(8); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 5 or ct eq nt;
   when "M23":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(4);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 23 and O(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b) eq 8
                                                              or ct eq nt;
   when "L2289":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(289) are a and b where a has order 2,
//b has order 3, ab has order 29 and abab^-1 has order 72.
//Standard generators of the double cover 2.L2(289) = SL2(289) are preimages
//A and B where B has order 3,  and AB has order 29.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 29 and O(a*b*a*b^2) eq 72 or ct eq nt;
   when "2L2289":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 29 and CO(a*b*a*b^2) eq 72 or ct eq nt;
   when "L38":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 21 or ct eq nt;
   when "U52":
     z,a,A := F(8); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 or ct eq nt;
   when "L2256":
//Not in ATLAS database, so I have chosen my own standard generators
//standard generators for PSL(2,256), a order 2, b order 3, order(ab)=51,
//order [a,b]=85.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 51 and Order((a,b)) eq 85 or ct eq nt;
   when "TF42":
     z,a,A := F(10); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 or ct eq nt;
   when "A11":
     z,a,A := F(21); //to power into 3A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 3); A:=A^(o div 3);
     z,b,B := F(9);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 or ct eq nt;
   when "2A11":
     z,a,A := FC(21,21); //to power into 3A
     a:=a^7; A:=A^7;
     if not z then return false,_,_; end if;
     z,b,B := F(9);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C; 
            until CO(a*b) eq 11 or ct eq nt;
   when "L2343":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(343) are a and b where a has order 2,
//b has order 3, ab has order 19 and abab^-1 has order 171.
//Standard generators of the double cover 2.L2(343) = SL2(343) are preimages
//A and B where B has order 3,  and AB has order 19.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 19 and O(a*b*a*b^2) eq 171 or ct eq nt;
   when "2L2343":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 19 and CO(a*b*a*b^2) eq 72 or ct eq nt;
   when "Sz32":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     //not all elements of order 4 will work!
     ct:=0;
     repeat ct+:=1;
       z,b,B := F(4);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0;
       repeat sct+:=1;
          if sct eq 101 then break; end if;
          c,C := R(); b := bb^c; B := BB^C;
       until O(a*b) eq 5 and O(a*b^2) eq 25 and O(a*b*a*b^2*a*b^3) eq 25;
     until sct le 100 or ct eq nt;
   when "L2361":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(361) are a and b where a has order 2, b has
//order 3, ab has order 45 and abab^-1 has order 36.
//Standard generators of the double cover 2.L2(361) = SL2(361) are preimages
//A and B where B has order 3,  and AB has order 45.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 45 and O(a*b*a*b^2) eq 36 or ct eq nt;
   when "2L2361":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 45 and CO(a*b*a*b^2) eq 36 or ct eq nt;
   when "L39": //not in ATLAS, so must find standard generators!
     //a of order2, b order 5, ab order 3 works fine.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 3 or ct eq nt;
   when "U39":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(6);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 15 or ct eq nt;
   when "HS":
     z,a,A := F(4); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(20); //to power into 5A
     o:=O(b); b:=b^(o div 5); B:=B^(o div 5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 11 or ct eq nt;
   when "2HS":
     z,a,A := FC(4,4); //to power into 2A
     if not z then return false,_,_; end if;
     a:=a^2; A:=A^2;
     z,b,B := FC(20,20); //to power into 5A
     if not z then return false,_,_; end if;
     b:=b^4; B:=B^4;
     z,d,D := FC(3,6); //just to get the central element
     if not z then return false,_,_; end if;
     b:=b*d^3; B:=B*D^3;
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0;
     oa:=a; oA:=A;
     repeat
       a:=oa; A:=oA; sct:=0;
       while sct le 20 do sct+:=1;
           c,C := R(); b := bb^c; B := BB^C; 
           if  O(a*b) eq 11 then break; end if;
       end while;
       if sct gt 20 then
          a := a*d^3; A:=A*D^3; sct:=0;
          while sct le 20 do sct+:=1;
            c,C := R(); b := bb^c; B := BB^C; 
            if  O(a*b) eq 11 then break; end if;
          end while;
       end if;
     until sct le 20 or ct eq nt;
   when "J3":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(6); //to power into 3A
     if not z then return false,_,_; end if;
     o:=O(b); b:=b^(o div 3); B:=B^(o div 3);
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 19 and O(a*b*a*b^2) eq 9 or ct eq nt;
   when "3J3":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     ct := 0;
     repeat ct+:=1;
       z,b,B := FC(6,6);
       if not z then return false,_,_; end if;
       o:=O(b); b:=b^(o div 3); B:=B^(o div 3);
       bb := b; BB := B;
       sct:=0;
       while sct lt 20 do
         c,C := R(); b := bb^c; B := BB^C; 
         if CO(a*b) eq 19 and CO(a*b*a*b^2) eq 9 and
                                            O(a*b*a*b*a*b^2) eq 17 then
            break;
         end if;
         sct := sct+1;
       end while;
     until sct lt 20 or ct eq nt;
   when "U311":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 37 and O(a*b*a*b^2) eq 4 or ct eq nt;
   when "3U311":
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := FC(3,3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 37 and CO(a*b*a*b^2) eq 4 or ct eq nt;
   when "L2529":
//Not in ATLAS database, so I have chosen my own standard generators
//Standard generators of L2(529) are a and b where a has order 2,
//b has order 3, ab has order 53 and abab^-1 has order 264.
//Standard generators of the double cover 2.L2(529) = SL2(529) are preimages
//A and B where B has order 3,  and AB has order 53.
     z,a,A := F(2);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 53 and O(a*b*a*b^2) eq 264 or ct eq nt;
   when "2L2529":
     z,a,A := F(4);
     if not z then return false,_,_; end if;
     z,b,B := F(3);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 53 and CO(a*b*a*b^2) eq 264 or ct eq nt;
   when "S47":
     z,a,A := F(42); //to power into 2A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 7 or ct eq nt;
   when "2S47":
     z,a,A := FC(42,42); //to power into 3A
     if not z then return false,_,_; end if;
     o:=O(a); a:=a^(o div 2); A:=A^(o div 2);
     z,b,B := F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C; 
            until O(a*b) eq 7 or ct eq nt;
   when "O8p2":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(6);
       if not z then return false,_,_; end if;
       a := a^3; A := A^3;
       z,b,B := F(5);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 12 and O(a*b^2) eq 15 and
                   O(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b) eq 8) or sct eq 120;
     until sct lt 120 or ct eq nt;
   when "2O8p2":
     ct:=0;
     repeat ct+:=1;
       repeat z,a,A := Fb(6); until CO(a) eq 6;
       a := a^3; A := A^3;
       z,b,B := F(5);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (CO(a*b) eq 12 and O(a*b^2) eq 15 and O(a*b*a*b^2) eq 15 and
                   CO(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b) eq 8) or sct eq 120;
     until sct lt 120 or ct eq nt;
   when "2^2O8p2":
     ct:=0;
     repeat ct+:=1;
       repeat z,a,A := Fb(6); until CO(a) eq 6;
       a := a^3; A := A^3;
       z,b,B := F(5);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (CO(a*b) eq 12 and O(a*b^2) eq 15 and O(a*b*a*b^2) eq 30 and
                   CO(a*b*a*b*a*b*a*b*b*a*b*a*b*b*a*b*b) eq 8) or sct eq 120;
     until sct lt 120 or ct eq nt;
   when "O8p3":
     ct:=0;
     repeat ct+:=1;
       z,a,A := F(10);
       if not z then return false,_,_; end if;
       a := a^5; A := A^5;
       z,b,B := F(5);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 13 and O(a*b^2) eq 14) or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "2O8p3":
     ct:=0;
     repeat ct+:=1;
       repeat z,a,A := F(10); until CO(a) eq 10;
       if not z then return false,_,_; end if;
       a := a^5; A := A^5;
       z,b,B := F(5);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13  and Order(a*b^2) eq 28 or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "2^2O8p3":
     ct:=0;
     repeat ct+:=1;
       repeat z,a,A := F(10); until CO(a) eq 10;
       if not z then return false,_,_; end if;
       a := a^5; A := A^5;
       z,b,B := F(40);
       if not z then return false,_,_; end if;
       b := b^8; B := B^8;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until O(a*b) eq 13 or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "O8p4":
     //not in ATLAS - this i very bad - must try and improve
     z,a,A := F(34);
     if not z then return false,_,_; end if;
     a := a^17; A := A^17;
     z,b,B := F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
          until (O(a*b) eq 65 and O(a*b^2) eq 9 and Order(a*b*a*b^2) eq 17)
                                           or ct eq 200*nt;
     if ct eq 200*nt then return false,_,_; end if;
   when "O8m2":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(6);
       if not z then return false,_,_; end if;
       a := a^3; A := A^3;
       //If C(a) has element of order 5, then this is no good
       nogood := false;
       for i in [1..50] do
         repeat x:=Random(G); b:=a^x; o:=Order(a*b); until IsOdd(o);
         y:=x*((a*b)^((o-1) div 2));
         if Order(y) mod 5 eq 0 then nogood:=true; break;end if;
       end for;
       if nogood then sct:=50; continue; end if;
       z,b,B := F(9); //to cube into 3C
       if not z then return false,_,_; end if;
       b := b^3; B := B^3;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 17 and O(a*b*a*b^2) eq 17 and
                   O(a*b*a*b*a*b*b) eq 30) or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "O8m3":
     ct:=0;
     repeat ct+:=1;
       z,a,A := F(26);
       if not z then return false,_,_; end if;
       //13th power is in Class 2A
       a := a^13; A := A^13;
       tct := 0; repeat tct +:=1; z,b,B := Fb(4:nt:=10*nt);
         if not z then return false,_,_; end if;
       //only b in Class 4F will give O(a*b) = 41
         sct := 0; repeat sct+:=1;  c := Random(G);
         until O(a*b^c) eq 41 or sct eq 20;
       until O(a*b^c) eq 41 or tct eq nt;
       z := O(a*b^c) eq 41;
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 41 and O(a*b^2) eq 6 and O(a*b*a*b^2) eq 41)
                      or sct eq 120;
      until sct lt 120 or ct eq nt;
   when "2O8m3":
     ct:=0;
     repeat ct+:=1;
       z,a,A := F(52);
       if not z then return false,_,_; end if;
       //13th power is in inverse image of Class 2A
       a := a^13; A := A^13;
       tct := 0; repeat tct +:=1; z,b,B := Fb(4:nt:=10*nt);
         if not z then return false,_,_; end if;
       //only b in Class 4F will give O(a*b) = 41
         sct := 0; repeat sct+:=1;  c := Random(G);
         until O(a*b^c) eq 41 or sct eq 20;
       until O(a*b^c) eq 41 or tct eq nt;
       z := O(a*b^c) eq 41;
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 41 and O(a*b^2) eq 12 and O(a*b*a*b^2) eq 41)
                      or sct eq 120;
      until sct lt 120 or ct eq nt;
   when "O8m4":
     //not in ATLAS
     ct:=0;
     z,a,A := F(60);
     if not z then return false,_,_; end if;
     a := a^30; A := A^30;
     z,b,B := F(9);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 102 and O(a*b^2) eq 105) or ct eq 10*nt;
     if ct eq 10*nt then return false,_,_; end if;
   when "O10m2":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(18);
       if not z then return false,_,_; end if;
       a := a^9; A := A^9;
       //If C(a) has element of order 7, then this is no good
       nogood := false;
       for i in [1..50] do
         repeat x:=Random(G); b:=a^x; o:=Order(a*b); until IsOdd(o);
         y:=x*((a*b)^((o-1) div 2));
         if Order(y) mod 7 eq 0 then nogood:=true; break;end if;
       end for;
       if nogood then sct:=50; tct:=nt; continue; end if;
       tct := 0;
       repeat tct +:= 1;
         z,b,B := F(5); //could be in 5A
         if not z then return false,_,_; end if;
         bb := b; BB := B;
         sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 33 and O(a*b*a*b*a*b^2) eq 18) or sct eq 20;
       until sct lt 20 or tct eq nt;
     until tct lt nt or ct eq nt;
   when "S82":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(24);
       if not z then return false,_,_; end if;
       a := a^12; A := A^12; //a is in 2B
       tct := 0;
       repeat tct +:= 1;
         z,b,B := F(5); //could be in 5A - want it in 5B
         if not z then return false,_,_; end if;
         bb := b; BB := B;
         sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
            until (O(a*b) eq 17 and O(a*b^2) eq 21) or sct eq 20;
       until sct lt 20 or tct eq nt;
     until tct lt nt or ct eq nt;
   when "U62":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(10);
       if not z then return false,_,_; end if;
       //5th power is in Class 2A
       a := a^5; A := A^5;
       if Projective then
         aa:=a; AA:=A;
         while Order(a) ne 2 do a:=a*(aa^2); A:=A*(AA)^2; end while;
       end if;
       z,b,B:= Fb(7);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       if Projective then
         bb:=b; BB:=B;
         while Order(b) ne 7 do b:=b*(bb^7); B:=B*(BB^7); end while;
       end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 11 and O(a*b^2) eq 18) or sct eq 120;
      until sct lt 120 or ct eq nt;
   when "3U62":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(10);
       if not z then return false,_,_; end if;
       //5th power is in Class 2A
       a := a^5; A := A^5;
       z,b,B:= Fb(7);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 33 and O(a*b^2) eq 18) or sct eq 120;
      until sct lt 120 or ct eq nt;
   when "U72":
     ct:=0;
     repeat ct+:=1;
       z,a,A := Fb(10);
       if not z then return false,_,_; end if;
       //5th power is in Class 2A
       a := a^5; A := A^5;
       z,b,B:= Fb(7);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1;  c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 33 and O(a*b^2) eq 45) or sct eq 120;
      until sct lt 120 or ct eq nt;
   when "U82":
     z,a,A := F(14);
     if not z then return false,_,_; end if;
     a := a^7; A := A^7;
     z,b,B:= F(14);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 85 and O(a*b^2) eq 18) or ct eq nt;
   when "U92":
     //standardgens due to Rob Wilson
     z,a,A := Fb(86);
     if not z then return false,_,_; end if;
     a := a^43; A := A^43;
     z,b,B:= F(19);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 19 and O(a*b*a*b^2) eq 90) or ct eq nt;
   when "3U92":
     //standardgens due to Rob Wilson
     z,a,A := Fb(86);
     if not z then return false,_,_; end if;
     a := a^43; A := A^43;
     z,b,B:= F(19);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until O(a*b) eq 19 or ct eq nt;
   when "U53":
     z,a,A := Fb(21);
     if not z then return false,_,_; end if;
     a := a^7; A := A^7;
     z,b,B:= F(5);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until O(a*b) eq 16 or ct eq nt;
   when "S64":
     //SG not in ATLAS
     z,a,A := Fb(34);
     if not z then return false,_,_; end if;
     a := a^17; A := A^17;
     z,b,B:= F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until O(a*b) eq 13 or ct eq nt;
   when "S65":
     z,a,A := F(26);
     if not z then return false,_,_; end if;
     a := a^13; A := A^13;
     z,b,B:= F(40);
     if not z then return false,_,_; end if;
     b := b^5; B := B^5;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 9 and O(a*b*a*b*a*b*b*a*b*b) eq 15) or ct eq 2*nt;
     if ct eq 2*nt then return false,_,_; end if;
   when "2S65":
     ct := 0;
     repeat ct +:= 1;
       z,a,A := F(26);
       if not z then return false,_,_; end if;
       a := a^13; A := A^13;
       z,b,B:= F(40);
       if not z then return false,_,_; end if;
       b := b^5; B := B^5;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1; c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 9 and O(a*b^2) eq 31) or sct eq 120;
     until sct lt 120 or ct eq nt;
   when "S83":
     ct := 0;
     repeat ct +:= 1;
       z,a,A := F(2);
       if not z then return false,_,_; end if;
       z,b,B:= F(28);
       if not z then return false,_,_; end if;
       b := b^7; B := B^7;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1; c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 14 and Order((a,b)) eq 9) or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "2S83":
     ct := 0;
     repeat ct +:= 1;
       repeat z,a,A := F(2); until CO(a) eq 2;
       if not z then return false,_,_; end if;
       repeat z,b,B:= F(28); until CO(b) eq 28;
       if not z then return false,_,_; end if;
       b := b^7; B := B^7;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1; c,C := R(); b := bb^c; B := BB^C;
       until (O((a,b)) eq 9 and O(a*b^3*(a*b)^4) eq 9 and
              O(a*b*a*b^2*a*b) eq 78) or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "S122":
     //not in ATLAS
     z,a,A := F(62);
     if not z then return false,_,_; end if;
     a := a^31; A := A^31;
     z,b,B:= F(13);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 15 and O((a,b)) eq 3) or ct eq nt;
   when "O75":
     //not in ATLAS
     z,a,A := F(62);
     if not z then return false,_,_; end if;
     a := a^31; A := A^31;
     z,b,B:= F(7);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 31 and O((a,b)) eq 2) or ct eq nt;
   when "O93":
   //different from standard gens in ATLAS, which used b in Class 9N/O
     ct := 0;
     repeat ct +:= 1;
       z,a,A := F(40);
       if not z then return false,_,_; end if;
       a := a^20; A := A^20; //into 2A or 2D - want 2A
       z,b,B:= F(21);
       if not z then return false,_,_; end if;
       bb := b; BB := B;
       sct:=0; repeat sct+:=1; c,C := R(); b := bb^c; B := BB^C;
       until (O(a*b) eq 15 and O((a,b)) eq 3) or sct eq 50;
     until sct lt 50 or ct eq nt;
   when "O10p2":
     //not in ATLAS
     z,a,A := F(60);
     if not z then return false,_,_; end if;
     a := a^30; A := A^30;
     z,b,B:= F(18);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 31 and O(a*b^2) eq 24 and O(a*b*a*b^2) eq 51 and
               O(a*b*a*b^2*a*b^3) eq 9) or ct eq 5*nt;
     if ct eq 5*nt then return false,_,_; end if;
   when "O12p2":
     //not in ATLAS
     z,a,A := F(34);
     if not z then return false,_,_; end if;
     a := a^17; A := A^17;
     z,b,B:= F(35);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 105 and O(a*b^2) eq 21 and O(a*b*a*b^2*a*b^3) eq 60)
                       or ct eq 20*nt;
     if ct eq 20*nt then return false,_,_; end if;
   when "O12m2":
     //not in ATLAS
     z,a,A := F(102);
     if not z then return false,_,_; end if;
     a := a^51; A := A^51;
     z,b,B:= F(35);
     if not z then return false,_,_; end if;
     bb := b; BB := B;
     ct:=0; repeat ct+:=1; c,C := R(); b := bb^c; B := BB^C;
     until (O(a*b) eq 65 and O(a*b^2) eq 65 and O(a*b*a*b^2) eq 24 and
            O(a*b*a*b^2*a*b^3) eq 42) or ct eq 20*nt;
     if ct eq 20*nt then return false,_,_; end if;
   else gpname,
     "is not a valid identifier for a small quasisimple or sporadic group";
   return false,_,_;
  end case;
  if ct eq nt then return false, _, _; end if;
  return true, [a,b], [A,B];
end function;

CheckSG := function(G,a,b,aa,bb)
//for checking standard generators applied to G.
//Do a quick check to see if the map a->aa, b->bb appears to be a homomorphism
  F:=FreeGroup(2);
  h1:=hom<F->G|a,b>; h2:=hom<F->G|aa,bb>;
  for i in [1..100] do
    g := Random(F,30,50); 
    if Order(h1(g)) ne Order(h2(g)) then
      "NOT A HOMOMORPHISM!";
      return false;
    end if;
  end for;
  return true;
end function;

CheckSGGrp := function(s : G:=Sym(1))
//Check standard generators code of ATLAS group s.
  if Type(G) eq GrpPerm and Degree(G) eq 1  then
    if #PermRepKeys(ATLASGroup(s)) gt 0 then
      G:=X^Random(Sym(Degree(X))) where X:=PermutationGroup(s,1);
    elif #MatRepKeys(ATLASGroup(s)) gt 0 then
      G:=X^Random(GL(Dimension(X),BaseRing(X))) where X:=MatrixGroup(s,1);
    else "No ATLAS representation of",s,"available";
      return false;
    end if;
  end if;
  gens := [G.i : i in [1..Ngens(G)]];
  isit := false;
  repeat  isit, l1, l2 :=StandardGens(G,s);
  if not isit then "ERROR";end if;until isit;
  a:=l1[1]; b:=l1[2];
  assert Evaluate(l2[1],gens) eq a and Evaluate(l2[2],gens) eq b;
  for i in [1..50] do
i;
    repeat  isit, l1, l2 := StandardGens(G,s);
     if not isit then "ERROR";end if; until isit;
    if isit and not CheckSG(G,a,b,l1[1],l1[2]) then
      "FATAL ERROR!";
      return false;
    end if;
  end for;
  return true;
end function;

intrinsic StandardCopy(gpname :: MonStgElt) -> Grp, BoolElt  
{The standard copy of gpname + flag to indicate whether projective or not}

    //deal with all of the L2p together
    fl, head, p := parse_L2p(gpname);
    if fl then
	if head eq "L2" then
	  return SL(2,p), true;
	elif head eq "2L2" then
	  return SL(2,p), false;
	end if;
    end if;

  case gpname:
   when "A5": 
     gp := Alt(5); proj :=false;
   when "2A5": 
     gp := SL(2,5); proj :=false;
   when "A6": 
     gp := Alt(6); proj :=false;
   when "2A6": 
     gp := SL(2,9); proj :=false;
   when "3A6": 
     gp := PermutationGroup("3A6",1); proj :=false;
   when "6A6": 
     gp := MatrixGroup("6A6",1); proj :=false;
   when "A7": 
     gp := Alt(7); proj :=false;
   when "2A7": 
     gp := MatrixGroup("2A7",1); proj :=false;
   when "3A7": 
     gp := PermutationGroup("3A7",1); proj :=false;
   when "6A7": 
     gp := MatrixGroup("6A7",1); proj :=false;
   when "A8": 
     gp := Alt(8); proj :=false;
   when "2A8": 
     gp := MatrixGroup("2A8",1); proj :=false;
   when "A9":
     gp := Alt(9); proj :=false;
   when "2A9":
     gp := MatrixGroup("2A9",1); proj :=false;
   when "A10":
     gp := Alt(10); proj :=false;
   when "2A10":
     gp := MatrixGroup("2A10",1);
   when "A11":
     gp := Alt(11); proj :=false;
   when "2A11":
     gp := MatrixGroup("2A11",1);
   when "L28": 
     gp := SL(2,8); proj :=false;
   when "L216": 
     gp := SL(2,16); proj :=false;
   when "U33": 
     gp := SU(3,3); proj :=false;
   when "L225":
     gp := SL(2,25); proj :=true;
   when "2L225":
     gp := SL(2,25); proj :=false;
   when "L227": 
     gp := SL(2,27); proj :=true;
   when "2L227": 
     gp := SL(2,27); proj :=false;
   when "L232": 
     gp := SL(2,32); proj :=false;
   when "L249":
     gp := SL(2,49); proj :=true;
   when "2L249":
     gp := SL(2,49); proj :=false;
   when "L2256":
     gp := SL(2,256); proj :=false;
   when "L264":
     gp := SL(2,64); proj :=false;
   when "L281":
     gp := SL(2,81); proj :=true;
   when "2L281":
     gp := SL(2,81); proj :=false;
   when "L2121":
     gp := SL(2,121); proj :=true;
   when "2L2121":
     gp := SL(2,121); proj :=false;
   when "L2125":
     gp := SL(2,125); proj :=true;
   when "2L2125":
     gp := SL(2,125); proj :=false;
   when "L2128":
     gp := SL(2,128); proj :=false;
   when "L2169":
     gp := SL(2,169); proj :=true;
   when "2L2169":
     gp := SL(2,169); proj :=false;
   when "L2243":
     gp := SL(2,243); proj :=true;
   when "2L2243":
     gp := SL(2,243); proj :=false;
   when "L2289":
     gp := SL(2,289); proj :=true;
   when "2L2289":
     gp := SL(2,289); proj :=false;
   when "L2343":
     gp := SL(2,343); proj :=true;
   when "2L2343":
     gp := SL(2,343); proj :=false;
   when "L2361":
     gp := SL(2,361); proj :=true;
   when "2L2361":
     gp := SL(2,361); proj :=false;
   when "L2529":
     gp := SL(2,529); proj :=true;
   when "2L2529":
     gp := SL(2,529); proj :=false;

   when "L33": 
     gp := SL(3,3); proj :=false;
   when "L34": 
     gp := SL(3,4); proj :=true;
   when "3L34": 
     gp := SL(3,4); proj :=false;
   when "2L34":
     gp := PermutationGroup("2L34",1); proj :=false;
   when "4aL34":
     gp := PermutationGroup("4aL34",1); proj :=false;
   when "4bL34":
     gp := PermutationGroup("4bL34",1); proj :=false;
   when "6L34":
     gp := PermutationGroup("6L34",1); proj :=false;
   when "12aL34":
     gp := PermutationGroup("12aL34",1); proj :=false;
   when "12bL34":
     gp := PermutationGroup("12bL34",1); proj :=false;
   when "L35":
     gp := SL(3,5); proj :=false;
   when "L37":
     gp := SL(3,7); proj :=true;
   when "3L37":
     gp := SL(3,7); proj :=false;
   when "L38":
     gp := SL(3,8); proj :=false;
   when "L39":
     gp := SL(3,9); proj :=false;
   when "L43":
     gp := SL(4,3); proj :=true;
   when "2L43":
     gp := SL(4,3); proj :=false;
   when "L52":
     gp := SL(5,2); proj :=false;

   when "U33":
     gp := SU(3,3); proj :=false;
   when "U34":
     gp := SU(3,4); proj :=false;
   when "U35":
     gp := SU(3,5); proj :=true;
   when "U37":
     gp := SU(3,7); proj :=false;
   when "U38":
     gp := SU(3,8); proj :=true;
   when "3U38":
     gp := SU(3,8); proj :=false;
   when "U39":
     gp := SU(3,9); proj :=false;
   when "U311":
     gp := SU(3,11); proj :=true;
   when "3U311":
     gp := SU(3,11); proj :=false;
   when "U42":
     gp := SU(4,2); proj :=false;
   when "2U42":
     gp := Sp(4,3); proj :=false;
   when "U43":
     gp := SU(4,3); proj :=true;
   when "2U43":
     gp := SU(4,3); proj :=true;
   when "4U43":
     gp := SU(4,3); proj :=false;
   when "U52":
     gp := SU(5,2); proj :=false;
   when "U53":
     gp := SU(5,3); proj :=true;
   when "U62":
     gp := SU(6,2); proj :=true;
   when "3U62":
     gp := SU(6,2); proj :=false;
   when "U72":
     gp := SU(7,2); proj :=false;
   when "U82":
     gp := SU(8,2); proj :=false;
   when "U92":
     gp := SU(9,2); proj :=true;
   when "3U92":
     gp := SU(9,2); proj :=false;

   when "S44":
     gp := Sp(4,4); proj :=false;
   when "S45":
     gp := Sp(4,5); proj :=true;
   when "2S45":
     gp := Sp(4,5); proj :=false;
   when "S47":
     gp := Sp(4,7); proj :=true;
   when "2S47":
     gp := Sp(4,7); proj :=false;
   when "S62":
     gp := Sp(6,2); proj :=false;
   when "2S62":
     gp := PermutationGroup("2S62",1); proj :=false;
   when "S82":
     gp := Sp(8,2); proj :=false;
   when "S64":
     gp := Sp(6,4); proj :=true;
   when "S65":
     gp := Sp(6,5); proj :=true;
   when "2S65":
     gp := Sp(6,5); proj :=false;
   when "S82":
     gp := Sp(8,2); proj :=false;
   when "S83":
     gp := Sp(8,3); proj :=true;
   when "2S83":
     gp := Sp(8,3); proj :=false;
   when "S102":
     gp := Sp(10,2); proj :=true;
   when "S122":
     gp := Sp(12,2); proj :=true;

   when "O73":
     gp := Omega(7,3); proj :=false;
   when "O75":
     gp := Omega(7,5); proj :=false;
   when "O93":
     gp := Omega(9,3); proj :=false;
   when "O8p2":
     gp := OmegaPlus(8,2); proj :=false;
   when "O8p3":
     gp := OmegaPlus(8,3); proj :=true;
   when "2O8p3":
     gp := OmegaPlus(8,3); proj :=false;
   when "O8p4":
     gp := OmegaPlus(8,4); proj :=false;
   when "O10p2":
     gp := OmegaPlus(10,2); proj :=false;
   when "O12p2":
     gp := OmegaPlus(12,2); proj :=false;
   when "O8m2":
     gp := OmegaMinus(8,2); proj :=false;
   when "O8m3":
     gp := OmegaMinus(8,3); proj :=false;
   when "2O8m3":
     gp := MatrixGroup("2O8m3",2); proj :=false;
   when "O10m2":
     gp := OmegaMinus(10,2); proj :=false;
   when "O12m2":
     gp := OmegaMinus(12,2); proj :=false;

   when "Sz8":
     gp := Sz(8); proj :=false;
   when "Sz32":
     gp := Sz(32); proj :=false;
   when "2Sz8":
     gp := PermutationGroup("2Sz8",1); proj :=false;
   when "G23":
     gp := G2(3); proj :=false;
   when "3G23":
     gp := PermutationGroup("2G23",1); proj :=false;
   when "TF42":
     gp := MatrixGroup("TF42",1); proj :=false;

   when "M11": 
     gp := PermutationGroup("M11",1); proj :=false;
   when "M12":
     gp := PermutationGroup("M12",1); proj :=false;
   when "2M12":
     gp := PermutationGroup("2M12",1); proj :=false;
   when "M22":
     gp := PermutationGroup("M22",1); proj :=false;
   when "2M22":
     gp := PermutationGroup("2M22",1); proj :=false;
   when "3M22":
     gp := PermutationGroup("3M22",1); proj :=false;
   when "6M22":
     gp := PermutationGroup("6M22",1); proj :=false;
   when "4M22":
     gp := PermutationGroup("4M22",1); proj :=false;
   when "12M22":
     gp := PermutationGroup("12M22",1); proj :=false;
   when "M23":
     gp := PermutationGroup("M23",1); proj :=false;
   when "M24":
     gp :=  PermutationGroup("M24",1); proj :=false;
   when "J1":
     gp := PermutationGroup("J1",1); proj :=false;
   when "J2":
     gp := PermutationGroup("J2",1); proj :=false;
   when "2J2":
     gp := PermutationGroup("2J2",1); proj :=false;
   when "J3":
     gp := PermutationGroup("J3",1); proj :=false;
   when "3J3":
     gp := MatrixGroup("J3",1); proj :=false;
   when "HS":
     gp := PermutationGroup("HS",1); proj :=false;
   when "2HS":
     gp := PermutationGroup("2HS",1); proj :=false;
   when "McL":
     gp :=  PermutationGroup("McL",1); proj :=false;
   when "He":
     gp :=  PermutationGroup("He",1); proj :=false;
   when "Ru":
     gp :=  PermutationGroup("Ru",1); proj :=false;
   when "Suz":
     gp :=  PermutationGroup("Suz",1); proj :=false;
   when "ON":
     gp :=  MatrixGroup("ON",1); proj :=false;
   when "Co3":
     gp :=  PermutationGroup("Co3",1); proj :=false;
   when "Co2":
     gp :=  PermutationGroup("Co2",1); proj :=false;
   when "F22":
     gp :=  PermutationGroup("F22",1); proj :=false;
   when "Fi22":
     gp :=  PermutationGroup("F22",1); proj :=false;
   else
     error gpname, "is not a valid identifier, or no standard copy available";
   end case;
   flag, gens := StandardGenerators(gp, gpname : Projective:=proj);
   assert flag;
   gp := sub< gp | gens >;
   return gp, proj;
end intrinsic;

intrinsic IsomorphismToStandardCopy (G:: Grp, str :: MonStgElt :
          AutomorphismGroup := false,
          Projective := false,
          MaxTries := 2000) -> BoolElt, Map
{Use standard generators to find a (possibly projective) isomorphism from
sporadic or small quasisimple group G to its standard copy}
    local flag, A, GG, proj, AA;
    flag, A := StandardGenerators(G, str :
                        AutomorphismGroup := AutomorphismGroup,
                        Projective := Projective,
                        MaxTries := MaxTries);
    if not flag then return false, _; end if;
    GG, proj := StandardCopy(str);
    flag, AA := StandardGenerators(GG, str :
                        Projective := proj,
                        MaxTries := MaxTries);
    if not flag then return false, _; end if;
    return true, hom< sub<G|A[1],A[2]> -> GG | AA[1], AA[2] >;
end intrinsic;

intrinsic StandardGeneratorsGroupNames() -> SetIndx
{List of strings to which StandardGenerators can be applied}
  return {@
 "A5","2A5","A6","2A6","3A6","6A6","A7","2A7","3A7","6A7","A8","2A8",
 "A9","2A9","A10","2A10","A11","2A11",
 "L2p (for any prime p)",
 "L28","L216","L225","2L225","L227","2L227","L232","L249","2L249",
 "L264","L281","2L281","L2121","2L2121","L2125","2L2125","L2128",
 "L2169","2L2169","L2243","2L2243","L2289","2L2289", "L2256","L2343","2L2343",
 "L2529","2L2529","L2361","2L2361",
 "L33","L34","3L34", "2L34","4aL34","4bL34","6L34","12aL34","12bL34",
 "L35","L37","3L37","L38","L39",
 "L43","2L43",
 "L52",
 "U33","U34","U35","3U35","U37","U38","3U38","U39","U311","3U311","U313",
 "U316",
 "U42","2U42","U43","2U43","4U43","6aU43","6bU43","12aU43","U44","U45",
 "U52","U53","U54","U62","3U62","U63","U72","U82","U92","3U92",
 "S44","S45","2S45","S47","2S47",
 "S62","2S62","S64","S65","2S65","S82","S83","2S83","S102","S122",
 "O8p2","2O8p2","2^2O8p2","O8p3","2O8p3","O8p4","O10p2","O12p2",
 "O8m2","O8m3","2O8m3","O8m4", "O10m2","O12m2",
 "O73","O75","O93",
 "Sz8","2Sz8","Sz32",
 "G23","3G23","G24",
 "F42","TF42",
 "E62","TE62","TD42","TD43",
 "M11","M12","2M12","M22","2M22","3M22","6M22","4M22","12M22","M23","M24",
 "J1","J2","2J2","J3","3J3","HS","2HS",
 "McL","He","Ru","Suz","ON",
 "Co1","Co2","Co3","Fi22","Fi23","Fi24","J4","HN","Ly","Th","B","M" @};
/* the following are in Eamonn's file sporadics.m but not here
 "S102","O73","U313","U316","U44","U45","U54","U63","E62",
 "TE62","TD42","TD43","G24","G25","F42","M24",
 "McL","He","Ru","Suz","ON",
 "Co3","Co2","Co1","F22","Fi22","Fi23","Fi24","J4","HN","Ly","Th","B","M"
*/
end intrinsic;
