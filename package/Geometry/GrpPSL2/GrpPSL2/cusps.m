freeze;

/////////////////////////////////////////////////////
//                                                 //
//  Functions related to cusps and ellptic points  //
//                                                 //
//                                                 //
/////////////////////////////////////////////////////


/////////////////////////////////////////////////////
//                                                 //
//  Functions for finding cusps of a congruence    //
//  a subgroup and their widths                    //
//                                                 //
/////////////////////////////////////////////////////

import "coercion.m":  MemberTest;

forward FindCusps;

procedure TestCusps(G) // test the routines, for Gamma0(N) or Gamma1(N)
    "Testing", G; 
    printf "Computing cusps and widths via Farey sequence ... "; time
    cusps, widths := FindCusps(G);
    assert &+widths eq Index(G);
    delete G`cusp_widths;
    printf "Computing widths ... "; time
    assert widths eq Widths(G);
    delete G`cusps; delete G`cusp_widths;
    printf "Listing cusps directly ... "; time
    mycusps := Cusps(G);
    printf "Computing widths ... "; time
    mywidths := Widths(G);
    assert #cusps eq #mycusps;
    assert SequenceToMultiset(widths) eq SequenceToMultiset(mywidths);
    printf "Checking cusps match up ... "; time
    assert &and[ #[s: s in cusps | IsEquivalent(G,s,ss)] eq 1 : ss in mycusps];
end procedure;


intrinsic Cusps(G::GrpPSL2) -> SeqEnum
    {returns a list of coset representatives of G in PSL2(Z);
    only defined for G a subgroup of PSL2(Z)} 
    // the method used is to use the Gluing relations from
    // the Farey sequence to work out which cusps are
    // identified and add up the widths from the Farey
    // Width sequence.
    // There is probably a better way than the below to
    // solve this problem - it's just finding cycles and
    // their lengths in the coset graph - maybe use graph
    // methods in a future version.

    // Special cases for Gamma0 and Gamma1 added by Steve Donnelly, April 2009
    // (listing cusps quickly but not getting the Farey sequence)
    // TO DO: extend this to intermediate groups too?

    require Sprint(G`MatrixGroup) eq "GL(2, IntegerRing())" :
           "G must be a subgroup of SL_2(Z)";
    //PSL := PSL2(Integers());    
    //require IsFiniteIndex(G,PSL): "G must have finite index in SL_2(Z)";

    if not assigned G`cusps then
        N := Level(G);
        if N eq 1 then 
            G`cusps := [Cusp(1,0:Quick)];
        elif IsGamma0(G) then
            // List classes of pairs [A,C] of coprime integers, modulo N 
            // and modulo [A,C] ~ [A+C,C] and [A,C] ~ [u*A,u*C] for u in (Z/N)*
            G`cusps := [Cusps()| Cusp(1,0:Quick), Cusp(0,1:Quick)];
            for C in Exclude(Divisors(N), 1) do 
               As := [1..C-1];
               As := [A: A in As | GCD(A,C) eq 1]; 
               if C eq N then Exclude(~As,1); end if; // because 1/N ~ oo
               // mod out action of units u with u*C = C mod N
               unitsC := [u: u in [1+CC .. N by CC] | GCD(u,N) eq 1] where CC is N div C; 
               As := [A: A in As | not exists{u : u in unitsC | (u*A) mod C lt A}];
               for A in As do
                  AA := A;
                  while GCD(AA,C) ne 1 do
                     AA +:= N;
                  end while;
                  Append(~G`cusps, Cusp(AA,C:Quick));
               end for;
            end for;
        elif IsGamma1(G) then 
            // List classes of pairs [A,C] of coprime integers, modulo N 
            // and modulo [A,C] ~ [A+C,C] and [A,C] ~ [-A,-C]. 
            // We write C = c*d where d = (C,N) and choose c > 0 as small as possible.
            G`cusps := [Cusps()| [1,0], [0,1]];
            for d in Divisors(N) do 
               dd := N div d;
               if d eq 1 then
                  Cs := [c : c in [2 .. N div 2] | GCD(c,dd) eq 1]; // because A/1 ~ 0/1
               elif d eq N then 
                  Cs := [N];
               else
                  Cs := [c*d : c in [1 .. N div (2*d)] | GCD(c,dd) eq 1];
               end if;
               for C in Cs do 
                  As := [1..d];
                  As := [A: A in As | GCD(A,d) eq 1]; 
                  if C eq N then Exclude(~As,1); end if; // because 1/N ~ oo
                  if C eq N or 2*C eq N then 
                     // -C = C mod N, so mod out action by -1
                     As := [A: A in As | (-A) mod d ge A];
                  end if;
                  for A in As do 
                     AA := A;
                     while GCD(AA,C) ne 1 do
                        AA +:= N;
                     end while;
                     Append(~G`cusps, Cusp(AA,C:Quick));
                  end for;
               end for; 
            end for; // d,c
        else
	    _:=FindCusps(G);
        end if;
    end if;
    return G`cusps;
end intrinsic;


intrinsic Widths(G::GrpPSL2) -> SeqEnum
{Sequence containing the CuspWidth of each element of Cusps(G)}

    require Sprint(G`MatrixGroup) eq "GL(2, IntegerRing())" : 
           "G must be a subgroup of SL_2(Z)";
    //PSL := PSL2(Integers());    
    //require IsSubgroup(G,PSL): "G must be a subgroup of SL_2(Z)";
    //require IsFiniteIndex(G,PSL): "G must have finite index in SL_2(Z)";

    // Widths are computed in FindCusps (which computes the Farey sequence). 
    // So CuspWidth will be used only when the direct code for cusps is used.
    // Added April 2009, SRD

    cusps := Cusps(G);
    if not assigned G`cusp_widths then
        G`cusp_widths := [CuspWidth(G,s) : s in cusps];
    end if;
    return G`cusp_widths;
end intrinsic;


// following function uses the Farey symbol to find the
// cusps and their widths

function FindCusps(G)
    FS := FareySymbol(G);	
    cusplist := Cusps(FS);
    labels := Labels(FS);
    FSwidths := Widths(FS);
    cusps := [];
    widths := [];
    done := false;
    not_passed_through := [1..#cusplist];
    number_of_cusps := 0;
    while not done do
	// note that infinity is listed twice, which is
	// why we have 1 in the next line, not 0
	if #not_passed_through le 1 then
	    done := true;
	else
	    number_of_cusps +:= 1;
	    this := Sort(not_passed_through)[1];
	    Exclude(~not_passed_through,this);	   
	    Append(~cusps,cusplist[this]);
	    Append(~widths,0);
	    this_done := false;
	    this_width := 0;
	    linked_cusp := this;
	    while not this_done do
		widths[#widths] +:= FSwidths[linked_cusp];
		link_label := labels[linked_cusp];
		if link_label lt 0 then		    
		    next_cusp := linked_cusp + 1;
		    if next_cusp eq #cusplist then
			next_cusp := 1;
		    end if;
		else
		   neighbours := [i : i in [1..(#cusplist-1)] |
		   labels[i] eq link_label];
		    next_cusp :=		    
		    [i : i in neighbours | i ne linked_cusp][1] + 1;
		    if next_cusp eq #cusplist  then
			next_cusp := 1;
		    end if;
		end if;		
		if next_cusp eq this then
		    this_done := true;
		else
		    Exclude(~not_passed_through,next_cusp);
		    linked_cusp := next_cusp;
		end if;
	    end while;
	end if;
    end while;
    G`cusps := cusps;
    G`cusp_widths := [Integers()!(w/2) : w in widths];
    return G`cusps, G`cusp_widths;
end function;


/////////////////////////////////////////////////////
//                                                 //
//  Functions for finding elliptic points          //
//  of a congruence                                //
//  asubgroup and their widths                     //
//                                                 //
/////////////////////////////////////////////////////


intrinsic EllipticPoints(G::GrpPSL2,H::SpcHyp) -> SeqEnum
   {returns a list of inequivalent elliptic points of the congruence
   subgroup G acting on the upperhalf plane H}
   FS := FareySymbol(G);
   labels := Labels(FS);
   cusps := Cusps(FS);
   ellipticPoints := [];
   elliptic2 := [i : i in [1..#labels] | labels[i] eq -2];
   elliptic3 := [i : i in [1..#labels] | labels[i] eq -3];
   P := PSL2(Integers());
   for i in elliptic2 do
      x := Eltseq(cusps[i]);
      y := Eltseq(cusps[i+1]);
      // note if the first cusp is infinity, need to make it -infinity:
      if cusps[i] eq Cusps()![1,0] then
	 x := [-1,0];
      end if;
      M := P![y[1],x[1],y[2],x[2]];
      Append(~ellipticPoints,M*H.1);
   end for;
   for i in elliptic3 do
      x := Eltseq(cusps[i]);
      y := Eltseq(cusps[i+1]);
      if cusps[i] eq Cusps()![1,0] then
	 x := [-1,0];
      end if;
      M := P![y[1],x[1],y[2],x[2]];
      Append(~ellipticPoints,M*H.2);
   end for;
   return [H|e : e in ellipticPoints];
end intrinsic;


intrinsic EllipticPoints(G::GrpPSL2) -> SeqEnum
   {returns a list of inequivalent elliptic points of the congruence
   subgroup G acting on the upperhalf plane}
   H := UpperHalfPlaneWithCusps();   
   return EllipticPoints(G,H);
end intrinsic;


intrinsic Width(G::GrpPSL2,x::Any) -> RngIntElt
{Same as CuspWidth}
   require Type(x) in {Infty, FldRatElt, SetCspElt} :
          "The cusp should be given either as a rational number, " *
          "Infinity(), or an element of Cusps()";
   return CuspWidth(G, x);
end intrinsic;


intrinsic CuspWidth(G::GrpPSL2,x::Infty) -> RngIntElt
{The width of the cusp x relative to the group G, which should be a subgroup of PSL_2(Z)}
   return CuspWidth(G,Cusps()!x);
end intrinsic;


intrinsic CuspWidth(G::GrpPSL2,x::FldRatElt) -> RngIntElt
{"} // "
   return CuspWidth(G,Cusps()!x);
end intrinsic;


intrinsic CuspWidth(G::GrpPSL2,x::SetCspElt) -> RngIntElt
{"} // "
if false and assigned G`cusp_widths then
      S := G`cusps;
      if exists(i){i : i in [1..#S] | x`u eq S[i]`u and x`v eq S[i]`v} then
         return G`cusp_widths[i];
      end if;
      // Could identify x in G`cusp_widths using IsEquivalent(G, x, xx)
      // but quicker just to do the calculation 
   end if;

   // find gamma in SL2Z such that x = gamma(i*oo)
   A,C := Explode(Eltseq(x));
   _,D,B := XGCD(A,-C); 
   gamma := Matrix(2, 2, [A,B,C,D]);
   gammai := Matrix(2, 2, [D,-B,-C,A]);
   for w in Divisors(Level(G)) do 
      stab := gamma * Matrix(2, 2, [1,w,0,1]) * gammai;
      if MemberTest(G, stab) then // direct call, faster than 'stab in G'
         return w;
      end if;
   end for;
end intrinsic;

