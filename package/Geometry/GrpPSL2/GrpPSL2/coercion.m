freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//   Congruence subgroups                                         //
//                                                                //
//                         Coercions                              //
//                                                                // 
////////////////////////////////////////////////////////////////////

/****************           CHANGES LOG:            ****************          

   hav: update 14 October 2002: changed member test to take into
                                account Dirichlet characters.
   
   Jan 2007, Steve: Fix mistake in MemberTest (see below).

 ******************************************************************/

// the following function defines the member test
// corresponding to the group labled A = [n,m,p]


function MemberTest(G,g)
   // currently only works for congruence subgroups:
   // assert IsCongruence(G);
   error if not(Type(g[1,1]) eq RngIntElt),
      "Argument in coercion of sequences to matrices"
      * " should be a sequence of integers.";
   A := CongruenceIndices(G)[1];   
   n,m,p := Explode(A);
   // now compute the value of the Dirichlet Character on g[1,1], if needed.
   // we assume that the subgroup list consists of a list containing
   // exactly one Dirichlet character.  This will have been defined when
   // the group was construced with the
   // CongruenceSubgroup(A::SeqEnum,char::GrpDrchElt)
   // function in the creation.m file.
   if assigned G`subgroup_list  then
      char := G`subgroup_list[1];
      g11 := Evaluate(char,g[1,1]);
   else
      // for the test below to work for either definition of g[1,1],
      // ie, whether g[1,1] is the result of evaluation a Dirichlet
      // character, or the result of taking g11 mod m, we make sure the
      // reduction mod m is -1 or 1 when this is the residue class.
      // we assume that the function mod returns a value between 0 and m-1
      //
      // Modification by Steve: 
      // This doesn't seem quite right.
      // In the case where g11 is a diagonal matrix entry, we want to require 
      // that g11 is 1 or -1. However when it is a character value, we want to 
      // require that it is exactly 1.
      // I'm now doing this by setting g11:=1 if it is m-1 (instead of g11:=-1), 
      // and then the test is whether g11 eq 1. 
      // Example: 
      // > Chi17 := DirichletGroup(17,CyclotomicField(EulerPhi(17)));
      // > GG := CongruenceSubgroup([17,17,1], Chi17.1^8); 
      // > GG![3, 1, 17, 6];  
      // now gives an error, as it should since the character value at 3 is -1.
      g11 := g[1,1] mod m;
      if g11 eq m-1 then
	 // g11 := -1;
	 g11 := 1;
      end if;
   end if;
   case [n eq 1, m eq 1, p eq 1]: 
      when [ false, true, true ]:
         return (g[2,1] mod n) eq 0;
      when [ false, false, true ]:
         return ((g[2,1] mod n) eq 0)
	        //and  ((g11 eq 1) or (g11 eq -1));
	        and  g11 eq 1;
      when [ false, false, false ]:
         return ((g[2,1] mod n) eq 0)
	        //and  ((g11 eq 1) or (g11 eq -1))
	        and  g11 eq 1
                and (g[1,2] mod p) eq 0;
      when [ false, true, false ]:
         return (g[2,1] mod n) eq 0
                and (g[1,2] mod p) eq 0;	     
      when [ true, false, false ]:
         //return ((g11 eq 1) or (g11 eq -1))
         return (g11 eq 1)
                and (g[1,2] mod p) eq 0;
      when [ true, true, false ]:
         return (g[1,2] mod p) eq 0;
      when [ true, true, true ]:
         return true;
   end case;    
end function;


function exactly_divides(d,N)
   if N mod d ne 0 then
      return false;
   end if;   
   return GCD(d,Integers()!(N/d)) eq 1;
end function;
   
function MemberTestWithInvolutions(G,g)
   // L := G`Levels;
   // we must have L = [N,1,1]!
   // don't want to add a test for this, in order not to
   // slow things down.
   // also assume Determinant is not 1,
   // also assume we're working with the normalizer of
   // Gamma_0(N) for now
   // also earlier testing should ensure d is positive
   d := Determinant(g);
   N := Level(G);
   // should next line be "...mod d eq 1"?
   if not (g[2,1] mod N eq 0 and g[1,1] mod d eq 0 and g[2,2] mod d eq 0) then
      return false;
   end if;
   if not exactly_divides(d,N) then
      return false;
   end if;
   return true;
end function;



// the following is used by the functions in
// the farey sequence files, so that when coercing
// we do not need to waste vast amounts of time
// checking membership, when by
// construction those algorithms are producing matrices
// the the groups they are supposed to be in.
function init_psl2_elt_from_integer_matrix(G,A)
   X := New(GrpPSL2Elt); 
   X`Parent := G;
   X`Element := A;
   return X;
end function;


function init_psl2_elt(G,A)
    /* The basic internal creation function. */ 
    X := New(GrpPSL2Elt); 
    X`Parent := G;
    coeffs := [ x : x in Eltseq(A) ];
    // some normalization of coefficients:
    if Type(G) eq FldRat then
	if G`BaseRing eq Rationals() then
	    // multiply through by lcm of denominaors,
	    // then divide by gcd of matrix entries
	    // to get a matrix with coprime integer entries
	    // if the BaseRing is the integers, then we should
	    // already have this propetry.
	    denoms := [Denominator(a) : a in coeffs];
	    numers := [Numerator(a) : a in coeffs];
	    gcd := Gcd(numers);
	    lcm := Lcm(denoms);
	    coeffs := [ Integers()!(x*lcm/gcd) : x in coeffs];	
	    if (coeffs[1] lt 0) or
		(coeffs[1] eq 0 and coeffs[2] lt 0) then
		coeffs := [-x : x in coeffs];	    
	    end if;	    
	end if;
    end if;
    if Type(G) eq RngInt then
	if G`BaseRing eq Integers() or G`BaseRing eq Rationals() then
	    if (coeffs[1] lt 0) or
		(coeffs[1] eq 0 and coeffs[2] lt 0) then
		coeffs := [-x : x in coeffs];	    
	    end if;	    
	end if;
    end if;	
    X`Element := A;
    return X;
end function; 

function BalancedLift(x,p)
   x := Integers()!x;
   if x le (p div 2) then 
      return x;
   end if;
   return x - p;
end function;

function CoprimeLift(a,b,p)
   a := Integers()!a;
   b := Integers()!b;
   if a eq 0 then 
      if b ne 1 then
         a := p; 
      end if;
   end if;
   k := 1;
   u := 1;
   if b lt 0 then u := -1; end if;
   while GCD(a,b) ne 1 do
      b +:= u*(-1)^k*k*p;
      k +:= 1;
   end while;
   return a, b;
end function;

function UnitMatrixLift(G,A)
   p := Characteristic(BaseRing(Parent(A)));
   A := [ BalancedLift(x,p) : x in Eltseq(A) ];
   a, b := CoprimeLift(A[1],A[2],p);
   c := A[3]; 
   d := A[4];
   k := (a*d - b*c - 1) div p;
   _, d1, c1 := XGCD(a,-b);
   return G![a,b,c-k*p*c1,d-k*p*d1];     
end function;


function normalization(S)
    if Universe(S) eq Integers() then
	g := Gcd(S);
	S := [Integers()!(a/g) : a in S];
    else
	denoms := [Denominator(a) : a in S];
	numers := [Numerator(a) : a in S];
	gcd := Gcd(numers);
	lcm := Lcm(denoms);
	S := [ Integers()!(x*lcm/gcd) : x in S];	
    end if;
    // now S should be a list of integers
    return S;
end function;


intrinsic IsCoercible(G::GrpPSL2,S::.) -> BoolElt, GrpPSL2Elt 
  {The element of G defined by S.}

  case Type(S):
	  when RngIntElt:
	    // since projective, [a,0,0,a] = [1,0,0,1]
      return true, init_psl2_elt(G,G`MatrixGroup![1,0,0,1]);

    when GrpPSL2Elt:
      if Type(G`BaseRing) eq FldRat or (assigned S`Parent and S`Parent cmpeq G) 
        or MemberTest(G,S`Element) then
        if S`Parent cmpeq G then
		      return true, S; 
	      else 
		      return true, init_psl2_elt(G,S`Element);   
	      end if;
	    end if;
	    R := G`BaseRing; P := S`Parent`BaseRing; 
	    if Type(R) eq FldFin and Type(P) eq RngInt then
	      return true, init_psl2_elt(G,G`MatrixGroup!S`Element);
	    elif Type(R) eq RngInt and Type(P) eq FldFin and
	      P eq PrimeField(P) then
	      return true, init_psl2_elt(G,
	      UnitMatrixLift(G`MatrixGroup,S`Element) );
	    end if;

    when GrpMatElt,AlgMatElt:
//    		 print "tt";
      M := Parent(S);
	    if Degree(M) eq 2 and BaseRing(M) eq BaseRing(G)
	        and BaseRing(M) eq Rationals() or MemberTest(G,S) then
	      return true, init_psl2_elt(G,S);
      end if;

    when AlgQuatElt, AlgQuatOrdElt, AlgAssVOrdElt:
//         print "tt";
	    if IsCoercible(Domain(G`MatrixRepresentation), S) then
        g := init_psl2_elt(G, S);
        return true, g;
	    end if;

    when SeqEnum:
//    		 print "tt";
      if #S ne 4 then
	      return false, "Illegal coercion: when argument is a sequence,
	        it must have length 4";
	    end if;

 	    // could consider using the following:
 	    //
	    // val, S := CanChangeUniverse(S,BaseRing(G));
	    // if not val then
	    // return false, "Illegal coercion, invalid sequence universe.";
	    // end if;
	
      if assigned G`IsShimuraGroup then
        // Shimura subgroup
        return false;
      end if;

      if (not ((Universe(S) cmpeq Integers())
	        or (Universe(S) cmpeq Rationals()))) then
  	      return false, "Illegal coercion, entries should be integers or rationals";
   	      // note, would like to have other number fields and their
  	      // integer rings allowed later.
	    end if;

	    if S eq [Parent(S[1])|0,0,0,0] then
	      return false, "Illegal coercion, trying to coerce zero matrix";
	    end if;
	    Sn := normalization(S);
	    det := Sn[1]*Sn[4] - Sn[2]*Sn[3];      
	    if det eq 0 then
	      return false, "Illegal coercion, determinant zero";
	    end if;
	    if det lt 0 then
	      return false, "Illegal coercion, negative determinant";
	    end if;
	    if (Type(G`BaseRing) eq RngInt and G`BaseRing eq Integers()) or
       (assigned G`AtkinLehnerInvolutions and Dimension(G`AtkinLehnerInvolutions) gt 0)
	      then	 
	      if det ne 1 then
		      if not assigned G`AtkinLehnerInvolutions or
		          Dimension(G`AtkinLehnerInvolutions) eq 0 then
		        return false, "Illegal coercion, determinant not 1";
		      else
		        // warning!  need to check the following
		        // coercion actually works!
		        // note, need elements to be integers to check congruences:
		        A := MatrixAlgebra(Integers(),2)!Sn;
		        if MemberTestWithInvolutions(G,A) then
		          return true, init_psl2_elt(G,A);
     		    else
    		      return false, "Illegal coercion, not in normalizer";
    		    end if;
          end if;
    	  else
    		  A := MatrixAlgebra(Integers(),2)!Sn;
    		  if MemberTest(G,A) then
    		    return true, init_psl2_elt(G,A);
    		  end if;
    	  end if;

   	    return false,
	        "Illegal coercion, integers do not satisfy required congruences";
	    end if;

	    // need to check whether s has a square root in
 	    // G`BaseRing, and whether root(s)*r is invertible
	    // in the BaseRing.
	    if Type(G`BaseRing) in {RngInt,FldRat} then
	      s, r := SquarefreeFactorization(det);
	    else
	      s := det;
	      r := Parent(det)!1;
	    end if;
	    if Type(G`BaseRing) eq FldRat and G`BaseRing eq Rationals() then
        if s lt 0 then 
		      return false, "Illegal coercion, wrong determinant";
	      else
//		 		 print "tt";
    		  A := (G`MatrixGroup)!Sn;
 	  	    return true, init_psl2_elt(G,A);
	      end if;
	    elif Type(G`BaseRing) in {FldNum, FldQuad} then
	      if IsSquare(G`BaseRing!s) then
		      A := (G`MatrixGroup)!S; 
//	   	 print "tt";
    		  if MemberTest(G,A) then
		        return true, init_psl2_elt(G,A); 
		      else
		        return false, "The base ring must contain the square root of the determinant"; 
		      end if;
	      end if;
	    end if;
  end case;

  return false, "Illegal coercion"; 
end intrinsic;
