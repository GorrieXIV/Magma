freeze;

import "../Root/RootDtm.m": basisChange;

intrinsic FundamentalClosure( R::RootDtm, roots::SetEnum ) -> SetEnum
{ as in the fundam function in LiE

  if roots are given as tuples, returns tuples; 
  if roots are given as indices, returns indices.
}
	indicesgiven := (Type(Universe(roots)) eq RngInt);
	if (indicesgiven) then
		rtps := roots;
	else
		rtps := { RootPosition(R, r : Basis := "Root") : r in roots};
	end if;

	sd := sub<R | rtps>;
	newrts := SimpleRoots(sd);
	newrtps := { RootPosition(R, newrts[i] : Basis := "Standard") : i in [1..NumberOfRows(newrts)] };

	if (indicesgiven) then
		return newrtps;
	else
		return { Root(R, r : Basis := "Root") : r in newrtps };
	end if;
end intrinsic;

intrinsic ClosureLiE( R::RootDtm, roots::SetEnum ) -> SetEnum
{ closure, as in LiE 
  if roots are given as tuples, returns tuples; 
  if roots are given as indices, returns indices.

  We implement the algorithm described on page 60 of the LiE manual
}
  indicesgiven := (Type(Universe(roots)) eq RngInt);
  if (indicesgiven) then 
    rtps := roots;
  else
    rtps := { RootPosition(R, r : Basis := "Root") : r in roots};
  end if;

  /* make all roots positive roots */
  newrtps := {}; npr := NumberOfPositiveRoots(R);
  for r in rtps do
	  if r gt npr then 
	    Include(~newrtps, r - npr);
	  else
	    Include(~newrtps, r);
      end if;
  end for;
  rtps := newrtps;

  /* run fundam */
  fundamres := FundamentalClosure( R, rtps );

  /* first, find the various isolated components */
  isolcomps := {};
  while (#fundamres gt 0) do
	i := Min(fundamres);
	thiscomp := { j : j in fundamres | InnerProduct(R, i, j) ne 0 };
	Include(~isolcomps, thiscomp);
	fundamres diff:= thiscomp;
  end while;

  /* then, for each component, do the following:
     for every pair alpha, beta of short roots,
	 see whether alpha-beta is a positive root,
	 and, if so, replace alpha by alpha-beta. */
  for comp0 in isolcomps do
    changed := #Seqset(RootNorms(R)) ge 2;
	comp := comp0;
	while (changed) do
	  changed := false;
	  shortrts := { r : r in comp | RootNorm(R, r) eq 1 };

	  for i in shortrts do for j in shortrts do
	  if (i ne j) then
		newrt := Root(R, i : Basis := "Root") - Root(R, j : Basis := "Root");
		newrt := RootPosition(R, newrt : Basis := "Root");
		if (newrt ne 0 and IsPositive(R, newrt)) then 
		  changed := true;
		  Exclude(~comp, i);
		  Include(~comp, newrt);
		  break i;
		end if;
	  end if;
	  end for; end for;
	  
	end while;
	fundamres join:= comp;
  end for;

  fundamres := FundamentalClosure( R, fundamres );

  if (indicesgiven) then
    return fundamres;
  else
    return { Root(R, r : Basis := "Root") : r in fundamres };
  end if;
end intrinsic;

function OldRestrictionMatrix(R,S)
/*
A matrix M which maps fundamental weights from R (in the standard basis)
  to fundamental weights of S (in the standard basis as well). The dimensions of
  R and S must be equal, and the rank of R must be at least the rank of S. 
  Moreover, R must be semisimple.

  Note that M is not unique.
*/
/*	pre: R semisimple, Dimension(R) eq Dimension(S) (=: dim), Rank(R) ge Rank(S);
 
	let FWRst be the fundamental weights of R (in the standard basis): Rank(R) x dim
	let FWSst be the fundamental weights of S (in the standard basis): Rank(S) x dim
	let FWSwt be the fundamental weights of S (in the weight basis): Rank(S) x Rank(S)

	let M be the image (in S, in the weight basis) of the fundamental weights of R ( Rank(R) x Rank(S) )

	then we want to find a matrix A ( dim x dim ), such that:

		FWRst . A . M = ( FWSwt )
				        (   0   )  Rank(R) - Rank(S) rows of zeroes

	id est, A maps the fundamental weights of R to the fundamental weights of S. The M
	comes in to make sure that we can use then non-semisimplicity of S (if so).

	We actually solve
		
		A . M = FWRst^-1 * ( FWSwt )
                           (   0   )

*/
	FWRst := FundamentalWeights(R : Basis := "Standard");
	FWSwt := FundamentalWeights(S : Basis := "Weight");
	cr := CoefficientRing(FWSwt);
	dim := Dimension(R);

	M := Matrix([
		basisChange(S, FWRst[i], "Standard", "Weight", false)
		: i in [1..NumberOfRows(FWRst)]
	]);

	RHS := FWRst^-1*VerticalJoin(FWSwt, ChangeRing( Matrix( [ [ 0 : i in [1..Rank(S)] ] : j in [Rank(S)+1..Rank(R)] ] ), cr ) );
	cons, A, nsp := IsConsistent(M, RHS );

	c := 0;
	for b in Basis(nsp) do
		for i in [1..NumberOfRows(A)] do
			c +:= 1;
			A[i] +:= c*b;
		end for;
	end for;

	return A;
end function;



intrinsic RestrictionMatrix(R::RootDtm, roots::SeqEnum) -> AlgMatElt
{ For a simply connected root datum R and a sequence of roots Q forming
a fundamental basis for a closed subdatum S of R, this function computes a
restriction matrix for the fundamental Lie subgroup of type S of the Lie group 
corresponding to R. }

	//Some declarations
	dimR := Dimension(R); rnkR := Rank(R); 
	n := #roots;
	if Universe(roots) cmpeq Integers() then
		roots := [ Root(R,i : Basis := "Root") :  i in roots ];
	end if;
	rootimgs := ChangeRing(Matrix(roots), Rationals())*ChangeRing(CartanMatrix(R), Rationals());

	//Initialize result to identity matrix
	res := IdentityMatrix(Rationals(), dimR);

	//Traverse the given roots
	for j in [1..n] do
		v := rootimgs[j];
		p := RootPosition(R, roots[j] : Basis := "Root");
		if p eq 0 then error "One of the given roots is not a root written in the ``Root'' basis."; end if;
		norm := RootNorm(R, p);
		
		k := rnkR; while (v[k] eq 0) do k -:= 1; end while;
		if k lt j then error "Set of roots is not independent."; end if;

		if v[k] lt 0 then
			v[k] := -v[k];
			for i in [j..n] do rootimgs[i][k] := -rootimgs[i][k]; end for;
			for i in [k-j+1..rnkR] do res[i][k] := -res[i][k]; end for;
		end if;

		k -:= 1;
		while k ge j do
			v := rootimgs[j];
			//Clear v[k+1] by unimodular column operations with column j
			u := ChangeRing(Matrix([[0,1],[1,0],[v[k+1],v[k]]]), Rationals());
			l := 1;
			if (v[k] lt 0) then 
				u[3][2] := -v[k];
				u[1][2] := -1;
			end if;

			// subtract column |l| some times into column |3-l| 
			repeat
				q := Floor(u[3][3-l] / u[3][l]);
				for i in [1..3] do u[i][3-l] -:= q*u[i][l]; end for;
				l := 3 - l;
			until u[3][l] eq 0;
			if l eq 1 then 
				utmp := u;
				u[1][1] := utmp[1][2]; u[1][2] := utmp[1][1];
				u[2][1] := utmp[2][2]; u[2][2] := utmp[2][1];
			end if;

			// combine columns k and k+1
			for i in [j..n] do
				img_i_k := rootimgs[i][k];
				rootimgs[i][k]   := img_i_k*u[1][1] + rootimgs[i][k+1]*u[2][1];
				rootimgs[i][k+1] := img_i_k*u[1][2] + rootimgs[i][k+1]*u[2][2];
			end for;
			for i in [k-j+1..rnkR] do
				res_i_k := res[i][k];
				res[i][k]   := res_i_k*u[1][1] + res[i][k+1]*u[2][1];
				res[i][k+1] := res_i_k*u[1][2] + res[i][k+1]*u[2][2];
			end for;
	
			//Next column
			k -:= 1;
		end while;

		for i in [1..rnkR] do
			inpr := RootNorm(R, i)*roots[j][i]; //this is (omega_i,alpha[j])
			if not IsIntegral(inpr/norm) then
				error "Supposed root has non-integral Cartan product.";
			end if;
			res[i][j] := inpr / norm; //this is <omega_i, alpha[j]>
		end for;
		
	end for;

	return res;
end intrinsic;


intrinsic RestrictionMatrix(R::RootDtm, S::RootDtm) -> AlgMatElt
{ A matrix M which maps fundamental weights from R (in the standard basis)
  to fundamental weights of S (in the standard basis as well). The dimensions of
  R and S must be equal, and the rank of R must be at least the rank of S. 
  Moreover, R must be semisimple.

  Note that M is not unique.
}

	require Dimension(R) eq Rank(R) : "R must be semisimple.";
	require Dimension(R) eq Dimension(S) : "Dimensions of rootdata must be equal.";
	require Rank(R) ge Rank(S) : "Rank(R) must be greater than or equal to Rank(S).";
	require IsWeaklySimplyConnected(R) : "R must be a simply connected root datum.";
	require IsWeaklySimplyConnected(S) : "S must be a simply connected root datum.";

	fw := FundamentalWeights(S : Basis := "Standard");
	roots := [ fw[i] : i in [1..NumberOfRows(fw) ] ];
	return RestrictionMatrix(R, roots);
end intrinsic;


