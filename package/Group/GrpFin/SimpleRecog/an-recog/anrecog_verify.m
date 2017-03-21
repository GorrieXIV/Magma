freeze;

// implementation by Jonathan Conder 2013 of Beals et al. (2003) 
// algorithm to recognise constructively Alt(n) or Sym (n), and 
// their perfect central extensions 
//
declare attributes Grp: AlternatingOrSymmetricData;

/* 
 * Input:
 *  s: an element of G suspected to be (3, 4, ..., n)
 *  t: an element of G suspected to be (1, 2, 3)
 *  n: degree
 *  isEqual: method to test equality in the group
 * Output:
 *  b: true iff s and t correspond to the suspected permutations (under some isomorphism)
 */
function CheckGenerators(s, t, n, isEqual)
    if IsOdd(n) then
        if not isEqual(t^3, One(Parent(s))) or not isEqual(s^(n - 2), One(Parent(s))) or not isEqual((s * t)^n, One(Parent(s))) then
            return false;
        else
            si := s^(-1);
            tsk := t;
            tsik := t;

            for k := 1 to (n - 3) div 2 do
                tsk *:= s;
                tsik *:= si;

                if not isEqual((tsik * tsk)^2, One(Parent(s))) then
                    return false;
                end if;
            end for;

            return true;
        end if;
    else
        if not isEqual(t^3, One(Parent(s))) or not isEqual(s^(n - 2), One(Parent(s))) or not isEqual((s * t)^(n - 1), One(Parent(s))) then
            return false;
        else
            si := s^(-1);
            tsk := t;
            sik := One(Parent(s));

            T := [t, t^(-1)];
            tk := 1;

            for k := 1 to (n - 2) div 2 do
                tsk *:= s;
                sik *:= si;
                tk := 3 - tk;

                if not isEqual((T[tk] * sik * tsk)^2, One(Parent(s))) then
                    return false;
                end if;
            end for;

            return true;
        end if;
    end if;
end function;



/* This is the method of Beals et al to check whether a group G with
 * subgroup <s,t> = Alt(n) is isomorphic to Alt(n) or Sym(n).
 *
 * Input:
 *  s, t: elements of a group G, such that <s,t> is isomorphic to Alt(n)
 *  y, z: SLPs evaluating to s, t
 *  n: degree of the alternating group
 *  Epsilon: a number between 0 and 1 (default value 0.01)
 *  Extension: true if G is suspected to be a central extension of Alt(n) or Sym(n) (default value false)
 *             if set, p2e is no longer a homomorphism
 *  Asymptotic: if true, the second map returned will perform better asymptotically, but worse in practice
 * Output:
 *  b: true if G is isomorphic to Alt(n) or Sym(n)
 *     false if not (in which case nothing else is returned)
 *  e2p: an isomorphism from G to Alt(n) or Sym(n)
 *  p2e: an isomorphism from Alt(n) or Sym(n) to G
 *  e2w: an isomorphism from G to WordGroup(G)
 *  w2e: an isomorphism from WordGroup(G) to G
 *  o: true if G is isomorphic to Sym(n), false if G is isomorphic to Alt(n)
 * Probability of incorrectly returning false:
 *  at most Epsilon
 * Side effects:
 *  G`AlternatingOrSymmetricData is set to a tuple with the following contents:
 *   o: true iff G contains an odd permutation, whence G is isomorphic to Sym(n)
 *   n: the degree of G as a permutation group
 *   s: an element of G corresponding to (3, 4, ..., n) (n odd) or (1, 2)(3, 4, ..., n) (n even)
 *   t: an element of G corresponding to (1, 2, 3)
 *   y: a word in the generators of G which evaluates to s
 *   z: a word in the generators of G which evaluates to t
 *   Z: the centre of G
 */
function VerifyAlternatingOrSymmetric(s, t, y, z, n: Extension := false, Asymptotic := false)
    G := Parent(s);
    W := Parent(y);
	F := SLPGroup(2);

	if Extension then
		function Is1(g)
			for i := 1 to Ngens(G) do
				if G.i * g ne g * G.i then
					return false;
				end if;
			end for;

			return true;
		end function;
	else
		function Is1(g)
			return IsId(g);
		end function;
	end if;

	/*
	 * Input:
	 *  s: an element of G suspected to be (1, 2, ..., n)
	 *  t: an element of G suspected to be (1, 2)
	 * Output:
	 *  b: true iff s and t correspond to the suspected permutations (under some isomorphism)
	 */
	function CheckSymGenerators(s, t)
		if not Is1(t^2) or not Is1(s^n) or not Is1((s * t)^(n - 1)) then
			return false;
		else
			si := s^(-1);
			tsk := t * s;
			tsik := t * si;

			if not Is1((si * tsk * t)^3) then
				return false;
			end if;

			for k := 2 to n div 2 do
				tsk *:= s;
				tsik *:= si;
				if not Is1((tsik * tsk)^2) then
					return false;
				end if;
			end for;

			return true;
		end if;
	end function;


    if IsOdd(n) then
		/*
		 * Input:
		 *  s: an element of G representing the coset Z(G)(3, 4, ..., n)
		 *  t: an element of G representing the coset Z(G)(1, 2, 3)
		 * Output:
		 *  L: a list of elements of G which generate Z(G)
		 * Note:
		 *  this function also works if s and t are words in the generators of G,
		 *  in which case L is the corresponding list for these words
		 */
		function ListCentralGenerators(s, t)
			L := [t^3, s^(n - 2), (s * t)^n];

			si := s^(-1);
			tsk := t;
			tsik := t;

			for k := 1 to (n - 3) div 2 do
				tsk *:= s;
				tsik *:= si;

				Append(~L, (tsik * tsk)^2);
			end for;

			return L;
		end function;
    else
		/*
		 * Input:
		 *  s: an element of G representing the coset Z(G)(1, 2)(3, 4, ..., n)
		 *  t: an element of G representing the coset Z(G)(1, 2, 3)
		 * Output:
		 *  L: a list of elements of G which generate Z(G)
		 * Note:
		 *  this function also works if s and t are words in the generators of G,
		 *  in which case L is the corresponding list for these words
		 */
		function ListCentralGenerators(s, t)
			L := [t^3, s^(n - 2), (s * t)^(n - 1)];

			si := s^(-1);
			tsk := t;
			sik := Id(Parent(s));

			T := [t, t^(-1)];
			tk := 1;

			for k := 1 to (n - 2) div 2 do
				tsk *:= s;
				sik *:= si;
				tk := 3 - tk;

				Append(~L, (T[tk] * sik * tsk)^2);
			end for;

			return L;
		end function;

    end if;



	if Asymptotic then
		/*
		 * Input:
		 *  a: an even permutation of degree n
		 * Output:
		 *  g: a word in the two standard generators for Alt(n) which evaluates to a
		 */
		function EvenPermutationToWord(a)
			b := Sym(n) ! a;
			g := Id(F);

			w := F.1;
			x := F.2;

			p := 1;
			q := 1 - 2 * ModByPowerOf2(n, 1);

			for i := 1 to n - 2 do
				j := i;
				k := i^b;

				while j ne k do
					// want h = (i, k) (n - 1, n) or h = (n - 1, n) (i, k)
					if i eq n - 2 then
						// x = (n - 2, n) (n - 1, n)
						if k eq n then
							h := x^p;
						else
							h := x^(-p);
						end if;
					elif k le n - 2 then
						if k gt i + 1 then
							c := x^(w^(k - i - 2));
						end if;

						// h1 = (i, i + 1, n - 1)^p
						h1 := (x^(w^(n - i - 3)))^p;
						// h2 := (i, n, i + 1)^p
						h2 := (h1^w)^q;
						// h = (i, i + 1) (n - 1, n) or h = (n - 1, n) (i, i + 1)
						h := h2 * h1 * h2;

						if k gt i + 1 then
							// conjugate by (i, k, i + 1)
							h ^:= c^(IsOdd(k - i) select q else -1);
						end if;
					else
						h1 := x^(w^(n - i - 3));
						h2 := h1^w;

						if k lt n xor p ne 1 then
							h := h2^q * h1;
						else
							h := h1^(-1) * h2^(-q);
						end if;
					end if;

					g *:= h;
					p := -p;

					b *:= Sym(n) ! (j, k);
					j := k;
					k ^:= b;
				end while;

				if IsEven(n - i) then
					x ^:= w * x;
					w *:= x;
				else
					u := w * x;
					x ^:= -1;
					u := x^u;
					w *:= x * u^(-1);
					x := u;
				end if;

				q := -q;
			end for;

			return g;
		end function;
	else
		/*
		 * Output:
		 *  Y: a list of words corresponding to (3, 2, 1), (4, 3, 2), ..., (n, n - 1, n - 2)
		 */
		function DomainTripleCover()
			g := F.2;
			Y := [g];
			m := 4;

			if IsEven(n) then
				g := F.2^(-1);
				g ^:= g^F.1;
				Append(~Y, g);
				m +:= 1;
			end if;

			for i := m to n do
				g ^:= F.1;
				Append(~Y, g);
			end for;

			return Y;
		end function;

		A := [Alt(n) ! (i, i + 1, i + 2) : i in [1 .. n - 2]];
		Y := DomainTripleCover();

		/*
		 * Input:
		 *  a: an even permutation of degree n
		 * Output:
		 *  g: a word in the two standard generators for Alt(n) which evaluates to a
		 */
		function EvenPermutationToWord(a)
			g := Id(F);

			for i := 1 to n - 2 do
				k := i^a;
				j := k - 2;

				// multiply g by (k, k - 1, ..., i) or (k, k - 1, ..., i + 1)
				// and a by the inverse
				while j ge i do
					g := Y[j] * g;
					a *:= A[j];
					j -:= 2;
				end while;

				// adjust (k, k - 1, ..., i + 1) to (k, k - 1, ..., i + 2, i)
				// after which a fixes {1, 2, ..., i} pointwise
				if j eq i - 1 then
					g := Y[i]^(-1) * g;
					a *:= A[i]^(-1);
				end if;
			end for;

			return g;
		end function;
	end if;

	if Asymptotic then
		/*
		 * Input:
		 *  a: a permutation of degree n
		 * Output:
		 *  g: a word in the two standard generators for Sym(n) which evaluates to a
		 */
		function PermutationToWord(a)
			g := Id(F);

			w := F.1 * F.2;
			x := F.2;

			for i := 1 to n - 1 do
				j := i;
				k := i^a;

				while j ne k do
					// h = (i, k)
					h := x^(w^(k - i - 1));
					g *:= h;

					a *:= Sym(n) ! (j, k);
					j := k;
					k ^:= a;
				end while;

				x ^:= F.1;
				w *:= x;
			end for;

			return g;
		end function;
	else
		/*
		 * Output:
		 *  Y: a list of words corresponding to (1, 2), (2, 3), ..., (n - 1, n)
		 */
		function DomainDoubleCover()
			g := F.2;
			Y := [g];

			for i := 2 to n do
				g ^:= F.1;
				Append(~Y, g);
			end for;

			return Y;
		end function;

		A := [Sym(n) ! (i, i + 1) : i in [1 .. n - 1]];
		Y := DomainDoubleCover();

		/*
		 * Input:
		 *  a: a permutation of degree n
		 * Output:
		 *  g: a word in the two standard generators for Sym(n) which evaluates to a
		 */
		function PermutationToWord(a)
			g := Id(F);

			for i := 1 to n - 1 do
				k := i^a;
				j := k - 1;

				// multiply g by (k, k - 1, ..., i) and a by the inverse
				while j ge i do
					g := Y[j] * g;
					a *:= A[j];
					j -:= 1;
				end while;
			end for;

			return g;
		end function;
	end if;

	// [(1, 2, 3), (1, 2, 4), ..., (1, 2, 11)]
	E := [(j gt 0) select (Self(j)^s)^(2 * ModByPowerOf2(n, 1) - 1) else t : j in [0 .. (n ge 11) select 8 else 2]];

	/*
	 * Output:
	 *  X: a list of elements of G corresponding to compositions of the cycles
	 *     (1, 2, 3, 4, 5), (6, 7, 8, 9, 10), ..., (5k - 4, 5k - 3, 5k - 2, 5k - 1, 5k)
	 *     where k = n div 5, such that X[j] contains the ith such cycle iff
	 *     the jth most significant bit of i among the lowest m is 1,
	 *     where m = Ilog2(k) + 1, and otherwise X[m + j] contains this cycle
	 */
	function DomainCover()
		k := n div 5;
		m := Ilog2(k) + 1;

		// a = (1, 2, 3, 4, 5)
		a := E[1] * E[2]^(-1) * E[3];
		X := [(m le j and j - m lt m) select a else Id(G) : j in [1 .. 2 * m]];

		// a = (6, 7, 8, 9, 10)
		a := E[4] * E[5]^(-1) * E[6] * E[7]^(-1) * E[8] * E[4]^(-1);
		c := s^5;

		for i := 2 to k do
			for j := 1 to m do
				if BitwiseAnd(i, ShiftLeft(1, m - j)) ne 0 then
					X[j] *:= a;
				else
					X[m + j] *:= a;
				end if;
			end for;
			// a = (5 * i + 1, 5 * i + 2, ..., 5 * i + 5)
			a ^:= c;
		end for;

		return X;
	end function;

	if n ge 11 then
		X := DomainCover();
	else
		X := [];
	end if;

	/*
	 * Input:
	 *  i: an integer between 1 and n
	 *  j: an integer between i and n
	 * Output:
	 *  g: an element of G corresponding to a permutation which maps i to j
	 */
	function ConjugateMap(i, j)
		if i lt 3 then
			if j lt 3 then
				return t^(j - i);
			else
				return t^(3 - i) * s^(j - 3);
			end if;
		else
			return s^(j - i);
		end if;
	end function;

	/*
	 * Input:
	 *  S: a list of 3-element subsets of {0, 1, 2, 3, 4}
	 *  T: a list of elements of G such that T[k] corresponds to a 3-cycle with support
	 *     {i + j : j in S[k]}, for some fixed integer i between 1 and n
	 *  r: the number of points to compute images for
	 *  K: a set specifying which image points are unavailable
	 *  g: an element of G, which corresponds to some permutation a
	 * Output:
	 *  L: a list of integers between 1 and n such that a maps i, i + 1, ..., i + r - 1 to L[1], L[2], ..., L[r]
	 *  K: a set specifying which image points are unavailable
	 */
	function ElementImages(S, T, r, K, g)
		m := #X div 2;
		I := [0 : i in [1 .. r]];
		J := [[n - n mod 5 + 1 .. n] : i in [1 .. r]];

		for j := 1 to m do
			l := 0;

			for k := 1 to #T do
				h := T[k]^g;

				if Is1((X[j], h)) then
					b := 0;
					l := k;
					break;
				elif Is1((X[j + m], h)) then
					b := 1;
					l := k;
					break;
				end if;
			end for;

			if l le 0 then
				error Error("Input group not isomorphic to Alt(n) or Sym(n)");
			end if;

			for i := 1 to r do
				bi := b;

				if i notin S[l] then
					for k := 1 to #S do
						if S[k] diff S[l] eq {i} then
							li := k;
							break;
						end if;
					end for;

					if not Is1((X[j + b * m], T[li]^g)) then
						bi := 1 - b;
						J[i] := [];
					end if;
				end if;

				I[i] *:= 2;
				I[i] +:= bi;
			end for;
		end for;

		L := [0 : i in [1 .. r]];
		for i := 1 to r do
			if 0 lt I[i] and 5 * I[i] le n then
				J[i] := [5 * I[i] + j : j in [-4 .. 0]] cat J[i];
			end if;

			H := [];

			for k := 1 to #S do
				if i in S[k] then
					Append(~H, T[k]^g);
					for l := k + 1 to #S do
						if S[k] meet S[l] eq {i} then
							Append(~H, T[l]^g);
							break k;
						end if;
					end for;
				end if;
			end for;

			C := [E[1]] cat [E[2 * k]^(-1) * E[2 * k + 1] : k in [1 .. 4]];
			l := 1;

			for j in J[i] do
				c := ConjugateMap(l, j);
				l := j;
				for k := 1 to #C do
					C[k] ^:= c;
				end for;

				N := [0, 0];
				for h in C do
					for k := 1 to 2 do
						if Is1((h, H[k])) then
							if N[k] ge 1 then
								continue j;
							end if;
							N[k] +:= 1;
						end if;
					end for;
				end for;

				if j in K then
					error Error("Input group not isomorphic to Alt(n) or Sym(n)");
				else
					Include(~K, j);
				end if;

				L[i] := j;
				break;
			end for;

			if L[i] le 0 then
				error Error("Input group not isomorphic to Alt(n) or Sym(n)");
			end if;
		end for;

		return L, K;
	end function;

	/*
	 * Input:
	 *  g: an element of G, which corresponds to some permutation a
	 * Output:
	 *  L: a list of integers between 1 and n such that a maps [1, 2, ..., n] to L
	 */
	function ElementToSmallDegreePermutation(g)
		T := [E[i] : i in [1 .. 3]];
		T cat:= [E[i]^(-1) * E[j] : j in [i + 1 .. 3], i in [1 .. 3]];
		T cat:= [E[i] * E[j]^(-1) : j in [i + 1 .. 3], i in [1 .. 3]];
		Append(~T, T[9] * T[7]);

		L := [0 : i in [1 .. n]];
		K := {};
		H := [T[1], T[6]];

		for l := 1 to n do
			for j := 1 to n do
				if j eq 1 then
					c := Id(G);
				else
					c *:= ConjugateMap(j - 1, j);
				end if;

				for i := 1 to #H do
					h1 := H[i]^g;
					S := [1, 1];

					for k := 1 to 2 do
						h2 := T[5 * k - 4]^c;

						h := h2 * h1;
						if Is1(h) then
							continue i;
						end if;

						h := h2 * h;
						if Is1(h) then
							continue i;
						end if;

						h := h1^(-1) * h * h2;
						if Is1(h) then
							continue j;
						end if;

						if Is1(h^2) then
							S[k] := 2;
						end if;
					end for;

					if S[1] eq S[2] then
						if S[1] eq 1 then
							for k := 2 to 5 do
								if Is1((h1, T[k]^c)) then
									continue j;
								end if;
							end for;
						end if;
					else
						m := (S[1] gt S[2]) select 1 else 2;

						for k := 1 to 2 do
							if Is1((h1, T[2 * m + 4 + k]^c)) then
								continue j;
							end if;
						end for;
					end if;
				end for;

				if j in K then
					error Error("Input group not isomorphic to Alt(n) or Sym(n)");
				else
					Include(~K, j);
				end if;

				L[l] := j;
				break;
			end for;

			if L[l] le 0 then
				error Error("Input group not isomorphic to Alt(n) or Sym(n)");
			end if;

			c := ConjugateMap(l, l + 1);
			for i := 1 to #H do
				H[i] ^:= c;
			end for;
		end for;

		return L;
	end function;

	/*
	 * Input:
	 *  g: an element of G, which corresponds to some permutation a
	 * Output:
	 *  L: a list of integers between 1 and n such that a maps [1, 2, ..., n] to L
	 */
	function ElementToPermutation(g)
		if n lt 11 then
			return ElementToSmallDegreePermutation(g);
		end if;

		S := [];
		T := [];

		for i := 1 to 5 do
			for j := i + 1 to 5 do
				for k := j + 1 to 5 do
					// h = (i + 2, j + 2, k + 2)
					h := E[j] * E[k]^(-1) * E[i] * E[j]^(-1);
					Append(~T, h);

					H := {i, j, k};
					Append(~S, H);
				end for;
			end for;
		end for;

		T1 := [E[i] : i in [1 .. 3]];
		T1 cat:= [E[i]^(-1) * E[j] : j in [i + 1 .. 3], i in [1 .. 3]];
		T1 cat:= [E[i] * E[j]^(-1) : j in [i + 1 .. 3], i in [1 .. 3]];
		Append(~T1, T[1]);

		K := {};
		L, K := ElementImages(S, T1, 2, K, g);
		c := s^5;

		for r := 1 to (n - 2) div 5 do
			J, K := ElementImages(S, T, 5, K, g);
			L cat:= J;

			for i := 1 to #T do
				T[i] ^:= c;
			end for;
		end for;

		r := (n - 2) mod 5;
		if r gt 0 then
			J, K := ElementImages(S, T, r, K, g);
			L cat:= J;
		end if;

		return L;
	end function;

	o := false;
	P := Alt(n);

	G1 := s;
	G2 := t;

	S1 := y;
	S2 := z;

	if Asymptotic then
		P2E := func<a | Evaluate(EvenPermutationToWord(a), [G1, G2])>;
		P2W := func<a | Evaluate(EvenPermutationToWord(a), [S1, S2])>;
	else
		P2E := func<a | Evaluate(EvenPermutationToWord(a), [G1 * G2^(2 * ModByPowerOf2(n, 1) - 1), G2^(-1)])>;
		P2W := func<a | Evaluate(EvenPermutationToWord(a), [S1 * S2^(2 * ModByPowerOf2(n, 1) - 1), S2^(-1)])>;
	end if;

	for i := 1 to Ngens(G) do
		try
			b := Sym(n) ! ElementToPermutation(G.i);
		catch e
			return false, _, _, _, _, _;
		end try;

		if not o and IsOdd(b) then
			c := Sym(n) ! (1, 2) * b;

			h := P2E(c);
			w := P2W(c);

			o := true;
			P := Sym(n);

			G2 := h * (G.i)^(-1);
			S2 := w * (W.i)^(-1);

			G1 := G2^(1 - ModByPowerOf2(n, 1)) * s * t;
			S1 := S2^(1 - ModByPowerOf2(n, 1)) * y * z;

			if not CheckSymGenerators(G1, G2) then
				return false, _, _, _, _, _;
			end if;

			P2E := func<a | Evaluate(PermutationToWord(a), [G1, G2])>;
			P2W := func<a | Evaluate(PermutationToWord(a), [S1, S2])>;
		end if;

		h := P2E(b);
		d := G.i * h^(-1);

		if not Is1(d) then
			return false, _, _, _, _, _;
		end if;
	end for;

	e2p := hom<G -> P | g :-> P ! ElementToPermutation(g)>;
	p2e := hom<P -> G | a :-> P2E(a)>;

	if Extension then
		C := ListCentralGenerators(s, t);
		D := ListCentralGenerators(y, z);

		L := [];
		M := [];

		for i := 1 to #C do
			if not IsId(C[i]) then
				j := Index(L, C[i]);
				if j le 0 then
					Append(~L, C[i]);
					Append(~M, D[i]);
				elif #M[j] gt #D[i] then
					M[j] := D[i];
				end if;
			end if;
		end for;

		Z := sub<G | L>;
		Z2W := hom<Z -> W | M>;

		function E2W(g)
			b := e2p(g);
			h := P2E(b);
			d := g * h^(-1);

			return Z2W(d) * P2W(b);
		end function;
	else
		Z := sub<G | Id(G)>;
		Z2W := hom<Z -> W | g :-> Id(W)>;
		E2W := func<g | P2W(e2p(g))>;
	end if;

	G`AlternatingOrSymmetricData := <o, n, G1, G2, S1, S2, Z, Is1, ElementToPermutation, P2E, E2W, P2W, Z2W>;

	e2w := hom<G -> W | g :-> E2W(g)>;
	w2e := hom<W -> G | w :-> Evaluate(w, G)>;

	return true, e2p, p2e, e2w, w2e, o;
end function;

/*
 * Input:
 *  G: a group which has been constructively recognised using RecogniseAlternatingOrSymmetric
 *  g: a suspected element of G
 * Output:
 *  b: true if g is a member of G, false otherwise
 *  w: if g is in G, a word in the generators of G which evaluates to g
 */
intrinsic AlternatingOrSymmetricElementToWord(G::Grp, g::GrpElt) -> BoolElt, GrpSLPElt
{ If g is an element of the group G which has been constructively recognised 
using RecogniseAlternatingOrSymmetric, this function returns true and an 
element of the word group for G which evaluates to g. 
Otherwise, it returns false. }
    require Type (G) in {GrpPerm, GrpMat}: "Input group type incorrect";
	require assigned G`AlternatingOrSymmetricData: "G has not been constructively recognised";

	T := G`AlternatingOrSymmetricData;
	o := T[1];
	n := T[2];
	P := o select Sym(n) else Alt(n);

	Z := T[7];
	Is1 := T[8];
	E2P := T[9];
	P2E := T[10];
	P2W := T[12];
	Z2W := T[13];

	try
		b := P ! E2P(g);
	catch e
		return false, _;
	end try;

	h := P2E(b);
	try
		d := Z ! (g * h^(-1));
	catch e
		return false, _;
	end try;

	return true, Z2W(d) * P2W(b);
end intrinsic;
