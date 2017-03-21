174,1
V,AlgSeries,1
S,Domain,Get the domain of the power series (resp. its polynomial approximants),0,1,0,0,0,0,0,0,0,472,,64,-38,-38,-38,-38,-38
S,ExponentLattice,Get the exponent lattice of the power series represented by 'series',0,1,0,0,0,0,0,0,0,472,,303,-38,-38,-38,-38,-38
S,Expand,"Given a representation 'series' of a power series 'alpha'. Let 'beta := alpha(x_1^e,...,x_n^e)' where 'e' is the denominator of the exponent lattice in 'tagged_series'. Return the expansion of 'beta' up to order less than 'ord'",0,2,0,0,0,0,0,0,0,148,,0,0,472,,36,63,-38,-38,-38,-38
S,DefiningPolynomial,Get the defining polynomial of the power series represented by 'tagged',0,1,0,0,0,0,0,0,0,472,,312,-38,-38,-38,-38,-38
S,Order,"Given a series 'series' return its order times the exponent denominator, i.e., the order of the first term returned by 'Expand'. If 'series' is the zero series, this function will not terminate. Set 'TestZero' to 'true' if you want a return value of '-1' in this case. But note that zero testing is expensive and the return value 'infinity' would be more appropriate for most applications",0,1,0,0,0,0,0,0,0,472,,148,-38,-38,-38,-38,-38
S,SimplifyRep,"Simplifies the representation of series 'series'. This is an expensive operation, but subsequent operations on 'series' will be fast",0,1,0,0,0,0,0,0,0,472,,472,-38,-38,-38,-38,-38
S,IsZero,Determines if the power series is zero,0,1,0,0,0,0,0,0,0,472,,36,-38,-38,-38,-38,-38
S,eq,Decides if two power series are equal,0,2,0,0,0,0,0,0,0,472,,0,0,472,,36,-38,-38,-38,-38,-38
S,IsEqual,,0,2,0,0,0,0,0,0,0,472,,0,0,472,,36,-38,-38,-38,-38,-38
S,IsPolynomial,Determines whether the series is actually a polynomial (with integral exponents),0,1,0,0,0,0,0,0,0,472,,36,63,-38,-38,-38,-38
S,PolyToSeries,Given a multivariate polynomial 's'. Return the atomic algebraic power series representation of 's',0,1,0,0,0,0,0,0,0,63,,472,-38,-38,-38,-38,-38
S,AlgebraicPowerSeries,"Define an atomic algebraic power series by giving its defining polynomial 'defpol', an initial expansion 'init'. The exponent lattice is taken to be the standard lattice. Optionally specify a sequence 'subs' of series that should be substituted into 'defpol'",0,2,0,0,0,0,0,0,0,63,,0,0,312,,472,-38,-38,-38,-38,-38
S,AlgebraicPowerSeries,"Define an atomic algebraic power series by giving its defining polynomial 'defpol', an initial expansion 'init'. The exponent lattice is taken to be (1/e)*the standard lattice. Optionally specify a sequence 'subs' of series that should be substituted into 'defpol'",0,3,0,0,0,0,0,0,0,148,,0,0,63,,0,0,312,,472,-38,-38,-38,-38,-38
S,AlgebraicPowerSeries,"Define an atomic algebraic power series by giving its defining polynomial 'defpol', an initial expansion 'init' and its exponent lattice '1/e*Gamma'. Optionally specify a sequence 'subs' of series that should be substituted into 'defpol'",0,4,0,0,0,0,0,0,0,148,,0,0,164,,0,0,63,,0,0,312,,472,-38,-38,-38,-38,-38
S,EvaluationPowerSeries,"Given a series 'series', a sequence 'nu' of vectors in the dual of the exponent lattice and a sequence 'v' (of the same length) of polynomials. Return the series obtained by substituting 'x^mu :-> prod_i v[i]^<nu[i],mu>' where 'x' is the coordinate vector of 'series' (if that homomorphism is defined)",0,3,0,0,0,0,0,0,0,82,,0,0,82,,0,0,472,,472,-38,-38,-38,-38,-38
S,ImplicitFunction,The unique series with zero constant term defined by 'defpol' (fulfilling the conditions of the implicit function theorem). Optionally specify a sequence 'subs' of series that should be substituted into 'defpol',0,1,0,0,0,0,0,0,0,312,,472,-38,-38,-38,-38,-38
S,ScaleGenerators,If '1/e*Gamma' is the exponent lattice of the power series 'series' and '(mu_i)_i' the sequence of its generators return the power series after the substitution 'x^(mu_i) :-> lambda[i]*x^(mu_i)',0,2,0,0,0,0,0,0,0,82,,0,0,472,,472,-38,-38,-38,-38,-38
S,ChangeRing,If 'S' is a multivariate polynomial domain compatible with the approximation domain of the power series 'series' return the same power series with new approximation domain 'S',0,2,0,0,0,0,0,0,0,64,,0,0,472,,472,-38,-38,-38,-38,-38
S,AlgComb,Given a polynomial 'comb' in 'r' variables and a sequence 'series' of 'r' algebraic power series (in the same domain) returns the power series obtained by substituting the elements of 'series' for the variables of 'comb',1,1,1,82,0,472,2,0,0,0,0,0,0,0,82,,0,0,63,,472,-38,-38,-38,-38,-38
S,Add,,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
S,+,Add two power series,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
S,Sub,,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
S,-,Subtract two power series,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
S,Mult,,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
S,*,Multiply two power series,0,2,0,0,0,0,0,0,0,472,,0,0,472,,472,-38,-38,-38,-38,-38
