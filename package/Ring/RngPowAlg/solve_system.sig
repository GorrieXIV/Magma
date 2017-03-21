174,1
S,AllRoots,"Find all roots to a polynomial equation. For a class of conjugate roots (with respect to the ground field) only one representative (in an appropriate extension) is returned. The first return value is a list '[* [* x, m *] ... *]' where 'x' is a root with multiplicity 'm'. If the ground field has to be extended, the algebraic elements will be displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return value is the value of 'ExtCount' plus the number of field extensions that have been introduced during the computation",0,1,0,0,0,0,0,0,0,312,,168,-45,-38,-38,-38,-38
S,RepresentativePoints,"The scheme points of the zero-dimensional scheme X, returned as points of X over field extensions. (There is one point for each irreducible component)",0,1,0,0,0,0,0,0,0,-1,,168,-38,-38,-38,-38,-38
S,SolveZeroDimIdeal,"Find the solutions of the (at most) zero-dimensional ideal 'I' of a multivariate polynomial ring. For a class of conjugate solutions (with respect to the ground field) only one representative (in an appropriate extension) is returned. The first return value is a list '[* <[x_1, ..., x_n], m, d>, ... *]' where '[x_1, ..., x_n]' is a solution of 'I', 'm' its multiplicity and 'd' the degree of the residue field over the ground field. If the ground field has to be extended, the algebraic elements will be displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return value is the value of 'ExtCount' plus the number of field extensions that have been introduced during the computation",0,1,0,0,0,0,0,0,0,64,,168,148,-38,-38,-38,-38
S,OSolveZeroDimIdeal,"Find the solutions of the (at most) zero-dimensional ideal 'I' of a multivariate polynomial ring. For a class of conjugate solutions (with respect to the ground field) only one representative (in an appropriate extension) is returned. The first return value is a list '[* <[x_1, ..., x_n], m, d>, ... *]' where '[x_1, ..., x_n]' is a solution of 'I', 'm' its multiplicity and 'd' the degree of the residue field over the ground field. If the ground field has to be extended, the algebraic elements will be displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return value is the value of 'ExtCount' plus the number of field extensions that have been introduced during the computation",0,1,0,0,0,0,0,0,0,64,,168,148,-38,-38,-38,-38
S,SolveInProductSpace,"Given an ideal 'id' of a polynomial ring 'P' of rank 'n' and a sequence 'seq' s.t. the 'seq[i]' mark blocks of projective coordinates. Assuming that 'id' defines a zero-dimensional subset in the corresponding product space (with projective and affine components) returns a list of all (finitely many) points in the subset. For example, if 'n=6' and 'seq=[0,2,5]' then '[P.1 : P.2]' and '[P.3 : P.4 : P.5]' are the blocks of projective coordinates and 'P.6' is an affine coordinate. Then 'id' should be a two-dimensional ideal homogeneous w.r.t. total degrees for both blocks separately. It defines a point set in 'P^1 X P^2 X A^1'. If no projective coordinates are intended use 'seq=[0]'. If the ground field has to be extended, the algebraic elements will be displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return value is the value of 'ExtCount' plus the number of field extensions that have been introduced during the computation",0,1,0,0,0,0,0,0,0,64,,168,148,-38,-38,-38,-38