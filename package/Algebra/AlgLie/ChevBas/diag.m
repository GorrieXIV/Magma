freeze;

/* 
 * Dan Roozemond, 2010. 
 */

simdiag := function(Ms)
	local a,b;
	a,b := CommonEigenspaces([ Matrix(m) : m in Ms]);
	return a, SequenceToList(b);
end function;
