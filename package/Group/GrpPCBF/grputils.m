freeze;

/*
====================================================

Filename: grputils.m

Date: 10/03/2009

Description: 

Comments: 

====================================================
*/



WordMultiply := function(indeximgs, word)
	/*

	Arguments:

		indeximgs: Sequence of group elements, Type(s): SeqEnum
	
		word: Sequence of integers representing a word in group elements indexed by indeximgs, Type(s): SeqEnum

	Parameters:
	

	Return Type(s):

		GrpElt

	Description:
	
		Computes the product of the sequence of group elements represented by word.

	*/
	ans := Identity(Parent(indeximgs[1]));
	for i in [1 .. #word] do
		ans *:= word[i] gt 0 select indeximgs[word[i]] else (indeximgs[-word[i]])^-1; // multiply by inverse for negative entries
	end for;
	return ans;
end function;

