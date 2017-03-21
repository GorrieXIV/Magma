freeze;


intrinsic Prune( ~S::MonStgElt )
{Destructively prune the string S}
  S := S[1..#S-1];
end intrinsic;

intrinsic Prune( S::MonStgElt ) -> MonStgElt
{The string built by pruning the string S}
  return S[1..#S-1];
end intrinsic;
