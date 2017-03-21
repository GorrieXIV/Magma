freeze;

// import "/usr/local/lib/magma/2.18-5/package/Group/GrpPC/pgrps/unipotent.m": PGroupStabiliser;

import "pgroup-unipotent.m": PGroupStabiliser;

/* Much of this code was similar to intrinsic copy of UnipotentStabiliser
   but there were some differences (known mostly to Elliot Costi), so 
   we retained it.

   See that file, package/Group/GrpPC/pgrps/unipotent.m, for some more 
   information.

   Dan Roozemond, Mar 2011.
   While cleaning up *this* file so that it uses more of ^^ *that* file, 
   I came across the following differences, and changed things so that:

   * The VectorCF, NextSubspaceCF, and SubspaceCF in *this* were 
     identical to the ones in *that*, provided the latter are called 
     with optional parameter InitStr := "XB".
   * The PGroupStabiliser in *this* was identical to the one in *that*
     provided the latter is called with InitStr := <"XB", "XB">.
   * The UnipotentStabiliser in *this* is identical to the intrinsic
     with InitStr := <"XB", "XB"> (and with the added caveat that the 
     intrinsic doesn't support the optional ComputeBase parameter.)
   
 */


/* G is a p-subgroup of GL(d, q) where GF(q) has characteristic p;
   U is a subspace of the vector space G acts on. This function
   returns the stabilizer of U in G (stab), a canonical form for U (cf),
   an element of G (trans) that maps U to cf, and an SLP for trans
   in WordGroup (G) */

function UnipotentStabiliser (G, U: ComputeBase := true)

  W := WordGroup(G); 
   cf, trans, transslp, stab := PGroupStabiliser (G, U, W: 
      ComputeBase := ComputeBase, InitStrs := <"XB","XB">);

   return stab, cf, trans, transslp;

end function;

