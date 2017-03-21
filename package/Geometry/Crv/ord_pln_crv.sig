174,1
A,Crv,3,b_ord,ord_mult,Iadj
S,CanonicalImage,Returns the image of C under canonical map phi and whether C is hyperelliptic,0,2,0,0,0,0,0,0,0,376,,0,0,371,,371,36,-38,-38,-38,-38
S,CanonicalImage,Returns the image of C under canonical map defined by eqns and whether C is hyperelliptic,0,2,0,0,0,0,0,0,0,82,,0,0,371,,371,36,-38,-38,-38,-38
S,AdjointIdealForNodalCurve,Assuming plane curve C only has double points computes the adjoint ideal,0,1,0,0,0,0,0,0,0,371,,64,-38,-38,-38,-38,-38
S,AdjointLinearSystemForNodalCurve,Assuming plane curve C only has double points computes the adjoint linear system of degree d,0,2,0,0,0,0,0,0,0,148,,0,0,371,,167,-38,-38,-38,-38,-38
S,AdjointLinearSystemFromIdeal,I is the (saturated) adjoint ideal of a plane projective curve. Returns the degree d adjoint linear system of the curve,0,2,0,0,0,0,0,0,0,148,,0,0,64,,167,-38,-38,-38,-38,-38
S,CanonicalLinearSystemFromIdeal,I is the (saturated) adjoint ideal of a plane projective curve. Returns the canonical linear system of the curve,0,2,0,0,0,0,0,0,0,148,,0,0,64,,167,-38,-38,-38,-38,-38
S,HasOnlyOrdinarySingularities,"Returns whether plane curve C only has ordinary singularities. Also returns the maximum multiplicity of a singular point (1 if F is non-singular). If the boolean parameter Adjoint is true AND the curve is ordinary, then the adjoint ideal is computed and is a third return value",0,1,0,0,0,0,0,0,0,371,,36,148,64,-38,-38,-38
S,AdjointIdeal,"For ordinary plane curve C, returns the adjoint ideal. If C is not ordinary, an error results",0,1,0,0,0,0,0,0,0,371,,64,-38,-38,-38,-38,-38
S,HasOnlyOrdinarySingularitiesMonteCarlo,"For plane curve C over Q determines whether all singularities are PROBABLY ordinary using mod p reduction for 5 good primes. If so, also returns the maximum multiplicity of a singularity",0,1,0,0,0,0,0,0,0,371,,36,148,-38,-38,-38,-38
