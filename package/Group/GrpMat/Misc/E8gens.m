freeze;

//	E8gens.m
//
//	D E Taylor and L J Rylands
//
//	21 September 1997
//
// ====================================================
// Generators for the groups of type E8 as 248 x 248 matrices
//  
//  Reference:
//  Howlett, Rylands & Taylor, Matrix generators for exceptional groups of
//  type, J. Symbolic Comp. (2001) 31, 429-445.
// ----------------------------------------------------
// History
// ~~~~~~~
//  21 Sep 97	Used the Maple program Lie.mpl to create the
//		matrices for the adjoint representation of
//		the Lie algebra.
//
//  23 Sep 97	Used a pre-computed version of the Coxeter element
//
//  3  Jul 05   Speed-ups by Bill Unger: Precomputed versions of e8^2/2 and
//              f8^2/2, Only work in finite field (not rationals),
//              Reduce amount of coercion.
// ----------------------------------------------------
// Comments
// ~~~~~~~~
// 1) This is the adjoint action.
// 2) Checked orders of random elements for E8(2) and E8(5): OK
// ====================================================
// ----------------------------------------------------
//
//      1   3   4   5   6   7   8
// E_8  o---o---o---o---o---o---o
//              |
//            2 o
//
// ----------------------------------------------------
//  The Lie algebra of type E8 with respect to a
//  Chevalley basis.
// ----------------------------------------------------
LieZE8 := function(F);

// Even though all matrix entries are integers, we
// use the rationals so that we can divide later on.

// No we don't, we work over F and also return e8^2/2: Bill Unger 3/7/05

  M := MatrixRing( F, 248 );

// The root element e8 in the Lie algebra

  one := F!1;
  m1 := F!-1;
  e8 := Zero( M );

  e8[1, 2] := one;
  e8[20, 24] := m1;
  e8[23, 28] := m1;
  e8[27, 32] := m1;
  e8[31, 36] := m1;
  e8[34, 39] := m1;
  e8[35, 41] := m1;
  e8[38, 45] := m1;
  e8[40, 46] := m1;
  e8[43, 50] := m1;
  e8[44, 51] := m1;
  e8[48, 55] := m1;
  e8[49, 57] := m1;
  e8[53, 60] := m1;
  e8[54, 62] := m1;
  e8[56, 63] := m1;
  e8[59, 66] := m1;
  e8[61, 68] := m1;
  e8[65, 72] := m1;
  e8[67, 75] := m1;
  e8[71, 80] := m1;
  e8[74, 82] := m1;
  e8[78, 86] := m1;
  e8[79, 87] := m1;
  e8[85, 93] := m1;
  e8[92, 100] := m1;
  e8[99, 107] := m1;
  e8[106, 114] := m1;
  e8[113, 127] := one;
  e8[113, 128] := m1+m1;
  e8[128, 136] := one;
  e8[135, 143] := one;
  e8[142, 150] := one;
  e8[149, 157] := one;
  e8[156, 164] := one;
  e8[162, 170] := one;
  e8[163, 171] := one;
  e8[167, 175] := one;
  e8[169, 178] := one;
  e8[174, 182] := one;
  e8[177, 184] := one;
  e8[181, 188] := one;
  e8[183, 190] := one;
  e8[186, 193] := one;
  e8[187, 195] := one;
  e8[189, 196] := one;
  e8[192, 200] := one;
  e8[194, 201] := one;
  e8[198, 205] := one;
  e8[199, 206] := one;
  e8[203, 209] := one;
  e8[204, 211] := one;
  e8[208, 214] := one;
  e8[210, 215] := one;
  e8[213, 218] := one;
  e8[217, 222] := one;
  e8[221, 226] := one;
  e8[225, 229] := one;
  e8[247, 248] := m1;

// construct e8^2/2 as well

  e82 := Zero( M );

  e82[ 113, 136 ] := m1;

  return e8, e82;

end function;

// ----------------------------------------------------
// Generators for the group E8(F), F a finite field.
// ----------------------------------------------------
intrinsic E8gens(F::FldFin) -> AlgMatElt, AlgMatElt
{Steinberg generators for E_8(F)}

// Matrices for the fundamental root elements in the Lie algebra

  e8, e82 := LieZE8(F);

// The matrix of the negative of a fundamental root is almost
// the transpose of the matrix of the positive root:

  evert := function( e, i );
    K := BaseRing(Parent(e));
    f := Transpose( e );
    zero := K!0;

    f[128+i,120+i] := zero;
    for j in [1..8] do
      f[120+j,121-i] := zero;
    end for;

    f[120+i,121-i] := K!-1;
    for j in [1..8] do
      f[128+i,120+j] := -e[121-i,120+j];
    end for;

    return f;
  end function;

  M := MatrixRing( F, 248 );

  exp2 := func< M, e, e2, a | M!1 + a*e + a*a*e2 >;

  one := F!1;
  m1 := F!-1;

// x_a(1), a = 1..8

  x8 := exp2( M, e8, e82, one);

// A Coxeter element.

  w := Zero( M );

  w[ 1 , 11 ] := one;
  w[ 2 , 1 ] := m1;
  w[ 3 , 2 ] := m1;
  w[ 4 , 3 ] := m1;
  w[ 5 , 4 ] := m1;
  w[ 6 , 5 ] := m1;
  w[ 7 , 9 ] := m1;
  w[ 8 , 7 ] := m1;
  w[ 9 , 10 ] := m1;
  w[ 10 , 13 ] := one;
  w[ 11 , 15 ] := one;
  w[ 12 , 16 ] := one;
  w[ 13 , 18 ] := one;
  w[ 14 , 19 ] := one;
  w[ 15 , 25 ] := one;
  w[ 16 , 22 ] := one;
  w[ 17 , 23 ] := one;
  w[ 18 , 29 ] := one;
  w[ 19 , 27 ] := one;
  w[ 20 , 28 ] := m1;
  w[ 21 , 33 ] := one;
  w[ 22 , 34 ] := one;
  w[ 23 , 32 ] := m1;
  w[ 24 , 6 ] := one;
  w[ 25 , 47 ] := one;
  w[ 26 , 38 ] := one;
  w[ 27 , 39 ] := m1;
  w[ 28 , 8 ] := one;
  w[ 29 , 53 ] := one;
  w[ 30 , 44 ] := one;
  w[ 31 , 45 ] := m1;
  w[ 32 , 12 ] := m1;
  w[ 33 , 59 ] := one;
  w[ 34 , 60 ] := m1;
  w[ 35 , 51 ] := m1;
  w[ 36 , 14 ] := m1;
  w[ 37 , 65 ] := one;
  w[ 38 , 66 ] := m1;
  w[ 39 , 21 ] := m1;
  w[ 40 , 58 ] := one;
  w[ 41 , 17 ] := m1;
  w[ 42 , 78 ] := one;
  w[ 43 , 72 ] := m1;
  w[ 44 , 73 ] := one;
  w[ 45 , 26 ] := m1;
  w[ 46 , 20 ] := m1;
  w[ 47 , 85 ] := one;
  w[ 48 , 86 ] := m1;
  w[ 49 , 81 ] := one;
  w[ 50 , 30 ] := m1;
  w[ 51 , 31 ] := m1;
  w[ 52 , 24 ] := m1;
  w[ 53 , 93 ] := m1;
  w[ 54 , 94 ] := one;
  w[ 55 , 37 ] := one;
  w[ 56 , 89 ] := m1;
  w[ 57 , 35 ] := m1;
  w[ 58 , 36 ] := m1;
  w[ 59 , 101 ] := one;
  w[ 60 , 42 ] := one;
  w[ 61 , 102 ] := m1;
  w[ 62 , 43 ] := one;
  w[ 63 , 40 ] := m1;
  w[ 64 , 41 ] := m1;
  w[ 65 , 109 ] := m1;
  w[ 66 , 48 ] := one;
  w[ 67 , 110 ] := one;
  w[ 68 , 49 ] := one;
  w[ 69 , 50 ] := one;
  w[ 70 , 46 ] := m1;
  w[ 71 , 117 ] := one;
  w[ 72 , 54 ] := one;
  w[ 73 , 55 ] := one;
  w[ 74 , 129 ] := m1;
  w[ 75 , 56 ] := one;
  w[ 76 , 57 ] := one;
  w[ 77 , 52 ] := m1;
  w[ 78 , 137 ] := m1;
  w[ 79 , 130 ] := one;
  w[ 80 , 61 ] := one;
  w[ 81 , 62 ] := one;
  w[ 82 , 71 ] := m1;
  w[ 83 , 63 ] := one;
  w[ 84 , 64 ] := one;
  w[ 85 , 151 ] := one;
  w[ 86 , 79 ] := m1;
  w[ 87 , 74 ] := one;
  w[ 88 , 68 ] := one;
  w[ 89 , 69 ] := one;
  w[ 90 , 80 ] := m1;
  w[ 91 , 70 ] := one;
  w[ 92 , 158 ] := one;
  w[ 93 , 92 ] := one;
  w[ 94 , 87 ] := m1;
  w[ 95 , 82 ] := one;
  w[ 96 , 76 ] := one;
  w[ 97 , 88 ] := m1;
  w[ 98 , 77 ] := one;
  w[ 99 , 166 ] := one;
  w[ 100 , 99 ] := one;
  w[ 101 , 100 ] := one;
  w[ 102 , 95 ] := m1;
  w[ 103 , 90 ] := one;
  w[ 104 , 84 ] := one;
  w[ 105 , 96 ] := m1;
  w[ 106 , 174 ] := one;
  w[ 107 , 106 ] := one;
  w[ 108 , 107 ] := one;
  w[ 109 , 108 ] := one;
  w[ 110 , 103 ] := m1;
  w[ 111 , 97 ] := one;
  w[ 112 , 104 ] := m1;
  w[ 113 , 182 ] := one;
  w[ 114 , 113 ] := one;
  w[ 115 , 114 ] := one;
  w[ 116 , 115 ] := one;
  w[ 117 , 116 ] := one;
  w[ 118 , 111 ] := m1;
  w[ 119 , 105 ] := one;
  w[ 120 , 118 ] := one;
  w[ 121 , 121 ] := m1;
  w[ 121 , 123 ] := one;
  w[ 122 , 122 ] := m1;
  w[ 122 , 124 ] := one;
  w[ 123 , 121 ] := m1;
  w[ 123 , 124 ] := one;
  w[ 124 , 121 ] := m1;
  w[ 124 , 122 ] := m1;
  w[ 124 , 124 ] := one;
  w[ 124 , 125 ] := one;
  w[ 125 , 121 ] := m1;
  w[ 125 , 122 ] := m1;
  w[ 125 , 124 ] := one;
  w[ 125 , 126 ] := one;
  w[ 126 , 121 ] := m1;
  w[ 126 , 122 ] := m1;
  w[ 126 , 124 ] := one;
  w[ 126 , 127 ] := one;
  w[ 127 , 121 ] := m1;
  w[ 127 , 122 ] := m1;
  w[ 127 , 124 ] := one;
  w[ 127 , 128 ] := one;
  w[ 128 , 121 ] := m1;
  w[ 128 , 122 ] := m1;
  w[ 128 , 124 ] := one;
  w[ 129 , 131 ] := one;
  w[ 130 , 144 ] := one;
  w[ 131 , 138 ] := m1;
  w[ 132 , 133 ] := one;
  w[ 133 , 134 ] := one;
  w[ 134 , 135 ] := one;
  w[ 135 , 136 ] := one;
  w[ 136 , 67 ] := one;
  w[ 137 , 145 ] := m1;
  w[ 138 , 152 ] := one;
  w[ 139 , 146 ] := m1;
  w[ 140 , 141 ] := one;
  w[ 141 , 142 ] := one;
  w[ 142 , 143 ] := one;
  w[ 143 , 75 ] := one;
  w[ 144 , 153 ] := m1;
  w[ 145 , 165 ] := one;
  w[ 146 , 159 ] := one;
  w[ 147 , 154 ] := m1;
  w[ 148 , 149 ] := one;
  w[ 149 , 150 ] := one;
  w[ 150 , 83 ] := one;
  w[ 151 , 172 ] := one;
  w[ 152 , 161 ] := m1;
  w[ 153 , 173 ] := one;
  w[ 154 , 167 ] := one;
  w[ 155 , 162 ] := m1;
  w[ 156 , 157 ] := one;
  w[ 157 , 91 ] := one;
  w[ 158 , 179 ] := one;
  w[ 159 , 169 ] := m1;
  w[ 160 , 180 ] := one;
  w[ 161 , 181 ] := one;
  w[ 162 , 175 ] := one;
  w[ 163 , 170 ] := m1;
  w[ 164 , 98 ] := one;
  w[ 165 , 185 ] := one;
  w[ 166 , 186 ] := one;
  w[ 167 , 178 ] := m1;
  w[ 168 , 187 ] := one;
  w[ 169 , 188 ] := one;
  w[ 170 , 119 ] := one;
  w[ 171 , 112 ] := m1;
  w[ 172 , 197 ] := m1;
  w[ 173 , 192 ] := one;
  w[ 174 , 193 ] := one;
  w[ 175 , 120 ] := m1;
  w[ 176 , 194 ] := one;
  w[ 177 , 195 ] := one;
  w[ 178 , 132 ] := one;
  w[ 179 , 203 ] := m1;
  w[ 180 , 199 ] := one;
  w[ 181 , 200 ] := one;
  w[ 182 , 139 ] := one;
  w[ 183 , 201 ] := one;
  w[ 184 , 140 ] := m1;
  w[ 185 , 208 ] := m1;
  w[ 186 , 209 ] := m1;
  w[ 187 , 206 ] := one;
  w[ 188 , 147 ] := m1;
  w[ 189 , 207 ] := one;
  w[ 190 , 148 ] := one;
  w[ 191 , 213 ] := m1;
  w[ 192 , 214 ] := m1;
  w[ 193 , 160 ] := m1;
  w[ 194 , 212 ] := one;
  w[ 195 , 155 ] := one;
  w[ 196 , 156 ] := m1;
  w[ 197 , 225 ] := m1;
  w[ 198 , 218 ] := m1;
  w[ 199 , 219 ] := m1;
  w[ 200 , 168 ] := one;
  w[ 201 , 163 ] := m1;
  w[ 202 , 164 ] := one;
  w[ 203 , 229 ] := m1;
  w[ 204 , 223 ] := m1;
  w[ 205 , 176 ] := one;
  w[ 206 , 177 ] := m1;
  w[ 207 , 171 ] := one;
  w[ 208 , 232 ] := m1;
  w[ 209 , 191 ] := one;
  w[ 210 , 228 ] := m1;
  w[ 211 , 183 ] := m1;
  w[ 212 , 184 ] := one;
  w[ 213 , 235 ] := m1;
  w[ 214 , 198 ] := m1;
  w[ 215 , 189 ] := m1;
  w[ 216 , 190 ] := one;
  w[ 217 , 237 ] := m1;
  w[ 218 , 204 ] := m1;
  w[ 219 , 205 ] := one;
  w[ 220 , 196 ] := one;
  w[ 221 , 241 ] := one;
  w[ 222 , 210 ] := m1;
  w[ 223 , 211 ] := one;
  w[ 224 , 202 ] := one;
  w[ 225 , 243 ] := one;
  w[ 226 , 217 ] := m1;
  w[ 227 , 215 ] := one;
  w[ 228 , 216 ] := one;
  w[ 229 , 221 ] := m1;
  w[ 230 , 222 ] := one;
  w[ 231 , 220 ] := one;
  w[ 232 , 226 ] := one;
  w[ 233 , 227 ] := one;
  w[ 234 , 224 ] := one;
  w[ 235 , 230 ] := one;
  w[ 236 , 231 ] := one;
  w[ 237 , 233 ] := one;
  w[ 238 , 234 ] := one;
  w[ 239 , 236 ] := one;
  w[ 240 , 239 ] := m1;
  w[ 241 , 242 ] := m1;
  w[ 242 , 240 ] := m1;
  w[ 243 , 244 ] := m1;
  w[ 244 , 245 ] := m1;
  w[ 245 , 246 ] := m1;
  w[ 246 , 247 ] := m1;
  w[ 247 , 248 ] := m1;
  w[ 248 , 238 ] := one;

// Steinberg's generators:

  if #F lt 4 then

    return x8, w;

  else

    f8   := evert( e8, 8 );

    // f8^2/2
    f82 := M!0;
    f82[136, 113] := m1;

    xi := PrimitiveElement( F );

// H8 is a diagonal element and n8xi is n_8(xi)

    H8 := exp2(M, e8, e82, xi)*exp2(M, f8, f82, -xi^-1)*exp2(M, e8, e82, xi)*
	    exp2(M, e8, e82, m1)*exp2(M, f8, f82, one)*exp2(M, e8, e82, m1);

    return H8, x8 * w;

  end if;

end intrinsic;
