package _weierstrass

/*
This implements prime order short Weierstrass curves defined over a field
k with char(k) != 2, 3 (`y^2 = x^3 + ax + b`). for the purpose of
implementing ECDH and ECDSA.  Use of this package for other purposes is
NOT RECOMMENDED.

As an explicit simplicity/performance tradeoff, projective representation
was chosen so that it is possible to use the complete addition
formulas.

See:
- https://eprint.iacr.org/2015/1060.pdf
- https://hyperelliptic.org/EFD/g1p/auto-shortw-projective.html

WARNING: The point addition and doubling formulas are specialized for
`a = -3`, which covers secp256r1, secp384r1, secp521r1, FRP256v1, SM2,
and GOST 34.10.  The brainpool curves and secp256k1 are NOT SUPPORTED
and would require slightly different formulas.
*/

// Curve is a named curve.
Curve :: enum {
	Invalid,
	Secp256r1,
	// Secp384r1,
	// Secp521r1,
}

Point_p256r1 :: struct {
	_x: Field_Element_p256r1,
	_y: Field_Element_p256r1,
	_z: Field_Element_p256r1,
}

pt_identity :: proc "contextless" (p: ^$T) {
	fe_zero(&p._x)
	fe_one(&p._y)
	fe_zero(&p._z)
}

pt_generator :: proc "contextless" (p: ^$T) {
	when T == Point_p256r1 {
		fe_gen_x(&p._x)
		fe_gen_y(&p._y)
	} else {
		#panic("weierstrass: invalid curve")
	}
	fe_one(&p._z)
}

pt_clear :: proc "contextless" (p: ^$T) {
	fe_clear(&p._x)
	fe_clear(&p._y)
	fe_clear(&p._z)
}

pt_add :: proc "contextless" (p, a, b: ^$T) {
	// Algorithm 4 from "Complete addition formulas for prime
	// order elliptic curves" by Renes, Costello, and Batina.
	//
	// The formula is complete in that it is valid for all a and b,
	// without exceptions or extra assumptions about the inputs.
	//
	// The operation costs are `12M + 2mb + 29a`.

	t0, t1, t2, t3, t4, b: T
	x1, y1, z1 := &a._x, &a._y, &a._z
	x2, y2, z2 := &b._x, &b._y, &b._z
	x3, y3, z3: T

	fe_b(&b)

	// t0 := X1 * X2 ; t1 := Y1 * Y2 ; t2 := Z1 * Z2 ;
	fe_mul(&t0, x1, x2)
	fe_mul(&t1, y1, y2)
	fe_mul(&t2, z1, z2)

	// t3 := X1 + Y1 ; t4 := X2 + Y2 ; t3 := t3 * t4 ;
	fe_add(&t3, x1, y1)
	fe_add(&t4, x2, y2)
	fe_mul(&t3, &t3, &t4)

	// t4 := t0 + t1 ; t3 := t3 - t4 ; t4 := Y1 + Z1 ;
	fe_add(&t4, &t0, &t1)
	fe_sub(&t3, &t3, &t4)
	fe_add(&t4, y1, z1)

	// X3 := Y2 + Z2 ; t4 := t4 * X3 ; X3 := t1 + t2 ;
	fe_add(&x3, y2, z2)
	fe_mul(&t4, &t4, &x3)
	fe_add(&x3, &t1, &t2)

	// t4 := t4 - X3 ; X3 := X1 + Z1 ; Y3 := X2 + Z2 ;
	fe_sub(&t4, &t4, &x3)
	fe_add(&x3, x1, z1)
	fe_add(&y3, x2, z2)

	// X3 := X3 * Y3 ; Y3 := t0 + t2 ; Y3 := X3 - Y3 ;
	fe_mul(&x3, &x3, &y3)
	fe_add(&y3, &t0, &t2)
	fe_sub(&y3, &x3, &y3)

	// Z3 := b * t2 ; X3 := Y3 - Z3 ; Z3 := X3 + X3 ;
	fe_mul(&z3, &b, &t2)
	fe_sub(&x3, &y3, &z3)
	fe_add(&z3, &x3, &x3)

	// X3 := X3 + Z3 ; Z3 := t1 - X3 ; X3 := t1 + X3 ;
	fe_add(&x3, &x3, &z3)
	fe_sub(&z3, &t1, &x3)
	fe_add(&x3, &t1, &x3)

	// Y3 := b * Y3 ; t1 := t2 + t2 ; t2 := t1 + t2 ;
	fe_mul(&y3, &b, &y3)
	fe_add(&t1, &t2, &t2)
	fe_add(&t2, &t1, &t2)

	// Y3 := Y3 - t2 ; Y3 := Y3 - t0 ; t1 := Y3 + Y3 ;
	fe_sub(&y3, &y3, &t2)
	fe_sub(&y3, &y3, &t0)
	fe_add(&t1, &y3, &y3)

	// Y3 := t1 + Y3 ; t1 := t0 + t0 ; t0 := t1 + t0 ;
	fe_add(&y3, &t1, &y3)
	fe_add(&t1, &t0, &t0)
	fe_add(&t0, &t1, &t0)

	// t0 := t0 - t2 ; t1 := t4 * Y3 ; t2 := t0 * Y3 ;
	fe_sub(&t0, &t0, &t2)
	fe_mul(&t1, &t4, &y3)
	fe_mul(&t2, &t0, &y3)

	// Y3 := X3 * Z3 ; Y3 := Y3 + t2 ; X3 := t3 * X3 ;
	fe_mul(&y3, &x3, &z3)
	fe_add(&y3, &y3, &t2)
	fe_mul(&x3, &t3, &x3)

	// X3 := X3 - t1 ; Z3 := t4 * Z3 ; t1 := t3 * t0 ;
	fe_sub(&x3, &x3, &t1)
	fe_mul(&z3, &t4, &z3)
	fe_mul(&t1, &t3, &t0)

	// Z3 := Z3 + t1 ;
	fe_add(&z3, &z3, &t1)

	// return X3 , Y3 , Z3 ;
	fe_set(&p._x, &x3)
	fe_set(&p._y, &y3)
	fe_set(&p._z, &z3)

	fe_clear_vec([]T{&t0, &t1, &t2, &t3, &t4, &x3, &y3, &z3})
}

@(private)
pt_add_mixed :: proc "contextless" (p, a, b: ^$T) {
	// Algorithm 5 from "Complete addition formulas for prime
	// order elliptic curves" by Renes, Costello, and Batina.
	//
	// The formula is mixed in that it assumes the z-coordinate
	// of the addend (`Z2`) is `1`, meaning that it CAN NOT
	// handle the addend being the point at infinity.
	//
	// The operation costs are `11M + 2mb + 23a` saving
	// `1M + 6a` over `pt_add`.

	t0, t1, t2, t3, t4, b: T
	x1, y1, z1 := &a._x, &a._y, &a._z
	x2, y2, z2 := &b._x, &b._y, &b._z
	x3, y3, z3: T

	fe_b(&b)

	// t0 := X1 * X2 ; t1 := Y1 * Y2 ; t3 := X2 + Y2 ;
	fe_mul(&t0, x1, x2)
	fe_mul(&t1, y1, y2)
	fe_add(&t3, x2, y2)

	// t4 := X1 + Y1 ; t3 := t3 * t4 ; t4 := t0 + t1 ;
	fe_add(&t4, x1, y1)
	fe_mul(&t3, &t3, &t4)
	fe_add(&t4, &t0, &t1)

	// t3 := t3 − t4 ; t4 := Y2 * Z1 ; t4 := t4 + Y1 ;
	fe_sub(&t3, &t3, &t4)
	fe_mul(&t4, y2, z1)
	fe_add(&t4, &t4, y1)

	// Y3 := X2 * Z1 ; Y3 := Y3 + X1 ; Z3 := b * Z1 ;
	fe_mul(&y3, x2, z1)
	fe_add(&y3, &y3, x1)
	fe_mul(&z3, &b, z1)

	// X3 := Y3 − Z3 ; Z3 := X3 + X3 ; X3 := X3 + Z3 ;
	fe_sub(&x3, &y3, &z3)
	fe_add(&z3, &x3, &x3)
	fe_add(&x3, &x3, &z3)

	// Z3 := t1 − X3 ; X3 := t1 + X3 ;. Y3 := b * Y3 ;
	fe_sub(&z3, &t1, &x3)
	fe_add(&x3, &t1, &x3)
	fe_mul(&y3, &b, &y3)

	// t1 := Z1 + Z1 ; t2 := t1 + Z1 ; Y3 := Y3 − t2 ;
	fe_add(&t1, z1, z1)
	fe_add(&t2, &t1, z1)
	fe_sub(&y3, &y3, &t2)

	// Y3 := Y3 − t0 ; t1 := Y3 + Y3 ; Y3 := t1 + Y3 ;
	fe_sub(&y3, &y3, &t0)
	fe_add(&t1, &y3, &y3)
	fe_add(&y3, &t1, &y3)

	// t1 := t0 + t0 ; t0 := t1 + t0 ; t0 := t0 − t2 ;
	fe_add(&t1, &t0, &t0)
	fe_add(&t0, &t1, &t0)
	fe_sub(&t0, &t0, &t2)

	// t1 := t4 * Y3 ; t2 := t0 * Y3 ; Y3 := X3 * Z3 ;
	fe_mul(&t1, &t4, &y3)
	fe_mul(&t2, &t0, &y3)
	fe_mul(&y3, &x3, &z3)

	// Y3 := Y3 + t2 ; X3 := t3 * X3 ; X3 := X3 − t1 ;
	fe_add(&y3, &y3, &t2)
	fe_mul(&x3, &t3, &x3)
	fe_sub(&x3, &x3, &t1)

	// Z3 := t4 * Z3 ; t1 := t3 * t0 ; Z3 := Z3 + t1 ;
	fe_mul(&z3, &t4, &z3)
	fe_mul(&t1, &t3, &t0)
	fe_add(&z3, &z3, &t1)

	// return X3 , Y3 , Z3 ;
	fe_set(&p._x, &x3)
	fe_set(&p._y, &y3)
	fe_set(&p._z, &z3)

	fe_clear_vec([]T{&t0, &t1, &t2, &t3, &t4, &x3, &y3, &z3})
}

pt_double :: proc "contextless" (p, a: ^$T) {
	// Algorithm 6 from "Complete addition formulas for prime
	// order elliptic curves" by Renes, Costello, and Batina.
	//
	// The formula is complete in that it is valid for all a,
	// without exceptions or extra assumptions about the inputs.
	//
	// The operation costs are `8M + 3S + 2mb + 21a`.

	t0, t1, t2, t3, b: T
	x, y, z := &a._x, &a._y, &a._z
	x3, y3, z3: T

	fe_b(&b)

	// t0 := X ^2; t1 := Y ^2; t2 := Z ^2;
	fe_square(&t0, x)
	fe_square(&t1, y)
	fe_square(&t2, z)

	// t3 := X * Y ; t3 := t3 + t3 ; Z3 := X * Z ;
	fe_mul(&t3, x, y)
	fe_add(&t3, &t3, &t3)
	fe_mul(&z3, x, z)

	// Z3 := Z3 + Z3 ; Y3 := b * t2 ; Y3 := Y3 - Z3 ;
	fe_add(&z3, &z3, &z3)
	fe_mul(&y3, &b, &t2)
	fe_sub(&y3, &y3, &z3)

	// X3 := Y3 + Y3 ; Y3 := X3 + Y3 ; X3 := t1 - Y3 ;
	fe_add(&x3, &y3, &y3)
	fe_add(&y3, &x3, &y3)
	fe_sub(&x3, &t1, &y3)

	// Y3 := t1 + Y3 ; Y3 := X3 * Y3 ; X3 := X3 * t3 ;
	fe_add(&y3, &t1, &y3)
	fe_mul(&y3, &x3, &y3)
	fe_mul(&x3, &x3, &t3)

	// t3 := t2 + t2 ; t2 := t2 + t3 ; Z3 := b * Z3 ;
	fe_add(&t3, &t2, &t2)
	fe_add(&t2, &t2, &t3)
	fe_mul(&z3, &b, &z3)

	// Z3 := Z3 - t2 ; Z3 := Z3 - t0 ; t3 := Z3 + Z3 ;
	fe_sub(&z3, &z3, &t2)
	fe_sub(&z3, &z3, &t0)
	fe_add(&t3, &z3, &z3)

	// Z3 := Z3 + t3 ; t3 := t0 + t0 ; t0 := t3 + t0 ;
	fe_add(&z3, &z3, &t3)
	fe_add(&t3, &t0, &t0)
	fe_add(&t0, &t3, &t0)

	// t0 := t0 - t2 ; t0 := t0 * Z3 ; Y3 := Y3 + t0 ;
	fe_sub(&t0, &t0, &t2)
	fe_mul(&t0, &t0, &z3)
	fe_add(&y3, &y3, &t0)

	// t0 := Y * Z ; t0 := t0 + t0 ; Z3 := t0 * Z3 ;
	fe_mul(&t0, y, z)
	fe_add(&t0, &t0, &t0)
	fe_mul(&z3, &t0, &z3)

	// X3 := X3 - Z3 ; Z3 := t0 * t1 ; Z3 := Z3 + Z3 ;
	fe_sub(&x3, &x3, &z3)
	fe_mul(&z3, &t0, &t1)
	fe_add(&z3, &z3, &z3)

	// Z3 := Z3 + Z3 ;
	fe_add(&z3, &z3, &z3)

	// return X3 , Y3 , Z3 ;
	fe_set(&p._x, &x3)
	fe_set(&p._y, &y3)
	fe_set(&p._z, &z3)

	fe_clear_vec([]T{&t0, &t1, &t2, &t3, &x3, &y3, &z3})
}

pt_sub :: proc "contextless" (p, a, b: ^$T) {
	b_neg: T
	pt_negate(&b_neg, b)
	pt_add(p, a, &b_neg)

	fe_clear(&b_neg)
}

pt_negate :: proc "contextless" (p, a: ^$T) {
	fe_set(&p._x, &a._x)
	fe_neg(&p._y, &a._y)
	fe_set(&p._z, &a._z)
}

pt_rescale :: proc "contextless" (p, a: ^$T) {
	// A = 1/Z1
	// X3 = A*X1
	// Y3 = A+Y1
	// Z3 = 1
	//
	// As per "From A to Z: Projective coordinates leakage in the wild"
	// leaking the Z-coordinate is bad. The modular inversion algorithm
	// used in this library is based on Fermat's Little Theorem.
	//
	// See: https://eprint.iacr.org/2020/432.pdf

	was_identity := pt_is_identity(a)

	z_inv, ident: T
	fe_inv(&z_inv, &a._z)
	fe_mul(&p._x, &a._x, &z_inv)
	fe_mul(&p._y, &a._y, &z_inv)
	fe_one(&p._z)

	pt_identity(&ident)
	pt_cond_select(p, p, &ident, ctrl)

	fe_clear(&z_inv)
}

pt_cond_select :: proc "contextless" (p, a, b: ^$T, ctrl: int) {
	fe_cond_select(&p._x, &a._x, &b._x, ctrl)
	fe_cond_select(&p._y, &a._y, &b._y, ctrl)
	fe_cond_select(&p._z, &a._z, &b._z, ctrl)
}

pt_is_identity :: proc "contextless" (p: ^$T) -> int {
	return fe_is_zero(&p._z)
}
