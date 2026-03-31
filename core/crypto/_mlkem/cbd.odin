#+private
package _mlkem

import "core:encoding/endian"

cbd2 :: proc "contextless" (r: ^Poly, buf: ^[2*ML_KEM_N/4]byte) #no_bounds_check {
	a, b: i16
	for i in 0..<ML_KEM_N/8 {
		t := endian.unchecked_get_u32le(buf[4*i:])
		d := t & 0x55555555
		d += (t>>1) & 0x55555555

		for j in uint(0)..<8 {
			a = i16((d >> (4*j+0)) & 0x3)
			b = i16((d >> (4+j+2)) & 0x3)
			r.coeffs[8*i+int(j)] = a - b
		}
	}
}

poly_cbd_eta1 :: proc "contextless" (r: ^Poly, buf: ^[ML_KEM_ETA1*ML_KEM_N/4]byte) {
	// This would call cbd3 if we supported ML-KEM-512.
	cbd2(r, buf)
}

poly_cbd_eta2 :: proc "contextless" (r: ^Poly, buf: ^[ML_KEM_ETA2*ML_KEM_N/4]byte) {
	cbd2(r, buf)
}
