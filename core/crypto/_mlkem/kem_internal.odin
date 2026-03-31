package _mlkem

import "core:crypto"
import subtle "core:crypto/_subtle"

// This implementation is derived from the PQ-CRYSTALS reference
// implementation [[ https://github.com/pq-crystals/kyber ]],
// primarily for licensing reasons.  Arguably mlkem-native is
// a more "up to date" codebase, but the changes to the
// ref code is minor and they slapped an attribution-required
// license on something that was originally CC-0/Apache 2.0.

// "Private Key"
Decapsulation_Key :: struct {
	pke_dk: K_PKE_Decryption_Key,
	ek: Encapsulation_Key,
	seed: [ML_KEM_SYMBYTES*2]byte, // (d, z)
}

// "Public Key"
Encapsulation_Key :: struct {
	pke_ek: K_PKE_Encryption_Key,
	raw_bytes: [ML_KEM_INDCPA_PUBLICKEYBYTES_MAX]byte,
	h: [ML_KEM_SYMBYTES]byte,
}

@(require_results)
encapsulation_key_set_bytes :: proc(
	ek: ^Encapsulation_Key,
	k: int,
	b: []byte,
) -> bool {
	k_len: int
	switch k {
	case ML_KEM_K_768:
		k_len = ML_KEM_ENCAPSKEYBYTES_768
	case ML_KEM_K_1024:
		k_len = ML_KEM_ENCAPSKEYBYTES_1024
	case:
		return false
	}
	if len(b) != k_len {
		return false
	}

	pke_ek := &ek.pke_ek
	_ = unpack_pk(&pke_ek.pv, pke_ek.p[:], b)
	pke_ek.k = k
	_ = pack_pk(ek.raw_bytes[:k_len], &pke_ek.pv, pke_ek.p[:], k)
	hash_h(ek.h[:], b)

	ok := crypto.compare_constant_time(ek.raw_bytes[:k_len], b) == 1
	if !ok {
		crypto.zero_explicit(ek, size_of(Encapsulation_Key))
	}

	return ok
}

kem_keygen_internal :: proc(
	dk: ^Decapsulation_Key,
	ek: ^Encapsulation_Key,
	d, z: []byte,
	k: int,
) {
	ensure(len(d) == ML_KEM_SYMBYTES, "crypto/mlkem: invalid d")
	ensure(len(z) == ML_KEM_SYMBYTES, "crypto/mlkem: invalid z")

	dk_ek := &dk.ek

	k_pke_keygen(&dk_ek.pke_ek, &dk.pke_dk, d, k)

	ek_len := polyvec_byte_size(k) + ML_KEM_SYMBYTES
	ek_bytes := dk_ek.raw_bytes[:ek_len]
	ensure(
		pack_pk(ek_bytes, &dk_ek.pke_ek.pv, dk_ek.pke_ek.p[:], k),
		"crypto/mlkem: failed to pack K-PKE ek",
	)
	hash_h(dk_ek.h[:], ek_bytes)
	copy(dk.seed[:ML_KEM_SYMBYTES], d)
	copy(dk.seed[ML_KEM_SYMBYTES:], z)

	k_pke_encryption_key_set(&ek.pke_ek, &dk_ek.pke_ek)
	copy(ek.raw_bytes[:], ek_bytes)
	copy(ek.h[:], dk_ek.h[:])
}

// The `_internal` "de-randomized" versions of ML-KEM.Encaps and
// ML-KEM.Decaps are only ever to be called by the actual non-interal
// implementation or test cases.

kem_encaps_internal :: proc(
	shared_secret: []byte,
	ciphertext: []byte,
	ek: ^Encapsulation_Key,
	randomness: []byte,
) {
	ensure(len(shared_secret) == ML_KEM_SYMBYTES, "crypto/mlkem: invalid K")
	ensure(len(randomness) == ML_KEM_SYMBYTES, "crypto/mlkem: invalid m")
	ensure(
		len(ciphertext) == ct_len_for_k(ek.pke_ek.k),
		"crypto/mlkem: invalid ciphertext length",
	)

	buf: [2*ML_KEM_SYMBYTES]byte
	defer crypto.zero_explicit(&buf, size_of(buf))

	hash_g(buf[:], randomness, ek.h[:])

	// Can't fail, ciphertext length is valid.
	_ = k_pke_encrypt(ciphertext, &ek.pke_ek, randomness, buf[ML_KEM_SYMBYTES:])

	copy(shared_secret, buf[:ML_KEM_SYMBYTES])
}

kem_decaps_internal :: proc(
	shared_secret: []byte,
	dk: ^Decapsulation_Key,
	ciphertext: []byte,
) {
	ct_len := ct_len_for_k(dk.pke_dk.k)
	ensure(
		len(ciphertext) == ct_len,
		"crypto/mlkem: invalid ciphertext length",
	)

	m_: [ML_KEM_SYMBYTES]byte
	defer crypto.zero_explicit(&m_, size_of(m_))

	// Can't fail, ciphertext length is valid.
	_ = k_pke_decrypt(m_[:], &dk.pke_dk, ciphertext)

	buf: [2*ML_KEM_SYMBYTES]byte
	defer crypto.zero_explicit(&buf, size_of(buf))

	ek := &dk.ek
	hash_g(buf[:], m_[:], ek.h[:])

	rkprf(shared_secret, dk.seed[ML_KEM_SYMBYTES:], ciphertext)

	ct_buf: [ML_KEM_CIPHERTEXTBYTES_MAX]byte
	defer crypto.zero_explicit(&ct_buf, size_of(ct_buf))
	ct_ := ct_buf[:ct_len]
	_ = k_pke_encrypt(ciphertext, &ek.pke_ek, m_[:], buf[ML_KEM_SYMBYTES:])

	ok := crypto.compare_constant_time(ciphertext, ct_)
	subtle.cmov_bytes(shared_secret, buf[:ML_KEM_SYMBYTES], ok)
}

@(private="file")
ct_len_for_k :: proc(k: int) -> int {
	switch k {
	case ML_KEM_K_768:
		return ML_KEM_CIPHERTEXTBYTES_768
	case ML_KEM_K_1024:
		return ML_KEM_CIPHERTEXTBYTES_1024
	case:
		panic("crypto/mlkem: invalid k for ciphertext length")
	}
}
