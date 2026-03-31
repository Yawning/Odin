package mlkem

import "core:crypto/_mlkem"

// Parameters are the supported ML-KEM parameter sets.
Parameters :: enum {
	Invalid,
	// ML-KEM-512 is not supported.
	ML_KEM_768,
	ML_KEM_1024,
}

// ENCAPS_KEY_SIZES are the per-parameter sizes of the encapsulation
// key in bytes.
ENCAPS_KEY_SIZES := [Parameters]int {
	.Invalid = 0,
	.ML_KEM_768 = _mlkem.ML_KEM_ENCAPSKEYBYTES_768,   // 1184-bytes
	.ML_KEM_1024 = _mlkem.ML_KEM_ENCAPSKEYBYTES_1024, // 1568-bytes
}

// CIPHERTEXT_SIZES are the per-parameter set sizes of the ciphertext
// in bytes.
CIPHERTEXT_SIZES := [Parameters]int {
	.Invalid = 0,
	.ML_KEM_768 = _mlkem.ML_KEM_CIPHERTEXTBYTES_768,    // 1088-bytes
	.ML_KEM_1024 = _mlkem.ML_KEM_CIPHERTEXTBYTES_1024,  // 1568-bytes
}

// DECAPS_KEY_SEED_SIZE is the size of a Decapsulation key in bytes.
DECAPS_KEY_SEED_SIZE :: 64 // (d, z) in NIST terms.

// SHARED_SECRET_SIZE is the size of the final shared secret in bytes.
SHARED_SECRET_SIZE :: 32

