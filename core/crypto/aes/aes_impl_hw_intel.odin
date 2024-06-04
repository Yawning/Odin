// Copyright (c) 2016 Thomas Pornin <pornin@bolet.org>
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//   1. Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHORS “AS IS” AND ANY EXPRESS OR
// IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
// THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//+build amd64
package aes

import "base:intrinsics"
import "core:crypto/_aes"
import "core:mem"
import "core:simd"
import "core:simd/x86"
import "core:sys/info"

// is_hardware_accelerated returns true iff hardware accelerated AES
// is supported.
is_hardware_accelerated :: proc "contextless" () -> bool {
	features, ok := info.cpu_features.?
	if !ok {
		return false
	}

	// Note: Everything has SSE2.
	ok = .aes in features
	ok &= .pclmulqdq in features
	return ok
}

@(private)
Context_Impl_Hardware :: struct {
	// Note: The ideal thing to do is for the expanded round keys to be
	// arrays of `__m128i`, however that implies alignment (or using AVX).
	//
	// All the people using e-waste processors that don't support an
	// insturction set that has been around for over 10 years are why
	// we can't have nice things.
	_sk_exp_enc: [15][16]byte,
	_sk_exp_dec: [15][16]byte,
	_num_rounds: int,
}

// Intel AES-NI based implementation.  Inspiration taken from BearSSL.
//
// Note: This assumes that the SROA optimization pass is enabled to be
// anything resembling performat otherwise, LLVM will not elide a massive
// number of redundant loads/stores it generates for every intrinsic call.

@(private="file", enable_target_feature="sse2")
expand_step128 :: #force_inline proc(k1, k2: x86.__m128i) -> x86.__m128i {
	k1, k2 := k1, k2
	tmp: x86.__m128i

	k2 = x86._mm_shuffle_epi32(k2, 0xff)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x10))
	k1 = x86._mm_xor_si128(k1, tmp)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x8c))
	k1 = x86._mm_xor_si128(k1, tmp)
	return x86._mm_xor_si128(k1, k2)
}

@(private="file", enable_target_feature="sse2")
expand_step192a :: #force_inline proc (k1_, k2_: ^x86.__m128i, k3: x86.__m128i) -> (x86.__m128i, x86.__m128i) {
	k1, k2, k3 := k1_^, k2_^, k3
	tmp: x86.__m128i

	k3 = x86._mm_shuffle_epi32(k3, 0x55)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x10))
	k1 = x86._mm_xor_si128(k1, tmp)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x8c))
	k1 = x86._mm_xor_si128(k1, tmp)
	k1 = x86._mm_xor_si128(k1, k3)

	tmp = k2
	tmp2 := x86._mm_slli_si128(k2, 0x04)
	tmp3 := x86._mm_shuffle_epi32(k1, 0xff)
	k2 = x86._mm_xor_si128(k2, tmp3)
	k2 = x86._mm_xor_si128(k2, tmp2)

	k1_, k2_ := k1_, k2_
	k1_^, k2_^ = k1, k2

	r1 := transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x44))
	r2 := transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(k1), transmute(x86.__m128)(k2), 0x4e))

	return r1, r2
}

@(private="file", enable_target_feature="sse2")
expand_step192b :: #force_inline proc (k1_, k2_: ^x86.__m128i, k3: x86.__m128i) -> x86.__m128i {
	k1, k2, k3 := k1_^, k2_^, k3
	tmp: x86.__m128i

	k3 = x86._mm_shuffle_epi32(k3, 0x55)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x10))
	k1 = x86._mm_xor_si128(k1, tmp)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x8c))
	k1 = x86._mm_xor_si128(k1, tmp)
	k1 = x86._mm_xor_si128(k1, k3)

	tmp2 := x86._mm_slli_si128(k2, 0x04)
	tmp3 := x86._mm_shuffle_epi32(k1, 0xff)
	k2 = x86._mm_xor_si128(k2, tmp3)
	k2 = x86._mm_xor_si128(k2, tmp2)

	k1_, k2_ := k1_, k2_
	k1_^, k2_^ = k1, k2

	return k1
}

@(private="file", enable_target_feature="sse2")
expand_step256b :: #force_inline proc(k1, k2: x86.__m128i) -> x86.__m128i {
	k1, k2 := k1, k2
	tmp: x86.__m128i

	k2 = x86._mm_shuffle_epi32(k2, 0xaa)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x10))
	k1 = x86._mm_xor_si128(k1, tmp)
	tmp = transmute(x86.__m128i)(x86._mm_shuffle_ps(transmute(x86.__m128)(tmp), transmute(x86.__m128)(k1), 0x8c))
	k1 = x86._mm_xor_si128(k1, tmp)
	return x86._mm_xor_si128(k1, k2)
}

@(private="file", enable_target_feature="aes")
derive_dec_keys :: proc(ctx: ^Context_Impl_Hardware, sks: ^[15]x86.__m128i, num_rounds: int) {
	intrinsics.unaligned_store((^x86.__m128i)(&ctx._sk_exp_dec[0]), sks[num_rounds])
	for i in 1 ..< num_rounds {
		tmp := x86._mm_aesimc_si128(sks[i])
		intrinsics.unaligned_store((^x86.__m128i)(&ctx._sk_exp_dec[num_rounds - i]), tmp)
	}
	intrinsics.unaligned_store((^x86.__m128i)(&ctx._sk_exp_dec[num_rounds]), sks[0])
}

@(private, enable_target_feature="sse2,aes")
init_impl_hw :: proc(ctx: ^Context_Impl_Hardware, key: []byte) {
	sks: [15]x86.__m128i = ---

	// Compute the encryption keys.
	num_rounds, key_len := 0, len(key)
	switch key_len {
	case _aes.KEY_SIZE_128:
		sks[0] = intrinsics.unaligned_load((^x86.__m128i)(raw_data(key)))
		sks[1] = expand_step128(sks[0], x86._mm_aeskeygenassist_si128(sks[0], 0x01))
		sks[2] = expand_step128(sks[1], x86._mm_aeskeygenassist_si128(sks[1], 0x02))
		sks[3] = expand_step128(sks[2], x86._mm_aeskeygenassist_si128(sks[2], 0x04))
		sks[4] = expand_step128(sks[3], x86._mm_aeskeygenassist_si128(sks[3], 0x08))
		sks[5] = expand_step128(sks[4], x86._mm_aeskeygenassist_si128(sks[4], 0x10))
		sks[6] = expand_step128(sks[5], x86._mm_aeskeygenassist_si128(sks[5], 0x20))
		sks[7] = expand_step128(sks[6], x86._mm_aeskeygenassist_si128(sks[6], 0x40))
		sks[8] = expand_step128(sks[7], x86._mm_aeskeygenassist_si128(sks[7], 0x80))
		sks[9] = expand_step128(sks[8], x86._mm_aeskeygenassist_si128(sks[8], 0x1b))
		sks[10] = expand_step128(sks[9], x86._mm_aeskeygenassist_si128(sks[9], 0x36))
		num_rounds = _aes.ROUNDS_128
	case _aes.KEY_SIZE_192:
		k0 := intrinsics.unaligned_load((^x86.__m128i)(raw_data(key)))
		k1 := x86.__m128i{
			intrinsics.unaligned_load((^i64)(raw_data(key[16:]))),
			0,
		}
		sks[0] = k0
		sks[1], sks[2] = expand_step192a(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x01))
		sks[3] = expand_step192b(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x02))
		sks[4], sks[5] = expand_step192a(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x04))
		sks[6] = expand_step192b(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x08))
		sks[7], sks[8] = expand_step192a(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x10))
		sks[9] = expand_step192b(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x20))
		sks[10], sks[11] = expand_step192a(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x40))
		sks[12] = expand_step192b(&k0, &k1, x86._mm_aeskeygenassist_si128(k1, 0x80))
		num_rounds = _aes.ROUNDS_192
	case _aes.KEY_SIZE_256:
		sks[0] = intrinsics.unaligned_load((^x86.__m128i)(raw_data(key)))
		sks[1] = intrinsics.unaligned_load((^x86.__m128i)(raw_data(key[16:])))
		sks[2] = expand_step128(sks[0], x86._mm_aeskeygenassist_si128(sks[1], 0x01))
		sks[3] = expand_step256b(sks[1], x86._mm_aeskeygenassist_si128(sks[2], 0x01))
		sks[4] = expand_step128(sks[2], x86._mm_aeskeygenassist_si128(sks[3], 0x02))
		sks[5] = expand_step256b(sks[3], x86._mm_aeskeygenassist_si128(sks[4], 0x02))
		sks[6] = expand_step128(sks[4], x86._mm_aeskeygenassist_si128(sks[5], 0x04))
		sks[7] = expand_step256b(sks[5], x86._mm_aeskeygenassist_si128(sks[6], 0x04))
		sks[8] = expand_step128(sks[6], x86._mm_aeskeygenassist_si128(sks[7], 0x08))
		sks[9] = expand_step256b(sks[7], x86._mm_aeskeygenassist_si128(sks[8], 0x08))
		sks[10] = expand_step128(sks[8], x86._mm_aeskeygenassist_si128(sks[9], 0x10))
		sks[11] = expand_step256b(sks[9], x86._mm_aeskeygenassist_si128(sks[10], 0x10))
		sks[12] = expand_step128(sks[10], x86._mm_aeskeygenassist_si128(sks[11], 0x20))
		sks[13] = expand_step256b(sks[11], x86._mm_aeskeygenassist_si128(sks[12], 0x20))
		sks[14] = expand_step128(sks[12], x86._mm_aeskeygenassist_si128(sks[13], 0x40))
		num_rounds = _aes.ROUNDS_256
	case:
		panic("crypto/aes: invalid AES key size")
	}
	for i in 0 ..= num_rounds {
		intrinsics.unaligned_store((^x86.__m128i)(&ctx._sk_exp_enc[i]), sks[i])
	}

	// Compute the decryption keys.  GCM and CTR do not need this, however
	// ECB, CBC, OCB3, etc do.
	derive_dec_keys(ctx, &sks, num_rounds)

	ctx._num_rounds = num_rounds

	mem.zero_explicit(&sks, size_of(sks))
}

@(private, enable_target_feature="sse2,aes")
encrypt_block_hw :: proc(ctx: ^Context_Impl_Hardware, dst, src: []byte) {
	blk := intrinsics.unaligned_load((^x86.__m128i)(raw_data(src)))

	blk = x86._mm_xor_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[0])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[1])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[2])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[3])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[4])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[5])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[6])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[7])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[8])))
	blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[9])))
	switch ctx._num_rounds {
	case _aes.ROUNDS_128:
		blk = x86._mm_aesenclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[10])))
	case _aes.ROUNDS_192:
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[10])))
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[11])))
		blk = x86._mm_aesenclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[12])))
	case _aes.ROUNDS_256:
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[10])))
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[11])))
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[12])))
		blk = x86._mm_aesenc_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[13])))
		blk = x86._mm_aesenclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_enc[14])))
	}

	intrinsics.unaligned_store((^x86.__m128i)(raw_data(dst)), blk)
}

@(private, enable_target_feature="sse2,aes")
decrypt_block_hw :: proc(ctx: ^Context_Impl_Hardware, dst, src: []byte) {
	blk := intrinsics.unaligned_load((^x86.__m128i)(raw_data(src)))

	blk = x86._mm_xor_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[0])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[1])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[2])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[3])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[4])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[5])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[6])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[7])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[8])))
	blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[9])))
	switch ctx._num_rounds {
	case _aes.ROUNDS_128:
		blk = x86._mm_aesdeclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[10])))
	case _aes.ROUNDS_192:
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[10])))
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[11])))
		blk = x86._mm_aesdeclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[12])))
	case _aes.ROUNDS_256:
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[10])))
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[11])))
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[12])))
		blk = x86._mm_aesdec_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[13])))
		blk = x86._mm_aesdeclast_si128(blk, intrinsics.unaligned_load((^x86.__m128i)(&ctx._sk_exp_dec[14])))
	}

	intrinsics.unaligned_store((^x86.__m128i)(raw_data(dst)), blk)
}

@(private)
ctr_blocks_hw :: proc(ctx: ^Context_CTR, dst, src: []byte, nr_blocks: int) {
	panic("todo")
}

@(private)
gcm_seal_hw :: proc(ctx: ^Context_Impl_Hardware, dst, tag, nonce, aad, plaintext: []byte) {
	panic("todo")
}

@(private)
gcm_open_hw :: proc(ctx: ^Context_Impl_Hardware, dst, nonce, aad, ciphertext, tag: []byte) -> bool {
	panic("todo")
}
