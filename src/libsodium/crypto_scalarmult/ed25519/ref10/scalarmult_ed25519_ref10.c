
#include <string.h>

#include "crypto_scalarmult_ed25519.h"
#include "crypto_hash.h"
#include "private/ed25519_ref10.h"
#include "utils.h"

static int
_crypto_scalarmult_ed25519_is_inf(const unsigned char s[32])
{
    unsigned char c;
    unsigned int  i;

    c = s[0] ^ 0x01;
    for (i = 1; i < 31; i++) {
        c |= s[i];
    }
    c |= s[31] & 0x7f;

    return ((((unsigned int) c) - 1U) >> 8) & 1;
}

static inline void
_crypto_scalarmult_ed25519_clamp(unsigned char k[32])
{
    k[0] &= 248;
    k[31] |= 64;
}

static int
_crypto_scalarmult_ed25519(unsigned char *q, const unsigned char *n,
                           const unsigned char *p, const int clamp)
{
    unsigned char *t = q;
    ge25519_p3     Q;
    ge25519_p3     P;
    unsigned int   i;

    if (ge25519_is_canonical(p) == 0 || ge25519_has_small_order(p) != 0 ||
        ge25519_frombytes(&P, p) != 0 || ge25519_is_on_main_subgroup(&P) == 0) {
        return -1;
    }
    for (i = 0; i < 32; ++i) {
        t[i] = n[i];
    }
    if (clamp != 0) {
        _crypto_scalarmult_ed25519_clamp(t);
    }
    t[31] &= 127;

    ge25519_scalarmult(&Q, t, &P);
    ge25519_p3_tobytes(q, &Q);
    if (_crypto_scalarmult_ed25519_is_inf(q) != 0 || sodium_is_zero(n, 32)) {
        return -1;
    }
    return 0;
}

int
crypto_scalarmult_ed25519(unsigned char *q, const unsigned char *n,
                          const unsigned char *p)
{
    return _crypto_scalarmult_ed25519(q, n, p, 1);
}

int
crypto_scalarmult_ed25519_noclamp(unsigned char *q, const unsigned char *n,
                                  const unsigned char *p)
{
    return _crypto_scalarmult_ed25519(q, n, p, 0);
}

static int
_crypto_scalarmult_ed25519_base(unsigned char *q,
                                const unsigned char *n, const int clamp)
{
    unsigned char *t = q;
    ge25519_p3     Q;
    unsigned int   i;

    for (i = 0; i < 32; ++i) {
        t[i] = n[i];
    }
    if (clamp != 0) {
        _crypto_scalarmult_ed25519_clamp(t);
    }
    t[31] &= 127;

    ge25519_scalarmult_base(&Q, t);
    ge25519_p3_tobytes(q, &Q);
    if (_crypto_scalarmult_ed25519_is_inf(q) != 0 || sodium_is_zero(n, 32)) {
        return -1;
    }
    return 0;
}

int
crypto_scalarmult_ed25519_base(unsigned char *q,
                               const unsigned char *n)
{
    return _crypto_scalarmult_ed25519_base(q, n, 1);
}

int
crypto_scalarmult_ed25519_base_noclamp(unsigned char *q,
                                       const unsigned char *n)
{
    return _crypto_scalarmult_ed25519_base(q, n, 0);
}

/* Blind a secret key with a 32-byte hash (param) by essentially adding the two together
then deriving a new public key. The param's 3 lowest bits and highest byte will be cleared.
The original secret key should have the 3rd most significant bit cleared to ensure the addition 
does not wrap, which would have the possibility of setting the lowest bits, causing a weak key
which additionally will not work due to the clamping that libsodium applies to each operation.
This means that this blinding technique is not designed to be repeated serially. There is a small
safety margin of a few bits, but as a rule, do not blind already blinded keys more than 16 times. */
int
crypto_blind_ed25519_secret_key(unsigned char *out, const unsigned char *skey,
	const unsigned char *param)
{
	unsigned char clampkey[32];
	unsigned char clamparam[32];
	unsigned int  i;
	fe25519 paramfe, skeyfe, added;

	/* First we clamp the original secret key seed, although this should already have been done. */
	for (i = 0; i < 32; ++i) {
		clampkey[i] = skey[i];
	}
	_crypto_scalarmult_ed25519_clamp(clampkey);
	fe25519_frombytes(skeyfe, clampkey);

	/* Next we quasi-clamp the parameter (at least 31 public bytes, possibly the hash of something known) */
	for (i = 0; i < 31; ++i) {
		clamparam[i] = param[i];
	}
	clamparam[31] = 0; /* ensure param is always < 2^248 so as long as seed is always < 2^254 + 2^253 ... + 2^248 addition won't wrap */
	clamparam[0] &= 248; /* lowest 3 bits should be 0 so it's a multiple of 8, the cofactor */
	fe25519_frombytes(paramfe, clamparam);
	/* we could have started with fewer input bits and multiplied by 8, but there's no real benefit to doing that */

	/* Finally we add them together. */
	fe25519_add(added, paramfe, skeyfe);
	fe25519_tobytes(out, added);

	/* now need to generate pkey for libsodium (stored directly after the private key) */
	ge25519_p3 Q;
	ge25519_scalarmult_base(&Q, out);
	ge25519_p3_tobytes(out + 32, &Q);

	sodium_memzero(clampkey, sizeof(clampkey));
	sodium_memzero(clamparam, sizeof(clamparam));
	sodium_memzero(paramfe, sizeof(paramfe));
	sodium_memzero(skeyfe, sizeof(skeyfe));
	sodium_memzero(added, sizeof(added));

	if ((out[0] & 7) != 0) { /* check for sanity's sake. Could also check for equivalency mod l, not sure it's worth the cost */
		return -1; /* maybe bad inputs created weak output? */
	}

	return 0;
}

/* Blind a public key with a 32-byte hash (param) by multiplying the param by the base point and
adding the two together as group elements. The param's 3 lowest bits and highest byte will be cleared first. */
int
crypto_blind_ed25519_public_key(unsigned char *out, const unsigned char *pkey,
	const unsigned char *param)
{
	unsigned char clamparam[32];
	unsigned int  i;
	ge25519_p3 parambp;
	ge25519_p3 p;
	ge25519_cached pcached;
	ge25519_p1p1 geres;

	/* same as the secret key blinding */
	for (i = 0; i < 31; ++i) {
		clamparam[i] = param[i];
	}
	clamparam[31] = 0;
	clamparam[0] &= 248;

	ge25519_scalarmult_base(&parambp, clamparam);
	if (ge25519_frombytes(&p, pkey) == -1) {
		return -1;
	}
	ge25519_p3_to_cached(&pcached, &p);
	ge25519_add(&geres, &parambp, &pcached);
	ge25519_p1p1_to_p3(&p, &geres);
	ge25519_p3_tobytes(out, &p);

	sodium_memzero(clamparam, sizeof(clamparam));
	sodium_memzero(&parambp, sizeof(parambp));
	sodium_memzero(&p, sizeof(p));
	sodium_memzero(&pcached, sizeof(pcached));
	sodium_memzero(&geres, sizeof(geres));

	return 0;
}

size_t
crypto_scalarmult_ed25519_bytes(void)
{
    return crypto_scalarmult_ed25519_BYTES;
}

size_t
crypto_scalarmult_ed25519_scalarbytes(void)
{
    return crypto_scalarmult_ed25519_SCALARBYTES;
}
