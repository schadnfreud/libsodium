#include <stdio.h>
#include <string.h>

#define TEST_NAME "aead_chacha20poly1305"
#include "cmptest.h"

static unsigned char firstkey[crypto_aead_chacha20poly1305_KEYBYTES] = {
    0x42, 0x90, 0xbc, 0xb1, 0x54, 0x17, 0x35, 0x31,
    0xf3, 0x14, 0xaf, 0x57, 0xf3, 0xbe, 0x3b, 0x50,
    0x06, 0xda, 0x37, 0x1e, 0xce, 0x27, 0x2a, 0xfa,
    0x1b, 0x5d, 0xbd, 0xd1, 0x10, 0x0a, 0x10, 0x07
};

static unsigned char m[10U] = {
    0x86, 0xd0, 0x99, 0x74, 0x84, 0x0b, 0xde, 0xd2, 0xa5, 0xca
};

static unsigned char nonce[crypto_aead_chacha20poly1305_NPUBBYTES] = {
    0xcd, 0x7c, 0xf6, 0x7b, 0xe3, 0x9c, 0x79, 0x4a
};

static unsigned char ad[10U] = {
    0x87, 0xe2, 0x29, 0xd4, 0x50, 0x08, 0x45, 0xa0, 0x79, 0xc0
};

static unsigned char c[10U + crypto_aead_chacha20poly1305_ZEROBYTES];

int main(void)
{
    unsigned char m2[10U];
    size_t         i;

    crypto_aead_chacha20poly1305_encrypt(c, NULL, m, sizeof m, ad, sizeof ad,
                                         NULL, nonce, firstkey);
    for (i = 0U; i < sizeof c; ++i) {
        printf(",0x%02x", (unsigned int) c[i]);
        if (i % 8 == 7) {
            printf("\n");
        }
    }
    printf("\n");

    if (crypto_aead_chacha20poly1305_decrypt(m2, NULL, NULL, c, sizeof c,
                                             ad, sizeof ad,
                                             nonce, firstkey) != 0) {
        printf("crypto_aead_chacha20poly1305_ad_open() failed\n");
    }
    if (memcmp(m, m2, sizeof m) != 0) {
        printf("m != m2\n");
    }

    for (i = 0U; i < sizeof c; i++) {
        c[i] ^= (i + 1U);
        if (crypto_aead_chacha20poly1305_decrypt(m2, NULL, NULL, c, sizeof c,
                                                 ad, sizeof ad,
                                                 nonce, firstkey) == 0 ||
            memcmp(m, m2, sizeof m) == 0) {
            printf("message can be forged\n");
        }
        c[i] ^= (i + 1U);
    }
    return 0;
}