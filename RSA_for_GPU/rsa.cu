#include <stdio.h>
#include <gmp.h>

#define MODULUS_SIZE 2048
#define BLOCK_SIZE (MODULUS_SIZE/8) 

typedef struct {
	mpz_t n; /* Modulus */
	mpz_t e; /* Public Exponent */
} public_key;

typedef struct {
	mpz_t n; /* Modulus */
	mpz_t e; /* Public Exponent */
	mpz_t d; /* Private Exponent */
	mpz_t p; /* Starting prime p */
	mpz_t q; /* Starting prime q */
} private_key;

int main() {


	return 0;
}