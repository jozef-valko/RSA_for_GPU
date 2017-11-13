
#include "cuda_runtime.h"
#include "device_launch_parameters.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>

#define MAX_BLOCKS 131072
#define MAX_DIM 512

int debug = 0;

struct public_key {
	unsigned long long n;
	unsigned long long e;
};

struct private_key {
	unsigned long long p;
	unsigned long long q;
	unsigned long long n;
	unsigned long long d;
};

struct message {
	unsigned char *msg;
	unsigned long long size;
	unsigned long long numBlocks;
};

__device__ unsigned long long rsa_modExp(unsigned long long b, unsigned long long e, unsigned long long m)
{
	if (b < 0 || e < 0 || m <= 0) {
		printf("Error of arguments!\n");
		return NULL;
	}
	b = b % m;
	if (e == 0)
		return 1;
	if (e == 1)
		return b;
	if (e % 2 == 0) {
		return (rsa_modExp(b * b % m, e / 2, m) % m);
	}
	if (e % 2 == 1) {
		return (b * rsa_modExp(b, (e - 1), m) % m);
	}
	return NULL;
}

__global__ void encrypt(unsigned long long e, unsigned long long n, int bufSize, unsigned long long numBlocks, unsigned char *message, unsigned long long *encrypted) {
	int blockId = blockIdx.y * gridDim.x + blockIdx.x;
	int threadId = blockId * blockDim.x + threadIdx.x;
	if (threadId < numBlocks) {
		unsigned char *buf;
		int j, flag = 0;
		unsigned long long tempNumber = 0;
		buf = (unsigned char*)malloc(bufSize * sizeof(unsigned char));
		for (j = 0; j < bufSize; j++) {
			if (!flag) {
				buf[j] = *(message + threadId * bufSize + j);
				if ((threadId == numBlocks - 1) && buf[j] == 255) {
					flag = 1;
				}
			}
			else {
				buf[j] = 0;
			}
		}
		//print_hex(buf, bufSize);
		tempNumber = buf[0];
		for (j = 1; j < bufSize; j++) {
			tempNumber = tempNumber << 8;
			tempNumber += buf[j];
		}
		//printf("%d. Message is %llu\n", i + 1, tempNumber);
		encrypted[threadId] = rsa_modExp(tempNumber, e, n);
		//printf("Encrypted: %llu\n", encrypted);
		free(buf);
	}
}

struct message strToInt(int bufSize, unsigned long long decrypted, int flag) {
	struct message decMsg;
	int i;
	unsigned long long int temp;
	decMsg.msg = (unsigned char *)malloc(bufSize * sizeof(unsigned char));
	decMsg.size = 0;
	for (i = bufSize - 1; i >= 0; i--) {
		temp = decrypted >> 8;
		temp = temp << 8;
		decMsg.msg[i] = decrypted - temp;
		if (flag && decMsg.msg[i] == 255) {
			decMsg.size = i;
		}
		decrypted = decrypted >> 8;
	}
	if (decMsg.size == 0) {
		decMsg.size = bufSize;
	}
	return decMsg;
}

int checkPrime(unsigned long long n) {
	int i;
	if (n % 2 == 0)
		return 1;
	for (i = 3; i <= sqrt(n); i += 2)
	{
		// podmienka pre neprvocislo
		if (n % i == 0)
			return 1;
	}
	return 0;
}

unsigned long long int nextPrime(unsigned long long n) {
	while (checkPrime(n) != 0) {
		if (n % 2 == 0)
			n++;
		n += 2;
	}
	return n;
}

unsigned long long gcd(unsigned long long a, unsigned long long b)
{
	unsigned long long temp;
	while (1)
	{
		temp = a % b;
		if (temp == 0)
			return b;
		a = b;
		b = temp;
	}
}

unsigned long long EEA(unsigned long long a, unsigned long long b) {
	unsigned long long x = 0, y = 1, u = 1, v = 0, gcd = b, m, n, q, r;
	while (a != 0) {
		q = gcd / a;
		r = gcd % a;
		m = x - u*q;
		n = y - v*q;
		gcd = a;
		a = r;
		x = u;
		y = v;
		u = m;
		v = n;
	}
	return y;
}

void rsa_gen_keys(struct public_key *pub, struct private_key *priv, int modSize)
{
	int i;
	int bufSize = modSize / 16;
	unsigned char *buf;
	unsigned long long int phi;
	buf = (unsigned char*)malloc(bufSize * sizeof(unsigned char) + 1);

	pub->e = 65537;
	srand(time(NULL));

	do {
		for (i = 0; i < bufSize; i++) {
			buf[i] = rand() % 0xFF;
		}
		buf[0] |= 0xC0;
		buf[bufSize - 1] |= 0x01;
		priv->p = buf[0];
		for (i = 1; i < bufSize; i++) {
			priv->p = priv->p << 8;
			priv->p += buf[i];
		}
		priv->p = nextPrime(priv->p);
		while (priv->p % pub->e == 1) {
			priv->p = nextPrime(priv->p);
		}

		do {
			for (i = 0; i < bufSize; i++) {
				buf[i] = rand() % 0xFF;
			}
			buf[0] |= 0xC0;
			buf[bufSize - 1] |= 0x01;
			priv->q = buf[0];
			for (i = 1; i < bufSize; i++) {
				priv->q = priv->q << 8;
				priv->q += buf[i];
			}
			priv->q = nextPrime(priv->q);
			while (priv->q % pub->e == 1) {
				priv->q = nextPrime(priv->q);
			}
		} while (priv->p == priv->q);
		priv->n = priv->p * priv->q;
		pub->n = priv->n;
		phi = (priv->p - 1) * (priv->q - 1);
		priv->d = EEA(phi, pub->e);
		while (priv->d < 0) {
			priv->d = priv->d + phi;
		}
	} while (priv->d >= priv->n);

	if (debug) {
		printf("---------------Public Key-----------------\n");
		printf("n is [%llu]\n", pub->n);
		printf("e is [%llu]\n", pub->e);
		printf("---------------Private Key------------------\n");
		printf("n is [%llu]\n", priv->n);
		printf("d is [%llu]\n", priv->d);
		printf("p is [%llu]\n", priv->p);
		printf("q is [%llu]\n", priv->q);
	}
}

void rsa_encrypt(unsigned long long e, unsigned long long n, int bufSize, struct message message, char *cipher)
{
	int i, j, flag = 0;
	unsigned long long *encrypted;
	unsigned long long *d_encrypted;
	unsigned char *d_message;
	unsigned long long tempNumber = 0;
	float time_spent;
	cudaError_t cudaStatus;
	if (cipher == NULL) {
		cipher = "cipher";
	}

	encrypted = (unsigned long long *)malloc(message.numBlocks * sizeof(unsigned long long));

	cudaStatus = cudaMalloc(&d_encrypted, message.numBlocks * sizeof(unsigned long long));
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo alokovanie d_encrypted!\n");
		cudaFree(d_encrypted);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaStatus = cudaMalloc(&d_message, message.size * sizeof(unsigned char));
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo alokovanie d_message!\n");
		cudaFree(d_encrypted);
		cudaFree(d_message);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaStatus = cudaMemcpy(d_message, message.msg, message.size * sizeof(unsigned char), cudaMemcpyHostToDevice);
	if (cudaStatus != cudaSuccess) {
		cudaFree(d_encrypted);
		cudaFree(d_message);
		free(encrypted);
		free(message.msg);
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo kopirovanie vstupneho buffra!\n");
		exit(1);
	}

	int blockDim = message.numBlocks;
	dim3 gridDim;
	if (blockDim > MAX_DIM) {
		gridDim.x = blockDim / MAX_DIM + 1;
		blockDim = MAX_DIM;
		if (gridDim.x > MAX_DIM) {
			gridDim.y = gridDim.x / MAX_DIM + 1;
			gridDim.x = MAX_DIM;
			if (gridDim.y > MAX_DIM) {
				fprintf(stderr, "[rsa_encrypt]: Prekroceny maximalny limit pamate na GPU!\n");
				cudaFree(d_encrypted);
				cudaFree(d_message);
				free(encrypted);
				free(message.msg);
				exit(1);
			}
		}
	}

	if (debug) {
		printf("GridDim na GPU: %d x %d\nBlockDim na GPU: %d\n", gridDim.x, gridDim.y, blockDim);
	}
	
	cudaEvent_t start, stop;
	cudaEventCreate(&start);
	cudaEventCreate(&stop);
	cudaEventRecord(start, 0);

	encrypt << <gridDim, blockDim >> > (e, n, bufSize, message.numBlocks, d_message, d_encrypted);
	//zmenit hodnotu registra od Kupka
	cudaStatus = cudaGetLastError();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
		cudaFree(d_message);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaStatus = cudaDeviceSynchronize();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: cudaDeviceSynchronize vratila chybovy kod %d po spusteni kernelu!\n", cudaStatus);
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
		cudaFree(d_message);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaEventRecord(stop, 0);
	cudaEventSynchronize(stop);
	cudaEventElapsedTime(&time_spent, start, stop);
	cudaEventDestroy(start);
	cudaEventDestroy(stop);

	if (debug) {
		printf("Sifrovanie zabralo %.2f ms.\n", time_spent);
	}

	cudaStatus = cudaMemcpy(encrypted, d_encrypted, message.numBlocks * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo kopirovanie vystupneho buffra!\n");
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
		cudaFree(d_message);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	FILE *cipher_file;
	cipher_file = fopen(cipher, "w");
	for (i = 0; i < message.numBlocks; i++) {
		fprintf(cipher_file, "%llu ", encrypted[i]);
	}
	fclose(cipher_file);
	if (debug) {
		printf("Sifrovanie dokoncene. Sifra je ulozena v subore %s.\n", cipher);
	}
	
	cudaFree(d_encrypted);
	cudaFree(d_message);
	free(encrypted);
	free(message.msg);
}

//void rsa_decrypt(unsigned long long d, unsigned long long n, int bufSize, char *cipher, char *output)
//{
//	struct message decMsg;
//	unsigned long long int *cipherMsg, *temp, decrypted, c;
//	long long numBlocks;
//	int i;
//	FILE *output_file, *cipher_file;
//	if (output != NULL) {
//		output_file = fopen(output, "wb");
//	}
//	else {
//		output_file = stdout;
//		if (debug) {
//			printf("Desifrovany text:\n");
//		}
//	}
//	cipher_file = fopen(cipher, "r");
//	decMsg.msg = (unsigned char *)malloc(sizeof(unsigned char) * bufSize);
//	cipherMsg = (unsigned long long *)malloc(sizeof(unsigned long long));
//	numBlocks = 1;
//	for (i = 0; fscanf(cipher_file, "%llu", &c) != EOF; i++) {
//		cipherMsg[i] = c;
//		if (i == numBlocks - 1) {
//			numBlocks *= 2;
//			temp = (unsigned long long *)realloc(cipherMsg, numBlocks * sizeof(unsigned long long));
//			if (temp) {
//				cipherMsg = temp;
//			}
//			else {
//				fprintf(stderr, "[rsa_decrypt]: Realokacia pamate zlyhala.\n");
//				exit(1);
//			}
//		}
//	}
//	numBlocks = i;
//	temp = (unsigned long long *)realloc(cipherMsg, numBlocks * sizeof(unsigned long long));
//	if (temp) {
//		cipherMsg = temp;
//	}
//	else {
//		fprintf(stderr, "[rsa_decrypt]: Realokacia pamate zlyhala.\n");
//		exit(1);
//	}
//	fclose(cipher_file);
//	for (i = 0; i < numBlocks - 1; i++) {
//		decrypted = rsa_modExp(cipherMsg[i], d, n);
//		//printf("Decrypted: %llu\n", decrypted);
//		decMsg = strToInt(bufSize, decrypted, 0);
//		fwrite(decMsg.msg, 1, decMsg.size, output_file);
//	}
//	decrypted = rsa_modExp(cipherMsg[i], d, n);
//	decMsg = strToInt(bufSize, decrypted, 1);
//	fwrite(decMsg.msg, 1, decMsg.size, output_file);
//	if (output != NULL) {
//		fclose(output_file);
//	}
//	if (debug && output != NULL) {
//		printf("\nDesifrovanie dokoncene. Vystup je ulozeny v subore %s.\n", output);
//	}
//	else if (debug) {
//		printf("\nDesifrovanie dokoncene. Vystup je na stdout.\n");
//	}
//}

struct message inputString(char *input, long long bufSize) {
	FILE *input_file;
	struct message message;
	long sizeOfFile = 0;
	//nacitanie suboru do buffra
	if (input != NULL) {
		input_file = fopen(input, "rb");
		fseek(input_file, 0, SEEK_END);
		sizeOfFile = ftell(input_file);
		rewind(input_file);
		if (debug) {
			printf("Velkost suboru je:\t\t%ld\n", sizeOfFile);
		}
		message.msg = (unsigned char *)malloc(sizeof(unsigned char) * (sizeOfFile + 1));
		message.size = fread(message.msg, 1, sizeOfFile, input_file);
		message.msg[sizeOfFile] = 255;
		message.size++;
		fclose(input_file);
	}
	//nacitanie znakov zo standardneho vstupu
	/*else {
		freopen(NULL, "rb", stdin);
		input_file = stdin;
		fseek(input_file, 0, SEEK_END);
		sizeOfFile = ftell(input_file);
		fseek(input_file, 0, SEEK_SET);
		if (sizeOfFile > 0) {
			if (debug) {
				printf("Velkost suboru je:\t\t%ld\n", sizeOfFile);
			}
			message = (unsigned char *)malloc(sizeof(unsigned char) * sizeOfFile);
			sizeOfFile = fread(message, sizeof(unsigned char), sizeOfFile, input_file);
			if (debug) {
				printf("Nacitana velkost suboru je:\t%ld\n", sizeOfFile);
			}
			message[sizeOfFile] = '\0';
		}
		else {
			message = (unsigned char *)malloc(sizeof(unsigned char) * 1024);
			fgets((char*)message, 1023, input_file);
			sizeOfFile = strlen((char*)message);
			message[sizeOfFile - 1] = '\0';
		}
	}*/
	if (sizeOfFile % bufSize != 0) {
		message.numBlocks = sizeOfFile / bufSize + 1;
	}
	else {
		message.numBlocks = sizeOfFile / bufSize;
	}
	return message;
}

void help(char *argv) {
	FILE *help;
	char input;
	help = fopen("help.txt", "r");
	while (fscanf(help, "%c", &input) != EOF) {
		printf("%c", input);
	}
	fclose(help);
}

int main(int argc, char **argv) {
	struct public_key pub[1];
	struct private_key priv[1];
	int modSize = 32, bufSize = modSize / 8;
	int i, flag = 0;
	clock_t begin, end;
	double time_spent;
	char *output;

	if (argc > 1) {
		for (i = 1; i < argc; i++) {
			if (!strcmp(argv[i], "-b")) {
				debug = 1;
				break;
			}
		}
		for (i = 1; i < argc; i++) {
			if (!strcmp(argv[i], "-h")) {
				help(argv[0]);
			}
			else if (!strcmp(argv[i], "-g")) {
				rsa_gen_keys(pub, priv, modSize);
				i++;
				char *filename1, *filename2;
				if (i < argc && (strcmp(argv[i], "-e") != 0 && strcmp(argv[i], "-d") != 0 && strcmp(argv[i], "-h") != 0) && strcmp(argv[i], "-b") != 0) {
					filename1 = (char*)malloc((strlen(argv[i]) + 1) * sizeof(char));
					filename2 = (char*)malloc((strlen(argv[i]) + 5) * sizeof(char));
					filename1[0] = '\0';
					filename2[0] = '\0';
					strcat(filename1, argv[i]);
					strcat(filename2, filename1);
					strcat(filename2, ".pub");
				}
				else {
					i--;
					filename1 = (char*)malloc(7 * sizeof(char));
					filename2 = (char*)malloc(11 * sizeof(char));
					filename1[0] = '\0';
					filename2[0] = '\0';
					strcat(filename1, "rsakey");
					strcat(filename2, filename1);
					strcat(filename2, ".pub");
				}
				FILE *keyFile;
				keyFile = fopen(filename1, "w");
				fprintf(keyFile, "%llu %llu %llu %llu", priv->n, priv->d, priv->p, priv->q);
				fclose(keyFile);
				keyFile = fopen(filename2, "w");
				fprintf(keyFile, "%llu %llu", pub->n, pub->e);
				fclose(keyFile);
				if (debug) {
					printf("Kluce boli ulozene do suborov %s and %s...\n", filename1, filename2);
				}
			}
			else if (!strcmp(argv[i], "-e") || !strcmp(argv[i], "-d")) {
				i++;
				if (i < argc) {
					FILE *key;
					key = fopen(argv[i], "r");
					if (key != NULL)
					{
						//testujem ci je to subor s verejnym klucom, ak ano tak ho citam
						if (strstr(argv[i], ".pub") != NULL) {
							if (fscanf(key, "%llu", &pub->n) != EOF) {
								if (fscanf(key, "%llu", &pub->e) != EOF) {
									if (debug) {
										printf("Nacitane kluce:\nn: %llu\ne: %llu\n", pub->n, pub->e);
									}
								}
								else {
									fprintf(stderr, "Zly vstupny subor s klucom!\n");
									return 0;
								}
							}
							else {
								fprintf(stderr, "Zly vstupny subor s klucom!\n");
								return 0;
							}
						}
						//citam subor so sukromnym klucom
						else {
							flag = 1;
							if (fscanf(key, "%llu", &priv->n) != EOF) {
								if (fscanf(key, "%llu", &priv->d) != EOF) {
									if (debug) {
										printf("Nacitane kluce:\nn: %llu\nd: %llu\n", priv->n, priv->d);
									}
								}
							}
						}
						fclose(key);
					}
					else {
						fprintf(stderr, "Nepodarilo sa otvorit subor s klucom!\n");
						return 0;
					}
					i++;
					if (argv[i] == NULL) {
						if (debug && !strcmp(argv[i - 2], "-e")) {
							printf("Nebol zadany vstupny subor, citam stdin.\n");
						}
						output = NULL;
					}
					else {
						if (argv[i + 1] != NULL) {
							output = (char*)malloc(strlen(argv[i + 1]) * sizeof(char));
							strcpy(output, argv[i + 1]);
						}
						else {
							output = NULL;
						}
					}

					if (!strcmp(argv[i - 2], "-e")) {
						struct message message;
						begin = clock();
						//nacitanie vstupu do buffra
						message = inputString(argv[i], bufSize);
						if (message.msg == NULL) {
							fprintf(stderr, "Chyba pri citani zo vstupu!\n");
							exit(1);
						}
						end = clock();
						time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
						if (debug) {
							printf("Nacitanie spravy zabralo %lf sekund.\n", time_spent);
							printf("Pocet blokov: %llu\n", message.numBlocks);
						}
						if (flag) {
							rsa_encrypt(priv->d, priv->n, bufSize, message, output);
						}
						else {
							rsa_encrypt(pub->e, pub->n, bufSize, message, output);
						}
						return 0;
					}
					else {
						if (argv[i] != NULL) {
							char *cipher;
							cipher = (char*)malloc(strlen(argv[i]) * sizeof(char));
							strcpy(cipher, argv[i]);
							begin = clock();
							if (flag) {
								//rsa_decrypt(priv->d, priv->n, bufSize, cipher, output);
							}
							else {
								//rsa_decrypt(pub->e, pub->n, bufSize, cipher, output);
							}
							end = clock();
							time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
							if (debug) {
								printf("Desifrovanie zabralo %lf sekund.\n", time_spent);
							}
						}
						else {
							fprintf(stderr, "Nebol zadany vstupny subor na desifrovanie.\n");
							exit(1);
						}
						return 0;
					}
				}
				else {
					fprintf(stderr, "Chyba subor s klucom!\n");
					exit(1);
				}
			}
			else if (!strcmp(argv[i], "-b")) {
				if (!debug) {
					debug = 1;
				}
			}
			else {
				fprintf(stderr, "%s je zly argument, skus znova alebo pouzi -h pre pomoc.\n", argv[i]);
				return 0;
			}
		}
		return 0;
	}
	else {
		fprintf(stderr, "Malo argumentov, skus znova alebo pouzi -h pre pomoc.\n");
		return 0;
	}
}

