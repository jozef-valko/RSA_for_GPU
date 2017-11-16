
#include "cuda_runtime.h"
#include "device_launch_parameters.h"

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>

#define MAX_KEYBOARD_INPUT 1024
#define MAX_DIM 1024

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

//GPU kernel na vypocet zasifrovaneho, resp. otvoreneho textu
__global__ void rsa_modExp(unsigned long long e, unsigned long long n, unsigned long long numBlocks, unsigned long long *encrypted) {
	int blockId = blockIdx.y * gridDim.x + blockIdx.x;
	int threadId = blockId * blockDim.x + threadIdx.x;
	if (threadId < numBlocks) {
		if (n == 1) {
			encrypted[threadId] = 0;
		}
		else {
			unsigned long long result = 1;
			encrypted[threadId] = encrypted[threadId] % n;
			while (e > 0) {
				if (e % 2 == 1) {
					result = (result * encrypted[threadId]) % n;
				}
				e = e >> 1;
				encrypted[threadId] = (encrypted[threadId] * encrypted[threadId]) % n;
			}
			encrypted[threadId] = result;
		}
	}
}

//funkcia na konvertovanie cisla na ASCII znaky
struct message intToStr(int bufSize, unsigned long long decrypted, int flag) {
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

//rozsireny Euklidov algoritmus
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
		//generovanie bajtov pre prvocislo p
		for (i = 0; i < bufSize; i++) {
			buf[i] = rand() % 0xFF;
		}
		//prvy bajt nastavime na same jednotky, aby sme zabezpecili dostatocne velke cislo
		buf[0] |= 0xFF;
		//posledny bit na 1 aby to bolo neparne cislo
		buf[bufSize - 1] |= 0x01;
		priv->p = buf[0];
		for (i = 1; i < bufSize; i++) {
			priv->p = priv->p << 8;
			priv->p += buf[i];
		}
		//do p ulozime nasledujuce prvocislo
		priv->p = nextPrime(priv->p);
		while (priv->p % pub->e == 1) {
			priv->p = nextPrime(priv->p);
		}
		//generovanie prvocisla q
		do {
			for (i = 0; i < bufSize; i++) {
				buf[i] = rand() % 0xFF;
			}
			buf[0] |= 0xFF;
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
		//vypocet modula
		priv->n = priv->p * priv->q;
		pub->n = priv->n;
		phi = (priv->p - 1) * (priv->q - 1);
		//vypocet sukromneho kluca pomocou rozsireneho Euklidovho algoritmu
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
	unsigned char *buf;
	clock_t begin, end;
	float time_spent;
	cudaError_t cudaStatus;

	//priprava blokov na sifrovanie, konvertovanie bloku na jedno cislo
	encrypted = (unsigned long long *)malloc(message.numBlocks * sizeof(unsigned long long));
	if (!encrypted) {
		fprintf(stderr, "[rsa_encrypt]: Nepodarilo sa alokovat pamat pre buffer encrypted\n");
		exit(1);
	}
	buf = (unsigned char*)malloc(bufSize * sizeof(unsigned char));
	if (!buf) {
		fprintf(stderr, "[rsa_encrypt]: Nepodarilo sa alokovat pamat pre buffer\n");
		exit(1);
	}
	begin = clock();
	for (i = 0; i < message.numBlocks; i++) {
		for (j = 0; j < bufSize; j++) {
			if (!flag) {
				buf[j] = *(message.msg + i * bufSize + j);
				if ((i == message.numBlocks - 1) && buf[j] == 255) {
					flag = 1;
				}
			}
			else {
				buf[j] = 0;
			}
		}
		//print_hex(buf, bufSize);
		encrypted[i] = buf[0];
		for (j = 1; j < bufSize; j++) {
			encrypted[i] = encrypted[i] << 8;
			encrypted[i] += buf[j];
		}
	}
	free(buf);
	end = clock();
	time_spent = ((double)(end - begin) / CLOCKS_PER_SEC) * 1000;
	if (debug) {
		printf("Priprava blokov na sifrovanie trvala %lf ms\n", time_spent);
	}

	cudaEvent_t start, stop;
	cudaEventCreate(&start);
	cudaEventCreate(&stop);
	cudaEventRecord(start, 0);
	
	cudaStatus = cudaMalloc(&d_encrypted, message.numBlocks * sizeof(unsigned long long));
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo alokovanie d_encrypted\n");
		cudaFree(d_encrypted);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaStatus = cudaMemcpy(d_encrypted, encrypted, message.numBlocks * sizeof(unsigned long long), cudaMemcpyHostToDevice);
	if (cudaStatus != cudaSuccess) {
		cudaFree(d_encrypted);
		free(encrypted);
		free(message.msg);
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo kopirovanie vstupneho buffra d_encrypted\n");
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
				fprintf(stderr, "[rsa_encrypt]: Prekroceny maximalny limit pamate na GPU\n");
				cudaFree(d_encrypted);
				free(encrypted);
				free(message.msg);
				exit(1);
			}
		}
	}

	if (debug) {
		printf("Rozmer mriezky blokov na GPU: %d x %d blokov\nPocet vlakien na blok na GPU: %d\n", gridDim.x, gridDim.y, blockDim);
	}

	//spustenie sifrovania na GPU
	rsa_modExp << <gridDim, blockDim >> > (e, n, message.numBlocks, d_encrypted);
	
	cudaStatus = cudaGetLastError();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	cudaStatus = cudaDeviceSynchronize();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: cudaDeviceSynchronize vratila chybovy kod %d po spusteni kernelu\n", cudaStatus);
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
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
		printf("Sifrovanie trvalo %.2f ms\n", time_spent);
	}

	cudaStatus = cudaMemcpy(encrypted, d_encrypted, message.numBlocks * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_encrypt]: Zlyhalo kopirovanie vystupneho buffra\n");
		fprintf(stderr, "[rsa_encrypt]: Sifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_encrypted);
		free(encrypted);
		free(message.msg);
		exit(1);
	}

	FILE *cipher_file;
	if (cipher != NULL) {
		cipher_file = fopen(cipher, "wb");
	}
	else {
		freopen(NULL, "wb", stdout);
		cipher_file = stdout;
		if (debug) {
			printf("Zasifrovany text:\n");
		}
	}

	begin = clock();
	unsigned long long sizeWritten = fwrite(encrypted, sizeof(unsigned long long), message.numBlocks, cipher_file);
	if (cipher != NULL) {
		fclose(cipher_file);
	}

	if (sizeWritten != message.numBlocks) {
		fprintf(stderr, "[rsa_encrypt]: Nepodarilo sa ulozit sifru do suboru\n");
		free(encrypted);
		exit(1);
	}
	end = clock();
	time_spent = ((double)(end - begin) / CLOCKS_PER_SEC) * 1000;
	if (debug && cipher != NULL) {
		printf("Zapis sifry na vystup trval %lf ms\n", time_spent);
		printf("Sifrovanie dokoncene. Sifra je ulozena v subore %s\n", cipher);
	}
	else if (debug) {
		printf("\nZapis sifry na vystup trval %lf ms\n", time_spent);
		printf("Sifrovanie dokoncene. Sifra je na stdout\n");
	}
	cudaFree(d_encrypted);
	free(encrypted);
	free(message.msg);
}

void rsa_decrypt(unsigned long long d, unsigned long long n, int bufSize, char *input, char *output)
{
	unsigned long long *d_decrypted;
	unsigned long long *decrypted;
	unsigned long long numBlocks;
	unsigned long long sizeOfFile;
	cudaError_t cudaStatus;
	clock_t begin, end;
	float time_spent;
	int i;
	FILE *output_file, *cipher_file;
	
	//nacitanie zasifrovaneho textu
	begin = clock();
	if (input != NULL) {
		//nacitanie ZT zo suboru
		cipher_file = fopen(input, "rb");
		if(!cipher_file){
			fprintf(stderr, "[rsa_decrypt]: Nepodarilo sa otvorit subor %s\n", input);
			exit(1);
		}
		fseek(cipher_file, 0, SEEK_END);
		sizeOfFile = ftell(cipher_file);
		rewind(cipher_file);
		sizeOfFile /= 8;
		decrypted = (unsigned long long *)malloc(sizeof(unsigned long long) * sizeOfFile);
		if (!decrypted) {
			fprintf(stderr, "[rsa_decrypt]: Alokacia pamate pre decrypted zlyhala\n");
			exit(1);
		}
		numBlocks = fread(decrypted, sizeof(unsigned long long), sizeOfFile, cipher_file);
		fclose(cipher_file);
	}
	else {
		//nacitanie ZT zo stdin
		freopen(NULL, "rb", stdin);
		cipher_file = stdin;
		fseek(cipher_file, 0, SEEK_END);
		sizeOfFile = ftell(cipher_file);
		rewind(cipher_file);
		if (sizeOfFile > 0) {
			decrypted = (unsigned long long *)malloc(sizeof(unsigned long long) * sizeOfFile);
			if (!decrypted) {
				fprintf(stderr, "[rsa_decrypt]: Alokacia pamate pre decrypted zlyhala\n");
				exit(1);
			}
			numBlocks = fread(decrypted, sizeof(unsigned long long), sizeOfFile, cipher_file);
		}
		else {
			fprintf(stderr, "[rsa_decrypt]: Pokus o zadanie sifry manualne z klavesnice\n");
			exit(1);
		}
	}
	end = clock();
	time_spent = ((double)(end - begin) / CLOCKS_PER_SEC) * 1000;
	if (debug) {
		printf("Nacitanie sifry trvalo %lf ms.\n", time_spent);
		printf("Pocet blokov: %llu\n", numBlocks);
	}
	realloc(decrypted, numBlocks * sizeof(unsigned long long));
	
	//priprava GPU na desifrovanie
	cudaStatus = cudaMalloc(&d_decrypted, numBlocks * sizeof(unsigned long long));
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_decrypt]: Zlyhalo alokovanie d_decrypted\n");
		cudaFree(d_decrypted);
		free(decrypted);
		exit(1);
	}

	cudaStatus = cudaMemcpy(d_decrypted, decrypted, numBlocks * sizeof(unsigned long long), cudaMemcpyHostToDevice);
	if (cudaStatus != cudaSuccess) {
		cudaFree(d_decrypted);
		free(decrypted);
		fprintf(stderr, "[rsa_decrypt]: Zlyhalo kopirovanie vstupneho buffra d_decrypted\n");
		exit(1);
	}

	//vypocet dimensii blokov a vlakien, na ktorych sa spusti vypocet
	int blockDim = numBlocks;
	dim3 gridDim;
	if (blockDim > MAX_DIM) {
		gridDim.x = blockDim / MAX_DIM + 1;
		blockDim = MAX_DIM;
		if (gridDim.x > MAX_DIM) {
			gridDim.y = gridDim.x / MAX_DIM + 1;
			gridDim.x = MAX_DIM;
			if (gridDim.y > MAX_DIM) {
				fprintf(stderr, "[rsa_decrypt]: Prekroceny maximalny limit pamate na GPU\n");
				cudaFree(d_decrypted);
				free(decrypted);
				exit(1);
			}
		}
	}

	if (debug) {
		printf("Rozmer mriezky blokov na GPU: %d x %d blokov\nPocet vlakien na blok na GPU: %d\n", gridDim.x, gridDim.y, blockDim);
	}

	cudaEvent_t start, stop;
	cudaEventCreate(&start);
	cudaEventCreate(&stop);
	cudaEventRecord(start, 0);

	//spustenie deifrovania na GPU
	rsa_modExp << <gridDim, blockDim >> > (d, n, numBlocks, d_decrypted);

	cudaStatus = cudaGetLastError();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_decrypt]: Desifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_decrypted);
		free(decrypted);
		exit(1);
	}

	cudaStatus = cudaDeviceSynchronize();
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_decrypt]: cudaDeviceSynchronize vratila chybovy kod %d po spusteni kernelu\n", cudaStatus);
		fprintf(stderr, "[rsa_decrypt]: Desifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_decrypted);
		free(decrypted);
		exit(1);
	}

	cudaEventRecord(stop, 0);
	cudaEventSynchronize(stop);
	cudaEventElapsedTime(&time_spent, start, stop);
	cudaEventDestroy(start);
	cudaEventDestroy(stop);

	if (debug) {
		printf("Desifrovanie trvalo %.2f ms\n", time_spent);
	}

	cudaStatus = cudaMemcpy(decrypted, d_decrypted, numBlocks * sizeof(unsigned long long), cudaMemcpyDeviceToHost);
	if (cudaStatus != cudaSuccess) {
		fprintf(stderr, "[rsa_decrypt]: Zlyhalo kopirovanie vystupneho buffra\n");
		fprintf(stderr, "[rsa_decrypt]: Desifrovanie zlyhalo: %s\n", cudaGetErrorString(cudaStatus));
		cudaFree(d_decrypted);
		free(decrypted);
		exit(1);
	}

	if (output != NULL) {
		output_file = fopen(output, "wb");
	}
	else {
		output_file = stdout;
		if (debug) {
			printf("Desifrovany text:\n");
		}
	}
	
	//konvertovanie desifrovanej spravy na citatelny text a zapis do suboru
	begin = clock();
	struct message decMsg;
	for (i = 0; i < numBlocks - 1; i++) {
		decMsg = intToStr(bufSize, decrypted[i], 0);
		fwrite(decMsg.msg, 1, decMsg.size, output_file);
		free(decMsg.msg);
	}
	decMsg = intToStr(bufSize, decrypted[i], 1);
	fwrite(decMsg.msg, 1, decMsg.size, output_file);
	free(decMsg.msg);
	end = clock();
	time_spent = ((double)(end - begin) / CLOCKS_PER_SEC) * 1000;

	if (output != NULL) {
		fclose(output_file);
	}
	if (debug && output != NULL) {
		printf("Zapis desifrovanej spravy do suboru trval %lf ms\n", time_spent);
		printf("Desifrovanie dokoncene. Vystup je ulozeny v subore %s\n", output);
	}
	else if (debug) {
		printf("\nZapis spravy na vystup %lf ms\n", time_spent);
		printf("Desifrovanie dokoncene. Vystup je na stdout\n");
	}
}

struct message inputString(char *input, long long bufSize) {
	FILE *input_file;
	struct message message;
	unsigned long long sizeOfFile;
	//nacitanie suboru do buffra
	if (input != NULL) {
		input_file = fopen(input, "rb");
		if(!input_file){
			fprintf(stderr, "[inputString]: Nepodarilo sa otvorit subor %s\n", input);
			exit(1);
		}
		fseek(input_file, 0, SEEK_END);
		sizeOfFile = ftell(input_file);
		rewind(input_file);
		if (debug) {
			printf("Velkost suboru je:\t\t%llu\n", sizeOfFile);
		}
		message.msg = (unsigned char *)malloc(sizeof(unsigned char) * (sizeOfFile + 1));
		if (!message.msg) {
			fprintf(stderr, "[inputString]: Nepodarilo sa alokovat pamat pre buffer\n");
			exit(1);
		}
		message.size = fread(message.msg, 1, sizeOfFile, input_file);
		if (debug) {
			printf("Nacitana velkost suboru je:\t%llu\n", message.size);
		}
		message.msg[sizeOfFile] = 255;
		message.size++;
		fclose(input_file);
	}
	//nacitanie suboru zo standardneho vstupu
	else {
		freopen(NULL, "rb", stdin);
		input_file = stdin;
		fseek(input_file, 0, SEEK_END);
		sizeOfFile = ftell(input_file);
		fseek(input_file, 0, SEEK_SET);
		if (sizeOfFile > 0) {
			//citanie suboru zo stdin
			if (debug) {
				printf("Velkost suboru je:\t\t%llu\n", sizeOfFile);
			}
			message.msg = (unsigned char *)malloc(sizeof(unsigned char) * sizeOfFile);
			if (!message.msg) {
				fprintf(stderr, "[inputString]: Nepodarilo sa alokovat pamat pre buffer\n");
				exit(1);
			}
			message.size = fread(message.msg, 1, sizeOfFile, input_file);
			if (debug) {
				printf("Nacitana velkost suboru je:\t%llu\n", message.size);
			}
			message.msg[message.size++] = 255;
		}
		else {
			//nacitanie znakov zo stdin
			message.msg = (unsigned char *)malloc(sizeof(unsigned char) * (MAX_KEYBOARD_INPUT + 1));
			if (!message.msg) {
				fprintf(stderr, "[inputString]: Nepodarilo sa alokovat pamat pre buffer\n");
				exit(1);
			}
			fgets((char*)message.msg, MAX_KEYBOARD_INPUT, input_file);
			message.size = strlen((char*)message.msg);
			message.msg[message.size++] = 255;
			sizeOfFile = message.size;
		}
	}
	if (sizeOfFile % bufSize != 0) {
		message.numBlocks = sizeOfFile / bufSize + 1;
	}
	else {
		message.numBlocks = sizeOfFile / bufSize;
	}
	return message;
}

void help(char *argv) {
	//nacitanie suboru s helpom a jeho nasledne zobrazenie na obrazovku
	FILE *help;
	char *input;
	help = fopen("help.txt", "rb");
	if(!help){
			fprintf(stderr, "[help]: Nepodarilo sa otvorit subor s pouzivatelskou priruckou\n");
			exit(1);
	}
	fseek(help, 0, SEEK_END);
	int sizeOfFile = ftell(help);
	rewind(help);
	input = (char*)malloc(sizeOfFile * sizeof(char));
	if (!input) {
		fprintf(stderr, "[help]: Nepodarilo sa alokovat pamat pre buffer\n");
		exit(1);
	}
	fread(input, sizeof(char), sizeOfFile, help);
	fclose(help);
	input[sizeOfFile] = '\0';
	printf("%s", input);
}

int main(int argc, char **argv) {
	struct public_key pub[1];
	struct private_key priv[1];
	int modSize = 32, bufSize = modSize / 8;
	int i, flag = 0;
	clock_t begin, end;
	double time_spent;
	char *output, *input;

	if (argc > 1) {
		for (i = 1; i < argc; i++) {
			//prepinac, ktory zapina debugovaci mod
			if (!strcmp(argv[i], "-b")) {
				if (argc == 2) {
					fprintf(stderr, "Malo argumentov, skus znova alebo pouzi -h pre pomoc.\n");
					return 0;
				}
				debug = 1;
				break;
			}
		}
		for (i = 1; i < argc; i++) {
			//prepinac, ktory vypise help
			if (!strcmp(argv[i], "-h")) {
				help(argv[0]);
			}
			//prepinac na vygenerovanie a ulozenie klucov k RSA
			else if (!strcmp(argv[i], "-g")) {
				rsa_gen_keys(pub, priv, modSize);
				i++;
				char *filename1, *filename2;
				if (i < argc && (strcmp(argv[i], "-e") != 0 && strcmp(argv[i], "-d") != 0 && strcmp(argv[i], "-h") != 0) && strcmp(argv[i], "-b") != 0) {
					//nacitanie nazvu vystupneho suboru zo vstupu
					filename1 = (char*)malloc((strlen(argv[i]) + 1) * sizeof(char));
					if (!filename1) {
						fprintf(stderr, "[main]: Nepodarilo sa alokovat pamat pre buffer filename1\n");
						exit(1);
					}
					filename2 = (char*)malloc((strlen(argv[i]) + 5) * sizeof(char));
					if (!filename2) {
						fprintf(stderr, "[main]: Nepodarilo sa alokovat pamat pre buffer filename1\n");
						exit(1);
					}
					filename1[0] = '\0';
					filename2[0] = '\0';
					strcat(filename1, argv[i]);
					strcat(filename2, filename1);
					strcat(filename2, ".pub");
				}
				else {
					//v pripade, ze na vstupe nie je nazov vystupneho suboru, pouziju sa defaultne nazvy
					i--;
					filename1 = (char*)malloc(7 * sizeof(char));
					filename2 = (char*)malloc(11 * sizeof(char));
					filename1[0] = '\0';
					filename2[0] = '\0';
					strcat(filename1, "rsakey");
					strcat(filename2, filename1);
					strcat(filename2, ".pub");
				}
				//ulozenie klucov do suborov
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
				return 0;
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
						//inak citam subor so sukromnym klucom
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
					//spracovanie dalsich vstupnych argumentov
					i++;
					if (argv[i] == NULL) {
						if (debug) {
							printf("Nebol zadany vstupny subor, citam stdin.\n");
						}
						input = NULL;
						output = NULL;
					}
					else {
						input = (char*)malloc(strlen(argv[i]) * sizeof(char));
						if (!input) {
							fprintf(stderr, "[main]: Nepodarilo sa alokovat pamat pre buffer input\n");
							exit(1);
						}
						strcpy(input, argv[i]);
						if (argv[i + 1] != NULL) {
							output = (char*)malloc(strlen(argv[i + 1]) * sizeof(char));
							if (!input) {
								fprintf(stderr, "[main]: Nepodarilo sa alokovat pamat pre buffer output\n");
								exit(1);
							}
							strcpy(output, argv[i + 1]);
						}
						else {
							output = NULL;
						}
					}
					//spustenie modu sifrovania
					if (!strcmp(argv[i - 2], "-e")) {
						struct message message;
						begin = clock();
						//nacitanie vstupu do buffra
						message = inputString(input, bufSize);
						if (message.msg == NULL) {
							fprintf(stderr, "Chyba pri citani zo vstupu!\n");
							exit(1);
						}
						end = clock();
						time_spent = (double)(end - begin) / CLOCKS_PER_SEC * 1000;
						if (debug) {
							printf("Nacitanie spravy zabralo %lf ms\n", time_spent);
							printf("Pocet blokov: %llu\n", message.numBlocks);
						}
						//sifrovanie sukromnym alebo verejnym klucom, na zaklade nacitaneho kluca
						if (flag) {
							rsa_encrypt(priv->d, priv->n, bufSize, message, output);
						}
						else {
							rsa_encrypt(pub->e, pub->n, bufSize, message, output);
						}
						return 0;
					}
					//spustenie modu desifrovania
					else {
						//desifrovanie sukromnym alebo verejnym klucom, na zaklade nacitaneho kluca
						if (flag) {
							rsa_decrypt(priv->d, priv->n, bufSize, input, output);
						}
						else {
							rsa_decrypt(pub->e, pub->n, bufSize, input, output);
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

