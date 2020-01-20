#include "Xoodoo.h"
#include <iostream>
#include <iomanip>
#include <vector>
#include <ctime>
#include <fstream>
using namespace std;

Xoodoo::Xoodoo() {
	IL = new bool* [SIZE];
	for (int i = 0; i < SIZE; i++) {
		IL[i] = new bool[SIZE];
	}

	for (int i = 0; i < SIZE; i++) {
		for (int j = 0; j < SIZE; j++) {
			IL[i][j] = 0;
		}
	}
	loadThetaReverse("thetaReverse.txt");

	//encode IL to speed up the calculation
	IL_Encoded = new UINT32 * [SIZE];
	int IL_Encoded_ColNum = SIZE / 32;
	for (int i = 0; i < SIZE; i++) {
		IL_Encoded[i] = new UINT32[IL_Encoded_ColNum];
	}

	for (int i = 0; i < SIZE; i++) {
		for (int j = 0; j < IL_Encoded_ColNum; j++) {
			IL_Encoded[i][j] = 0;
			for (int z = 0; z < 32; z++) {
				if(IL[i][z + j * 32])
					IL_Encoded[i][j] = IL_Encoded[i][j] | EXP[z];
			}
		}
	}

	counter = new bool [EXP[16]];
	bool bit = 0;
	int count = 0;
	for (UINT32 i = 0; i < EXP[16]; i++) {
		count = 0;
		for (int j = 0; j < 16; j++) {
			if (((i >> j) & 0x1) == 1) {
				count++;
			}
		}
		if (count % 2 == 0) {
			counter[i] = 0;
		}
		else {
			counter[i] = 1;
		}
	}

	srand(time(NULL));
}

void Xoodoo::loadThetaReverse(string name) {
	ifstream inFile(name);
	int pos;
	for (int i = 0; i < SIZE; i++) {
		for (int j = 0; j < 133; j++) {
			inFile >> pos;
			IL[i][pos] = 1;
		}
	}
	inFile.close();
}

Xoodoo::~Xoodoo() {
	for (int i = 0; i < SIZE; i++) {
		delete[]IL[i];
	}
	delete[]IL;
}

UINT32 Xoodoo::toUINT32(bool* arr, int gr) {
	UINT64 value = 0;
	int start = gr * 32;
	for (int i = 0; i < 32; i++) {
		if (arr[start + i]) {
			value |= EXP[i];
		}
	}
	return value;
}

UINT32 Xoodoo::getRandUINT32() {
	UINT32 num0 = rand() % EXP[16];
	UINT32 num1 = rand() % EXP[16];
	num0 = num0 * EXP[16] + num1;
	return num0;
}

UINT32 Xoodoo::LL(UINT32 number, int n) {
	if (n == 0) {
		return number;
	}
	return (number << n) | (number >> (32 - n));
}

UINT32 Xoodoo::RR(UINT32 number, int n) {
	if (n == 0) {
		return number;
	}
	return (number >> n) | (number << (32 - n));
}

void Xoodoo::shiftRow(int r, UINT32 row[]) {
	UINT32 tmp[4];
	for (int i = 0; i < 4; i++) {
		tmp[i] = row[(i - r + 4) % 4];
	}
	for (int i = 0; i < 4; i++) {
		row[i] = tmp[i];
	}
}

void Xoodoo::shiftRowInverse(int r, UINT32 row[]) {
	UINT32 tmp[4];
	for (int i = 0; i < 4; i++) {
		tmp[i] = row[(i + r) % 4];
	}
	for (int i = 0; i < 4; i++) {
		row[i] = tmp[i];
	}
}

void Xoodoo::outputState(UINT32 state[]) {
	for (int i = 2; i >= 0; i--) {
		for (int j = 0; j < 4; j++) {
			cout << setw(8) << hex << state[i * 4 + j];
			cout << " ";
		}
		cout << endl;
	}
}

void Xoodoo::permutation(int rounds, UINT32 state[], int startIndex) {
	//one round
	UINT32 P[4], E[4];
	UINT32 B[12];
	for (int r = 0; r < rounds; r++) {
		P[0] = state[0] ^ state[4] ^ state[8];
		P[1] = state[1] ^ state[5] ^ state[9];
		P[2] = state[2] ^ state[6] ^ state[10];
		P[3] = state[3] ^ state[7] ^ state[11];

		E[0] = LL(P[3], 5) ^ LL(P[3], 14);
		E[1] = LL(P[0], 5) ^ LL(P[0], 14);
		E[2] = LL(P[1], 5) ^ LL(P[1], 14);
		E[3] = LL(P[2], 5) ^ LL(P[2], 14);

		for (int row = 0; row < 3; row++) {
			for (int col = 0; col < 4; col++) {
				state[row * 4 + col] ^= E[col];
			}
		}

		//Rho west
		shiftRow(1, state + 4);
		for (int i = 8; i < 12; i++) {
			state[i] = LL(state[i], 11);
		}

		//constant addition
		state[0] = state[0] ^ CONS[r + startIndex];

		//kai operation
		B[0] = state[0] ^ ((~state[4]) & state[8]);
		B[1] = state[1] ^ ((~state[5]) & state[9]);
		B[2] = state[2] ^ ((~state[6]) & state[10]);
		B[3] = state[3] ^ ((~state[7]) & state[11]);

		B[4] = state[4] ^ ((~state[8]) & state[0]);
		B[5] = state[5] ^ ((~state[9]) & state[1]);
		B[6] = state[6] ^ ((~state[10]) & state[2]);
		B[7] = state[7] ^ ((~state[11]) & state[3]);

		B[8] = state[8] ^ ((~state[0]) & state[4]);
		B[9] = state[9] ^ ((~state[1]) & state[5]);
		B[10] = state[10] ^ ((~state[2]) & state[6]);
		B[11] = state[11] ^ ((~state[3]) & state[7]);

		for (int i = 0; i < 12; i++) {
			state[i] = B[i];
		}

		//Rho east
		for (int i = 4; i < 8; i++) {
			state[i] = LL(state[i], 1);
		}
		shiftRow(2, state + 8);
		for (int i = 8; i < 12; i++) {
			state[i] = LL(state[i], 8);
		}
	}
}

void Xoodoo::permutationInverse(int rounds, UINT32 state[], int startIndex) {
	UINT32 B[12];
	bool stateVector[SIZE], output[SIZE];
	for (int r = rounds - 1; r >= 0; r--) {
		//The inverse of Rho east
		for (int i = 4; i < 8; i++) {
			state[i] = RR(state[i], 1);
		}
		shiftRowInverse(2, state + 8);
		for (int i = 8; i < 12; i++) {
			state[i] = RR(state[i], 8);
		}

		//Kai operation
		B[0] = state[0] ^ ((~state[4]) & state[8]);
		B[1] = state[1] ^ ((~state[5]) & state[9]);
		B[2] = state[2] ^ ((~state[6]) & state[10]);
		B[3] = state[3] ^ ((~state[7]) & state[11]);

		B[4] = state[4] ^ ((~state[8]) & state[0]);
		B[5] = state[5] ^ ((~state[9]) & state[1]);
		B[6] = state[6] ^ ((~state[10]) & state[2]);
		B[7] = state[7] ^ ((~state[11]) & state[3]);

		B[8] = state[8] ^ ((~state[0]) & state[4]);
		B[9] = state[9] ^ ((~state[1]) & state[5]);
		B[10] = state[10] ^ ((~state[2]) & state[6]);
		B[11] = state[11] ^ ((~state[3]) & state[7]);

		for (int i = 0; i < 12; i++) {
			state[i] = B[i];
		}

		//constant addition
		state[0] = state[0] ^ CONS[r];

		//The inverse of Rho west
		shiftRowInverse(1, state + 4);
		for (int i = 8; i < 12; i++) {
			state[i] = RR(state[i], 11);
		}

		//The inverse of Theta
		for (int i = 0; i < 12; i++) {
			for (int j = 0; j < 32; j++) {
				stateVector[j + i * 32] = (state[i] >> j) & 0x1;
			}
		}

		//Multiply with IL
		/*for (int i = 0; i < SIZE; i++) {
			output[i] = 0;
			for (int j = 0; j < SIZE; j++) {
				output[i] = output[i] ^ (stateVector[j] & IL[i][j]);
			}
		}*/
		optimizedMatrixMul(state, IL_Encoded, SIZE / 32, SIZE, output);
		for (int i = 0; i < 12; i++) {
			state[i]=toUINT32(output, i);
		}
	}
}

void Xoodoo::zeroSumDistinguisher(int rounds) {
	int position[36] = { 1, 4, 8, 10, 13, 15, 17, 19, 22, 24, 27, 31, 34, 35, 38, 39, 43, 44, 48, 52, 53, 57, 61, 62, 96, 100, 101, 105, 106, 109, 110, 114, 115, 119, 123, 124 };
	//choose 33 from this positions
	UINT32 state[12], consPart[12], sum[12];
	UINT32 stateInverse[12], sumInverse[12];

	/*for (int i = 0; i < 33; i++) {
		cout << "$S^6[" << position[i] / 64 << "][0][" << position[i] % 64 << "]";
		if (position[i] / 64 == 0) {
			cout << "=S^6[" << position[i] / 64 << "][1][" << position[i] % 64 << "] ";
		}
		cout << "=v_0^{" << i + 1 << "}$, ";
		if ((i + 1) % 2 == 0) {
			cout << "\\\\" << endl;
		}
	}
	system("pause");*/

	for (int i = 0; i < 12; i++) {
		consPart[i] = getRandUINT32();
		//consPart[i] = 0;
		sum[i] = 0;
		sumInverse[i] = 0;
	}
	bool stateVector[160], tmpVector[160];
	for (int i = 0; i < 160; i++) {
		tmpVector[i] = (consPart[i / 32] >> (i % 32)) & 0x1;
		stateVector[i] = tmpVector[i];
	}

	UINT64 end = 0;
	int cubeSize = 0;

	if (rounds == 5) {
		end = EXP[17];
		cubeSize = 17;
	}

	else if (rounds == 6) {
		end = 0x200000000;
		cubeSize = 33;
	}

	bool bitValue = 0;
	UINT32 blockValue = 0;

	int startTime = clock();
	for (UINT64 ite = 0; ite < end; ite++) {
		for (int i = 0; i < 12; i++) {
			state[i] = consPart[i];
		}

		for (int i = 0; i < cubeSize; i++) {
			bitValue = (ite >> i) & 0x1;
			stateVector[position[i]] = tmpVector[position[i]] ^ bitValue;
			if (position[i] < 32) {
				stateVector[position[i] + 128] = tmpVector[position[i] + 128] ^ bitValue;
			}
		}

		//from stateVector to state[0],state[1],state[2],state[3],state[4]
		for (int i = 0; i < 5; i++) {
			state[i] = toUINT32(stateVector, i);
		}

		for (int i = 0; i < 12; i++) {
			stateInverse[i] = state[i];
		}
		permutation(rounds, state, rounds);
		permutationInverse(rounds, stateInverse);

		//update sum
		for (int i = 0; i < 12; i++) {
			sum[i] = sum[i] ^ state[i];
		}

		for (int i = 0; i < 12; i++) {
			sumInverse[i] = sumInverse[i] ^ stateInverse[i];
		}

		if (ite % EXP[25] == 0) {
			cout << "attempt: " << hex << ite / EXP[25] << endl;
		}
	}
	int endTime = clock();
	cout << "Running time: " << (endTime - startTime) / 1000 << endl;

	//output sum
	cout << "sum: " << endl;
	outputState(sum);

	cout << endl << "sum of inverse: " << endl;
	outputState(sumInverse);
}

void Xoodoo::zeroSumDistinguisherMul(int rounds, int threadNumber,UINT32 *consPart, UINT32* result, UINT32* resultInverse) {
	int position[36] = { 1, 4, 8, 10, 13, 15, 17, 19, 22, 24, 27, 31, 34, 35, 38, 39, 43, 44, 48, 52, 53, 57, 61, 62, 96, 100, 101, 105, 106, 109, 110, 114, 115, 119, 123, 124 };
	//choose 33 from this positions
	UINT32 state[12], sum[12];
	UINT32 stateInverse[12], sumInverse[12];

	/*for (int i = 0; i < 33; i++) {
		cout << "$S^6[" << position[i] / 64 << "][0][" << position[i] % 64 << "]";
		if (position[i] / 64 == 0) {
			cout << "=S^6[" << position[i] / 64 << "][1][" << position[i] % 64 << "] ";
		}
		cout << "=v_0^{" << i + 1 << "}$, ";
		if ((i + 1) % 2 == 0) {
			cout << "\\\\" << endl;
		}
	}
	system("pause");*/

	for (int i = 0; i < 12; i++) {
		sum[i] = 0;
		sumInverse[i] = 0;
	}
	bool stateVector[160], tmpVector[160];
	for (int i = 0; i < 160; i++) {
		tmpVector[i] = (consPart[i / 32] >> (i % 32)) & 0x1;
		stateVector[i] = tmpVector[i];
	}

	UINT64 start = 0;
	UINT64 end = 0;
	int cubeSize = 0;

	if (rounds == 5) {//ThreadNum: 4
		start = threadNumber * EXP[15];
		end = start + EXP[15];
		cubeSize = 17;
	}

	else if (rounds == 6) {//ThreadNum:16
		UINT64 num = threadNumber;
		start = num * EXP[29];
		end = start + EXP[29];
		cubeSize = 33;
	}

	bool bitValue = 0;
	UINT32 blockValue = 0;

	for (UINT64 ite = start; ite < end; ite++) {
		for (int i = 0; i < 12; i++) {
			state[i] = consPart[i];
		}

		for (int i = 0; i < cubeSize; i++) {
			bitValue = (ite >> i) & 0x1;
			stateVector[position[i]] = tmpVector[position[i]] ^ bitValue;
			if (position[i] < 32) {
				stateVector[position[i] + 128] = tmpVector[position[i] + 128] ^ bitValue;
			}
		}

		//from stateVector to state[0],state[1],state[2],state[3],state[4]
		for (int i = 0; i < 5; i++) {
			state[i] = toUINT32(stateVector, i);
		}

		for (int i = 0; i < 12; i++) {
			stateInverse[i] = state[i];
		}
		permutation(rounds, state, rounds);
		permutationInverse(rounds, stateInverse);

		//update sum
		for (int i = 0; i < 12; i++) {
			sum[i] = sum[i] ^ state[i];
		}

		for (int i = 0; i < 12; i++) {
			sumInverse[i] = sumInverse[i] ^ stateInverse[i];
		}

		if (ite % EXP[25] == 0) {
			cout << "attempt: " << hex << ite / EXP[25] << endl;
		}
	}

	for (int i = 0; i < 12; i++) {
		result[i] = sum[i];
		resultInverse[i] = sumInverse[i];
	}

	//output sum
	/*cout << "sum: " << endl;
	outputState(sum);

	cout << endl << "sum of inverse: " << endl;
	outputState(sumInverse);*/
}

void Xoodoo::optimizedMatrixMul(UINT32* state, UINT32** matrix, int col, int row, bool* value) {
	UINT32 tmp;
	for (int i = 0; i < row; i++) {
		value[i] = 0;
		for (int j = 0; j < col; j++) {
			tmp = matrix[i][j] & state[j];
			value[i] ^= counter[(tmp & 0xffff)];
			value[i] ^= counter[((tmp >> 16) & 0xffff)];
		}
	}
}