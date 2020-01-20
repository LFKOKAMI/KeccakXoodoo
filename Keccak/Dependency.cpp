#include "Dependency.h"
#include <iostream>
#include <fstream>
#include <string>
#include <ctime>
#include <cstring>
#include <iomanip>
using namespace std;

//generate a 64-bit value
UINT64 Dependency::getRandUINT64() {
	UINT64 t1 = 0, t2 = 0;
	t1 = (rand() << 16) | rand();
	t2 = (rand() << 16) | rand();

	t1 = (t1 + preT1) & 0xffffffff;
	t2 = (t2 + preT2) & 0xffffffff;

	t1 = t1 << 32;
	preT1 = t1;
	preT2 = t2;
	return t1 | t2;
}

Dependency::Dependency() {
	srand(time(NULL));
	preT1 = preT2 = 0;

	LMKeccak = new int*[1600];
	for (int i = 0; i < 1600; i++) {
		LMKeccak[i] = new int[11];
	}

	rhoPiKeccak = new int[1600];
	inverseRhoPi = new int[1600];

	loadLinearMatrix(".//data//linearize.txt", 1600, 11, LMKeccak);
	loadRhoPi(".//data//RhoPi.txt", 1600, rhoPiKeccak, inverseRhoPi);

	//test the correctness
	/*for (int i = 0; i < 1600; i++) {
		for (int j = 0; j < 11; j++) {
			cout << LMKeccak[i][j] << " ";
		}
		cout << endl;
	}
	cout << endl << "Mapping:" << endl;
	for (int i = 0; i < 1600; i++) {
		cout << rhoPiKeccak[i] << endl;
	}*/

	//map
	int count = 0;
	for (int i = 0; i < 18; i++) {
		map[i][i] = i;
		for (int j = i + 1; j < 18; j++) {
			map[i][j] = 18 + count;
			count++;
			map[j][i] = map[i][j];
		}
	}

	//initialize the pre-computed array
	for (int i = 0; i < 1024; i++) {
		group[i] = i / 64;
		bitPos[i] = 63 - i % 64;
		if ((i + 1) % 64 == 0) {
			pause[i] = true;
		}
		else {
			pause[i] = false;
		}
	}

	encodedEquationSys = new UINT64*[KSIZE];
	equationSys = new bool* [KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		encodedEquationSys[i] = new UINT64[KSIZE / 64];
		equationSys[i] = new bool[KSIZE];
	}
}

Dependency::~Dependency() {
	for (int i = 0; i < 1600; i++) {
		delete[]LMKeccak[i];
		delete[]equationSys[i];
		delete[]encodedEquationSys[i];
	}
	delete[]LMKeccak;
	delete[]rhoPiKeccak;
	delete[]inverseRhoPi;
	delete[]equationSys;
	delete[]encodedEquationSys;
}

void Dependency::loadLinearMatrix(string filename, int row, int col, int** matrix){
	ifstream inFile(filename, ios::in);
	int pos = 0;

	for (int i = 0; i < row; i++) {
		for (int j = 0; j < col; j++) {
			inFile >> pos;
			matrix[i][j] = pos;
		}
	}
	inFile.close();

	cout << "loading is over!" << endl;
}

void Dependency::loadRhoPi(string filename, int row, int* map, int* inverseMap) {
	ifstream inFile(filename, ios::in);
	int pos = 0;

	for (int i = 0; i < row; i++) {
		inFile >> pos;
		inverseMap[i] = pos;
		map[pos] = i;
	}
	inFile.close();

	cout << "loading is over!" << endl;
}

void Dependency::outputMatrix(bool** matrix, int row, int col) {
	for (int i = 0; i < row; i++) {
		cout << i << ": ";
		for (int j = 0; j < col; j++) {
			if (matrix[i][j]) {
				cout << j << " ";
			}
		}
		cout << endl;
	}
}

void Dependency::setLeakedValue(bool leaked[],int length) {
	for (int i = 0; i < length; i++) {
		leakedValue[i] = leaked[i];
	}
}

void Dependency::linearLayerKeccak(UINT64 state[]) {
	UINT64 BC[5];
	UINT64 temp = 0;
	for (int x = 0; x < 5; x++) {
		BC[x] = state[x] ^ state[5 + x] ^ state[10 + x] ^ state[15 + x] ^ state[20 + x];
	}

	for (int x = 0; x < 5; x++) {
		temp = BC[MOD5(x + 4)] ^ ROL64(BC[MOD5(x + 1)], 1);
		for (int y = 0; y < 25; y += 5) {
			state[y + x] ^= temp;
		}
	}

	//Rho Pi
	temp = state[1];
	for (int x = 0; x < 24; x++) {
		BC[0] = state[KeccakP1600_PiLane[x]];
		state[KeccakP1600_PiLane[x]] = ROL64(temp, KeccakP1600_RotationConstants[x]);
		temp = BC[0];
	}
}

void Dependency::startTest2RoundKeccak_512() {
	vector<LinearExp> inputExpr;
	inputExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}

	UINT64 state[25];
	for (int i = 0; i < 25; i++) {
		state[i] = getRandUINT64();
	}

	UINT64 c[5];
	for (int i = 0; i < 5; i++) {
		c[i] = getRandUINT64();
	}

	//initialize inputExpr;
	for (int i = 0; i < 25; i++) {
		if (i <4) {//The variables
			getExpressionConstant(0, inputExpr, i);
			getExpression(inputExpr, i, i * 64);
		}
		else if (i >= 5 && i < 9) {
			getExpressionConstant(c[i - 5], inputExpr, i);
			getExpression(inputExpr, i, (i-5) * 64);
		}
		else {
			getExpressionConstant(state[i], inputExpr, i);
		}
	}

	bool isActive[25] = {
		1,1,0,0,0,
		1,0,0,0,0,
		1,1,0,0,0,
		0,1,0,0,0,
		1,1,0,0,0
	};

	//outputExpression(inputExpr);
	constructMatrix2RoundKeccak_512(c, state, inputExpr, isActive);

	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}
	inputExpr.clear();
}

void Dependency::constructMatrix2RoundKeccak_512(UINT64 c[],UINT64 state[], vector<LinearExp> &inputExpr,bool isActive[]) {
	//initilization (randomly choose 5 64-bit values c[])
	state[0] = 0;
	state[1] = 0;
	state[2] = 0;
	state[3] = 0;
	state[4] = c[4];
	for (int i = 0; i < 4; i++) {
		state[i + 5] = c[i];
	}
	linearLayerKeccak(state);//compute the output of after \theta \rho \pi operations

	//bool eqSys[448][449];//The target equation system
	int sysRow = 448;
	int sysCol = 449;
	/*for (int i = 0; i < sysRow; i++) {
		memset(eqSys[i], 0, sysCol);
	}*/
	//initilize the last column (the leaked values)

	vector<LinearExp> firstExpr;
	firstExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
	}

	//get the expression where variables are involved
	bool *posEquation;
	posEquation = new bool[sysCol];
	vector<int> possiblePos;
	for (int i = 0; i < 25; i++) {
		if (isActive[i]) {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = 0;
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				for (int col = 0; col < 11; col++) {
					firstExpr[j].constant = firstExpr[j].constant ^ inputExpr[LMKeccak[j][col]].constant;
					for (int k = 0; k < inputExpr[LMKeccak[j][col]].varPos.size(); k++) {
						posEquation[inputExpr[LMKeccak[j][col]].varPos[k]] ^= 1;
						possiblePos.push_back(inputExpr[LMKeccak[j][col]].varPos[k]);
					}
				}
				for (int k = 0; k < possiblePos.size(); k++) {
					if (posEquation[possiblePos[k]])
						firstExpr[j].varPos.push_back(possiblePos[k]);
				}
			}
		}
		else {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = BIT(state[i],j- i * 64);
			}
		}
	}

	/*///test the output
	cout << "After permutation: " << endl;
	system("pause");
	outputExpression(firstExpr);
	/////*/

	vector<LinearExp> secondExpr;
	secondExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondExpr[i].clear();
	}

	//start replacing the variables (\chi operation)
	int quadCounter = 256;
	int targetPos = 0;
	int choice = 0;
	for (int y=0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				//if A[x][y][z] = A[x][y][z] + A[x+1][y][z]A[x+2][y][z] + A[x+2][y][z]
				if (firstExpr[POS(MOD5(x + 1), y, z)].varPos.size()>0 && firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0) {
					choice = 0;
				}
				else {
					if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() >0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].constant == false) {
						choice = 1;
					}
					else if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].constant == true) {
						choice = 2;
					}
					else {
						choice = 3;
					}
				}

				if (choice == 0 || choice == 1) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
					//quadratic part
					if (choice == 0) {
						secondExpr[targetPos].varPos.push_back(quadCounter);
						quadCounter++;
					}
				}
				else if (choice == 2) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 1), y, z)].constant ^ 1;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else {
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
			}
		}
	}
	/*/////test
	cout << "After replacing quadratic terms:" << endl;
	system("pause");
	outputExpression(secondExpr);
	cout << "quacounter:" << quadCounter << endl;
	//////*/

	//constant addition
	constantAddition(secondExpr, 0);

	vector<LinearExp> finalExpr;
	finalExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		finalExpr[i].clear();
	}
	linearTransform(secondExpr, finalExpr, sysCol - 1);

	//update the equation system
	clearMatrix(equationSys, sysRow, sysCol);
	int currentRowNum = 0;
	for (int i = 0; i < 320; i++) {
		for (int j = 0; j < finalExpr[i].varPos.size(); j++) {
			equationSys[currentRowNum][finalExpr[i].varPos[j]] ^= 1;
		}
		equationSys[currentRowNum][sysCol - 1] = leakedValue[i] ^ finalExpr[i].constant;
		currentRowNum++;
	}
	//The linear relations in the 2nd row
	//leaked[320+i] leaked[320+64+i] leaked[320+128+i] = b[0] b[1] b[2]
	//b[0]=a[0] + b[1]a[2] + a[2]
	//b[1]=a[1] + b[2]a[3] + a[3]
	for (int z = 0; z < 64; z++) {
		if (leakedValue[320 + 64 + z] == 0) {//a[0]+a[2]=b[0]
			for (int i = 0; i < finalExpr[z+320].varPos.size(); i++) {//a[0]
				equationSys[currentRowNum][finalExpr[z + 320].varPos[i]] ^= 1;
			}
			for (int i = 0; i < finalExpr[z + 320+128].varPos.size(); i++) {//a[2]
				equationSys[currentRowNum][finalExpr[z + 320+128].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + z] ^ finalExpr[z + 320].constant ^ finalExpr[z + 320 + 128].constant;
			currentRowNum++;
		}
		else {//a[0]=b[0]
			for (int i = 0; i < finalExpr[z + 320].varPos.size(); i++) {//a[0]
				equationSys[currentRowNum][finalExpr[z + 320].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + z] ^ finalExpr[z + 320].constant;
			currentRowNum++;
		}

		if (leakedValue[320 + 128 + z] == 0) {//a[1]+a[3]=b[1]
			for (int i = 0; i < finalExpr[z + 320 + 64].varPos.size(); i++) {//a[1]
				equationSys[currentRowNum][finalExpr[z + 320 + 64].varPos[i]] ^= 1;
			}
			for (int i = 0; i < finalExpr[z + 320 + 192].varPos.size(); i++) {//a[3]
				equationSys[currentRowNum][finalExpr[z + 320 + 192].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + 64 + z] ^ finalExpr[z + 320 + 64].constant ^ finalExpr[z + 320 + 192].constant;
			currentRowNum++;
		}
		else {//a[1]=b[1]
			for (int i = 0; i < finalExpr[z + 320 + 64].varPos.size(); i++) {//a[1]
				equationSys[currentRowNum][finalExpr[z + 320 + 64].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + 64 + z] ^ finalExpr[z + 320 + 64].constant;
			currentRowNum++;
		}
	}
	cout << "current row num:" << dec << currentRowNum << endl;
	finalEquationSys(leakedValue, sysRow, sysCol, equationSys, encodedEquationSys);

	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
		secondExpr[i].clear();
		finalExpr[i].clear();
	}
	firstExpr.clear();
	secondExpr.clear();
	finalExpr.clear();
}

//2-round Keccak-384
void Dependency::startTest2RoundKeccak_384() {
	vector<LinearExp> inputExpr;
	inputExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}

	UINT64 state[25];
	for (int i = 0; i < 25; i++) {
		state[i] = getRandUINT64();
	}

	UINT64 c[8];
	for (int i = 0; i < 8; i++) {
		c[i] = getRandUINT64();
	}

	//initialize inputExpr;
	int flag[25] = {
		1,0,3,5,0,
		2,0,4,5,0,
		12,0,34,0,0,
		0,0,0,0,0,
		0,0,0,0,0
	};

	for (int i = 0; i < 25; i++) {
		if (flag[i] == 0) {
			getExpressionConstant(state[i], inputExpr, i);
		}
		else if (flag[i] >= 1 && flag[i]<=5) {
			getExpressionConstant(0, inputExpr, i);
			getExpression(inputExpr, i, (flag[i]-1) * 64);
			if (i == 8) {
				getExpressionConstant(c[2], inputExpr, i);
			}
		}
		else if (flag[i] == 12) {
			getExpressionConstant(c[0], inputExpr, i);
			getExpression(inputExpr, i, 0);
			getExpression(inputExpr, i, 64);
		}
		else if (flag[i] == 34) {
			getExpressionConstant(c[1], inputExpr, i);
			getExpression(inputExpr, i, 2*64);
			getExpression(inputExpr, i, 3*64);
		}
	}

	bool isActive[25] = {
		1,0,1,0,0,
		1,0,1,0,0,
		0,1,0,0,0,
		0,1,0,0,0,
		1,1,0,0,0
	};

	//outputExpression(inputExpr);
	constructMatrix2RoundKeccak_384(c, state, inputExpr, isActive);

	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}
	inputExpr.clear();
}

void Dependency::constructMatrix2RoundKeccak_384(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]) {
	//initilization (randomly choose 5 64-bit values c[])
	state[0] = 0;
	state[5] = 0;
	state[10] = c[0];

	state[1] = c[3];
	state[6] = c[4];
	state[11] = c[5];

	state[2] = 0;
	state[7] = 0;
	state[12] = c[1];

	state[3] = 0;
	state[8] = c[2];

	state[4] = c[6];
	state[9] = c[7];
	linearLayerKeccak(state);//compute the output of after \theta \rho \pi operations

	int sysRow = 384;
	int sysCol = 385;

	vector<LinearExp> firstExpr;
	firstExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
	}

	//get the expression where variables are involved
	bool* posEquation;
	posEquation = new bool[sysCol];
	vector<int> possiblePos;
	for (int i = 0; i < 25; i++) {
		if (isActive[i]) {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = 0;
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				for (int col = 0; col < 11; col++) {
					firstExpr[j].constant = firstExpr[j].constant ^ inputExpr[LMKeccak[j][col]].constant;
					for (int k = 0; k < inputExpr[LMKeccak[j][col]].varPos.size(); k++) {
						posEquation[inputExpr[LMKeccak[j][col]].varPos[k]] ^= 1;
						possiblePos.push_back(inputExpr[LMKeccak[j][col]].varPos[k]);
					}
				}
				for (int k = 0; k < possiblePos.size(); k++) {
					if (posEquation[possiblePos[k]])
						firstExpr[j].varPos.push_back(possiblePos[k]);
				}
			}
		}
		else {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = BIT(state[i], j - i * 64);
			}
		}
	}
	/*//////test the output
	cout << "After permutation: " << endl;
	outputExpression(firstExpr);
	system("pause");
	//////*/

	vector<LinearExp> secondExpr;
	secondExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondExpr[i].clear();
	}

	//start replacing the variables (\chi operation)
	int quadCounter = 320;
	int targetPos = 0;
	int choice = 0;
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				//if A[x][y][z] = A[x][y][z] + A[x+1][y][z]A[x+2][y][z] + A[x+2][y][z]
				if (firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0) {
					choice = 0;
				}
				else {
					if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].constant == false) {
						choice = 1;
					}
					else if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].constant == true) {
						choice = 2;
					}
					else {
						choice = 3;
					}
				}

				if (choice == 0 || choice == 1) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
					//quadratic part
					if (choice == 0) {
						secondExpr[targetPos].varPos.push_back(quadCounter);
						quadCounter++;
					}
				}
				else if (choice == 2) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 1), y, z)].constant ^ 1;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else {
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
			}
		}
	}

	/*/////test
	cout << "After replacing quadratic terms:" << endl;
	system("pause");
	outputExpression(secondExpr);
	cout << "quacounter:" << quadCounter << endl;
	//////*/

	//constant addition
	constantAddition(secondExpr, 0);

	vector<LinearExp> finalExpr;
	finalExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		finalExpr[i].clear();
	}
	linearTransform(secondExpr, finalExpr, sysCol - 1);

	//update the equation system
	clearMatrix(equationSys, sysRow, sysCol);
	int currentRowNum = 0;
	for (int i = 0; i < 320+64; i++) {//Additional 64 linear equations
		for (int j = 0; j < finalExpr[i].varPos.size(); j++) {
			equationSys[currentRowNum][finalExpr[i].varPos[j]] ^= 1;
		}
		equationSys[currentRowNum][sysCol - 1] = leakedValue[i] ^ finalExpr[i].constant;
		currentRowNum++;
	}
	cout << "current row num:" << dec << currentRowNum << endl;
	finalEquationSys(leakedValue, sysRow, sysCol, equationSys, encodedEquationSys);

	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
		secondExpr[i].clear();
		finalExpr[i].clear();
	}
	firstExpr.clear();
	secondExpr.clear();
	finalExpr.clear();
}

void Dependency::startTest3RoundKeccak_512() {
	vector<LinearExp> inputExpr;
	inputExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}

	UINT64 state[25],c[2];
	for (int i = 0; i < 25; i++) {
		state[i] = getRandUINT64();
	}
	//satisfy the conditions
	UINT64 B[5], tmp;
	B[0] = state[10] ^ state[15] ^ state[20];
	B[1] = state[11] ^ state[16] ^ state[21];
	B[2] = state[12] ^ state[17] ^ state[22];
	B[3] = state[13] ^ state[18] ^ state[23];
	B[4] = state[9] ^ state[14] ^ state[19] ^ state[24];

	state[POSWORD(4, 0)] = state[POSWORD(4, 4)];
	state[POSWORD(3, 1)] = state[POSWORD(3, 2)];

	tmp = B[4] ^ state[POSWORD(4, 0)];
	tmp = ROL64(tmp, 1);
	c[1] = state[POSWORD(3, 2)] ^ tmp ^ B[2];

	state[POSWORD(1, 0)] = state[POSWORD(1, 4)];
	state[POSWORD(1, 1)] = ~state[POSWORD(1, 4)];

	tmp = B[2] ^ c[1];
	tmp = ROL64(tmp, 1);
	c[0] = state[POSWORD(1, 4)] ^ tmp ^ B[0];
	c[0] = ~c[0];

	tmp = B[0] ^ c[0];
	tmp = ROL64(tmp, 1);
	state[POSWORD(3, 0)] = state[POSWORD(4, 4)] ^ tmp ^ state[POSWORD(3, 1)] ^ B[3];
	state[POSWORD(3, 0)] = ~state[POSWORD(3, 0)];


	//initialize inputExpr;
	int flag[25] = {
		1,0,2,0,0,
		1,0,2,0,0,
		0,0,0,0,0,
		0,0,0,0,0,
		0,0,0,0,0
	};

	for (int i = 0; i < 25; i++) {
		if (flag[i] == 0) {
			getExpressionConstant(state[i], inputExpr, i);
		}
		else{
			getExpressionConstant(0, inputExpr, i);
			getExpression(inputExpr, i, (flag[i] - 1) * 64);

			if (i == 5) {
				getExpressionConstant(c[0], inputExpr, i);
			}

			if (i == 7) {
				getExpressionConstant(c[1], inputExpr, i);
			}
		}
	}

	bool isActive[25] = {
		1,0,0,0,0,
		0,0,0,0,0,
		0,1,0,0,0,
		0,1,0,0,0,
		1,0,0,0,0
	};

	//outputExpression(inputExpr);
	constructMatrix3RoundKeccak_512(c, state, inputExpr, isActive);

	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}
	inputExpr.clear();
}

void Dependency::constructMatrix3RoundKeccak_512(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]) {
	state[0] = 0;
	state[5] = c[0];
	state[2] = 0;
	state[7] = c[1];
	linearLayerKeccak(state);//compute the output of after \theta \rho \pi operations
	int sysRow = 502;
	int sysCol = 495;

	vector<LinearExp> firstExpr;
	firstExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
	}

	//get the expression where variables are involved
	bool* posEquation;
	posEquation = new bool[sysCol];
	vector<int> possiblePos;
	for (int i = 0; i < 25; i++) {
		if (isActive[i]) {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = 0;
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				for (int col = 0; col < 11; col++) {
					firstExpr[j].constant = firstExpr[j].constant ^ inputExpr[LMKeccak[j][col]].constant;
					for (int k = 0; k < inputExpr[LMKeccak[j][col]].varPos.size(); k++) {
						posEquation[inputExpr[LMKeccak[j][col]].varPos[k]] ^= 1;
						possiblePos.push_back(inputExpr[LMKeccak[j][col]].varPos[k]);
					}
				}
				for (int k = 0; k < possiblePos.size(); k++) {
					if (posEquation[possiblePos[k]])
						firstExpr[j].varPos.push_back(possiblePos[k]);
				}
			}
		}
		else {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = BIT(state[i], j - i * 64);
			}
		}
	}
	/*////test the output
	cout << "After 0.5-round permutation: " << endl;
	outputExpression(firstExpr);
	system("pause");
	//////*/

	//the first round is linearized (only the constant part of the expressisons will be influenced)
	int targetPos = 0;
	int choice = 0;
	bool constantBitKai[KSIZE];
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);//A[x][y][z] = A[x][y][z] ^ (~A[x+1][y][z])A[x+2][y][z]
				constantBitKai[targetPos] = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
				if (x == 0 && y == 0) {//constant addition
					constantBitKai[targetPos] ^= BIT(RC[0], z);
				}
			}
		}
	}
	//Update firstExpr with constantBitKai
	//Update A[0][3][z]=A[0][3][z] + (A[1][3][z]+1)A[2][3][z]
	for (int z = 0; z < 64; z++) {
		if (firstExpr[POS(2, 3, z)].constant == 1) {
			firstExpr[POS(0, 3, z)].varPos.push_back(firstExpr[POS(1, 3, z)].varPos[0]);
		}
	}
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].constant = constantBitKai[i];
	}
	/*////test the output
	cout << "After 1-round permutation: " << endl;
	outputExpression(firstExpr);
	system("pause");
	/////*/

	//Compute secondExpr
	vector<LinearExp> secondExpr;
	secondExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondExpr[i].clear();
	}

	vector<LinearExp> thirdExpr;
	thirdExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		thirdExpr[i].clear();
	}
	//guess partial bits (t=54 bits). For test, the values are randomly chosen
	int t = 54;
	bool sum0[54];
	for (int i = 0; i < t; i++) {
		sum0[i] = rand() % 2;
	}

	//clear euqationSys
	clearMatrix(equationSys, sysRow, sysCol);
	//record the equations
	int currentRowNum = 0, x = 0;
	for (int z = 0; z < t; z++) {
		x = 0;//column 0
		equationSys[currentRowNum][sysCol - 1] = sum0[z];
		for (int y = 0; y < 5; y++) {
			for (int k = 0; k < firstExpr[POS(x, y, z)].varPos.size(); k++) {
				equationSys[currentRowNum][firstExpr[POS(x, y, z)].varPos[k]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] ^= firstExpr[POS(x, y, z)].constant;
		}
		currentRowNum++;
	}
	computeSecondExpr_512(sum0, 54, firstExpr,secondExpr,thirdExpr, sysCol,posEquation,possiblePos);

	/*/////test
	cout << "After 1.5-round permutation: " << endl;
	outputExpression(thirdExpr);
	cout << "1.5 rounds end" << endl;
	cout << "start replacing quadratic expressions:" << endl;
	system("pause");
	/////*/

	computeSecondExprKai_512(thirdExpr, secondExpr, sysCol, 128, posEquation, possiblePos);
	constantAddition(secondExpr, 1);

	vector<LinearExp> finalExpr;
	finalExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		finalExpr[i].clear();
	}
	linearTransform(secondExpr, finalExpr, sysCol - 1);

	//update the equation system
	for (int i = 0; i < 320; i++) {
		for (int j = 0; j < finalExpr[i].varPos.size(); j++) {
			equationSys[currentRowNum][finalExpr[i].varPos[j]] ^= 1;
		}
		equationSys[currentRowNum][sysCol - 1] = leakedValue[i] ^ finalExpr[i].constant;
		currentRowNum++;
	}
	//The linear relations in the 2nd row
	//leaked[320+i] leaked[320+64+i] leaked[320+128+i] = b[0] b[1] b[2]
	//b[0]=a[0] + b[1]a[2] + a[2]
	//b[1]=a[1] + b[2]a[3] + a[3]
	for (int z = 0; z < 64; z++) {
		if (leakedValue[320 + 64 + z] == 0) {//a[0]+a[2]=b[0]
			for (int i = 0; i < finalExpr[z + 320].varPos.size(); i++) {//a[0]
				equationSys[currentRowNum][finalExpr[z + 320].varPos[i]] ^= 1;
			}
			for (int i = 0; i < finalExpr[z + 320 + 128].varPos.size(); i++) {//a[2]
				equationSys[currentRowNum][finalExpr[z + 320 + 128].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + z] ^ finalExpr[z + 320].constant ^ finalExpr[z + 320 + 128].constant;
			currentRowNum++;
		}
		else {//a[0]=b[0]
			for (int i = 0; i < finalExpr[z + 320].varPos.size(); i++) {//a[0]
				equationSys[currentRowNum][finalExpr[z + 320].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + z] ^ finalExpr[z + 320].constant;
			currentRowNum++;
		}

		if (leakedValue[320 + 128 + z] == 0) {//a[1]+a[3]=b[1]
			for (int i = 0; i < finalExpr[z + 320 + 64].varPos.size(); i++) {//a[1]
				equationSys[currentRowNum][finalExpr[z + 320 + 64].varPos[i]] ^= 1;
			}
			for (int i = 0; i < finalExpr[z + 320 + 192].varPos.size(); i++) {//a[3]
				equationSys[currentRowNum][finalExpr[z + 320 + 192].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + 64 + z] ^ finalExpr[z + 320 + 64].constant ^ finalExpr[z + 320 + 192].constant;
			currentRowNum++;
		}
		else {//a[1]=b[1]
			for (int i = 0; i < finalExpr[z + 320 + 64].varPos.size(); i++) {//a[1]
				equationSys[currentRowNum][finalExpr[z + 320 + 64].varPos[i]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[320 + 64 + z] ^ finalExpr[z + 320 + 64].constant;
			currentRowNum++;
		}
	}
	cout << "current row num:" << dec << currentRowNum << endl;
	finalEquationSys(leakedValue, sysRow, sysCol, equationSys, encodedEquationSys);

	
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
		secondExpr[i].clear();
		thirdExpr[i].clear();
		finalExpr[i].clear();
	}
	firstExpr.clear();
	secondExpr.clear();
	possiblePos.clear();
	thirdExpr.clear();
	finalExpr.clear();
	delete[]posEquation;
}

void Dependency::computeSecondExpr_512(bool sum[], int length, vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, vector<LinearExp>& thirdExpr, int sysCol, bool* posEquation, vector<int>& possiblePos) {
	//Compute theta operation (special case: sum)
	int targetPos = 0;
	int zShift = 0;
	int xLShift = 0;
	int xRShift = 0;
	memset(posEquation, 0, sysCol);
	possiblePos.clear();
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			xLShift = (x - 1 + 5) % 5;
			xRShift = (x + 1) % 5;
			for (int z = 0; z < 64; z++) {
				zShift = (z - 1 + 64) % 64;
				targetPos = POS(x, y, z);
				secondExpr[targetPos].varPos.clear();
				possiblePos.clear();
				memset(posEquation, 0, sysCol);
				if (x == 1 && z < length) {//Column 1
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum[z];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xRShift, len, zShift)].constant;
						for (int k = 0; k < firstExpr[POS(xRShift, len, zShift)].varPos.size(); k++) {
							possiblePos.push_back(firstExpr[POS(xRShift, len, zShift)].varPos[k]);
						}
					}
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						possiblePos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
				else if(x==4 && (z>=1 && z<=length)){//Column 4
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum[zShift];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xLShift, len, z)].constant;
						for (int k = 0; k < firstExpr[POS(xLShift, len, z)].varPos.size(); k++) {
							possiblePos.push_back(firstExpr[POS(xLShift, len, z)].varPos[k]);
						}
					}
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						possiblePos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
				else {//Other positions
					secondExpr[targetPos].constant = firstExpr[targetPos].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						possiblePos.push_back(firstExpr[targetPos].varPos[k]);
					}
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xRShift, len, zShift)].constant;
						for (int k = 0; k < firstExpr[POS(xRShift, len, zShift)].varPos.size(); k++) {
							possiblePos.push_back(firstExpr[POS(xRShift, len, zShift)].varPos[k]);
						}
					}
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xLShift, len, z)].constant;
						for (int k = 0; k < firstExpr[POS(xLShift, len, z)].varPos.size(); k++) {
							//secondExpr[targetPos].varPos.push_back(firstExpr[POS(xLShift, len, z)].varPos[k]);
							possiblePos.push_back(firstExpr[POS(xLShift, len, z)].varPos[k]);
						}
					}
				}

				for (int k = 0; k < possiblePos.size(); k++) {
					posEquation[possiblePos[k]] ^= 1;
				}
				for (int k = 0; k < possiblePos.size(); k++) {
					if (posEquation[possiblePos[k]]) {
						secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
			}
		}
	}

	/*/////test
	cout << "After 1.25-round permutation: " << endl;
	outputExpression(secondExpr);
	cout << "After 1.25-round permutation ends" << endl;
	system("pause");
	/////*/

	//Rho Pi operations
	for (int i = 0; i < KSIZE; i++) {
		//copy constant
		thirdExpr[i].constant = secondExpr[inverseRhoPi[i]].constant;
		//copy variables
		thirdExpr[i].varPos.clear();
		for (int k = 0; k < secondExpr[inverseRhoPi[i]].varPos.size(); k++) {
			thirdExpr[i].varPos.push_back(secondExpr[inverseRhoPi[i]].varPos[k]);
		}
	}
}

void Dependency::computeSecondExprKai_512(vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, int sysCol,int startCounter, bool* posEquation, vector<int>& possiblePos) {
	int quadCounter = startCounter;
	int targetPos = 0;
	int choice = 0;
	possiblePos.clear();
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				//if A[x][y][z] = A[x][y][z] + A[x+1][y][z]A[x+2][y][z] + A[x+2][y][z]
				if (firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0) {
					choice = 0;
				}
				else {
					if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].constant == false) {
						choice = 1;
					}
					else if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].constant == true) {
						choice = 2;
					}
					else {
						choice = 3;
					}
				}

				if (choice == 0 || choice == 1) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
					//quadratic part
					if (choice == 0) {
						secondExpr[targetPos].varPos.push_back(quadCounter);
						quadCounter++;
					}
				}
				else if (choice == 2) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 1), y, z)].constant ^ 1;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else {
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
			}
		}
	}

	/*//////test
	cout << "After replacing quadratic terms:" << endl;
	system("pause");
	outputExpression(secondExpr);

	cout<< "totalCounter:" << quadCounter<< endl;
	cout << "New variables:" << quadCounter-startCounter << endl;
	system("pause");
	///////*/
}

void Dependency::startTest3RoundKeccak_384() {
	vector<LinearExp> inputExpr;
	inputExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}

	UINT64 state[25], c[2];
	for (int i = 0; i < 25; i++) {
		state[i] = getRandUINT64();
	}
	//satisfy the conditions
	UINT64 B[5], tmp, X,Y,Z,W;
	state[16] = ~state[21];//X=~Y
	state[13] = state[18];//Z=W;
	X = state[16];
	Y = state[21];
	Z = state[13];
	W = state[18];
	B[0] = state[15] ^ state[20];
	B[1] = state[16] ^ state[21];
	B[2] = state[17] ^ state[22];
	B[3] = state[13] ^ state[18] ^ state[23];
	B[4] = state[14] ^ state[19] ^ state[24];

	state[POSWORD(4, 0)] = state[POSWORD(4, 4)];
	state[POSWORD(4, 1)] = state[POSWORD(4, 4)];

	tmp = B[4] ^ state[POSWORD(4, 0)] ^ state[POSWORD(4, 1)];
	tmp = ROL64(tmp, 1);
	c[1] = Z ^ tmp ^ B[2];

	state[POSWORD(3, 1)] = B[2] ^ c[1] ^ tmp;

	tmp = B[2] ^ c[1];
	tmp = ROL64(tmp, 1);
	c[0] = X ^ B[0] ^ tmp;

	tmp = B[0] ^ c[0];
	tmp = ROL64(tmp, 1);
	state[POSWORD(3, 0)] = state[POSWORD(4, 4)] ^ B[3] ^ state[POSWORD(3, 1)]^tmp;
	state[POSWORD(3, 0)] = ~state[POSWORD(3, 0)];

	state[POSWORD(1, 0)] = Y;
	state[POSWORD(1, 1)] = X;
	state[POSWORD(1, 2)] = X;

	//initialize inputExpr;
	int flag[25] = {
		12,0,3,0,0,
		1,0,4,0,0,
		2,0,34,0,0,
		0,0,0,0,0,
		0,0,0,0,0
	};

	for (int i = 0; i < 25; i++) {
		if (flag[i] == 0) {
			getExpressionConstant(state[i], inputExpr, i);
		}
		else if (flag[i] >= 1 && flag[i] <= 4) {
			getExpressionConstant(0, inputExpr, i);
			getExpression(inputExpr, i, (flag[i] - 1) * 64);
		}

		if (i == 0) {
			getExpressionConstant(c[0], inputExpr, i);
			getExpression(inputExpr, i, 0);
			getExpression(inputExpr, i, 64);
		}

		if (i == 12) {
			getExpressionConstant(c[1], inputExpr, i);
			getExpression(inputExpr, i, 128);
			getExpression(inputExpr, i, 192);
		}
	}

	bool isActive[25] = {
		1,0,1,0,0,
		0,0,1,0,0,
		0,1,0,0,0,
		0,1,0,0,0,
		1,0,0,0,0
	};

	//outputExpression(inputExpr);
	constructMatrix3RoundKeccak_384(c, state, inputExpr, isActive);

	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}
	inputExpr.clear();
}

void Dependency::constructMatrix3RoundKeccak_384(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]) {
	state[0] = c[0];
	state[5] = 0;
	state[10] = 0;

	state[2] = 0;
	state[7] = 0;
	state[12] = c[1];
	linearLayerKeccak(state);//compute the output of after \theta \rho \pi operations

	int sysRow = 461;//3-round Keccak-384
	int sysCol = 461;

	vector<LinearExp> firstExpr;
	firstExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
	}

	//get the expression where variables are involved
	bool* posEquation;
	posEquation = new bool[sysCol];
	vector<int> possiblePos;
	for (int i = 0; i < 25; i++) {
		if (isActive[i]) {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = 0;
				memset(posEquation, 0, sysCol);
				possiblePos.clear();
				for (int col = 0; col < 11; col++) {
					firstExpr[j].constant = firstExpr[j].constant ^ inputExpr[LMKeccak[j][col]].constant;
					for (int k = 0; k < inputExpr[LMKeccak[j][col]].varPos.size(); k++) {
						posEquation[inputExpr[LMKeccak[j][col]].varPos[k]] ^= 1;
						possiblePos.push_back(inputExpr[LMKeccak[j][col]].varPos[k]);
					}
				}
				for (int k = 0; k < possiblePos.size(); k++) {
					if (posEquation[possiblePos[k]])
						firstExpr[j].varPos.push_back(possiblePos[k]);
				}
			}
		}
		else {
			for (int j = i * 64; j < i * 64 + 64; j++) {
				firstExpr[j].constant = BIT(state[i], j - i * 64);
			}
		}
	}
	/*///test the output
	cout << "After 0.5-round permutation: " << endl;
	outputExpression(firstExpr);
	cout << "0.5-round permutation ends " << endl;
	system("pause");
	////*/

	//the first round is linearized (only the constant part of the expressisons will be influenced)
	int targetPos = 0;
	int choice = 0;
	bool constantBitKai[KSIZE];
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);//A[x][y][z] = A[x][y][z] ^ (~A[x+1][y][z])A[x+2][y][z]
				constantBitKai[targetPos] = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
				if (x == 0 && y == 0) {//constant addition
					constantBitKai[targetPos] ^= BIT(RC[0], z);
				}
			}
		}
	}
	//Update the expression of A[0][0]
	for (int i = 0; i < 64; i++) {
		for (int j = 0; j < firstExpr[i + 128].varPos.size(); j++) {
			firstExpr[i].varPos.push_back(firstExpr[i + 128].varPos[j]);
		}
	}
	//Update firstExpr with constantBitKai
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].constant = constantBitKai[i];
	}
	/*////test the output
	cout << "After 1-round permutation: " << endl;
	outputExpression(firstExpr);
	cout << "1-round permutation ends " << endl;
	system("pause");
	////*/

	//Compute secondExpr
	vector<LinearExp> secondExpr;
	secondExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondExpr[i].clear();
	}

	vector<LinearExp> thirdExpr;
	thirdExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		thirdExpr[i].clear();
	}
	//guess partial bits (t=54 bits)
	int t = 13;
	bool *sum0,*sum1,*sum2;
	sum0 = new bool[64];
	sum1 = new bool[t];
	sum2 = new bool[64];
	//Exhaust all possible values of sum0, sum1, sum2;(For test, the values are randomly chosen)
	for (int i = 0; i < 64; i++) {
		sum0[i] = rand() % 2;
		sum2[i] = rand() % 2;
		if (i < 13) {
			sum1[i] = rand() % 2;
		}
	}

	//clear euqationSys
	clearMatrix(equationSys, sysRow, sysCol);
	//record the equations
	int currentRowNum = 0,x=0;
	for (int z = 0; z < 64; z++) {
		x = 0;//column 0
		equationSys[currentRowNum][sysCol - 1] = sum0[z];
		for (int y = 0; y < 5; y++) {
			for (int k = 0; k < firstExpr[POS(x, y, z)].varPos.size(); k++) {
				equationSys[currentRowNum][firstExpr[POS(x, y, z)].varPos[k]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] ^= firstExpr[POS(x, y, z)].constant;
		}
		currentRowNum++;
	}
	for (int z = 0; z < 64; z++) {
		x = 2;//column 0
		equationSys[currentRowNum][sysCol - 1] = sum0[z];
		for (int y = 0; y < 5; y++) {
			for (int k = 0; k < firstExpr[POS(x, y, z)].varPos.size(); k++) {
				equationSys[currentRowNum][firstExpr[POS(x, y, z)].varPos[k]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] ^= firstExpr[POS(x, y, z)].constant;
		}
		currentRowNum++;
	}
	for (int z = 0; z < t; z++) {
		x = 1;//column 0
		equationSys[currentRowNum][sysCol - 1] = sum0[z];
		for (int y = 0; y < 5; y++) {
			for (int k = 0; k < firstExpr[POS(x, y, z)].varPos.size(); k++) {
				equationSys[currentRowNum][firstExpr[POS(x, y, z)].varPos[k]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] ^= firstExpr[POS(x, y, z)].constant;
		}
		currentRowNum++;
	}

	computeSecondExpr_384(sum0, sum1, sum2, t, firstExpr, secondExpr, thirdExpr, sysCol, posEquation, possiblePos);

	/*/////test
	cout << "After 1.5-round permutation: " << endl;
	outputExpression(thirdExpr);
	cout << "1.5 rounds end" << endl;
	cout << "start replacing quadratic expressions:" << endl;
	system("pause");
	//////*/

	computeSecondExprKai_512(thirdExpr, secondExpr, sysCol, 256, posEquation, possiblePos);
	constantAddition(secondExpr, 1);
	/*/////test
	cout << "2 rounds end" << endl;
	cout << "start generating the equation system:" << endl;
	system("pause");
	//////*/

	for (int i = 0; i < KSIZE; i++) {
		thirdExpr[i].clear();
	}
	linearTransform(secondExpr, thirdExpr, sysCol-1);

	//update the equation system
	for (int i = 0; i < 320; i++) {
		for (int j = 0; j < thirdExpr[i].varPos.size(); j++) {
			equationSys[currentRowNum][thirdExpr[i].varPos[j]] ^= 1;
		}
		equationSys[currentRowNum][sysCol - 1] = leakedValue[i]^ thirdExpr[i].constant;
		currentRowNum++;
	}
	cout << "current row num:" << dec << currentRowNum << endl;

	finalEquationSys(leakedValue, sysRow, sysCol, equationSys, encodedEquationSys);

	firstExpr.clear();
	secondExpr.clear();
	possiblePos.clear();
	thirdExpr.clear();
	delete[]sum0;
	delete[]sum1;
	delete[]sum2;
	delete[]posEquation;
}

void Dependency::computeSecondExpr_384(bool sum0[], bool sum1[], bool sum2[], int length, vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, vector<LinearExp>& thirdExpr, int sysCol, bool* posEquation, vector<int>& possiblePos) {
	//Compute theta operation (special case: sum)
	int targetPos = 0;
	int zShift = 0;
	int xLShift = 0;
	int xRShift = 0;
	memset(posEquation, 0, sysCol);
	possiblePos.clear();
	bool flag = true;
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			xLShift = (x - 1 + 5) % 5;
			xRShift = (x + 1) % 5;
			for (int z = 0; z < 64; z++) {
				zShift = (z - 1 + 64) % 64;
				targetPos = POS(x, y, z);
				secondExpr[targetPos].clear();
				possiblePos.clear();
				memset(posEquation, 0, sysCol);
				flag = true;
				if (x == 1) {//Column 1
					secondExpr[targetPos].constant = firstExpr[targetPos].constant^sum0[z]^sum2[zShift];
				}
				else if (x == 3) {//Column 3
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum2[z];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xRShift, len, zShift)].constant;
					}
				}
				else if (x == 4) {
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum0[zShift];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xLShift, len, z)].constant;
					}
				}
				else if (x == 2 && z < length) {//sum1[0,1,..,length-1] are known
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum1[z];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xRShift, len, zShift)].constant;
					}
				}
				else if (x == 0 && z >= 1 && z <= length) {
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ sum1[zShift];
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xLShift, len, z)].constant;
					}
				}
				else {
					flag = false;
					secondExpr[targetPos].constant = firstExpr[targetPos].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						possiblePos.push_back(firstExpr[targetPos].varPos[k]);
					}
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xRShift, len, zShift)].constant;
						for (int k = 0; k < firstExpr[POS(xRShift, len, zShift)].varPos.size(); k++) {
							possiblePos.push_back(firstExpr[POS(xRShift, len, zShift)].varPos[k]);
						}
					}
					for (int len = 0; len < 5; len++) {
						secondExpr[targetPos].constant ^= firstExpr[POS(xLShift, len, z)].constant;
						for (int k = 0; k < firstExpr[POS(xLShift, len, z)].varPos.size(); k++) {
							//secondExpr[targetPos].varPos.push_back(firstExpr[POS(xLShift, len, z)].varPos[k]);
							possiblePos.push_back(firstExpr[POS(xLShift, len, z)].varPos[k]);
						}
					}
					//Update variables
					for (int k = 0; k < possiblePos.size(); k++) {
						posEquation[possiblePos[k]] ^= 1;
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]]) {
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
						}
					}
				}
				if (flag) {//Copy variables
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
					//cout << secondExpr[targetPos].constant << endl;
				}
			}
		}
	}

	/*////
	cout << "After 1.25-round permutation: " << endl;
	outputExpression(secondExpr);
	cout << "After 1.25-round permutation ends" << endl;
	system("pause");
	/////*/

	//Rho Pi operations
	for (int i = 0; i < KSIZE; i++) {
		//copy constant
		thirdExpr[i].constant = secondExpr[inverseRhoPi[i]].constant;
		//copy variables
		thirdExpr[i].varPos.clear();
		for (int k = 0; k < secondExpr[inverseRhoPi[i]].varPos.size(); k++) {
			thirdExpr[i].varPos.push_back(secondExpr[inverseRhoPi[i]].varPos[k]);
		}
	}
}

void Dependency::generateConditionMatrix_384(){
	//satisfy the conditions (construct the equation system)
	//Read conditions from file
	ifstream inFile(".//data//condition.txt");
	int x, y, z,conditionNums=0;
	bool value = 0;
	bool** matrix;
	bool* flag;
	matrix = new bool* [KSIZE];
	int colNum = KSIZE + 1 + 17;
	for (int i = 0; i < KSIZE; i++) {
		matrix[i] = new bool[colNum];
	}
	for (int i = 0; i < KSIZE; i++) {
		for (int j = 0; j < colNum; j++) {
			matrix[i][j] = 0;
		}
	}

	bool isConditional[KSIZE];
	bool conditionalValue[KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		isConditional[i] = false;
		conditionalValue[i] = false;
	}

	while (inFile >> x) {
		inFile >> y >> z >> value;
		cout << "A[" << x << "][" << y << "][" << z << "] = " << value << endl;
		isConditional[POS(x, y, z)] = true;
		conditionalValue[POS(x, y, z)] = value;
		//output the equations
		conditionEquations_384(x, y, z,value,matrix,conditionNums,colNum);
		conditionNums++;
	}
	inFile.close();
	cout << "Total number:" << conditionNums << endl;

	outputMatrixSpecial(matrix, conditionNums, colNum);
	cout << "The above is the original matrix" << endl;

	//Test the dependency between the cube variables and conditions
	ifstream cubeFile(".//data//cube.txt");
	int size[17],smallSize;
	int cubeIndex = 0, index = 0;
	int position[17][3];
	for (int i = 0; i < 17; i++) {
		size[i] = 2;
		if (i == 1) {
			size[i] = 3;
		}
	}
	while (cubeFile >> smallSize) {
		for (int i = 0; i < smallSize; i++) {
			cubeFile >> cubeIndex;
			position[index][i] = cubeIndex;
		}
		index++;
	}
	cubeFile.close();
	cout << "Total number:" << index << endl;
	//start replacing the cube variables
	int counter = 0;
	for (int i = 0; i < index; i++) {
		//search the matrix
		for (int row = 0; row < conditionNums; row++) {
			counter = 0;
			for (int k = 0; k < size[i]; k++) {
				if (matrix[row][position[i][k]]) {
					matrix[row][position[i][k]] = 0;
					counter++;
				}
			}
			if (counter > 0) {
				cout << "Replacing " << row << ": "<<counter<<endl;
				matrix[row][i + KSIZE] = 1;//replacing with new variables
			}
		}
	}
	outputMatrixSpecial(matrix, conditionNums, colNum);
	cout << "The above is the new matrix" << endl;
	system("pause");

	/*int nonzeroNum = 0;
	bool f = false;
	for (int i = 0; i < conditionNums; i++) {
		cout << i << ": ";
		for (int j = 0; j < KSIZE; j++) {
			if (matrix[i][j]) {
				getXYZ(j);
				cout << " ";
			}
		}
		for (int j = KSIZE; j < colNum-1; j++) {
			if (matrix[i][j]) {
				cout << "c[" << j - KSIZE << "] ";
			}
		}
		cout << matrix[i][colNum - 1] << endl;
	}*/

	elimination(matrix, KSIZE, colNum, true);

	//store the matrix
	int rowLength;
	ofstream conditionMatrix("conditionMatrix.txt");
	for (int i = 0; i < conditionNums; i++) {
		rowLength = 0;
		for (int j = 0; j < colNum-1; j++) {
			if (matrix[i][j]) {
				rowLength++;
			}
		}
		conditionMatrix << rowLength<<" ";
		for (int j = 0; j < colNum - 1; j++) {
			if (matrix[i][j]) {
				conditionMatrix << j << " ";
			}
		}
		conditionMatrix << matrix[i][colNum - 1] << endl;
	}
	conditionMatrix.close();

	//check
	/*nonzeroNum = 0;
	f = false;
	for (int i = 0; i < conditionNums; i++) {
		cout << i << ": ";
		for (int j = 0; j < KSIZE; j++) {
			if (matrix[i][j]) {
				getXYZ(j);
				cout << " ";
			}
		}
		for (int j = KSIZE; j < colNum-1; j++) {
			if (matrix[i][j]) {
				cout << "c[" << j - KSIZE << "] ";
			}
		}
		cout << matrix[i][colNum - 1] << endl;
	}*/

	bool c[17];
	bool state[KSIZE];
	bool stateTheta[KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		state[i] = rand() % 2;
	}
	for (UINT32 i = 0; i < DI[17]; i++) {
		for (int k = 0; k < 17; k++) {
			c[k] = (i >> k) & 0x1;
		}

		//cube variables
		for (int cu = 0; cu < 17; cu++) {
			state[position[cu][size[cu] - 1]] = c[cu];
			for (int s = 0; s < size[cu] - 1; s++) {
				state[position[cu][size[cu] - 1]] ^= state[position[cu][s]];
			}
		}
		//conditions
		for (int k = 71; k >= 0; k--) {
			for (int col = 0; col < colNum; col++) {
				if (matrix[k][col]) {
					state[col] = matrix[k][colNum - 1];
					for (int later = col + 1; later < KSIZE; later++) {
						if (matrix[k][later]) {
							state[col] ^= state[later];
						}
					}
					for (int later = KSIZE; later < colNum - 1; later++) {
						if (matrix[k][later]) {
							state[col] ^= c[later - KSIZE];
						}
					}
					break;
				}
			}
		}

		//Check the value after theta operation
		int xl, xr, zs;
		for (int x = 0; x < 5; x++) {
			xl = (x - 1 + 5) % 5;
			xr = (x + 1) % 5;
			for (int y = 0; y < 5; y++) {
				for (int z = 0; z < 64; z++) {
					zs = (z - 1 + 64) % 64;
					stateTheta[POS(x, y, z)] = state[POS(x, y, z)];
					for (int len = 0; len < 5; len++) {
						stateTheta[POS(x, y, z)] ^= state[POS(xl, len, z)];
						stateTheta[POS(x, y, z)] ^= state[POS(xr, len, zs)];
					}
				}
			}
		}
		//Verify
		int imcompatibleNum = 0;
		for (int k = 0; k < KSIZE; k++) {
			if (isConditional[k]) {
				//getXYZ(k);
				//cout<< ": ";
				//cout << stateTheta[k] << " " << conditionalValue[k];
				if (stateTheta[k] != conditionalValue[k]) {
					cout << " wrong";
					imcompatibleNum++;
				}
				//cout << endl;
			}
		}
		//cout << "Incompatible:" << imcompatibleNum << endl;
		//system("pause");
	}

	for (int i = 0; i < KSIZE; i++) {
		delete[]matrix[i];
	}
	delete[]matrix;
}

void Dependency::conditionEquations_384(int x, int y, int z,bool value,bool **matrix, int currentRow,int colNum) {
	//A[x][y][z] = A[x][y][z] + A[x-1][0,1,..,4][z] + A[x+1][0,1,..,4][z-1]
	int xL = (x - 1 + 5) % 5;
	int xR = (x + 1) % 5;
	int zS = (z - 1 + 64) % 64;
	int LSize[5] = { 2,3,3,3,2 };
	int RSize[5] = { 3,3,2,2,3 };

	cout << "A[" << x << "][" << y << "][" << z << "]" << " ";
	matrix[currentRow][POS(x, y, z)] = 1;
	for (int yc = 0; yc < 5; yc++) {
		cout << "A[" << xL << "][" << yc << "][" << z << "]" << " ";
		matrix[currentRow][POS(xL, yc, z)] = 1;
	}
	for (int yc = 0; yc < 5; yc++) {
		cout << "A[" << xR << "][" << yc << "][" << zS << "]" << " ";
		matrix[currentRow][POS(xR, yc, zS)] = 1;
	}

	cout << "= " << value << endl;
	matrix[currentRow][colNum-1] = value;
}

void Dependency::startTest4RoundKeccak_384() {
	vector<LinearExp> inputExpr;
	inputExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}

	//read cube
	ifstream cubeFile(".//data//cube.txt");
	int size[17], smallSize;
	int cubeIndex = 0, index = 0;
	int position[17][3];
	for (int i = 0; i < 17; i++) {
		size[i] = 2;
		if (i == 1) {
			size[i] = 3;
		}
	}
	while (cubeFile >> smallSize) {
		for (int i = 0; i < smallSize; i++) {
			cubeFile >> cubeIndex;
			position[index][i] = cubeIndex;
		}
		index++;
	}
	cubeFile.close();

	//initialize inputExpr (variables)
	int varNum = 0;
	for (int i = 0; i < 17; i++) {
		if (size[i] == 2) {
			inputExpr[position[i][0]].varPos.push_back(varNum);
			inputExpr[position[i][1]].varPos.push_back(varNum);
			varNum++;
		}
		else if (size[i] == 3) {
			inputExpr[position[i][0]].varPos.push_back(varNum);
			inputExpr[position[i][1]].varPos.push_back(varNum+1);
			inputExpr[position[i][2]].varPos.push_back(varNum);
			inputExpr[position[i][2]].varPos.push_back(varNum+1);
			varNum += 2;
		}
	}

	//read condition matrix
	int conditionNum = 72;
	ifstream conditionMatrixFile(".//data//conditionMatrix.txt");
	vector<vector<int> > conditionMatrix;
	vector<bool> value;
	value.resize(72);
	conditionMatrix.resize(72);
	int rowLength = 0,ele;
	for (int i = 0; i < conditionNum; i++) {
		conditionMatrix[i].clear();
		conditionMatrixFile >> rowLength;
		for (int j = 0; j < rowLength; j++) {
			conditionMatrixFile >> ele;
			conditionMatrix[i].push_back(ele);
		}
		conditionMatrixFile>>ele;
		value[i] = ele;
	}

	//generate random capacity part (1 bit condition)
	bool state[KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		state[i] = rand() % 2;
	}

	//assign the constants c[17] (random or exhaustive)
	bool c[17];
	for (int i = 0; i < 17; i++) {
		c[i] = rand() % 2;
	}

	//satisfy the conditions
	int len = 0;
	for (int i = conditionNum-1; i >=0; i--) {
		len = conditionMatrix[i].size();
		state[conditionMatrix[i][0]] = value[i];
		for (int col = 1; col < conditionMatrix[i].size(); col++) {
			if (conditionMatrix[i][col] >= KSIZE) {
				state[conditionMatrix[i][0]] ^= c[conditionMatrix[i][col]-KSIZE];
			}
			else {
				state[conditionMatrix[i][0]] ^= state[conditionMatrix[i][col]];
			}
		}
	}

	/*/////test the correctness
	bool isConditional[KSIZE];
	bool conditionalValue[KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		isConditional[i] = false;
		conditionalValue[i] = false;
	}
	int x, y, z;
	ifstream inFile(".//data//condition.txt");
	while (inFile >> x) {
		inFile >> y >> z >> ele;
		cout << "A[" << x << "][" << y << "][" << z << "] = " << ele << endl;
		isConditional[POS(x, y, z)] = true;
		conditionalValue[POS(x, y, z)] = ele;

	}
	inFile.close();

	bool stateTheta[KSIZE];
	//cube variables
	for (int cu = 0; cu < 17; cu++) {
		state[position[cu][size[cu] - 1]] = c[cu];
		for (int s = 0; s < size[cu] - 1; s++) {
			state[position[cu][size[cu] - 1]] ^= state[position[cu][s]];
		}
	}
	//Check the value after theta operation
	int xl, xr, zs;
	for (int x = 0; x < 5; x++) {
		xl = (x - 1 + 5) % 5;
		xr = (x + 1) % 5;
		for (int y = 0; y < 5; y++) {
			for (int z = 0; z < 64; z++) {
				zs = (z - 1 + 64) % 64;
				stateTheta[POS(x, y, z)] = state[POS(x, y, z)];
				for (int len = 0; len < 5; len++) {
					stateTheta[POS(x, y, z)] ^= state[POS(xl, len, z)];
					stateTheta[POS(x, y, z)] ^= state[POS(xr, len, zs)];
				}
			}
		}
	}
	//Verify
	int incompatibleNum = 0;
	for (int k = 0; k < KSIZE; k++) {
		if (isConditional[k]) {
			if (stateTheta[k] != conditionalValue[k]) {
				cout << " wrong";
				incompatibleNum++;
			}
		}
	}
	if (incompatibleNum == 0) {
		cout << "correct" << endl;
	}
	////////////////*/

	//initialize inputExpr (value)
	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].constant = state[i];
	}
	for (int i = 0; i < 17; i++) {
		for (int j = 0; j < size[i] - 1; j++) {
			inputExpr[position[i][j]].constant = 0;
		}
		inputExpr[position[i][size[i] - 1]].constant = c[i];
	}

	//outputExpression(inputExpr);
	constructMatrix4RoundKeccak_384(c, state, inputExpr);

	for (int i = 0; i < conditionNum; i++) {
		conditionMatrix[i].clear();
	}
	conditionMatrix.clear();
	value.clear();

	for (int i = 0; i < KSIZE; i++) {
		inputExpr[i].clear();
	}
	inputExpr.clear();
}

void Dependency::constructMatrix4RoundKeccak_384(bool c[], bool state[], vector<LinearExp>& inputExpr) {
	vector<LinearExp> firstExpr;
	firstExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
	}
	linearTransform(inputExpr, firstExpr,18);

	/*//////test
	outputExpression(firstExpr);
	cout << "0.5-round per ends" << endl << endl;
	//////*/

	bool isConditional[KSIZE];
	bool conditionalValue[KSIZE];
	for (int i = 0; i < KSIZE; i++) {
		isConditional[i] = false;
		conditionalValue[i] = false;
	}

	/*////check
	int x, y, z,ele;
	ifstream inFile(".//data//condition.txt");
	while (inFile >> x) {
		inFile >> y >> z >> ele;
		isConditional[rhoPiKeccak[POS(x, y, z)]] = true;
		conditionalValue[rhoPiKeccak[POS(x, y, z)]] = ele;
	}
	inFile.close();

	for (int i = 0; i < KSIZE; i++) {
		if (isConditional[i]) {
			if (firstExpr[i].varPos.size() > 0) {
				cout << "No var: ";
				getXYZ(i);
				getXYZ(inverseRhoPi[i]);
				cout << endl;
			}
			else {
				if (firstExpr[i].constant != conditionalValue[i]) {
					cout << "Value wrong: ";
					getXYZ(i);
					getXYZ(inverseRhoPi[i]);
					cout << endl;
				}
			}
		}
	}
	system("pause");
	//////*/

	vector<LinearExp> firstKaiExpr;
	firstKaiExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		firstKaiExpr[i].clear();
	}
	kaiTransform(firstExpr,firstKaiExpr,18);
	constantAddition(firstKaiExpr,0);
	//outputExpression(firstKaiExpr);

	/*///compare firstKai and first
	for (int i = 0; i < KSIZE; i++) {
		if (firstExpr[i].varPos.size() > 0) {
			if (firstKaiExpr[i].varPos.size() == 0) {
				cout << "wrong wrong wrong" << endl;
			}
			else {
				for (int j = 0; j < firstExpr[i].varPos.size(); j++) {
					if (firstExpr[i].varPos[j] != firstKaiExpr[i].varPos[j]) {
						cout << "wrong" << endl;
					}
				}
				for (int j = 0; j < firstExpr[i].varPos.size(); j++) {
					cout << firstExpr[i].varPos[j] << " ";
				}
				cout << endl;
				for (int j = 0; j < firstKaiExpr[i].varPos.size(); j++) {
					cout << firstKaiExpr[i].varPos[j] << " ";
				}
				cout << endl << endl;
			}
		}

		if (firstKaiExpr[i].varPos.size() > 0) {
			if (firstExpr[i].varPos.size() == 0) {
				cout << "wrong wrong: ";
				getXYZ(i);
				cout << endl;
			}
			else {
				for (int j = 0; j < firstExpr[i].varPos.size(); j++) {
					if (firstExpr[i].varPos[j] != firstKaiExpr[i].varPos[j]) {
						cout << "wrong" << endl;
					}
				}
				for (int j = 0; j < firstExpr[i].varPos.size(); j++) {
					cout << firstExpr[i].varPos[j] << " ";
				}
				cout << endl;
				for (int j = 0; j < firstKaiExpr[i].varPos.size(); j++) {
					cout << firstKaiExpr[i].varPos[j] << " ";
				}
				cout << endl << endl;
			}
		}
	}
	cout << "1-round per ends" << endl << endl;
	system("pause");
	//////*/

	//2-round
	vector<LinearExp> secondExpr;
	secondExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondExpr[i].clear();
	}
	linearTransform(firstKaiExpr, secondExpr, 18);

	/*//////test
	outputExpression(secondExpr);
	cout << "1.5-round per ends" << endl << endl;
	//////*/

	vector<LinearExp> secondKaiExpr;
	secondKaiExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		secondKaiExpr[i].clear();
	}
	kaiTransform(secondExpr, secondKaiExpr, 18);
	constantAddition(secondKaiExpr, 1);
	/*//////test
	outputExpression(secondKaiExpr);
	cout << "2-round per ends" << endl << endl;
	//////*/

	//3-round
	vector<LinearExp> thirdExpr;
	thirdExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		thirdExpr[i].clear();
	}
	linearTransform(secondKaiExpr, thirdExpr, 18);
	/*//////test
	outputExpression(thirdExpr);
	cout << "2.5-round per ends" << endl << endl;
	//////*/

	vector<LinearExp> thirdKaiExpr;
	thirdKaiExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		thirdKaiExpr[i].clear();
	}

	int totalVar = 18 + 9 * 17;
	kaiTransformReplace(thirdExpr, thirdKaiExpr, totalVar,map);
	constantAddition(thirdKaiExpr, 2);
	/*//////test
	outputExpression(thirdKaiExpr);
	cout << "3-round per ends" << endl << endl;
	//////*/

	int sysRow = 35 * 5;
	int sysCol = totalVar + 1;
	vector<LinearExp> finalExpr;
	finalExpr.resize(KSIZE);
	for (int i = 0; i < KSIZE; i++) {
		finalExpr[i].clear();
	}
	linearTransform(thirdKaiExpr, finalExpr, sysCol - 1);

	//update the equation system
	clearMatrix(equationSys, sysRow, sysCol);
	int currentRowNum = 0;
	for (int z = 0; z < 35; z++) {
		for (int x = 0; x < 5; x++) {
			for (int j = 0; j < finalExpr[POS(x,0,z)].varPos.size(); j++) {
				equationSys[currentRowNum][finalExpr[POS(x, 0, z)].varPos[j]] ^= 1;
			}
			equationSys[currentRowNum][sysCol - 1] = leakedValue[POS(x, 0, z)] ^ finalExpr[POS(x, 0, z)].constant;
			currentRowNum++;
		}
	}
	cout << "current row num:" << dec << currentRowNum << endl;
	finalEquationSys(leakedValue, sysRow, sysCol, equationSys, encodedEquationSys);

	for (int i = 0; i < KSIZE; i++) {
		firstExpr[i].clear();
		firstKaiExpr[i].clear();

		secondExpr[i].clear();
		secondKaiExpr[i].clear();

		thirdExpr[i].clear();
		thirdKaiExpr[i].clear();

		finalExpr[i].clear();
	}
	firstExpr.clear();
	firstKaiExpr.clear();
	secondExpr.clear();
	secondKaiExpr.clear();
	thirdExpr.clear();
	thirdKaiExpr.clear();
	finalExpr.clear();
}

void Dependency::linearTransform(vector<LinearExp>& inputExpr, vector<LinearExp>& outputExpr, int varLength) {
	vector<int> possiblePos;
	bool *posEquation;
	posEquation = new bool[varLength];
	memset(posEquation, 0, varLength);
	for (int i = 0; i < KSIZE; i++) {
		outputExpr[i].clear();
		outputExpr[i].constant = 0;
		memset(posEquation, 0, varLength);
		possiblePos.clear();
		for (int j = 0; j < 11; j++) {
			outputExpr[i].constant ^= inputExpr[LMKeccak[i][j]].constant;
			for (int k = 0; k < inputExpr[LMKeccak[i][j]].varPos.size(); k++) {
				possiblePos.push_back(inputExpr[LMKeccak[i][j]].varPos[k]);
				posEquation[inputExpr[LMKeccak[i][j]].varPos[k]] ^= 1;
			}
		}
		for (int j = 0; j < possiblePos.size(); j++) {
			if (posEquation[possiblePos[j]]) {
				outputExpr[i].varPos.push_back(possiblePos[j]);
			}
		}
	}
	delete[]posEquation;
	possiblePos.clear();
}

void Dependency::kaiTransform(vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, int varLength) {
	int targetPos,choice;
	vector<int> possiblePos;
	bool* posEquation;
	posEquation = new bool[varLength];
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);
				possiblePos.clear();
				memset(posEquation, 0, varLength);
				//A[x][y][z] = A[x][y][z] + (A[x+1][y][z])A[x+2][y][z] + A[x+2][y][z]
				if (firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0) {
					cout << "Quadratic term appears! Wrong" << endl;
					choice = 0;
					system("pause");
					return;
				}
				else {
					if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].constant == false) {
						choice = 1;
					}
					else if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].constant == true) {
						choice = 2;
					}
					else {
						choice = 3;
					}
				}

				if (choice == 1) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else if (choice == 2) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 1), y, z)].constant ^ 1;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else {
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
			}
		}
	}
	delete[]posEquation;
	possiblePos.clear();
}

void Dependency::kaiTransformReplace(vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, int varLength, int map[][18]) {
	int targetPos, choice;
	vector<int> possiblePos;
	bool* posEquation;
	posEquation = new bool[varLength];
	for (int y = 0; y < 5; y++) {
		for (int x = 0; x < 5; x++) {
			for (int z = 0; z < 64; z++) {
				targetPos = POS(x, y, z);
				possiblePos.clear();
				memset(posEquation, 0, varLength);
				//A[x][y][z] = A[x][y][z] + (A[x+1][y][z])A[x+2][y][z] + A[x+2][y][z]
				if (firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0) {
					choice = 0;
				}
				else {
					if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].constant == false) {
						choice = 1;
					}
					else if (firstExpr[POS(MOD5(x + 2), y, z)].varPos.size() == 0 && firstExpr[POS(MOD5(x + 1), y, z)].varPos.size() > 0 && firstExpr[POS(MOD5(x + 2), y, z)].constant == true) {
						choice = 2;
					}
					else {
						choice = 3;
					}
				}

				if (choice==0 || choice == 1) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
					}

					if (choice == 0) {//start replacing quadratic terms
						//update constant
						secondExpr[targetPos].constant = firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant;
						//Update linear term
						if (firstExpr[POS(MOD5(x + 2), y, z)].constant == 1) {
							//record the linear parts of firstExpr[POS(MOD5(x + 1), y, z)]
							for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
								posEquation[firstExpr[POS(MOD5(x+1), y, z)].varPos[i]] ^= 1;
								possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
							}
						}
						if (firstExpr[POS(MOD5(x + 1), y, z)].constant == 1) {
							//record the linear parts of firstExpr[POS(MOD5(x + 2), y, z)]
							for (int i = 0; i < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); i++) {
								posEquation[firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]] ^= 1;
								possiblePos.push_back(firstExpr[POS(MOD5(x + 2), y, z)].varPos[i]);
							}
						}
						//quadratic parts
						for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
							for (int j = 0; j < firstExpr[POS(MOD5(x + 2), y, z)].varPos.size(); j++) {
								//term: firstExpr[POS(MOD5(x + 1), y, z)].varPos[i] & firstExpr[POS(MOD5(x + 2), y, z)].varPos[j]
								posEquation[map[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]][firstExpr[POS(MOD5(x + 2), y, z)].varPos[j]]] ^= 1;
								possiblePos.push_back(map[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]][firstExpr[POS(MOD5(x + 2), y, z)].varPos[j]]);
							}
						}

						for (int k = 0; k < possiblePos.size(); k++) {
							if (posEquation[possiblePos[k]])
								secondExpr[targetPos].varPos.push_back(possiblePos[k]);
						}
					}
				}
				else if (choice == 2) {
					//replace quadratic terms with new variables, counted by quadCounter;
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ firstExpr[POS(MOD5(x + 1), y, z)].constant ^ 1;

					//store the linear parts
					for (int i = 0; i < firstExpr[targetPos].varPos.size(); i++) {
						posEquation[firstExpr[targetPos].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[targetPos].varPos[i]);
					}
					for (int i = 0; i < firstExpr[POS(MOD5(x + 1), y, z)].varPos.size(); i++) {
						posEquation[firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]] ^= 1;
						possiblePos.push_back(firstExpr[POS(MOD5(x + 1), y, z)].varPos[i]);
					}
					for (int k = 0; k < possiblePos.size(); k++) {
						if (posEquation[possiblePos[k]])
							secondExpr[targetPos].varPos.push_back(possiblePos[k]);
					}
				}
				else {
					secondExpr[targetPos].clear();
					secondExpr[targetPos].constant = firstExpr[targetPos].constant ^ (firstExpr[POS(MOD5(x + 1), y, z)].constant & firstExpr[POS(MOD5(x + 2), y, z)].constant) ^ firstExpr[POS(MOD5(x + 2), y, z)].constant;
					for (int k = 0; k < firstExpr[targetPos].varPos.size(); k++) {
						secondExpr[targetPos].varPos.push_back(firstExpr[targetPos].varPos[k]);
					}
				}
			}
		}
	}
	delete[]posEquation;
	possiblePos.clear();
}

void Dependency::finalEquationSys(bool* leakedValue, int rowNum, int colNum, bool** eqSys, UINT64** encodeEqSys) {
	//Encode the eqSys
	int varNum = colNum - 1;
	int encodeColNum = varNum / 64 + 2;
	if (varNum % 64 == 0) {
		encodeColNum--;
	}
	//compute encoded eqSys
	for (int i = 0; i < rowNum; i++) {
		for (int j = 0; j < encodeColNum-2; j++) {
			encodeEqSys[i][j] = toUINT64(eqSys[i], j);//full 64 bits
		}
		//deal with encodeColNum-2 (full or not full)
		UINT64 value = 0;
		for (int j = (encodeColNum - 2) * 64; j < varNum; j++) {
			if (eqSys[i][j]) {
				value |= DI[bitPos[j]];
			}
		}
		encodeEqSys[i][encodeColNum - 2] = value;
		encodeEqSys[i][encodeColNum - 1] = eqSys[i][colNum-1];
	}
	//encoded gauss elimination
	eliminationEncode(encodeEqSys, rowNum, encodeColNum, varNum);
}

void Dependency::constantAddition(vector<LinearExp>& inputExpr, int round) {
	for (int i = 0; i < 64; i++) {
		inputExpr[i].constant ^= BIT(RC[round], i);
	}
}

void Dependency::getExpression(vector<LinearExp>& expr, int pos,int varStart) {
	for (int i = 0; i < 64; i++) {
		expr[i+pos*64].varPos.push_back(i+varStart);
	}
}

void Dependency::getExpressionConstant(UINT64 constant, vector<LinearExp>& expr, int pos) {
	for (int i = 0; i < 64; i++) {
		expr[i + pos * 64].constant = BIT(constant, i);
	}
}

void Dependency::outputExpression(vector<LinearExp>& expr) {
	for (int i = 0; i < expr.size(); i++) {
		getXYZ(i);
		cout << ": ";
		for (int j = 0; j < expr[i].varPos.size(); j++) {
			cout << expr[i].varPos[j] << " ";
		}
		cout << expr[i].constant << endl;
	}
}

void Dependency::getXYZ(int pos) {
	int x, y, z;
	z = pos % 64;
	y = (pos / 64) / 5;
	x = (pos / 64) % 5;

	cout << "A[" << x << "][" << y << "][" << z << "]";
}

void Dependency::outputState(UINT64 state[]) {
	for (int i = 0; i < 5; i++) {
		for (int j = 0; j < 5; j++) {
			cout << hex << setw(17)<<state[i * 5 + j] << " ";
		}
		cout << endl;
	}
	system("pause");
}

void Dependency::clearMatrix(bool** matrix, int row, int col) {
	for (int i = 0; i < row; i++) {
		memset(matrix[i], 0, col);
	}
	for (int i = 0; i < row; i++) {
		for (int j = 0; j < col; j++) {
			if (matrix[i][j] != 0) {
				cout << "memset wrong" << endl;
				system("pause");
			}
		}
	}
}

void Dependency::elimination(bool** matrix, int rowNum, int colNum, bool isUp) {
	int variableNum = colNum - 1;
	bool isFirst = false;
	int targetRow = 0;

	for (int i = 0; i < variableNum; i++) {
		isFirst = true;
		for (int j = targetRow; j < rowNum; j++) {
			if (isFirst && matrix[j][i]) {
				isFirst = false;
				swap(matrix[j], matrix[targetRow]);
				targetRow++;
				//cout << "hit:" << i <<": "<<j<< endl;
				//system("pause");
			}
			else {
				if (matrix[j][i]) {//apply Gauss
					for (int k = i; k < colNum; k++) {
						matrix[j][k] ^= matrix[targetRow - 1][k];
					}
				}
			}
		}
	}

	//apply gauss elimination (up)
	/*if (isUp) {
		for (int i = 0; i < rowNum; i++) {
			for (int j = i + 1; j < rowNum; j++) {
				if (matrix[i][j]) {//elimination (up)
					for (int k = j; k < colNum; k++) {
						matrix[i][k] ^= matrix[j][k];
					}
				}
			}
		}
	}*/
}

void Dependency::outputMatrixSpecial(bool** matrix, int rowNum, int colNum){
	int nonzeroNum = 0;
	bool f = false;
	for (int i = 0; i < rowNum; i++) {
		cout << i << ": ";
		for (int j = 0; j < KSIZE; j++) {
			if (matrix[i][j]) {
				getXYZ(j);
				cout << " ";
			}
		}
		for (int j = KSIZE; j < colNum-1; j++) {
			if (matrix[i][j]) {
				cout << "c[" << j - KSIZE << "] ";
			}
		}
		cout << matrix[i][colNum - 1] << endl;
	}
}

void Dependency::eliminationEncode(UINT64** matrix, int rowNum, int colNum, int variableNum) {
	bool isFirst = false;
	int targetRow = 0;
	for (int i = 0; i < variableNum; i++) {
		isFirst = true;
		for (int j = targetRow; j < rowNum; j++) {
			if (isFirst && BIT(matrix[j][group[i]], bitPos[i])) {
				isFirst = false;
				swap(matrix[j], matrix[targetRow]);
				targetRow++;
			}
			else {
				if (BIT(matrix[j][group[i]], bitPos[i])) {//apply Gauss
					for (int k = group[i]; k < colNum; k++) {
						matrix[j][k] ^= matrix[targetRow - 1][k];
					}
				}
			}
		}
	}

	bool isAllZero = true;
	int allZeroNum = 0;
	bool isValid = true;
	for (int i = 0; i < rowNum; i++) {
		isAllZero = true;
		for (int j = 0; j < colNum; j++) {
			cout << hex << matrix[i][j] << " ";
			if (j<colNum-1 && matrix[i][j]!=0) {
				isAllZero = false;
			}
		}
		cout << endl;
		if (isAllZero) {
			if (matrix[i][colNum - 1] != 0) {
				isValid = false;
			}
			allZeroNum++;
		}
	}
	cout << "Number of variables:" << dec<<variableNum << endl;
	cout << "Number of equations:" << dec<<rowNum << endl;
	
	if (isValid) {
		cout << "Number of solutions: 2^" << dec << rowNum-variableNum-allZeroNum << endl;
	}
	else {
		cout << "The equation system is infeasible" << endl;
	}
}

UINT64 Dependency::toUINT64(bool* arr, int gr) {
	UINT64 value = 0;
	int start = gr * 64;
	for (int i = 0; i < 64; i++) {
		if (arr[start + i]) {
			value |= DI[bitPos[i]];
		}
	}
	return value;
}