#ifndef DEPENDENCY_H_
#define DEPENDENCY_H_

#include<vector>
#include<string>
using namespace std;

typedef unsigned long long UINT64;
typedef unsigned int UINT32;
typedef unsigned char UINT8;

#define ROL64(a, offset) ((((UINT64)a) << offset) ^ (((UINT64)a) >> (64-offset)))

#define RANDROW() (rand()%5)
#define RANDLANE() (rand()%64)
#define POS(x, y, z) ((y * 5 + x) * 64 + z)
#define POSWORD(x,y) (y * 5 + x)
#define smallPos(x, y, z) ((y * 5 + x) * 8 + z)
#define getX(x) ((x / 64) % 5)
#define getY(x) ((x / 64) / 5)
#define getZ(x) (x%64)
#define KSIZE 1600
#define XSIZE 384

#define    MOD5(argValue)    KeccakP1600_Mod5[argValue]
const UINT8 KeccakP1600_Mod5[10] = {
	0, 1, 2, 3, 4, 0, 1, 2, 3, 4
};

#define BIT(x,i) ((x>>i)&0x1)

const UINT8 KeccakP1600_RotationConstants[25] = {
	1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44
};

const UINT8 KeccakP1600_PiLane[25] = {
	10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1
};

const UINT64 RC[24] = {
	0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
	0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
	0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
	0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
	0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
	0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
};

const UINT64 DI[64] = {
	0x1, 0x2, 0x4, 0x8,
	0x10, 0x20, 0x40, 0x80,
	0x100, 0x200, 0x400, 0x800,
	0x1000, 0x2000, 0x4000, 0x8000,
	0x10000, 0x20000, 0x40000, 0x80000,
	0x100000, 0x200000, 0x400000, 0x800000,
	0x1000000, 0x2000000, 0x4000000, 0x8000000,
	0x10000000, 0x20000000, 0x40000000, 0x80000000,
	0x100000000, 0x200000000, 0x400000000, 0x800000000,
	0x1000000000, 0x2000000000, 0x4000000000, 0x8000000000,
	0x10000000000, 0x20000000000, 0x40000000000, 0x80000000000,
	0x100000000000, 0x200000000000, 0x400000000000, 0x800000000000,
	0x1000000000000, 0x2000000000000, 0x4000000000000, 0x8000000000000,
	0x10000000000000, 0x20000000000000, 0x40000000000000, 0x80000000000000,
	0x100000000000000, 0x200000000000000, 0x400000000000000, 0x800000000000000,
	0x1000000000000000, 0x2000000000000000, 0x4000000000000000, 0x8000000000000000
};

const UINT64 AND[64] = {
	0xfffffffffffffffe, 0xfffffffffffffffd, 0xfffffffffffffffb, 0xfffffffffffffff7,
	0xffffffffffffffef, 0xffffffffffffffdf, 0xffffffffffffffbf, 0xffffffffffffff7f,
	0xfffffffffffffeff, 0xfffffffffffffdff, 0xfffffffffffffbff, 0xfffffffffffff7ff,
	0xffffffffffffefff, 0xffffffffffffdfff, 0xffffffffffffbfff, 0xffffffffffff7fff,
	0xfffffffffffeffff, 0xfffffffffffdffff, 0xfffffffffffbffff, 0xfffffffffff7ffff,
	0xffffffffffefffff, 0xffffffffffdfffff, 0xffffffffffbfffff, 0xffffffffff7fffff,
	0xfffffffffeffffff, 0xfffffffffdffffff, 0xfffffffffbffffff, 0xfffffffff7ffffff,
	0xffffffffefffffff, 0xffffffffdfffffff, 0xffffffffbfffffff, 0xffffffff7fffffff,
	0xfffffffeffffffff, 0xfffffffdffffffff, 0xfffffffbffffffff, 0xfffffff7ffffffff,
	0xffffffefffffffff, 0xffffffdfffffffff, 0xffffffbfffffffff, 0xffffff7fffffffff,
	0xfffffeffffffffff, 0xfffffdffffffffff, 0xfffffbffffffffff, 0xfffff7ffffffffff,
	0xffffefffffffffff, 0xffffdfffffffffff, 0xffffbfffffffffff, 0xffff7fffffffffff,
	0xfffeffffffffffff, 0xfffdffffffffffff, 0xfffbffffffffffff, 0xfff7ffffffffffff,
	0xffefffffffffffff, 0xffdfffffffffffff, 0xffbfffffffffffff, 0xff7fffffffffffff,
	0xfeffffffffffffff, 0xfdffffffffffffff, 0xfbffffffffffffff, 0xf7ffffffffffffff,
	0xefffffffffffffff, 0xdfffffffffffffff, 0xbfffffffffffffff, 0x7fffffffffffffff
};

struct LinearExp {
	vector<int> varPos;
	bool constant;
	
	void clear() {
		varPos.clear();
		constant = 0;
	}
};

struct CubeVar {
	vector<int> pos;
	bool value;

	void clear() {
		pos.clear();
	}
};

class Dependency {
private:
	int** LMKeccak;//linear matrix of Keccak
	int* rhoPiKeccak;//
	int* inverseRhoPi;
	int map[18][18];
	int group[1024];
	int bitPos[1024];
	bool pause[1024];
	bool leakedValue[512];

	bool** equationSys;
	UINT64** encodedEquationSys;

	//for random number
	UINT64 preT1, preT2;
public:
	Dependency();
	~Dependency();
	void linearLayerKeccak(UINT64 state[]);
	UINT64 getRandUINT64();
	void setLeakedValue(bool leaked[],int length);

	void loadRhoPi(string filename,int row,int *map, int *inverseMap);
	void loadLinearMatrix(string filename, int row, int col,int **matrix);
	void outputMatrix(bool** matrix, int row, int col);

	//2-round Keccak-512,Keccak-384
	void startTest2RoundKeccak_512();
	void constructMatrix2RoundKeccak_512(UINT64 c[], UINT64 state[],vector<LinearExp>& inputExpr,bool isActive[]);
	void constructMatrix2RoundKeccak_384(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]);
	void startTest2RoundKeccak_384();

	//3-round Keccak-512, Keccak-384
	void startTest3RoundKeccak_512();
	void constructMatrix3RoundKeccak_512(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]);
	void computeSecondExpr_512(bool sum[], int length, vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, vector<LinearExp>& thirdExpr, int sysCol,bool *posEquation, vector<int> &possiblePos);
	void computeSecondExprKai_512(vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, int sysCol, int startCounter, bool* posEquation, vector<int>& possiblePos);
	void startTest3RoundKeccak_384();
	void constructMatrix3RoundKeccak_384(UINT64 c[], UINT64 state[], vector<LinearExp>& inputExpr, bool isActive[]);
	void computeSecondExpr_384(bool sum0[], bool sum1[], bool sum2[], int length, vector<LinearExp>& firstExpr, vector<LinearExp>& secondExpr, vector<LinearExp>& thirdExpr, int sysCol, bool* posEquation, vector<int>& possiblePos);

	//4-round Keccak-384
	void startTest4RoundKeccak_384();
	void constructMatrix4RoundKeccak_384(bool c[], bool state[], vector<LinearExp>& inputExpr);
	void linearTransform(vector<LinearExp>& inputExpr, vector<LinearExp>& outputExpr,int varLength);
	void kaiTransform(vector<LinearExp>& inputExpr, vector<LinearExp>& outputExpr,int varLength);
	void kaiTransformReplace(vector<LinearExp>& inputExpr, vector<LinearExp>& outputExpr, int varLength,int map[][18]);
	void constantAddition(vector<LinearExp>& inputExpr,int round);
	void generateConditionMatrix_384();
	void conditionEquations_384(int x, int y, int z,bool value,bool **matrix,int currentRow,int colNum);

	//leaked linear relations
	void finalEquationSys_512(bool* leakedValue, int rowNum, int colNum, bool** eqSys, UINT64** encodeEqSys);
	void finalEquationSys(bool *leakedValue, int rowNum, int colNum, bool **eqSys, UINT64 **encodeEqSys);
	void finalProEquationSys_384();//use probabilistic equations

	void getExpression(vector<LinearExp>& expr, int pos,int varStart);
	void getExpressionConstant(UINT64 constant,vector<LinearExp>& expr, int pos);
	void outputExpression(vector<LinearExp>& expr);
	void getXYZ(int pos);
	void outputState(UINT64 state[]);

	//elimination
	void elimination(bool** matrix, int rowNum, int colNum, bool isUp);
	void outputMatrixSpecial(bool** matrix,int rowNum,int colNum);
	void clearMatrix(bool** matrix, int row, int col);

	//Encoded Guass elimination
	void eliminationEncode(UINT64** matrix, int rowNum, int colNum, int variableNum);
	UINT64 toUINT64(bool* arr, int gr);
};

#endif
