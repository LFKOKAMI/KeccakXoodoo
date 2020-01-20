#ifndef _XOODOO_H_
#define _XOODOO_H_

#include <vector>
#include <string>
using namespace std;
typedef unsigned int UINT32;
typedef unsigned long long UINT64;

#define SIZE 384
#define DSIZE 768
#define BIT(x,i) ((x>>i)&0x1)

const UINT32 CONS[12] = { 0x00000058 , 0x00000038,0x000003C0,0x000000D0,0x00000120,0x00000014,0x00000060,0x0000002C,0x00000380,0x000000F0,0x000001A0,0x00000012 };

const UINT32 EXP[32] = {
	0x1,0x2,0x4,0x8,
	0x10,0x20,0x40,0x80,
	0x100,0x200,0x400,0x800,
	0x1000,0x2000,0x4000,0x8000,
	0x10000,0x20000,0x40000,0x80000,
	0x100000,0x200000,0x400000,0x800000,
	0x1000000,0x2000000,0x4000000,0x8000000,
	0x10000000,0x20000000,0x40000000,0x80000000
};

const UINT64 EXP64[64] = {
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

class Xoodoo {
private:
	bool** IL;
	UINT32** IL_Encoded;
	bool *counter;
public:
	Xoodoo();
	~Xoodoo();
	UINT32 toUINT32(bool* arr, int gr);
	void loadThetaReverse(string name);
	void permutation(int rounds, UINT32 state[], int startIndex = 0);
	void permutationInverse(int rounds, UINT32 state[], int startIndex = 0);
	void outputState(UINT32 state[]);

	void shiftRow(int r, UINT32 row[]);
	void shiftRowInverse(int r, UINT32 row[]);
	UINT32 getRandUINT32();
	UINT32 LL(UINT32 number, int n);
	UINT32 RR(UINT32 number, int n);

	//zero-sum distinguisher
	void zeroSumDistinguisher(int rounds);
	void zeroSumDistinguisherMul(int rounds, int threadNumber, UINT32* consPart, UINT32 *result, UINT32 *resultInverse);
	void optimizedMatrixMul(UINT32* state, UINT32** matrix, int col, int row, bool* value);
};

#endif
#pragma once
