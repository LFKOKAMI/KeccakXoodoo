#include "Xoodoo.h"
#include <thread>
#include <iostream>
using namespace std;

void startMultiThreading(UINT32* constPrt, UINT32* sum, UINT32* sumInverse,int threadNum) {
	Xoodoo xoodoo;
	xoodoo.zeroSumDistinguisherMul(6, threadNum, constPrt, sum, sumInverse);
}

int main() {
	Xoodoo xoodoo;

	UINT32 constPart[12],sum[16][12],sumInverse[16][12];
	for (int i = 0; i < 12; i++) {
		constPart[i] = xoodoo.getRandUINT32();
		cout << hex << constPart[i] << " ";
	}
	cout << endl;

	int totalThreadNum = 0;
	cout << "Input thread number:";
	cin >> totalThreadNum;

	thread task0(startMultiThreading, constPart, sum[0], sumInverse[0], 0);
	thread task1(startMultiThreading, constPart, sum[1], sumInverse[1], 1);
	thread task2(startMultiThreading, constPart, sum[2], sumInverse[2], 2);
	thread task3(startMultiThreading, constPart, sum[3], sumInverse[3], 3);
	thread task4(startMultiThreading, constPart, sum[4], sumInverse[4], 4);
	thread task5(startMultiThreading, constPart, sum[5], sumInverse[5], 5);
	thread task6(startMultiThreading, constPart, sum[6], sumInverse[6], 6);
	thread task7(startMultiThreading, constPart, sum[7], sumInverse[7], 7);
	thread task8(startMultiThreading, constPart, sum[8], sumInverse[8], 8);
	thread task9(startMultiThreading, constPart, sum[9], sumInverse[9], 9);
	thread task10(startMultiThreading, constPart, sum[10], sumInverse[10], 10);
	thread task11(startMultiThreading, constPart, sum[11], sumInverse[11], 11);
	thread task12(startMultiThreading, constPart, sum[12], sumInverse[12], 12);
	thread task13(startMultiThreading, constPart, sum[13], sumInverse[13], 13);
	thread task14(startMultiThreading, constPart, sum[14], sumInverse[14], 14);
	thread task15(startMultiThreading, constPart, sum[15], sumInverse[15], 15);

	task0.join();
	task1.join();
	task2.join();
	task3.join();
	task4.join();
	task5.join();
	task6.join();
	task7.join();
	task8.join();
	task9.join();
	task10.join();
	task11.join();
	task12.join();
	task13.join();
	task14.join();
	task15.join();

	UINT32 finalSum[12], finalSumInverse[12];
	for (int i = 0; i < 12; i++) {
		finalSumInverse[i] = 0;
		finalSum[i] = 0;
	}

	for (int i = 0; i < totalThreadNum; i++) {
		for (int j = 0; j < 12; j++) {
			finalSum[j] ^= sum[i][j];
		}

		for (int j = 0; j < 12; j++) {
			finalSumInverse[j] ^= sumInverse[i][j];
		}
	}

	for (int i = 0; i < 12; i++) {
		cout << hex << finalSum[i] << " ";
	}
	cout << endl;

	for (int i = 0; i < 12; i++) {
		cout << hex << finalSumInverse[i] << " ";
	}
	cout << endl;

	return 0;
}