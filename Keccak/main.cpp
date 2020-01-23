/*
The code is for clearly expaining the algebraic attacks on round-reduced Keccak. Therefore, it is not optimized.
*/

#include "Dependency.h"
#include <iostream>
#include <ctime>
using namespace std;

int main() {
	Dependency de;
	bool leakedValue[512];
	srand(time(NULL));
	for (int i = 0; i < 512; i++) {
		leakedValue[i] = rand() % 2;
	}
	de.setLeakedValue(leakedValue, 512);

	int choice = 0;

	cout << "0 -> 2-round Keccak-512" << endl;
	cout << "1 -> 2-round Keccak-384" << endl;
	cout << "2 -> 3-round Keccak-512" << endl;
	cout << "3 -> 3-round Keccak-384" << endl;
	cout << "4 -> 4-round Keccak-384" << endl << endl;

	cout << "Input your choice:";
	cin >> choice;

	if (choice == 0){
		de.startTest2RoundKeccak_512();
	}
	else if (choice == 1) {
		de.startTest2RoundKeccak_384();
	}
	else if (choice == 2) {
		de.startTest3RoundKeccak_512();
	}
	else if (choice == 3) {
		de.startTest3RoundKeccak_384();
	}
	else if (choice == 4) {
		de.startTest4RoundKeccak_384();
	}
	else {
		cout << "Input is invalid" << endl;
	}
	return 0;
}
