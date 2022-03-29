#include <stdio.h>

int g0 = 4, g1 = 4;

void bar() {
	g0++;
	g1++;
}

void baz() {
	g0++;
}

void foo() {
	int a[5];
	bar();
	a[g0] = 0;
	baz();
	printf("Hello");
	a[g1] = 0;
}

int main() {
	foo();
	return 0;
}


