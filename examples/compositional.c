#include <stdio.h>

int glob = 5;

int foo() {
	printf("hello");
}

int bar() {
	glob = 100;
}

int main() {
	int a[50];
	foo();
	bar();
	a[glob] = 0;
}
