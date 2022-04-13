#include<stdio.h>

int global = 0;

void main() {
	char a[10];
	printf("hello");
	a[global] = 42;
}
