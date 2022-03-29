#include<stdlib.h>
#include<stdio.h>

void foo() {
	int *p = malloc(sizeof(int));
	*p = 42;
	printf("Hi\n");
	if(*p != 42) {
		// This line is not reachable
	}
}

void main(int argc) {
	char c[argc];
	char *p = malloc(argc);
	foo();
}
