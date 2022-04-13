#include <stdlib.h>
#include <stdio.h>

void main(int argc) {
	char* a = malloc(5*sizeof(char));
	a = NULL;
	if(a[0] == 'a') {
		printf("Hello World!");
	}
	free(a);
}
