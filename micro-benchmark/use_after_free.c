#include <stdlib.h>

void main(int argc) {
	int *p1 = malloc(1*sizeof(int));
	p1[0] = 1;
	free(p1);
	int i = p1[0];
}
