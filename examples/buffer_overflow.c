#include <stdlib.h>

void main(int argc) {
	char* a = malloc(5*sizeof(char));
	a[6] = 0;
	free(a);
}
