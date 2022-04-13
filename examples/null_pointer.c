#include <stdlib.h>

void main(int argc) {
	char* a = malloc(5*sizeof(char));
	char c = a[6];
	free(a);
}
