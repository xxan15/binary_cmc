#include <stdio.h>

int global1 = 1;
int global2 = 2;
int global3 = 2;
int global4 = 2;

void main(int argc) {
	char a[10];
	printf("hello");
	if(argc < 8)
	    global1 = argc + global4;
	a[global1] = 1;
}


