int global1 = 1;
int global2 = 2;

int foo() {
	global2 = 5;
	return 0;
}

void main(int argc) {
	char a[10];
	//foo();
	global1 = global2;
	foo();
	a[global2] = 1;
}

