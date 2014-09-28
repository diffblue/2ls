int divByTwo(int n) {
	int acu=0;
	while (n > 0) {
		n=n/2;
		acu++;
	}
	return acu;
}
