//int fact(int n){
//	if (n==0) return 1;
//	else return n*fact(n-1);
//}

int fact(int n) {
	int fac = n;
	if (fac == 0)
		fac = 1;
	else {
		int i;
		for (i = n-1; i > 1; --i)
			fac = fac * i;
	}
	return fac;
}
