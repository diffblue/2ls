//int factorial(int n){
//	if (n <=0) return 1;
//	else return n*factorial(n-1);
//}

int doSum(int n) {
	int s=0, i, fac;
	while (n >= 0) {
		fac = n;
		if (fac == 0)
			fac = 1;
		else {
			for (i = n-1; i > 1; --i)
				fac = fac * i;
		}
		s = s + fac;
		n = n-1;
	}
	return s;
}
