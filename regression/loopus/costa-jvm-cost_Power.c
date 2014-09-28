//static int power(int x,int n){
//	if (n==0) return 1;
//	else return x*power(x,n-1);
//}

int power(int x, int n) {
	if (n == 0) return 1;
	int i;
	for (i=1; i < n; ++i) {
		x *= x;
	}
	return x;
}
