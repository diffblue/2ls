
int evenDigits(int n){
	int acu=0;
	for (int i=0; i<n; i++) {
		int subacu = 0, k = i;
		while (k > 0){
			k = k/2;
			subacu++;
		}
		acu = acu + subacu;
	}
	return acu;
}
