void sipmabubble(int A[100], int n) {
  /* n >= 0 */
  if (n >= 0) { //added by me (fabian)
	int tmp;

	int i, j;

	i = n;
	while(i >= 0){
	  j = 0;
	  while(j <= i-1){
		if(A[j] > A[j+1]){
		tmp = A[j];
			A[j] = A[j+1];
			A[j+1] = tmp;
	  }
		++j;
	  }
	  i--;
	}
  }
}
