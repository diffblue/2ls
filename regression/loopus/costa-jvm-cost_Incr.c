int nondet();

int add(int n){
	int res=0;
	int i=0;
	while (i<=n){
		res=res+i;
		if (nondet())
			i = i + 1;
		else if (nondet())
			i = i + 2;
		else
			i = i + 3;
	}
	return res;
}
