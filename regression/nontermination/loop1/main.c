int main(void)
{
	int i;
	while(1) { 
		if (i++) break;
		if (--i) break;
		while(1) { 
			if (i) break;
			if (i) break;
		}
	}
	
	return 0;
}
