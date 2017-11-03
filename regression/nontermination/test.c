int main (void)
{
	int i = 4, j = 4, k;
	__CPROVER_assume(3<=k && k<=4);
	while (j < 10) 
			{
				do
				{
					//i = ((i % 2) == 0) ? i + 1 : i - 1;
					//j = ((j % 2) == 0) ? j + 1 : j - 1;
					i >>= 1;
					j >>= 1;
				} while ((k < 10));
			}
	
	return 0;
}
