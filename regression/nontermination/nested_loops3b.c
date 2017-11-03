int main (void)
{
	int i = 4, j = 4, k = 4;
	while (j < 10) 
			{
				while (k < 10)
				{
					//i = ((i % 2) == 0) ? i + 1 : i - 1;
					//j = ((j % 2) == 0) ? j + 1 : j - 1;
					if (!i) break;
					i >>= 1;
					j >>= 1;
				}
			}
	
	return 0;
}
