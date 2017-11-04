int main (void)
{
	int i = 0, j = 0, k = 0;
	while (i < 10)
	{
		while (j < 10)
		{
			while (k < 10)
			{
				i >>= 1;
				j >>= 1;
			}
		}
	}
	
	return 0;
}
