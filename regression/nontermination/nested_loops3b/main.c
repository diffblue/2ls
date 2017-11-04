int main (void)
{
	int i = 4, j = 4, k = 4;
	while (j < 10) 
			{
				while (k < 10)
				{
					if (!i) break;
					i >>= 1;
					j >>= 1;
				}
			}
	
	return 0;
}
