int main (void)
{
	int i = 0, j = 0, k = 0;
	while (i < 10)
	{
		while (j < 10)
		{
			while (k < 10)
			{
				k = j - i;
			}
			j++;
		}
		i++;
	}
	
	return 0;
}
