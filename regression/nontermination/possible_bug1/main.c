int main(void)
{
	int i, counter = 1;
	for (i=1; i< 10;)
	{
		if (counter % 3 == 0) i++;
		counter++;
	}
	while (i) i=i;

	return 0;
}
