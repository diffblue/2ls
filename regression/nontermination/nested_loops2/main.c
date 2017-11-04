#include <stdio.h>

int main(void)
{   //few permutations - 4th is the same 3 times unwind to prove nontermination
    int i = 1, j = 2, k = 3;
    int counter = 1;
    while (1)
    {
	printf("%d %d %d\n", i, j, k);        
	if (counter % 2 ==0)
	{
		i = j + i;
        	j = i - j;
        	i = i - j;    
                counter--;
	}
	else
	{
		counter++;
	}
        //swap j and k
        j = j + k;
        k = j - k;
        j = j - k;
        //swap i and j 
    }
}
