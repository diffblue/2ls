#include <assert.h>

int main()
{
	int i = 5;
	int j = 4;
 	while (i > 1) {
		if (i > 2)
			i--;
		if (j > 2)
			j--;
	}
	return i;
}
