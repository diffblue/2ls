#include <assert.h>

int main()
{
	int i = 4;
	int j = 4;
 	while (i > 1) {
		if (i > 2)
			i--;
		j--;
	}
	return i;
}
