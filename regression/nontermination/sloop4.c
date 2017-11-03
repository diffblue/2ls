#include <assert.h>

int main()
{
	int i = 2;
 	while (i > 1) i--;
	assert(i==0);
	return i;
}
