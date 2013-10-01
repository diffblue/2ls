int z;

void f(unsigned l, int x, int y)
{
	while (l) {
                l--;
		x++;
		y++;
	}

	assert(x == y);
}

