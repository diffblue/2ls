int nondet();

int aaron2(int tx, int x, int y) {
  if (tx>=0) {
    while (x>=y) {
      if (tx<0) return 0;
      if (nondet()) 
	{
	  x=x-1-tx;
	}
      else
	{
	  y=y+1+tx;
	}
    }
  }
  return 0;
}
