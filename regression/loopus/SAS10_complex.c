int complex(int a, int b)
{
  while(a < 30)
    {
      while(b < a)
	{ 
	  if(b > 5) 
	    b = b + 7; 
	  else
	    b = b + 2;
	  if(b >= 10 && b <= 12) 
	    a = a + 10;
	  else 
	    a = a + 1;
	}
      a = a + 2; 
      b = b - 10; 
    }
  return 1;
}
