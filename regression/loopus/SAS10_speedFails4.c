
int speedFails4(int x, int n, int b){
  int t;
  if(b>=1) t=1; else  t=-1;

  while(x<=n)
    {
      if(b>=1)
	{
	  x=x+t;
	}
      else 
	{
	  x=x-t;
	}
    }
  
  return 0;
}

//YESSSSSSSSSSSSSSSSSSSSSSSSsss
