void main()
{
  int x,y;
  for(x=0;x<10;)
  {
    for(y=0;y<x;y++); 
    //*
    if(x==0) x=5;
    else if(x==5) x=3;
    else if(x==3) x=6;
    else if(x==6) x=2;
    else if(x==2) x=8;
    else x=10;
  }

  assert(x==10);
  assert(y==8);
}

