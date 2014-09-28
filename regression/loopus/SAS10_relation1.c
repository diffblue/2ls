int random();

int relation1(){
  int x,y;

  x=0;

  do {
    x=random();
    y=x;

    if ((x-y>2) || (x-y<1)) break;
  }
  while(x<10);

  return 0;
}
