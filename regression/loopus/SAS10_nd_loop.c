int random();

int nd_loop(){
  int x,y;

  x=0;

  do {
    y=x;
    x=random();

    if ((x-y>2) || (x-y<1)) break;
  }
  while(x<10);

  return 0;
}
