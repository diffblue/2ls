int f(int x) {
  return 2*x;
}

int g(int x) {
  int y = x;
  int state = 1, i, j;

  while(state!=0)
  {
    switch(state)
    {
      case 0: 
        i++;
        state = 1;
        break;
        case 1:
         j++;
         state = 2;
         break;
        case 2:
          i = i + j;
          x--;
          y++;
          if(x == 0) state = 0;
          else state = 1;
          break;
     }  
   }
  return y;
}

void main(void) {
  int x = 5; int result1, result2;
  if (x >= 0) {
    result1 = f(x);
    result2 = g(x);
    assert((result1 == result2));
  }
}
