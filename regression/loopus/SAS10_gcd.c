void gcd(int x, int y){
  if(x<=0) return;
  if(y<=0) return;
  while(x != y && x >= 1 && y >= 1)
    if(x<y) y = y-x;
    else x = x-y;
}
