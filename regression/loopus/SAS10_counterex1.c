int random();

void counterex1b(int n, int x, int y)
{
  while(x>=0){
    while(y>=0 && random()) y--;
    x--;
    while(y<=n && random()) y++;
  }
}
