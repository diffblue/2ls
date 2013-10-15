struct outer
{
  struct inner
  {
    int x, y;
  } a;
  
  int b, c, d;
};

int main()
{
  struct outer my_s1;
  struct inner my_s2;
  
  my_s1.b=1;
  assert(my_s1.b==1);
  
  my_s1.b++;
  assert(my_s1.b==2);
  
  my_s2.x=10;
  my_s1.a=my_s2;
  assert(my_s1.a.x==10);
  
  assert(my_s1.a.y==my_s2.y);
}
