int id(int a)
{
  return a;
}

void main() {
 int x,y,z;
 _Bool c;
 if (c)
   x = -1;
 else
   x = 2;
 int k = id(x);
 z = x * k;
 assert((z==-2));
}
