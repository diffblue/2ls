struct S
{
  int a, b, c;
  int array[4];
};

int main()
{
  struct S s1, s2;

  // copy full struct  
  s1=s2;

  assert(s1.a==s2.a && s1.b==s2.b);
  assert(s1.array[0]==s2.array[0]);
  assert(s1.array[1]==s2.array[1]);
  assert(s1==s2);
}
