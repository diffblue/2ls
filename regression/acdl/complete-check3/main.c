int main() {
  int x, y, c;

  __CPROVER_assume(1 <= x && x <= 3);
  if(c) 
    x++;
  else
    x--;     
  assert(x<0);
}

