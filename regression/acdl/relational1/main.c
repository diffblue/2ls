int get_random_1to10()
{
        int result;
        __CPROVER_assume(result>=1 && result <= 10);
        return result;
}

int main()
{
  int x = get_random_1to10();
  int y = 10 - x;
  assert(x+y <= 10);
} 
