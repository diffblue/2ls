#include <float.h>
int main(int argc, char** argv)
{
  float x;
   __CPROVER_assume(-FLT_MAX<=x && x<=FLT_MAX);  
  while(x>0.0f)
  {
    x *= 0.1f; //terminates
    //x *= 0.8f; //does not terminate
  }
  return 0;
}
