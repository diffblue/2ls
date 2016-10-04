int main(int argc, char** argv)
{
  float x=15.0f;

  while(x>=0) //doesn't terminate
  {
    x -= 0.15f;
    if(0>x && x>-0.15f) 
    {
      x = 15.0f;
    }
  }
}
