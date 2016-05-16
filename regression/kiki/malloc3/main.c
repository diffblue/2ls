void main()
{
/*  unsigned x = 5;
  int y, z = 3, w;
  if(!y)
  {
    z += y;
    w = x;
  }
  else
  {
    z -= y;
    w = x;
    }*/
  float *f;
  
  for(int z=0;z<1;z++)
  {
    //assert(w==5);
    f = malloc(5*sizeof(float));//malloc(w*sizeof(float));
    //f[1] = 2.0;
    f[2] = 1.0;
    //   assert(f[1]==2.0);
//    assert(f[2]==0.9);
  }
//  assert(f[1]==2.0);
  assert(f[2]==0.9);
}
