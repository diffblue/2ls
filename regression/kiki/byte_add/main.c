unsigned int mp_add(unsigned int a, unsigned int b)
{
    unsigned char r0, r1;
    unsigned int r;
    unsigned char i = 0;
    unsigned char na=1, nb=1;

    while ((i < na) || (i < nb)) {
      i = 2;
      r0 = 255;
      r1 = 1;
    }

/*    if(1) {
      i = i; r0 = r0; r1 = r1;
      }
*/
    
    while (i < (unsigned char)2) {
      if (i == (unsigned char)0) { r0 = (unsigned char)0; }
      if (i == (unsigned char)1) { r1 = (unsigned char)0; }
      i = i + (unsigned char)1;
    }

    r = r0 | (r1 << 8U);

    return r;
}


int main()
{
    unsigned int a = 176, b = 79, r, e;
    e = a + b;

    r = mp_add(a, b);

    assert(r == e);

    return 0;
}
