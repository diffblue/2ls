signed long int full_write(signed int fd, const void *buf, unsigned long int len, signed long int cc)
{
  signed long int total = (signed long int)0;
  for( ; !(len <= 0ul); len = len - (unsigned long int)cc)
  {
    if(cc < 0l)
    {
      if(!(total == 0l))
        return total;
      return cc;
    }
    total = total + cc;
    buf = (const void *)((const char *)buf + cc);
  }
}

void main()
{
  signed int fd; 
  char buf[256];
  unsigned long int len; 
  signed long int cc;
  full_write(fd,buf,len,cc);
}
