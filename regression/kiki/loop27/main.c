void main()                                                                                                                                                                                                        
{                                                                                                                                                                                                                  
  int x = 1, y = -1, z = 1;                                                                                                                                                                                        
                                                                                                                                                                                                                   
  do                                                                                                                                                                                                               
  {                                                                                                                                                                                                                
    z = y;                                                                                                                                                                                                         
    y = x;                                                                                                                                                                                                         
    x = -x;                                                                                                                                                                                                        
  }                                                                                                                                                                                                                
  while(x==z);                                                                                                                                                                                                     
  assert(0);                                                                                                                                                                                                       
}        
