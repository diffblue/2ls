void main()                                                                                                                                                                                                        
{                                                                                                                                                                                                                  
  int x = 1, y = -1, z = 1;                                                                                                                                                                                        
                                                                                                                                                                                                                   
  while(x==z)                                                                                                                                                                                                      
  {                                                                                                                                                                                                                
    z = y;                                                                                                                                                                                                         
    y = x;                                                                                                                                                                                                         
    x = -x;                                                                                                                                                                                                        
  }                                                                                                                                                                                                                
  assert(0);                                                                                                                                                                                                       
}      
