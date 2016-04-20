void main()                                                                                                                                                                                                        
{                                                                                                                                                                                                                  
  int x = 1, y = -1, z = 1;                                                                                                                                                                                        
                                                                                                                                                                                                                   
  while(1)                                                                                                                                                                                                         
  {                                                                                                                                                                                                                
    z = y;                                                                                                                                                                                                         
    y = x;                                                                                                                                                                                                         
    x = -x;                                                                                                                                                                                                        
    if(x!=z) break;                                                                                                                                                                                                
  }                                                                                                                                                                                                                
  assert(0);                                                                                                                                                                                                       
}        


