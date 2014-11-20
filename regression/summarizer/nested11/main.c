void main()
{
  int x,y;
  for(x=0;x<10;)
  {
    for(y=0;y<x;y++); 
    //*
    if(x==0) x=5;
    else if(x==5) x=3;
    else if(x==3) x=6;
    else if(x==6) x=2;
    else if(x==2) x=8;
    else x=10;
  }

  assert(x==10);
  assert(y==8);
}

/*
         
 x  y    
 0  0
 5  5
 3  3
 6  6
 2  2
 8  8
--
10  8


($guard#20 && $guard#ls22 ==> y#lb22 <= 9) && 
($guard#20 && $guard#ls22 ==> -((signed int)y#lb22) <= -1) && 

($guard#18 && $guard#ls39 ==> x#lb39 <= 10) && 
($guard#18 && $guard#ls39 ==> -((signed int)x#lb39) <= -2) && 
($guard#18 && $guard#ls39 ==> y#lb39 <= 9) && 
($guard#18 && $guard#ls39 ==> -((signed int)y#lb39) <= 0)




($guard#20%0%1 && $guard#ls22%0%1 ==> y#lb22%0%1 <= 8) && 
($guard#20%0%1 && $guard#ls22%0%1 ==> -((signed int)y#lb22%0%1) <= -2) && 

($guard#20%1%1 && $guard#ls22%1%1 ==> y#lb22%1%1 <= 9) &&
($guard#20%1%1 && $guard#ls22%1%1 ==> -((signed int)y#lb22%1%1) <= -2) && 

($guard#18%1 && $guard#ls39%1 ==> x#lb39%1 <= 10) && 
($guard#18%1 && $guard#ls39%1 ==> -((signed int)x#lb39%1) <= -2) && 
($guard#18%1 && $guard#ls39%1 ==> y#lb39%1 <= 8) && 
($guard#18%1 && $guard#ls39%1 ==> -((signed int)y#lb39%1) <= -2)




($guard#20%0%2 && $guard#ls22%0%2 ==> y#lb22%0%2 <= 8) && 
($guard#20%0%2 && $guard#ls22%0%2 ==> -((signed int)y#lb22%0%2) <= -3) && 

($guard#20%1%2 && $guard#ls22%1%2 ==> y#lb22%1%2 <= 3) && 
($guard#20%1%2 && $guard#ls22%1%2 ==> -((signed int)y#lb22%1%2) <= -3) && 

($guard#20%2%2 && $guard#ls22%2%2 ==> y#lb22%2%2 <= 9) && 
($guard#20%2%2 && $guard#ls22%2%2 ==> -((signed int)y#lb22%2%2) <= -3) && 

($guard#18%2 && $guard#ls39%2 ==> x#lb39%2 <= 10) && 
($guard#18%2 && $guard#ls39%2 ==> -((signed int)x#lb39%2) <= -6) && 
($guard#18%2 && $guard#ls39%2 ==> y#lb39%2 <= 8) && 
($guard#18%2 && $guard#ls39%2 ==> -((signed int)y#lb39%2) <= -3)

*/

