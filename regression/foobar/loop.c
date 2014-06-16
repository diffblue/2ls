int doit(int x)
{
  //__CPROVER_assume(x>=5);
  
  if(x>=5)
  {
    int z = 0;
    while(z<=10)
    {
      z = z + x;
    }
    z=z+1;
    
    
    return z;
  }
}

/*
(E) $cond#3 == x >= 5
(E) $guard#3 == TRUE
(E) $guard#4 == ($guard#3 && $cond#3)
(E) z#5 == 0
(E) z#phi6 == ($guard#ls8 ? z#7 : z#5)
(E) $cond#6 == !(z#phi6 <= 10)
(E) $guard#6 == ($guard#ls7 || $guard#4 && TRUE)
(E) z#7 == z#phi6 + x
(E) $guard#7 == ($guard#6 && !$cond#6)
(E) $cond#8 == TRUE
(E) z#9 == z#phi6 + 1
(E) $guard#9 == ($guard#6 && $cond#6 || $guard#ls7)
*/
/*
function to be analyzed: 
(E) $cond#3 == x >= 5
(E) $guard#3 == TRUE
(E) $guard#4 == ($guard#3 && $cond#3)
(E) z#5 == 0
(E) z#phi6 == ($guard#ls8 ? z#7 : z#5)
(E) $cond#6 == !(z#phi6 <= 10)
(E) $guard#6 == ($guard#ls7 || $guard#4 && TRUE)
(E) z#7 == z#phi6 + x
(E) $guard#7 == ($guard#6 && !$cond#6)
(E) $cond#8 == TRUE
(E) $guard#9 == ($guard#6 && $cond#6 || $guard#ls7)
*/
