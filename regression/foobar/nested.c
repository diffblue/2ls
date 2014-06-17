void main()
{
  

  int x=0, y=0;
  while(x<10)
    {
      if(x>=5)
	{
	  while(y<10)
	    {
	      if(y>0) y++; else  y--;
	      //  __CPROVER_assume(y<100); 
	    }
	}
      x++;
      __CPROVER_assume(x<200);
    }
  x=x+y;
  __CPROVER_assume(x<300);


}


/*


(E) $guard#14 == TRUE

x#15 == 0
y#17 == 0

*** 18 file ../regression/foobar/nested.c line 4 function main
(E) x#phi18 == ($guard#ls26 ? x#lb26 : x#15)
(E) y#phi18 == ($guard#ls26 ? y#lb26 : y#17)
(E) $cond#18 == !(x#phi18 < 10)
(E) $guard#18 == ($guard#14 || $guard#ls26)

*** 19 file ../regression/foobar/nested.c line 6 function main
(E) $cond#19 == !(x#phi18 >= 5)
(E) $guard#19 == (!$cond#18 && $guard#18)

*** 20 file ../regression/foobar/nested.c line 8 function main
(E) y#phi20 == ($guard#ls23 ? y#lb23 : y#phi18)
(E) $cond#20 == !(y#phi20 < 10)
(E) $guard#20 == (!$cond#19 && $guard#19 || $guard#ls23)

*** 21 file ../regression/foobar/nested.c line 10 function main
(E) y#21 == 1 + y#phi20
(E) $guard#21 == (!$cond#20 && $guard#20)

$cond#22 == y#21 < 100

*** 23 file ../regression/foobar/nested.c line 8 function main
(E) $cond#23 == TRUE
(E) $guard#23 == ($cond#22 && $guard#21)

*** 24 file ../regression/foobar/nested.c line 14 function main
(E) y#phi24 == ($cond#20 && $guard#20 ? y#phi20 : y#phi18)
(E) x#24 == 1 + x#phi18
(E) $guard#24 == ($cond#19 && $guard#19 || $cond#20 && $guard#20)

*** 25 file ../regression/foobar/nested.c line 15 function main
(E) $cond#25 == x#24 < 200

*** 26 file ../regression/foobar/nested.c line 4 function main
(E) $cond#26 == TRUE
(E) $guard#26 == ($cond#25 && $guard#24)

*** 27 file ../regression/foobar/nested.c line 17 function main
(E) x#27 == x#phi18 + y#phi18
(E) $guard#27 == ($cond#18 && $guard#18)

*** 28 file ../regression/foobar/nested.c line 18 function main
(E) $cond#28 == x#27 < 300

*** 29 file ../regression/foobar/nested.c line 19 function main
(E) $guard#29 == ($cond#28 && $guard#27)


 */
