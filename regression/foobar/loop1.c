//int y = 0;

void doit()
{
  int x = 0;  
  // y=1;

  while(x<10)
    ++x;
  
  // y++;
}

/*

x#phi16 == ($guard#ls19 ? x#lb19 : 0)
x#17 == 1 + x#phi16
$guard#17 == x#phi16 < 10

!$guard#ls19 || x#lb19 == 1

x#phi16' == ($guard#ls19' ? x#17 : 0)
x#17 == 1 + x#phi16'
$guard#17' == x#phi16' < 10

$guard#17' &&  x#17 != 1

====

x#phi16 == ($guard#ls19 ? 1 : 0)
x#17 == 1 + x#phi16
$guard#17 == x#phi16 < 10

x#17 == 1 || x#17 == 2

case 1: x#17 == 1
x#phi16' == ($guard#ls19' ? 1 : 0)
x#17 == 1 + x#phi16'
$guard#17' == x#phi16' < 10
$guard#17' &&  x#17 != 1
x#17 == 2
SAT

case 2: x#17 == 2
x#phi16' == ($guard#ls19' ? x#17 : 0)
x#17 == 1 + x#phi16'
$guard#17' == x#phi16' < 10
$guard#17' &&  x#17 != 1
x#17 == 3

====

x#phi16 == ($guard#ls19 ? x#lb19 : 0)
x#17 == 1 + x#phi16
$guard#17 == x#phi16 < 10

!$guard#ls19 || x#lb19 == 1

x#phi16 == 0 || x#phi16 == 1
x#17 == 1 || x#17 == 2

$guard#17 == true

$guard#17 &&  x#17 != 1
x#17 == 2

*/
