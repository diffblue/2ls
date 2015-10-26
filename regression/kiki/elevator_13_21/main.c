#include <assert.h>

int floorButtons_0  ;
int floorButtons_1  ;
int floorButtons_2  ;
int floorButtons_3  ;
int floorButtons_4  ;
int currentFloorID  =    1;

void main()
{
  int retValue_acc ;
  int i___0 ;
  assert(floorButtons_0==0);
  assert(floorButtons_1==0);
  assert(floorButtons_2==0);
  assert(floorButtons_3==0);
  assert(floorButtons_4==0);
  i___0 = 0;
  i___0 = currentFloorID - 1;
  while (1) {
    if (i___0 >= 0) {
    } else {
      break;
    }
    i___0 = currentFloorID + 1;
    {
      while (1) {
	if (i___0 < 5) {
	} else {
	  break;
	}
	if (i___0 == 0) {
	  if (floorButtons_0) {
	    retValue_acc = 1;
	    return (retValue_acc);
	  } else {
	    goto _L___6;
	  }
	} else {
	_L___6:  
	  if (i___0 == 1) {
	    if (floorButtons_1) {
	      retValue_acc = 1;
	      break; //return (retValue_acc);
	    } else {
	      goto _L___5;
	    }
	  } else {
	  _L___5: 
	    if (i___0 == 2) {
	      if (floorButtons_2) {
		retValue_acc = 1;
		break; //return (retValue_acc);
	      } else {
		goto _L___4;
	      }
	    } else {
	    _L___4: 
	      if (i___0 == 3) {
		if (floorButtons_3) {
		  retValue_acc = 1;
		  break; //return (retValue_acc);
		} else {
		  goto _L___3;
		}
	      } else {
	      _L___3: 
		if (i___0 == 4) {
		  if (floorButtons_4) {
		    retValue_acc = 1;
		    break; //return (retValue_acc);
		  }
		}
	      }
	    }
	  }
	}
	i___0 = i___0 + 1;
      }
    }
    i___0 = i___0 - 1;
  }
  assert(retValue_acc==1);
}
