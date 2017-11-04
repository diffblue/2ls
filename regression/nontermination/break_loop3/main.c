#include <stdio.h>
int main(void) {
	int i___0;
	int d = 0;
	int currentFloorID = 3;
	int floorButtons_0;
	int floorButtons_1;
	int floorButtons_2;
	int floorButtons_3;
	int floorButtons_4 = 0;
	int retValue_acc;
	if (d == 0) {
      i___0 = 0;
      i___0 = currentFloorID - 1;
      {
      while (1) {
		currentFloorID=currentFloorID;
		floorButtons_4=floorButtons_4;
        while_6_continue: /* CIL Label */ ;
        if (i___0 >= 0) {

        } else {
          goto while_6_break;
        }
        i___0 = currentFloorID + 1;
        {
        while (1) {
          while_7_continue: /* CIL Label */ ;
          if (i___0 < 5) {

          } else {
            goto while_7_break;
          }
          if (i___0 == 0) {
            if (floorButtons_0) {
              retValue_acc = 1;
              return (retValue_acc);
            } else {
              goto _L___6;
            }
          } else {
            _L___6: /* CIL Label */ 
            if (i___0 == 1) {
              if (floorButtons_1) {
                retValue_acc = 1;
                return (retValue_acc);
              } else {
                goto _L___5;
              }
            } else {
              _L___5: /* CIL Label */ 
              if (i___0 == 2) {
                if (floorButtons_2) {
                  retValue_acc = 1;
                  return (retValue_acc);
                } else {
                  goto _L___4;
                }
              } else {
                _L___4: /* CIL Label */ 
                if (i___0 == 3) {
                  if (floorButtons_3) {
                    retValue_acc = 1;
                    return (retValue_acc);
                  } else {
                    goto _L___3;
                  }
                } else {
                  _L___3: /* CIL Label */ 
                  if (i___0 == 4) {
                    if (floorButtons_4) {
                      retValue_acc = 1;
                      return (retValue_acc);
                    } else {

                    }
                  } else {

                  }
                }
              }
            }
          }
          i___0 = i___0 + 1;
          printf("%d %d %d %d %d %d %d %d %d\n", i___0,
                                           d,
                                           currentFloorID,
                                           floorButtons_0,
                                           floorButtons_1,
                                           floorButtons_2,
                                           floorButtons_3,
                                           floorButtons_4,
                                           retValue_acc);
        }
        while_7_break: /* CIL Label */ ;
        }
        i___0 = i___0 - 1;
      }
      while_6_break: /* CIL Label */ ;
      }
    } else {

    }
    return 0;
}
