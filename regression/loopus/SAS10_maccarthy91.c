void sipma91(int x, int z){
  int y1, y2;

  y1 = x;
  y2 = 1;

  if(y1 > 100) z = y1 - 10;
  else {
    while(y1 <= 100){
      y1 = y1 + 11;
      y2 = y2 + 1;
    }

    while(y2 > 1){
      y1 = y1 - 10;
      y2 = y2 - 1;
      if(y1 > 100 && y2 == 1) z = y1 - 10;
      else {
	if(y1 > 100){
          y1 = y1 - 10;
          y2 = y2 - 1;
        }
        y1 = y1 + 11;
        y2 = y2 + 1;
      }
    }
  }
}
