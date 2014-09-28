void loops(int n){
  /* n > 0 */
  if (n > 0) {  //this was added by me (fabian), Aachener also added this
	int x, y;
	
	x = n;
	if(x >= 0)
	  while(x >= 0){
		y = 1;
		if(y < x)
		  while(y < x)
			y = 2*y;
		x = x - 1;
	  }
  }

}

