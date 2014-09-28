int random();

int rsd (int r)
{
  int da,db,temp;

  if (r>=0){
    da = 2*r;
    db = 2*r;
    while (da >=r) {
      if (random()){
	da --;
      }
      else{
	temp = da;
	da = db - 1;
	db = da;
      }
    }
  }

  return 0;

  
}
