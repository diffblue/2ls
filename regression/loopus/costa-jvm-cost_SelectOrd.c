

int selectOrd(int lv, int v[]) {
	//	class SelectOrd{
	//    static void selectOrd(int v[]){
	for (int i=0; i<lv-2; i++){
		int tmp=v[i];
		int loc=i;
		for (int j=i+1; j<lv-1; j++){
			if (v[j]<v[loc]) loc=j;
		}
		v[i]=v[loc];
		v[loc]=tmp;
	}

	//	class OrdInser{
	//    static void ordInser(int[] v){
//	for (int i=1; i<lv; i++){
//		int temp = v[i];
//		int j = i - 1;
//		while ((v[j] > temp) && (j >= 0) ){
//			v[j+1] = v[j];
//			j--;
//		}
//		v[j+1] = temp;
//	}
	return 1;
}
