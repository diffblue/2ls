#include <stdlib.h>

typedef struct ListReverse {
	int data;
	struct ListReverse *next;
} ListReverse;

void del(ListReverse *l, int p, int a[], int la, int b[], int lb) {
	while (l != (ListReverse *)NULL) {
		if (l->data < p) {
			//			la = rm_vec(l->data, a, la);  //la=la-1;
			int i = 0;
			while (i < la && a[i] < l->data) {
				i++;
			}
			for (int j = i; j < la-1; j++)
				a[j] = a[j+1];
			la = la -1;
		}
		else {
			//			lb = rm_vec(l->data, b, lb);  //lb=lb-1;
			int i = 0;
			while (i < la && a[i] < l->data) {
				i++;
			}
			for (int j = i; j < la-1; j++)
				a[j] = a[j+1];
			lb = lb - 1;
		}
		l = l->next;
	}
}

//int rm_vec(int e, int a[], int la) {
//	int i = 0;
//	while (i < la && a[i] < e) {
//		i++;
//	}
//	for (int j = i; j < la-1; j++)
//		a[j] = a[j+1];
//	return la-1;
//}

//void del(ListReverse *l, int p, int a[], int la, int b[], int lb) {
//	while (l != (ListReverse *)NULL) {
//		if (l->data < p)
//			la = rm_vec(l->data, a, la);  //la=la-1;
//		else
//			lb = rm_vec(l->data, b, lb);  //lb=lb-1;
//		l = l->next;
//	}
//}


/*
split[l,p,a,la,b,lb] ==   1 +  loop1[l,la,lb],

   size: l>=0,la>=0,lb>=0


loop1[l,la,lb] ==   2,

   size: l=0

loop1[l,la,lb] ==   23 +  loop2[lb,0] + loop1[l',la,lb'],

   size: lb>= -1 , lb-1 <= lb' <= lb , l-l'>=1 , l'>=0

loop1[l,la,lb] ==   27 +  loop3[lb,j] + loop2[lb,0] + loop1[l',la,lb'],

   size: lb >= j ,  j>=0   , lb-1 <= lb' <= lb , l-l'>=1 , l'>=0

loop1[l,la,lb] ==   24 +  loop2[la,0] + loop1[l',la',lb],

   size: la>= -1 , la-1 <= la' <= la  , l-l'>=1 , l'>=0

loop1[l,la,lb] ==   28 +  loop3[la,j] + loop2[la,0] + loop1[l',la',lb],

   size: la-1 <= la' <= la , la >=j , j>=0  , l-l'>=1 , l'>=0


-------------------------------------------------
loop2[la,i] ==   3,
    size: i>=la , i>=0 ,

loop2[la,i] ==   8,
    size: i<la , i>=0 ,

loop2[la,i] ==   10 + loop2[la,i'],

    size: i < la , i>=0 , i'= i+1

--------------------------------------------------
loop3[la,j] ==   5,

    size: j>= la-1 , j>=0

loop3[la,j] ==   15 + m2[la,j'],

    size: j < la-1, j>=0 , j'=j+1

 */
