void realbubble(int *array, int length)
{
  int i, j, temp;
  int test; /*use this only if unsure whether the list is already sorted or not*/

  for(i = length - 1; i > 0; i--)
  {
    test=0;
    for(j = 0; j < i; j++)
    {
      if(array[j] > array[j+1]) /* compare neighboring elements */
      {
        temp = array[j];    /* swap array[j] and array[j+1] */
        array[j] = array[j+1];
        array[j+1] = temp;
        test=1;
      }
    } /*end for j*/
    if(test==0) break; /*will exit if the list is sorted!*/
  } /*end for i*/
      
}/*end bubbleSort*/
