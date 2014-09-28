int ax(int i, int j, int n) {
    i=0;
    do {
      j=0;
      while(j<n-1) ++j;
      ++i;
    }
    while(j>=n-1 && i<n-1);

  return 0;
}
