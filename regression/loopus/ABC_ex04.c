void ex04(int n) {
  for (int i = 0; i <= (n*n*n/2) - 1; i = i + 1)
    for (int j = 0; j <= n - 1; j = j + 1)
      for (int k = 0; k <= j - 1; k = k + 1)
        ;
} 
