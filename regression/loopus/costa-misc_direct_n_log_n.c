
void direct_n_log_n(int a, int b) {
  if (a >= 1 || a >= 2 || a >= 4) {
      while (a >= 2) {
        a = 1/2 * a;
      }
  }
  else
      return;
}
