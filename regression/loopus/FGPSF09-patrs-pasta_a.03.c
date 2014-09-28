int nondet();

void a(int a, int b, int c, int d) {
  if (a >= 2) {
    a = a - 1;
    while (b >= 2) {
      c = a;
      d = 2*a;
        while (1) {
          if (b >= d && b >= 1 + d) {
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b >= d && b >= 1 + d) {
            d = d + 1;
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b >= d && b >= 1 + d && d >= 1) {
            c = d;
            d = 2*d;
          }
          else if (b >= d && b >= 1 + d && d >= 1) {
            c = d + 1;
            d = 2*d + 2;
          }
          else if (b == d) {
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b == d && d >= 1) {
            c = d;
            d = 2*d;
          }
          else
            return;
        }
    }
  }
  else if (1 >= a) {
    b = b - 1;
    while (b >= 2) {
      c = a;
      d = 2*a;
        while (1) {
          if (b >= d && b >= 1 + d) {
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b >= d && b >= 1 + d) {
            d = d + 1;
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b >= d && b >= 1 + d && d >= 1) {
            c = d;
            d = 2*d;
          }
          else if (b >= d && b >= 1 + d && d >= 1) {
            c = d + 1;
            d = 2*d + 2;
          }
          else if (b == d) {
            if (a >= 2 && b >= 2 && a >= 1) {
              a = a - 1;
              break;
            }
            else if (a == 1 && b >= 2) {
              b = b - 1;
              break;
            }
            else
              return;
          }
          else if (b == d && d >= 1) {
            c = d;
            d = 2*d;
          }
          else
            return;
        }
    }
  }
  else
    return;
}
