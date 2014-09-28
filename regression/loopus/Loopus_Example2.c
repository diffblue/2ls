int nondet();

void Example2(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j) {
    c = 4;
    d = a;
    a = 0;
    b = 0;
      while (0 >= c || c >= 2) {
        e = j;
        j = nondet();
          if (0 >= b + 1 || b >= 1) {
            j = nondet();
            if (c == 0) {
              f = 0;
              j = nondet();
              if (e >= g + 1) {
                j = nondet();
                if (a == 1 && b == 0) {
                  j = nondet();
                  if (f == 0) {
                    i = 0;
                    h = 1;
                    j = nondet();
                    if (d + i >= 256) {
                      j = nondet();
                        return;
                    }
                    else if (255 >= d + i) {
                      j = nondet();
                      d = d + i;
                      a = 2;
                      b = h;
                      c = i;
                    }
                    else
                      return;
                  }
                  else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                    i = j;
                    j = nondet();
                    h = 1;
                    if (d + i >= 256) {
                      j = nondet();
                        return;
                    }
                    else if (255 >= d + i) {
                      j = nondet();
                      d = d + i;
                      a = 2;
                      b = h;
                      c = i;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
                else if (0 >= a || a >= 2 || 0 >= b + 1 || b >= 1) {
                  j = nondet();
                  h = b;
                  i = f;
                  if (d + i >= 256) {
                    j = nondet();
                      return;
                  }
                  else if (255 >= d + i) {
                    j = nondet();
                    d = d + i;
                    a = 2;
                    b = h;
                    c = i;
                  }
                  else
                    return;
                }
                else
                  return;
              }
              else if (g >= e) {
                j = nondet();
                if (g >= e + 1) {
                  j = nondet();
                  if (a == 2 && b == 0) {
                    j = nondet();
                    if (f == 0) {
                      i = 0;
                      h = 1;
                      j = nondet();
                      if (i >= d + 1) {
                        j = nondet();
                          return;
                      }
                      else if (d >= i) {
                        d = d - i;
                        b = h;
                        c = i;
                        j = nondet();
                        a = 1;
                      }
                      else
                        return;
                    }
                    else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                      i = j;
                      j = nondet();
                      h = 1;
                      if (i >= d + 1) {
                        j = nondet();
                          return;
                      }
                      else if (d >= i) {
                        d = d - i;
                        b = h;
                        c = i;
                        j = nondet();
                        a = 1;
                      }
                      else
                        return;
                    }
                    else
                      return;
                  }
                  else if (1 >= a || a >= 3 || 0 >= b + 1 || b >= 1) {
                    h = b;
                    j = nondet();
                    i = f;
                    if (i >= d + 1) {
                      j = nondet();
                        return;
                    }
                    else if (d >= i) {
                      d = d - i;
                      b = h;
                      c = i;
                      j = nondet();
                      a = 1;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
                else if (e >= g) {
                  j = nondet();
                    return;
                }
                else
                  return;
              }
              else
                return;
            }
            else if ((c >= 1 && c >= 2*j && 1 + 2*j >= c && j >= 0) || (0 >= c + 1 && 1 + c >= 2*j && 0 >= j && 2*j >= c)) {
              f = j;
              j = nondet();
              if (e >= g + 1) {
                j = nondet();
                if (a == 1 && b == 0) {
                  j = nondet();
                  if (f == 0) {
                    i = 0;
                    h = 1;
                    j = nondet();
                    if (d + i >= 256) {
                      j = nondet();
                        return;
                    }
                    else if (255 >= d + i) {
                      j = nondet();
                      d = d + i;
                      a = 2;
                      b = h;
                      c = i;
                    }
                    else
                      return;
                  }
                  else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                    i = j;
                    j = nondet();
                    h = 1;
                    if (d + i >= 256) {
                      j = nondet();
                        return;
                    }
                    else if (255 >= d + i) {
                      j = nondet();
                      d = d + i;
                      a = 2;
                      b = h;
                      c = i;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
                else if (0 >= a || a >= 2 || 0 >= b + 1 || b >= 1) {
                  j = nondet();
                  h = b;
                  i = f;
                  if (d + i >= 256) {
                    j = nondet();
                      return;
                  }
                  else if (255 >= d + i) {
                    j = nondet();
                    d = d + i;
                    a = 2;
                    b = h;
                    c = i;
                  }
                  else
                    return;
                }
                else
                  return;
              }
              else if (g >= e) {
                j = nondet();
                if (g >= e + 1) {
                  j = nondet();
                  if (a == 2 && b == 0) {
                    j = nondet();
                    if (f == 0) {
                      i = 0;
                      h = 1;
                      j = nondet();
                      if (i >= d + 1) {
                        j = nondet();
                          return;
                      }
                      else if (d >= i) {
                        d = d - i;
                        b = h;
                        c = i;
                        j = nondet();
                        a = 1;
                      }
                      else
                        return;
                    }
                    else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                      i = j;
                      j = nondet();
                      h = 1;
                      if (i >= d + 1) {
                        j = nondet();
                          return;
                      }
                      else if (d >= i) {
                        d = d - i;
                        b = h;
                        c = i;
                        j = nondet();
                        a = 1;
                      }
                      else
                        return;
                    }
                    else
                      return;
                  }
                  else if (1 >= a || a >= 3 || 0 >= b + 1 || b >= 1) {
                    h = b;
                    j = nondet();
                    i = f;
                    if (i >= d + 1) {
                      j = nondet();
                        return;
                    }
                    else if (d >= i) {
                      d = d - i;
                      b = h;
                      c = i;
                      j = nondet();
                      a = 1;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
                else if (e >= g) {
                  j = nondet();
                    return;
                }
                else
                  return;
              }
              else
                return;
            }
            else
              return;
          }
          else if (b == 0) {
            f = c;
            j = nondet();
            if (e >= g + 1) {
              j = nondet();
              if (a == 1 && b == 0) {
                j = nondet();
                if (f == 0) {
                  i = 0;
                  h = 1;
                  j = nondet();
                  if (d + i >= 256) {
                    j = nondet();
                      return;
                  }
                  else if (255 >= d + i) {
                    j = nondet();
                    d = d + i;
                    a = 2;
                    b = h;
                    c = i;
                  }
                  else
                    return;
                }
                else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                  i = j;
                  j = nondet();
                  h = 1;
                  if (d + i >= 256) {
                    j = nondet();
                      return;
                  }
                  else if (255 >= d + i) {
                    j = nondet();
                    d = d + i;
                    a = 2;
                    b = h;
                    c = i;
                  }
                  else
                    return;
                }
                else
                  return;
              }
              else if (0 >= a || a >= 2 || 0 >= b + 1 || b >= 1) {
                j = nondet();
                h = b;
                i = f;
                if (d + i >= 256) {
                  j = nondet();
                    return;
                }
                else if (255 >= d + i) {
                  j = nondet();
                  d = d + i;
                  a = 2;
                  b = h;
                  c = i;
                }
                else
                  return;
              }
              else
                return;
            }
            else if (g >= e) {
              j = nondet();
              if (g >= e + 1) {
                j = nondet();
                if (a == 2 && b == 0) {
                  j = nondet();
                  if (f == 0) {
                    i = 0;
                    h = 1;
                    j = nondet();
                    if (i >= d + 1) {
                      j = nondet();
                        return;
                    }
                    else if (d >= i) {
                      d = d - i;
                      b = h;
                      c = i;
                      j = nondet();
                      a = 1;
                    }
                    else
                      return;
                  }
                  else if ((f >= 2*j && 1 + 2*j >= f && j >= 0 && f >= 1) || (1 + f >= 2*j && 0 >= f + 1 && 0 >= j && 2*j >= f)) {
                    i = j;
                    j = nondet();
                    h = 1;
                    if (i >= d + 1) {
                      j = nondet();
                        return;
                    }
                    else if (d >= i) {
                      d = d - i;
                      b = h;
                      c = i;
                      j = nondet();
                      a = 1;
                    }
                    else
                      return;
                  }
                  else
                    return;
                }
                else if (1 >= a || a >= 3 || 0 >= b + 1 || b >= 1) {
                  h = b;
                  j = nondet();
                  i = f;
                  if (i >= d + 1) {
                    j = nondet();
                      return;
                  }
                  else if (d >= i) {
                    d = d - i;
                    b = h;
                    c = i;
                    j = nondet();
                    a = 1;
                  }
                  else
                    return;
                }
                else
                  return;
              }
              else if (e >= g) {
                j = nondet();
                  return;
              }
              else
                return;
            }
            else
              return;
          }
          else
            return;
      }
      j = nondet();
          return;
}
