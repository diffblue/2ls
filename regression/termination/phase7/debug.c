void main() {
  int guard21, guardls30, guard29, cond30;
  int ylb30, y29, y18, ulb30, uphi29;
  int cond25, guard22, u20;
  int yphi21, uphi21, cond22, cond23, guard23, guard24, guard26, cond27, guard27, guard28, u28;

  assert(yphi21 == (guardls30 ? ylb30 : y18));
  assert(uphi21 == (guardls30 ? ulb30 : u20));

  assert(cond22 == !(uphi21 < 2147483647));
  assert(cond23 == !(yphi21 < 10));
  assert(guard23 == (!cond22 && guard22));
  assert(guard24 == (!cond23 && guard23));
  assert(guard26 == (cond23 && guard23));
  assert(cond27 == !(yphi21 == 2147483647));
  assert(guard27 == (cond25 && guard24 || guard26));
  assert(u28 == 1 + uphi21);
  assert(guard28 == (!cond27 && guard27));
  assert(y29 == 1 + yphi21);
  assert(uphi29 == (cond27 && guard27 ? uphi21 : u28));
  assert(guard29 == (cond27 && guard27 || guard28));
    
  assert(guard21 && guardls30 && guard29 && cond30 && (-ylb30 <= -y29 || -ulb30 < -uphi29) && -ulb30 <= -uphi29);

}
