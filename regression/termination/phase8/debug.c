void main() {
  /* __CPROVER_bitvector[32] yphi21, ylb30, y18, uphi21, ulb30, u20, xlb30, xphi27, y29, uphi29, u28; */
  /* __CPROVER_bool guardls30, guard23, cond22, guard22, guard24, guard23, cond23, guard26, cond27;  */
  /* __CPROVER_bool guard21,  guard29, cond30; */
  /* __CPROVER_bool cond25; */
  /* __CPROVER_bool guard27, guard28; */

  /* __CPROVER_assume(yphi21 == (guardls30 ? ylb30 : y18)); */
  /* __CPROVER_assume(uphi21 == (guardls30 ? ulb30 : u20)); */

  /* __CPROVER_assume(cond22 == !(uphi21 < 2147483647)); */
  /* __CPROVER_assume(cond23 == !(yphi21 < 10)); */
  /* __CPROVER_assume(guard23 == (!cond22 && guard22)); */
  /* __CPROVER_assume(guard24 == (!cond23 && guard23)); */
  /* __CPROVER_assume(guard26 == (cond23 && guard23)); */
  /* __CPROVER_assume(cond27 == !(yphi21 == 2147483647)); */
  /* __CPROVER_assume(guard27 == (cond25 && guard24 || guard26)); */
  /* __CPROVER_assume(u28 == 1 + uphi21); */
  /* __CPROVER_assume(guard28 == (!cond27 && guard27)); */
  /* __CPROVER_assume(y29 == 1 + yphi21); */
  /* __CPROVER_assume(uphi29 == (cond27 && guard27 ? uphi21 : u28)); */
  /* __CPROVER_assume(guard29 == (cond27 && guard27 || guard28)); */
    
  //  assert(!(guard21 && guardls30 && guard29 && cond30 && (-(long)ylb30 <= -(long)y29 || -(long)ulb30 < -(long)uphi29) && -(long)ulb30 <= -(long)uphi29));
  //assert(!(guard21 && guardls30 && guard29 && cond30 && (-ylb30 <= -y29 || -ulb30 < -uphi29) && -ulb30 <= -uphi29));

  __CPROVER_bitvector[32] c0$1$0, c0$1$1, c0$1$2, c0$0$0, c0$0$1, c0$0$2; 

  /* assert(c0$1$0 * 4194304 + c0$1$1 * 2147483647 + c0$1$2 * -1656643584 > c0$1$0 * 4194303 + c0$1$1 * -2147483648 + c0$1$2 * -1656643583 || */
  /* 	 c0$0$0 * 4194304 + c0$0$1 * 2147483647 + c0$0$2 * -1656643584 > c0$0$0 * 4194303 + c0$0$1 * -2147483648 + c0$0$2 * -1656643583 && c0$1$0 * 4194304 + c0$1$1 * 2147483647 + c0$1$2 * -1656643584 >= c0$1$0 * 4194303 + c0$1$1 * -2147483648 + c0$1$2 * -1656643583); */

assert((signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$0 * (signed __CPROVER_bitvector[43])4194304) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$1 * (signed __CPROVER_bitvector[43])2147483647)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$1$2 * (signed __CPROVER_bitvector[43])-1656643584) > (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$0 * (signed __CPROVER_bitvector[43])4194303) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$1 * (signed __CPROVER_bitvector[43])-2147483648)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$1$2 * (signed __CPROVER_bitvector[43])-1656643583) || (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$0$0 * (signed __CPROVER_bitvector[43])4194304) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$0$1 * (signed __CPROVER_bitvector[43])2147483647)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$0$2 * (signed __CPROVER_bitvector[43])-1656643584) > (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$0$0 * (signed __CPROVER_bitvector[43])4194303) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$0$1 * (signed __CPROVER_bitvector[43])-2147483648)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$0$2 * (signed __CPROVER_bitvector[43])-1656643583) && (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$0 * (signed __CPROVER_bitvector[43])4194304) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$1 * (signed __CPROVER_bitvector[43])2147483647)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$1$2 * (signed __CPROVER_bitvector[43])-1656643584) >= (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$0 * (signed __CPROVER_bitvector[43])4194303) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])c0$1$1 * (signed __CPROVER_bitvector[43])-2147483648)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])c0$1$2 * (signed __CPROVER_bitvector[43])-1656643583));


  //assert((guard21 && guardls30 && guard21 && guardls30 && guard21 && guardls30 && guard29 && cond30 && guard29 && cond30 && guard29 && cond30 ==> (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xlb30) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])ylb30)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])ulb30) > (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xphi27) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])y29)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])uphi29) && (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xlb30) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])ylb30)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])ulb30) >= (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xlb30) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])y29)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])uphi29) || (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xlb30) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])ylb30)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])ulb30) > (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])xphi27) + (signed __CPROVER_bitvector[44])((signed __CPROVER_bitvector[43])0 * (signed __CPROVER_bitvector[43])y29)) + (signed __CPROVER_bitvector[45])((signed __CPROVER_bitvector[43])-1 * (signed __CPROVER_bitvector[43])uphi29)));

}
