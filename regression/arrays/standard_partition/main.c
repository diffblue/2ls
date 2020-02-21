// This example is taken from the SV-COMP benchmarks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/blob/main/c/array-examples/standard_partition_ground-1.c
//
// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
// 
//   http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

#define N 100

int main( ) {
  int aa[N];
  int a = 0;
  int b = 0;
  int c = 0;
  int bb[N];
  int cc[N];

  for(int i = 0; i < N; i++) {
    aa[i] = __VERIFIER_nondet_int();
  }

  while( a < N ) {
    if( aa[ a ] >= 0 ) {
      bb[ b ] = aa[ a ];
      b = b + 1;
    }
    else {
      cc[ c ] = aa[ a ];
      c = c + 1;
    }
    a = a + 1;
  }

  // This is neccessary since 2LS is not able to infer it
  __CPROVER_assume(b < N);
  __CPROVER_assume(c < N);

  int x;
  for ( x = 0 ; x < b ; x++ ) {
    __VERIFIER_assert(  bb[ x ] >= 0  );
  }

  for ( x = 0 ; x < c ; x++ ) {
    __VERIFIER_assert(  cc[ x ] < 0  );
  }
  return 0;
}


