// This example is taken from the SV-COMP benchmarks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/blob/main/c/array-examples/standard_copy1_ground-1.c
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

#define N 1000000

int main( ) {
  int a1[N];
  int a2[N];

  int i;
  for ( i = 0 ; i < N ; i++ ) {
    a1[i] = __VERIFIER_nondet_int();
  }

  for ( i = 0; i < N; i++ ) {
      a2[i] = a1[i];
  }

  int x;
  for ( x = 0 ; x < N ; x++ ) {
    __VERIFIER_assert(  a1[x] == a2[x]  );
  }
  return 0;
}

