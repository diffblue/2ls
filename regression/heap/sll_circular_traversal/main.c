// This example is taken from the SV-COMP benchmarks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/blob/main/c/list-ext3-properties/sll_circular_traversal-1.c
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

extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
/*
 * SLL circular traversal example:
 * Build circular sll (1-1-1-1-1).
 * Check and overwrite data to (1-2-3-4-5).
 * Directly continue the traversal, check data and deallocate.
 */
#include <stdlib.h>

typedef struct node {
  struct node* next;
  int data;
} *SLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

SLL sll_circular_create(int len, int data) {
  SLL const last = (SLL) malloc(sizeof(struct node));
  if(NULL == last){
    myexit(1);
  }
  last->next = last;
  last->data = data;
  SLL head = last;
  while(len > 1) {
    SLL new_head = (SLL) malloc(sizeof(struct node));
    if(NULL == new_head){
      myexit(1);
    }
    new_head->next = head;
    new_head->data = data;
    head = new_head;
    len--;
  }
  last->next = head;
  return head;
}

int main() {
  const int len = 5;
  const int data_init = 1;
  SLL const head = sll_circular_create(len, data_init);
  /* first traversal */
  int data_new = 1;
  SLL ptr = head;
  do {
    if(data_init != ptr->data) {
      goto ERROR;
    }
    ptr->data = data_new;
    ptr = ptr->next;
    data_new++;
  } while(ptr != head);
  /* second traversal */
  data_new = data_new - len;
  do {
    if(data_new != ptr->data) {
      goto ERROR;
    }
    SLL temp = ptr->next;
    if (ptr != head) {
        free(ptr);
    }
    ptr = temp;
    data_new++;
  } while(ptr != head);
  free(head);
  return 0;
 ERROR: {reach_error();abort();}
  return 1;
}

