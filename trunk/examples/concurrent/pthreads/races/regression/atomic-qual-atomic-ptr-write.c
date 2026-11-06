// #Safe

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2026 Levente Bajczi
//
// SPDX-License-Identifier: Apache-2.0

// _Atomic pointer: the pointer object is atomic, so writing p is race-free.
#include <pthread.h>

int v1, v2;
int * _Atomic p;

void *thr(void *arg) {
  (void)arg;
  p = &v1; // NORACE
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  p = &v2; // NORACE
  pthread_join(id, 0);
  return 0;
}
