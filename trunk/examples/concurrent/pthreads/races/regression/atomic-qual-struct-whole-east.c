// #Safe

// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2026 Levente Bajczi
//
// SPDX-License-Identifier: Apache-2.0

// _Atomic right of a struct type specifier, assigned as a whole.
#include <pthread.h>

struct S { int f; };
struct S _Atomic s;
struct S other;

void *thr(void *arg) {
  (void)arg;
  s = other; // NORACE
  return 0;
}

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  s = other; // NORACE
  pthread_join(id, 0);
  return 0;
}
