// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2011-2020 The SV-Benchmarks Community
//
// SPDX-License-Identifier: Apache-2.0

extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();

  while (x > 0) {
    y = 0;
    while (y < x) {
        y = y + 1;
    }
    x = x - 1;
  }
}
