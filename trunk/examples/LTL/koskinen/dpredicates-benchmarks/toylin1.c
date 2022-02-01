// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: toylin1.c
// Property: c > 5 => F(resp > 5)

int c;
int servers ;
int resp;
int curr_serv;

void init() {
  c = nondet(); assume(c>0);
  servers = 4;
  resp = 0;
  curr_serv = servers;
}

int body() {
  while(curr_serv > 0) {
    if(nondet()) {
      c--; curr_serv--;
      resp++;
    } else {
      assume(c < curr_serv);
      curr_serv--;
    }
  }
  while(1) { int ddd; ddd=ddd; }
}

int main() {}

