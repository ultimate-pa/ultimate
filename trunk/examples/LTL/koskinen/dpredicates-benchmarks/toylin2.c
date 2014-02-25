// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: toylin2.c
// Property: c > servers / 2 => F(resp > servers / 2)

unsigned int c;
int servers ;
int resp;
int curr_serv;
int serversdiv2;

void init() {
  c = nondet(); assume(c>0);
  servers = nondet(); assume(servers>0);
  serversdiv2 = nondet();
  if(nondet())
    assume(serversdiv2+serversdiv2==servers);
  else
    assume(serversdiv2+serversdiv2+1==servers);
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
