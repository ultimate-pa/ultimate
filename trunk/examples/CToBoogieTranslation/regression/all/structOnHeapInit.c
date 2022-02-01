/*
 * author: nutz, 17.04.2014
 * taken from s3_clnt.balst.01_false.i.cil.c (svcomp 2014 benchmarks)
 */
int main() {

}

struct ssl_method_st {
   int version ;
};

typedef struct ssl_method_st SSL_METHOD;

static SSL_METHOD SSLv3_client_data  ;

SSL_METHOD *SSLv3_client_method(void) 
{ 
  return (& SSLv3_client_data);
}

