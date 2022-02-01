/*
 * author: nutz, 17.04.2014
 * taken from s3_clnt.balst.01_false.i.cil.c (svcomp 2014 benchmarks)
 */
int main() {

}

struct ssl_st {
   int (*handshake_func)() ;
};
typedef struct ssl_st SSL;
int ssl3_connect(SSL *s ) 
{
	s->handshake_func = (int (*)())(& ssl3_connect);
}
