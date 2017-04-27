

void __automaton_fail( ) ;

int sent_encrypted   ;
void __utac_acc__EncryptDecrypt_spec__1(int msg ) 
{  

  sent_encrypted = 1;

}
void __utac_acc__EncryptDecrypt_spec__2(int client , int msg ) 
{  

      __automaton_fail();

}

void incoming(      ) ;

void mail(int client , int msg ) 
{  

  __utac_acc__EncryptDecrypt_spec__1(0);

  incoming(0, 0);

}
void outgoing__wrappee__Keys(int client , int msg ) 
{  

  mail(0, 0);

}
void outgoing__wrappee__Encrypt(int client , int msg ) 
{  

  outgoing__wrappee__Keys(0, 0);

}
void outgoing__wrappee__AddressBook(int client , int msg ) 
{  

    outgoing__wrappee__Encrypt(0, 0);

}
void outgoing(int client , int msg ) 
{ 

  outgoing__wrappee__AddressBook(0, 0);

}

void incoming(int client , int msg ) 
{  

  __utac_acc__EncryptDecrypt_spec__2(0, 0);

}

void __automaton_fail( ) 
{ 

  ERROR: __VERIFIER_error();

}

void test( ) ;

void bobToRjh( ) 
{  

    outgoing(0, 0);

}

void main( ) 
{  

    test();

}

void test( ) 
{  

  int splverifierCounter ;

  splverifierCounter = 0;
   
  while (1) {
     
    if (splverifierCounter < 4) ; else {
      goto while_3_break;
    }
    splverifierCounter = splverifierCounter + 1;
     
  }
  while_3_break:    

  bobToRjh();

}