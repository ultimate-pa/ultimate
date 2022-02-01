
void findPublicKey(int handle , int userid ) 
{  

  if (handle    ) ; else ;

}

void outgoing(      ) ;
void sendEmail(      ) ;

void test( ) ;

void bobToRjh( ) 
{  

  sendEmail(0, 0);
  outgoing(0, 0);

}

void main( ) 
{  

    test();

}


void setEmailTo(      ) ;

void incoming(      ) ;

void autoRespond(      ) ;
 
void verify(      ) ;

void mail(int client , int msg ) 
{  
  int tmp ;

  tmp = getEmailTo(0);
  incoming(tmp, 0);

}
void outgoing__wrappee__AutoResponder(int client , int msg ) 
{  

  mail(0, 0);

}
void outgoing(int client , int msg ) 
{ 

  outgoing__wrappee__AutoResponder(0, 0);

}

void incoming__wrappee__Sign(int client , int msg ) 
{  

    autoRespond(0, 0);

}
void incoming(int client , int msg ) 
{ 

  verify(client, 0);
  incoming__wrappee__Sign(0, 0);

}
 
void sendEmail(int sender , int receiver ) 
{  

  outgoing(0, 0);

}

void autoRespond(int client , int msg ) 
{  

  setEmailTo(0, 0);

}
 
void __utac_acc__SignVerify_spec__2(      ) ;
void verify(int client , int msg ) 
{ int __utac__ad__arg1 ;

  __utac__ad__arg1 = client;
   
  __utac_acc__SignVerify_spec__2(__utac__ad__arg1, 0);

}

int __ste_email_to0   ;
 
int getEmailTo(int handle ) 
{ int retValue_acc ;

    retValue_acc = __ste_email_to0;
    return  retValue_acc ;

}
void setEmailTo(int handle , int value ) 
{ 

    __ste_email_to0 = 1;

}

void __utac_acc__SignVerify_spec__2(int client , int msg ) 
{ int pubkey ;

        findPublicKey(client, 0);

    if (pubkey    ) {
       
     __VERIFIER_error();
       
    } else ;

}
 
void test( ) 
{  

  bobToRjh();

}