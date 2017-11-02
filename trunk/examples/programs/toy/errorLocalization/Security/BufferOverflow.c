#include <stdlib.h>
#include <stdio.h>


void __VERIFIER_error();

int get_passkey(void);


int main(void)
{
    int passkey;
    int correctPass = 0;
    int wrongPass = 0;

    printf("\n Enter the password : \n");
    passkey = get_passkey();
    //passkey = get_passkey();

    if(passkey == 1234)
    {
        // correcct password
        printf("\n Correct password \n");
        correctPass = 1;
    }
    else
    {
        // wrong password
        printf("\n Wrong password \n");
        wrongPass = 1;
    }

    if(correctPass)
    {
       /* Now Give root or admin rights to user*/
        printf ("\n Root privileges given to the user \n");
        if(wrongPass){
            __VERIFIER_error();
        }
    }
    return 0;
}
