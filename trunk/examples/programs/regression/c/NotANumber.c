//#Safe
// FIXED : 16.9.2012 / ML
// Bug Reported by Markus via Skype:
// Not a numeral exception in SMT for int var = 'A'
//
//Date: 30. July 2012
//Author: Markus Lindenmann
//
// heavily modified my Matthias at 06.03.2014, because original example violated
// C99 standard
//

int main() {
    int var = 'A';
    //@ assert var > 0;
}
