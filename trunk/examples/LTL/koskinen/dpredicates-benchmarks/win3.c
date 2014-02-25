// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: win3.c
// Property: F G Stored==0

#include "ctl.h"

int Stored;

void init() { Stored = 0; }



void callback() {}
void IoQueueWorkItem() {}

void body() {
    while(nondet()) {


           if (nondet()) {
               //
               // We are safely at PASSIVE_LEVEL, call callback directly
               // to perform
               // this operation immediately.
               //
               callback ();

           } else {
	       IoQueueWorkItem ();
               Stored = 1;
               break;
           }
    }

    // Lower Irql and process

    if (Stored==1) {
        callback ();
        Stored = 0;
    }
}

int main() {}
