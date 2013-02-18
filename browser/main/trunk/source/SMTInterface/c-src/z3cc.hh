#ifndef STALIN_Z3CC_HH_
#define STALIN_Z3CC_HH_

extern "C" {
#include <z3.h>
}

// Need to undef all definitions to prevent side effects
#undef __in
#undef __in_z
#undef __out
#undef __ecount
#undef __in_ecount
#undef __out_ecount
#undef __inout_ecount
#undef __inout
#undef Z3_API
#undef DEFINE_TYPE

#endif
