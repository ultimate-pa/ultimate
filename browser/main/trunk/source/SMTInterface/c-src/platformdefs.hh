#ifndef STALIN_PLATFORMDEFS_HH_
#define STALIN_PLATFORMDEFS_HH_

/*
 * This header handles platform specific ABI features like symbol export and
 * visibility.
 */
#include <jni.h>

// This definition is platform independant...
#define STALIN_CALL JNICALL

#if ((defined WIN) || (defined WIN32) || (defined WIN64) || \
     (defined _WIN32) || (defined _WIN64) || \
     (defined __NT__) || (defined __WIN32__) || (defined __WIN64__))
#  define STALIN_EXPORT extern "C" JNIEXPORT
#  define STALIN_INTERNAL
#elif (defined __linux__) || (defined __linux)
#  define STALIN_EXPORT extern "C" __attribute__((visibility("default")))
#  define STALIN_INTERNAL __attribute__((visibility("internal")))
#else
#  error "Operating system not supported."
#endif

#endif
