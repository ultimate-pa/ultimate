//#Safe
// *************************************************************
//
//     Branching-time reasoning for infinite-state systems
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// *************************************************************

// Benchmark: pgstream.c
// Property: AG( AFAG(ret==STATUS_OK)  \/ added<=0 )


//@ ltl invariant positive: []( <>[]AP(ret == 1) || AP(added <= 0));
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

//Ultimante Changes:
// if ... endif preprocessor blocks preprocessor code deleted
// preprocessorcode in property changed to actual value

#include <stdio.h>
#define AF_INET 1
#define AF_INET6 2
#define AF_UNIX 3
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()

#define PG_SOMAXCONN 10
#define SOCK_STREAM 1
#define STATUS_ERROR 0
#define STATUS_OK 1
int closed;
int MaxBackends;

//#define snprintf(a,b,c,d) __VERIFIER_nondet_int()
#define gettext(a) ""
#define ereport(a,b,c) __VERIFIER_nondet_int()
#define getaddrinfo_all(a,b,c,d) __VERIFIER_nondet_int()
#define listen(a,b) __VERIFIER_nondet_int()
#define snprintf(a,b,c,f) {}
#define errmsg(a,b,c,d) ()
#define errcode_for_socket_access() 1
//#define 
#define LOG 0
#define closesocket(a) { closed=1; }
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
#define __builtin___object_size(a,b) __VERIFIER_nondet_int()
#define socket(a,b,c) { return __VERIFIER_nondet_int(); }

/*postgresql-8.0.2/src/backend/libpq.c
 * StreamServerPort -- open a "listening" port to accept connections.
 *
 * Successfully opened sockets are added to the ListenSocket[] array,
 * at the first position that isn't -1.
 *
 * RETURNS: STATUS_OK or STATUS_ERROR
 */

int family;
char *hostName;
unsigned short portNumber;
char *unixSocketName;
int MaxListen;
int fd, err;
int maxconn;
int one;
int ret;
//char            portNumberStr[32];
//const char *familyDesc;
//char            familyDescBuf[64];
char       *service;
/* struct addrinfo *addrs = NULL, */
/*   *addr; */
/* struct addrinfo hint; */
int hint;
int                     listen_index;
int                     added;
int addr_ai_family;
int addr;
int MAXADDR;
int ListenSocket_OF_listen_index;
int ret;
char *sock_path;
int addrs;

  one = 1;
  listen_index = 0;
  added = 0;
  MAXADDR = __VERIFIER_nondet_int();
  addrs = __VERIFIER_nondet_int();

  MaxBackends = __VERIFIER_nondet_int();

  ret = __VERIFIER_nondet_int();

void main()
{
  __VERIFIER_assume(MaxBackends>0);
  __VERIFIER_assume(addrs>=0);
        /* Initialize hint structure */
        if (family == AF_UNIX)
        {
                /* Lock_AF_UNIX will also fill in sock_path. */
                /* if (Lock_AF_UNIX(portNumber, unixSocketName) != STATUS_OK) */
                /*         return STATUS_ERROR; */
                service = sock_path;
        }
        else
        {
                snprintf(1, sizeof(1), "%d", portNumber);
                service = 1;
        }

        ret = getaddrinfo_all(hostName, service, &hint, &addrs);
        if (ret || !addrs)
        {
	  if (hostName) {
                        /* ereport(LOG, */
                        /*                 (errmsg("could not translate host name \"%s\", service \"%s\" to address: %s", */
                        /*                                 hostName, service, gai_strerror(ret)))); */
	  } else {
                        /* ereport(LOG, */
                        /*  (errmsg("could not translate service \"%s\" to address: %s", */
                        /*                  service, gai_strerror(ret)))); */
                /* if (addrs) */
                /*         freeaddrinfo_all(hint.ai_family, addrs); */
	  }
	  //ret = STATUS_ERROR;
	  //while(1) { int qqq; qqq=qqq;}
        }

        for (addr = addrs; addr < MAXADDR; addr++) //  = addr->ai_next)
        {
                if (!IS_AF_UNIX(family) && IS_AF_UNIX(addr_ai_family))
                {
                        /*
                         * Only set up a unix domain socket when they really asked for
                         * it.  The service/port is different in that case.
                         */
                        goto loc_continue;
                }

                /* See if there is still room to add 1 more socket. */
                for (; listen_index < MaxListen; listen_index++)
                {
                        if (ListenSocket_OF_listen_index == -1)
                                break;
                }
                if (listen_index >= MaxListen)
                {
                        /* ereport(LOG, */
                        /*                 (errmsg("could not bind to all requested addresses: MAXLISTEN (%d) exceeded", */
                        /*                                 MaxListen))); */
                        break;
                }

                /* set up family name for possible error messages */
		  if(addr_ai_family==AF_INET) {
                                gettext("IPv4");
		  } else if(addr_ai_family==AF_INET6) {
                                gettext("IPv6");
		  } else if(addr_ai_family==AF_UNIX) {
                                gettext("Unix");
		  } else {
			  snprintf(1,/*familyDescBuf*/ 1, //sizeof(familyDescBuf),
                                                 gettext("unrecognized address family %d"),
                                                 addr_ai_family);
                                //familyDesc = familyDescBuf;
		  }

                if ((fd = __VERIFIER_nondet_int())) // socket(addr_ai_family, SOCK_STREAM, 0)) < 0)
                {
                        /* ereport(LOG, */
                        /*                 (errcode_for_socket_access(), */
                        /* /\* translator: %s is IPv4, IPv6, or Unix *\/ */
                        /*                  errmsg("could not create %s socket: %m", */
                        /*                                 familyDesc))); */
                        goto loc_continue;
                }

                if (__VERIFIER_nondet_int()) // !IS_AF_UNIX(addr_ai_family))
                {
		  if (__VERIFIER_nondet_int()) //(setsockopt(fd, SOL_SOCKET, SO_REUSEADDR,
		    //                       (char *) &one, sizeof(one))) == -1)
                        {
                                /* ereport(LOG, */
                                /*                 (errcode_for_socket_access(), */
                                /*                  errmsg("setsockopt(SO_REUSEADDR) failed: %m"))); */
                                /* closesocket(fd); */
                                goto loc_continue;
                        }
                }

                if (__VERIFIER_nondet_int()) // addr_ai_family == AF_INET6)
                {
		  if (__VERIFIER_nondet_int()) // setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY,
		    //                  (char *) &one, sizeof(one)) == -1)
                        {
                                /* ereport(LOG, */
                                /*                 (errcode_for_socket_access(), */
                                /*                  errmsg("setsockopt(IPV6_V6ONLY) failed: %m"))); */
                                closesocket(fd);
                                goto loc_continue;
                        }
                }

                /*
                 * Note: This might fail on some OS's, like Linux older than
                 * 2.4.21-pre3, that don't have the IPV6_V6ONLY socket option, and
                 * map ipv4 addresses to ipv6.  It will show ::ffff:ipv4 for all
                 * ipv4 connections.
                 */
                err = __VERIFIER_nondet_int(); // bind(fd, addr->ai_addr, addr->ai_addrlen);
                if (err < 0)
                {
                        /* ereport(LOG, */
                        /*                 (errcode_for_socket_access(), */
                        /* /\* translator: %s is IPv4, IPv6, or Unix *\/ */
                        /*                  errmsg("could not bind %s socket: %m", */
                        /*                                 familyDesc), */
                        /*                  (IS_AF_UNIX(addr_ai_family)) ? */
                        /*   errhint("Is another postmaster already running on port %d?" */
                        /*                   " If not, remove socket file \"%s\" and retry.", */
                        /*                   (int) portNumber, sock_path) : */
                        /*   errhint("Is another postmaster already running on port %d?" */
                        /*                   " If not, wait a few seconds and retry.", */
                        /*                   (int) portNumber))); */
                        closesocket(fd);
                        goto loc_continue;
                }

                if (addr_ai_family == AF_UNIX)
                {
		  if (__VERIFIER_nondet_int() != STATUS_OK)
                        {
                                closesocket(fd);
                                break;
                        }
                }

                /*
                 * Select appropriate accept-queue length limit.  PG_SOMAXCONN is
                 * only intended to provide a clamp on the request on platforms
                 * where an overly large request provokes a kernel error (are
                 * there any?).
                 */
                maxconn = MaxBackends * 2;
                if (maxconn > PG_SOMAXCONN)
                        maxconn = PG_SOMAXCONN;

                err = listen(fd, maxconn);
                if (err < 0)
                {

                        closesocket(fd);
                        goto loc_continue;
                }
                ListenSocket_OF_listen_index = fd;
		added++;

		if(1) { loc_continue: 0; }

        }

        //freeaddrinfo_all(hint.ai_family, addrs);

        if (!added) {
                ret = STATUS_ERROR;
		while(1) { int rrr; rrr=rrr; }
	}

        ret = STATUS_OK;
	while(1) { int ddd; ddd=ddd; }
}
