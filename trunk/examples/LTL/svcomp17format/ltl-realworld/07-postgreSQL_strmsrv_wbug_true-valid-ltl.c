extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

#include <stdio.h>
#define AF_INET 1
#define AF_INET6 2
#define AF_UNIX 3
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()
#define IS_AF_UNIX(a) __VERIFIER_nondet_int()

#define HAVE_IPV6 1
#define HAVE_UNIX_SOCKETS 1
#define PG_SOMAXCONN 10
#define SOCK_STREAM 1
#define STATUS_ERROR 0
#define STATUS_OK 1
#define gettext(a) ""
#define ereport(a,b,c) __VERIFIER_nondet_int()
#define getaddrinfo_all(a,b,c,d) __VERIFIER_nondet_int()
#define listen(a,b) __VERIFIER_nondet_int()
#define snprintf(a,b,c,f) {}
#define errmsg(a,b,c,d) ()
#define errcode_for_socket_access() 1
#define LOG 0
#define closesocket(a) { closed=1; }
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
#define __builtin___object_size(a,b) __VERIFIER_nondet_int()
#define socket(a,b,c) { return __VERIFIER_nondet_int(); }

int closed;
int MaxBackends;
int family;
char *hostName;
unsigned short portNumber;
char *unixSocketName;
int MaxListen;
int fd, err;
int maxconn;
int one;
int ret;
char *service;
int hint;
int listen_index;
int added;
int addr_ai_family;
int addr;
int MAXADDR;
int ListenSocket_OF_listen_index;
int ret;
char *sock_path;
int addrs;

// Initialization routine
int __INITIALIZED = 0;
void env_init() {
	one = 1;
	listen_index = 0;
	added = 0;
	MAXADDR = __VERIFIER_nondet_int();
	addrs = __VERIFIER_nondet_int();
	MaxBackends = __VERIFIER_nondet_int();
	ret = __VERIFIER_nondet_int();
	__INITIALIZED = 1;
}

int main()
{   
	env_init();
	__VERIFIER_assume(addrs>=0);
	__VERIFIER_assume(MaxBackends>0);

	if (family == AF_UNIX)
	{
		service = sock_path;
	}
	else
	{
		snprintf(1, sizeof(1), "%d", portNumber);
		service = (char*) 1;
	}

	ret = getaddrinfo_all(hostName, service, &hint, &addrs);
	if (ret || !addrs)
	{
		if (hostName) 
		{
			
		} 
		else 
		{
			
		}
	}
	
	for (addr = addrs; addr < MAXADDR; addr++)
	{
		if (!IS_AF_UNIX(family) && IS_AF_UNIX(addr_ai_family))
		{
			goto loc_continue;
		}

		for (; listen_index < MaxListen; listen_index++)
		{
			if (ListenSocket_OF_listen_index == -1)
				break;
		}
		if (listen_index >= MaxListen)
		{
			break;
		}

		if(addr_ai_family==AF_INET) 
		{
			gettext("IPv4");
		} 
		else if(addr_ai_family==AF_INET6) 
		{
			gettext("IPv6");
		} 
		else if(addr_ai_family==AF_UNIX) 
		{
			gettext("Unix");
		}
		else 
		{
			snprintf(1, 1, gettext("unrecognized address family %d"), addr_ai_family);
		}

		if ((fd = __VERIFIER_nondet_int()))
		{
			goto loc_continue;
		}

		if (__VERIFIER_nondet_int()) 
		{
			if (__VERIFIER_nondet_int()) 
			{
				goto loc_continue;
			}
		}

		if (__VERIFIER_nondet_int()) 
		{
			if (__VERIFIER_nondet_int()) 
			{
				closesocket(fd);
				goto loc_continue;
			}
		}

		err = __VERIFIER_nondet_int();
		if (err < 0)
		{
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

		if(1) 
		{ 
			loc_continue: 0; 
		}
	}

	if (!added) 
	{
		ret = STATUS_ERROR;
	}

	ret = STATUS_ERROR;

}
