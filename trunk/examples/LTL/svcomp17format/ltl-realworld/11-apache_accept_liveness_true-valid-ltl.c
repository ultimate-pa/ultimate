extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int do_ACCEPT; 

int accept_mutex_off() { return __VERIFIER_nondet_int(); }
int unixd_setup_child() { return __VERIFIER_nondet_int();}
int APR_STATUS_IS_EINTR(int a) { return __VERIFIER_nondet_int();}
int accept_mutex_on() {return __VERIFIER_nondet_int();}
int SAFE_ACCEPT(int a) {return __VERIFIER_nondet_int();}
int clean_child_exit(int a) { return __VERIFIER_nondet_int();}

#define DEFAULT_SERVER_LIMIT 256
#define MAX_SERVER_LIMIT 200000
#define HARD_THREAD_LIMIT 1

#define APEXIT_CHILDFATAL 1
#define APLOG_EMERG 1
#define APLOG_ERR 2
#define APLOG_MARK 3
#define APR_EGENERAL 4
#define APR_POLLIN 5
#define APR_POLL_SOCKET 6 
#define APR_SUCCESS 7
#define AP_MPMQ_RUNNING 8
#define AP_MPMQ_STARTING 9
#define NULL 0
#define SERVER_READY 1
int  ap_accept_lock_mech;
int  ap_listeners;
int  ap_lock_fname;
int  ap_max_mem_free;
int  ap_max_requests_per_child;
int  ap_scoreboard_image;
int  conn_rec;
int  current_conn;
int  numdesc;
int  pfd;
int  shutdown_pending;
int        pfd_desc_type;
int        pfd_desc_s;
int        pfd_reqevents;
int        pfd_client_data;

static volatile int die_now;
static int requests_this_child;
static int num_listensocks = 0;

void *ptrans;
void *allocator;
int status;
int i;
int lr;
void *pollset;
void *sbh;
void *bucket_alloc;
int last_poll_idx;
int child_num_arg;
int ap_threads_per_child;         /* Worker threads per child */
static void *accept_mutex;
static int ap_daemons_to_start=0;
static int ap_daemons_min_free=0;
static int ap_daemons_max_free=0;
static int ap_daemons_limit=0;      /* MaxClients */
static int server_limit = DEFAULT_SERVER_LIMIT;
static int first_server_limit = 0;
static int changed_limit_at_restart;
static int mpm_state = 1;//AP_MPMQ_STARTING;
static void *pod;
int ap_max_daemons_limit = -1;
void *ap_server_conf;
static int one_process = 0;
static void *pconf;               /* Pool for config stuff */
static void *pchild;              /* Pool for httpd child stuff */

static int ap_my_pid; /* it seems silly to call getpid all the time */
static int parent_pid;
static int my_child_num;
int ap_my_generation=0;
int tpf_child = 0;
char *tpf_server_name; // [256+1]; // INETD_SERVNAME_LENGTH+1];


 



/*****************************************************************
 * Child process main loop.
 * The following vars are static to avoid getting clobbered by longjmp();
 * they are really private to child_main.
 */
int getpid() { return __VERIFIER_nondet_int(); }
void ap_fatal_signal_child_setup(void *ap_server_conf) {}
void apr_allocator_create(void **allocator) {}
void apr_allocator_max_free_set(void *allocator, int ap_max_mem_free) {}
void apr_pool_create_ex(void **pchild, void *pconf, int NL, void *allocator) {}
void apr_allocator_owner_set(void *allocator, void *pchild) {}
void apr_pool_create(void **ptrans, void *pchild) {}
void apr_pool_tag(void *ptrans, char *asdf) {}
void ap_reopen_scoreboard(void *pchild, int NL, int z) {}
int apr_proc_mutex_child_init(void **accept_mutex, int ap_lock_fname, void *pchild) { return __VERIFIER_nondet_int(); }
void ap_log_error(int APm, int APe, int status, void *ap_server_conf, char *a, int b, int c) {}
void ap_log_error5(int APm, int APe, int status, void *ap_server_conf, char *a) {}
void ap_run_child_init(void *pchild, void *ap_server_conf) {}
void ap_create_sb_handle(void **sbh, void *pchild, int my_child_num, int z) {}
void ap_update_child_status(void *sbh, int SER, int NL) {}
void apr_pollset_create(void **pollset, int num_listensocks, void *pchild, int z) {}
void apr_pollset_add(void *pollset, int *pfd) {}
void *apr_bucket_alloc_create(void *pchild) { return (void *) __VERIFIER_nondet_int(); }
void apr_pool_clear(void *ptrans) {}
int apr_pollset_poll(void *pollset, int a, int *numdesc, const void **pdesc) { return __VERIFIER_nondet_int(); }
int ap_run_create_connection(void *ptrans, void *ap_server_conf, void *csd, int my_child_num, void *sbh, void *bucket_alloc) { return __VERIFIER_nondet_int(); }
void ap_process_connection(int current_conn, void *csd) {}
void ap_lingering_close(int current_conn) {}
int ap_mpm_pod_check(void *a) { return __VERIFIER_nondet_int(); }

// Initialization routine
int __INITIALIZED = 0;
void env_init() {
    ap_listeners = __VERIFIER_nondet_int(); 
    child_num_arg = __VERIFIER_nondet_int();
    do_ACCEPT = 0;
    die_now = 0;
    last_poll_idx = 0;
    ap_threads_per_child = 0;
    ap_daemons_to_start=0;
    ap_daemons_min_free=0;
    ap_daemons_max_free=0;
    ap_daemons_limit=0;      /* MaxClients */
    server_limit = DEFAULT_SERVER_LIMIT;
    first_server_limit = 0;
    __INITIALIZED = 1;
}


//static void child_main(int child_num_arg)
int main()
{
  __VERIFIER_assume(child_num_arg > 0);
  __VERIFIER_assume(ap_listeners > 0);



    mpm_state = AP_MPMQ_STARTING; /* for benefit of any hooks that run as this
                                   * child initializes
                                   */

    my_child_num = child_num_arg;
    ap_my_pid = getpid();
    requests_this_child = 0;

    ap_fatal_signal_child_setup(ap_server_conf);

    /* Get a sub context for global allocations in this child, so that
     * we can have cleanups occur when the child exits.
     */
    apr_allocator_create(&allocator);
    apr_allocator_max_free_set(allocator, ap_max_mem_free);
    apr_pool_create_ex(&pchild, pconf, NULL, allocator);
    apr_allocator_owner_set(allocator, pchild);

    apr_pool_create(&ptrans, pchild);
    apr_pool_tag(ptrans, "transaction");

    /* needs to be done before we switch UIDs so we have permissions */
    ap_reopen_scoreboard(pchild, NULL, 0);
    status = apr_proc_mutex_child_init(&accept_mutex, ap_lock_fname, pchild);
    if (status != APR_SUCCESS) {
        ap_log_error(APLOG_MARK, APLOG_EMERG, status, ap_server_conf,
                     "Couldn't initialize cross-process lock in child "
                     "(%s) (%d)", ap_lock_fname, ap_accept_lock_mech);
        clean_child_exit(APEXIT_CHILDFATAL);
    }

    if (unixd_setup_child()) {
        clean_child_exit(APEXIT_CHILDFATAL);
    }

    ap_run_child_init(pchild, ap_server_conf);

    ap_create_sb_handle(&sbh, pchild, my_child_num, 0);

    ap_update_child_status(sbh, SERVER_READY, NULL);

    /* Set up the pollfd array */
    /* ### check the status */
    (void) apr_pollset_create(&pollset, num_listensocks, pchild, 0);

    num_listensocks = __VERIFIER_nondet_int(); __VERIFIER_assume(num_listensocks>0);

    for (lr = ap_listeners, i = num_listensocks; i--; ) {
        int pfd = 0;

        pfd_desc_type = APR_POLL_SOCKET;
        pfd_desc_s = 1; // lr->sd;
        pfd_reqevents = APR_POLLIN;
        pfd_client_data = lr;

        /* ### check the status */
        (void) apr_pollset_add(pollset, &pfd);
    }

    mpm_state = AP_MPMQ_RUNNING;

    bucket_alloc = apr_bucket_alloc_create(pchild);

    while (!die_now) {
        conn_rec *current_conn;
        void *csd;

        /*
         * (Re)initialize this child to a pre-connection state.
         */

        apr_pool_clear(ptrans);

        if ((ap_max_requests_per_child > 0
             && requests_this_child++ >= ap_max_requests_per_child)) {
            clean_child_exit(0);
        }

        (void) ap_update_child_status(sbh, SERVER_READY, NULL);

        /*
         * Wait for an acceptable connection to arrive.
         */

        /* Lock around "accept", if necessary */
        SAFE_ACCEPT(accept_mutex_on());
	do_ACCEPT=1; do_ACCEPT=0;

        if (num_listensocks == 1) {
            /* There is only one listener record, so refer to that one. */
            lr = ap_listeners;
        }
        else {
            /* multiple listening sockets - need to poll */
            for (;;) {
	      int numdesc;
                const void *pdesc;

                /* timeout == -1 == wait forever */
                status = apr_pollset_poll(pollset, -1, &numdesc, &pdesc);
                if (status != APR_SUCCESS) {
                    if (APR_STATUS_IS_EINTR(status)) {
                        if (one_process && shutdown_pending) {
			  goto loc_return;
                        }
                        goto loc_continueA;
                    }
                    /* Single Unix documents select as returning errnos
                     * EBADF, EINTR, and EINVAL... and in none of those
                     * cases does it make sense to continue.  In fact
                     * on Linux 2.0.x we seem to end up with EFAULT
                     * occasionally, and we'd loop forever due to it.
                     */
                    ap_log_error5(APLOG_MARK, APLOG_ERR, status,
                                 ap_server_conf, "apr_pollset_poll: (listen)");
                    clean_child_exit(1);
                }

                /* We can always use pdesc[0], but sockets at position N
                 * could end up completely starved of attention in a very
                 * busy server. Therefore, we round-robin across the
                 * returned set of descriptors. While it is possible that
                 * the returned set of descriptors might flip around and
                 * continue to starve some sockets, we happen to know the
                 * internal pollset implementation retains ordering
                 * stability of the sockets. Thus, the round-robin should
                 * ensure that a socket will eventually be serviced.
                 */
                if (last_poll_idx >= numdesc)
                    last_poll_idx = 0;

                /* Grab a listener record from the client_data of the poll
                 * descriptor, and advance our saved index to round-robin
                 * the next fetch.
                 *
                 * ### hmm... this descriptor might have POLLERR rather
                 * ### than POLLIN
                 */
                lr = 1; //pdesc[last_poll_idx++].client_data;
		break;

	    loc_continueA: {int yyy2; yyy2=yyy2; }
            }
        }
        /* if we accept() something we don't want to die, so we have to
         * defer the exit
         */
        status = __VERIFIER_nondet_int(); // lr->accept_func(&csd, lr, ptrans);

        SAFE_ACCEPT(accept_mutex_off());      /* unlock after "accept" */

        if (status == APR_EGENERAL) {
            /* resource shortage or should-not-occur occured */
            clean_child_exit(1);
        }
        else if (status != APR_SUCCESS) {
	  goto loc_continueB;
        }

        /*
         * We now have a connection, so set it up with the appropriate
         * socket options, file descriptors, and read/write buffers.
         */

        current_conn = ap_run_create_connection(ptrans, ap_server_conf, csd, my_child_num, sbh, bucket_alloc);
        if (current_conn) {
            ap_process_connection(current_conn, csd);
            ap_lingering_close(current_conn);
        }

        /* Check the pod and the generation number after processing a
         * connection so that we'll go away if a graceful restart occurred
         * while we were processing the connection or we are the lucky
         * idle server process that gets to die.
         */
        if (ap_mpm_pod_check(pod) == APR_SUCCESS) { /* selected as idle? */
            die_now = 1;
        }
        else if (ap_my_generation != __VERIFIER_nondet_int()) {
	  //ap_scoreboard_image->global->running_generation) { /* restart? */
            /* yeah, this could be non-graceful restart, in which case the
             * parent will kill us soon enough, but why bother checking?
             */
            die_now = 1;
        }
    loc_continueB: { int uuu; uuu=uuu; }
    }
    clean_child_exit(0);
 loc_return:
    while(1) { int ddd; ddd=ddd; }
}
