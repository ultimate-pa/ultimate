extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER___VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
int do_ACCEPT;
int accept_mutex_off() { }
int unixd_setup_child() { }
int APR_STATUS_IS_EINTR(int a) { }
int accept_mutex_on() { }
int SAFE_ACCEPT(int a) { }
int clean_child_exit(int a) { }
int ap_accept_lock_mech;
int ap_listeners;
int ap_lock_fname;
int ap_max_mem_free;
int ap_max_requests_per_child;
int ap_scoreboard_image;
int conn_rec;
int current_conn;
int numdesc;
int pfd;
int shutdown_pending;
int pfd_desc_type;
int pfd_desc_s;
int pfd_reqevents;
int pfd_client_data;
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
int ap_threads_per_child;
static void *accept_mutex;
static int ap_daemons_to_start=0;
static int ap_daemons_min_free=0;
static int ap_daemons_max_free=0;
static int ap_daemons_limit=0;
static int server_limit = 256;
static int first_server_limit = 0;
static int changed_limit_at_restart;
static int mpm_state = 1;
static void *pod;
int ap_max_daemons_limit = -1;
void *ap_server_conf;
static int one_process = 0;
static void *pconf;
static void *pchild;
static int ap_my_pid;
static int parent_pid;
static int my_child_num;
int ap_my_generation=0;
int tpf_child = 0;
char *tpf_server_name;
  child_num_arg = __VERIFIER_nondet_int();
  do_ACCEPT = 0;
  die_now = 0;
  last_poll_idx = 0;
  ap_threads_per_child = 0;
  ap_daemons_to_start=0;
  ap_daemons_min_free=0;
  ap_daemons_max_free=0;
  ap_daemons_limit=0;
  server_limit = 256;
  first_server_limit = 0;
  ap_listeners = __VERIFIER_nondet_int();
int getpid() { return __VERIFIER_nondet_int(); }
void ap_fatal_signal_child_setup(int ap_server_conf) {}
void apr_allocator_create(int *allocator) {}
void apr_allocator_max_free_set(int allocator, int ap_max_mem_free) {}
void apr_pool_create_ex(int *pchild, int pconf, int NL, int allocator) {}
void apr_allocator_owner_set(int allocator, int pchild) {}
void apr_pool_create(int *ptrans, int pchild) {}
void apr_pool_tag(int ptrans, char *asdf) {}
void ap_reopen_scoreboard(int pchild, int NL, int z) {}
int apr_proc_mutex_child_init(int *accept_mutex, int ap_lock_fname, int pchild) { return __VERIFIER_nondet_int(); }
void ap_log_error(int APm, int APe, int status, int ap_server_conf, int a, int b, int c) {}
void ap_log_error5(int APm, int APe, int status, int ap_server_conf, int a) {}
void ap_run_child_init(int pchild, int ap_server_conf) {}
void ap_create_sb_handle(int *sbh, int pchild, int my_child_num, int z) {}
void ap_update_child_status(int sbh, int SER, int NL) {}
void apr_pollset_create(int *pollset, int num_listensocks, int pchild, int z) {}
void apr_pollset_add(int pollset, int *pfd) {}
void *apr_bucket_alloc_create(int pchild) {}
void apr_pool_clear(int ptrans) {}
int apr_pollset_poll(int pollset, int a, int *numdesc, int *pdesc) {}
int ap_run_create_connection(int ptrans, int ap_server_conf, int csd, int my_child_num, int sbh, int bucket_alloc) {}
void ap_process_connection(int current_conn, int csd) {}
void ap_lingering_close(int current_conn) {}
int ap_mpm_pod_check(int a) { return __VERIFIER_nondet_int(); }
void main()
{
  __VERIFIER_assume(child_num_arg > 0);
__VERIFIER_assume(ap_listeners > 0);
    mpm_state = 9;
    my_child_num = child_num_arg;
    ap_my_pid = getpid();
    requests_this_child = 0;
    ap_fatal_signal_child_setup(ap_server_conf);
    apr_allocator_create(&allocator);
    apr_allocator_max_free_set(allocator, ap_max_mem_free);
    apr_pool_create_ex(&pchild, pconf, 0, allocator);
    apr_allocator_owner_set(allocator, pchild);
    apr_pool_create(&ptrans, pchild);
    apr_pool_tag(ptrans, "transaction");
    ap_reopen_scoreboard(pchild, 0, 0);
    status = apr_proc_mutex_child_init(&accept_mutex, ap_lock_fname, pchild);
    if (status != 7) {
        ap_log_error(3, 1, status, ap_server_conf,
                     "Couldn't initialize cross-process lock in child "
                     "(%s) (%d)", ap_lock_fname, ap_accept_lock_mech);
        clean_child_exit(1);
    }
    if (unixd_setup_child()) {
        clean_child_exit(1);
    }
    ap_run_child_init(pchild, ap_server_conf);
    ap_create_sb_handle(&sbh, pchild, my_child_num, 0);
    ap_update_child_status(sbh, 1, 0);
    (void) apr_pollset_create(&pollset, num_listensocks, pchild, 0);
    num_listensocks = __VERIFIER_nondet_int(); __VERIFIER_assume(num_listensocks>0);
    for (lr = ap_listeners, i = num_listensocks; i--; ) {
        int pfd = 0;
        pfd_desc_type = 6;
        pfd_desc_s = 1;
        pfd_reqevents = 5;
        pfd_client_data = lr;
        (void) apr_pollset_add(pollset, &pfd);
    }
    mpm_state = 8;
    bucket_alloc = apr_bucket_alloc_create(pchild);
    while (!die_now) {
        conn_rec *current_conn;
        void *csd;
        apr_pool_clear(ptrans);
        if ((ap_max_requests_per_child > 0
             && requests_this_child++ >= ap_max_requests_per_child)) {
            clean_child_exit(0);
        }
        (void) ap_update_child_status(sbh, 1, 0);
        SAFE_ACCEPT(accept_mutex_on());
 do_ACCEPT=1; do_ACCEPT=0;
        if (num_listensocks == 1) {
            lr = ap_listeners;
        }
        else {
            for (;;) {
       int numdesc;
                const void *pdesc;
                status = apr_pollset_poll(pollset, -1, &numdesc, &pdesc);
                if (status != 7) {
                    if (APR_STATUS_IS_EINTR(status)) {
                        if (one_process && shutdown_pending) {
     goto loc_return;
                        }
                        goto loc_continueA;
                    }
                    ap_log_error5(3, 2, status,
                                 ap_server_conf, "apr_pollset_poll: (listen)");
                    clean_child_exit(1);
                }
                if (last_poll_idx >= numdesc)
                    last_poll_idx = 0;
                lr = 1;
  break;
     loc_continueA: {int yyy2; yyy2=yyy2; }
            }
        }
        status = __VERIFIER_nondet_int();
        SAFE_ACCEPT(accept_mutex_off());
        if (status == 4) {
            clean_child_exit(1);
        }
        else if (status != 7) {
   goto loc_continueB;
        }
        current_conn = ap_run_create_connection(ptrans, ap_server_conf, csd, my_child_num, sbh, bucket_alloc);
        if (current_conn) {
            ap_process_connection(current_conn, csd);
            ap_lingering_close(current_conn);
        }
        if (ap_mpm_pod_check(pod) == 7) {
            die_now = 1;
        }
        else if (ap_my_generation != __VERIFIER_nondet_int()) {
            die_now = 1;
        }
    loc_continueB: { int uuu; uuu=uuu; }
    }
    clean_child_exit(0);
 loc_return:
    while(1) { int ddd; ddd=ddd; }
}
