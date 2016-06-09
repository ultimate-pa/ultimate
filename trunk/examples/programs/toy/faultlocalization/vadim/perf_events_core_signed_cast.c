/*
 * commit https://git.kernel.org/cgit/linux/kernel/git/torvalds/linux.git/commit/kernel/events/core.c?id=8176cced706b5e5d15887584150764894e94e02f
 * exploit https://packetstormsecurity.com/files/121616/semtex.c
 * description https://bugzilla.redhat.com/show_bug.cgi?id=962792#c16
 * discussion http://arstechnica.com/security/2013/05/critical-linux-vulnerability-imperils-users-even-after-silent-fix/
 * PROPERTY: Memory safety, Valid dereference
 */


#include<stdlib.h>

void *malloc(size_t size);
void *calloc(size_t nitems, size_t size);

int copy_from_user();
int f();

void __VERIFIER_error(void);
int __VERIFIER_nondet_int(void);

#define PERF_TYPE_SOFTWARE 3
#define ENOENT 10
#define PERF_COUNT_SW_MAX 1024

typedef unsigned long u64;

int perf_swevent_enabled[PERF_COUNT_SW_MAX];

struct perf_event_attr {
	u64 config;
	int type;
};

struct perf_event {
	struct perf_event_attr attr;
	struct perf_event *parent;
	void (*destroy)(struct perf_event *);
};

struct perf_event_attr *get_from_user_event_attr(void);
//TODO: model which allocates memory and fills nondet values

static int swevent_hlist_get(struct perf_event *event) {
	return __VERIFIER_nondet_int();
}

static void swevent_hlist_put(struct perf_event *event) {
	return;
}

void static_key_slow_inc(int *key) {
	*key = *key + 1;
}

void static_key_slow_dec(int *key) {
	*key = *key - 1;
}

static void sw_perf_event_destroy(struct perf_event *event)
{
        u64 event_id = event->attr.config;

        static_key_slow_dec(&perf_swevent_enabled[event_id]);
        swevent_hlist_put(event);
}

static int perf_swevent_init(struct perf_event *event) {
        int event_id = event->attr.config;//bug is here: should use u64 instead of int

        if (event->attr.type != PERF_TYPE_SOFTWARE)
                return -ENOENT;

        if (event_id >= PERF_COUNT_SW_MAX)
                return -ENOENT;

        if (!event->parent) {
                int err;

                err = swevent_hlist_get(event);
                if (err)
                        return err;

                static_key_slow_inc(&perf_swevent_enabled[event_id]);
                event->destroy = sw_perf_event_destroy;
	}

	return 0;
}
static void free_event(struct perf_event *event)
{
        if (event->destroy)
                event->destroy(event);
	free(event);
}

static struct perf_event * perf_event_alloc(struct perf_event_attr *attr,
                 struct perf_event *parent_event)
{
        int err;
        struct perf_event *event;

        event = calloc(1, sizeof(*event));
        if (!event)
                return 0;
	event->parent = parent_event;
        err = perf_swevent_init(event);
        if (!err)
                goto err_ns;
	err = f();
	if(!err) 
		goto err_pmu;
	return event;
err_pmu:
        if (event->destroy)
                event->destroy(event);	
err_ns:
        free(event);
        return 0;
}


void main(void) {
	struct perf_event_attr *attr;
	struct perf_event *parent_event = 0;
	struct perf_event *event;
	attr = get_from_user_event_attr();
	event = perf_event_alloc(attr, parent_event);
	if(event) {
		free_event(event);
	}
}

