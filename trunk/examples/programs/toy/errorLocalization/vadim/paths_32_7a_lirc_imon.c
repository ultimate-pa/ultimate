/*
 * linux-4.2-rc1.tar.xz, 32_7a, drivers/staging/media/lirc/lirc_imon.ko, ldv_main0_sequence_infinite_withcheck_stateful
 * security
 * occurs on all paths
 * https://lkml.org/lkml/2015/11/16/427
 */

#include<stdlib.h>

void *malloc(size_t size);
void *calloc(size_t nitems, size_t size);

void *kzalloc(size_t size) {
	return calloc(1, size);
}

void kfree(void *p) {
	free(p);
}

void __VERIFIER_error();
int __VERIFIER_nondet_int(void);

struct mutex {
	int a;
};

#define ldv_assert(b) if(!(b)) __VERIFIER_error()

static int ldv_mutex_ctx_lock = 1;

void ldv_mutex_lock_ctx_lock(struct mutex *lock) 
{
	ldv_assert(ldv_mutex_ctx_lock == 1); 
	ldv_mutex_ctx_lock = 2;
}

void ldv_mutex_unlock_ctx_lock(struct mutex *lock) { 
	ldv_assert(ldv_mutex_ctx_lock == 2); 
	ldv_mutex_ctx_lock = 1;
}

struct usb_interface {
	struct mutex ctx_lock;
};

struct imon_context {
	int a;
};

int lirc_register_driver(void);
struct imon_context *context;

static int imon_probe(struct usb_interface *interface) {
	int retval = 0;
	int lirc_minor;
	context = kzalloc(sizeof(struct imon_context));
	if (!context)
		goto driver_unlock;

	ldv_mutex_lock_ctx_lock(&interface->ctx_lock);

	lirc_minor = lirc_register_driver();
	if (lirc_minor < 0) {
		//lirc_register_driver failed
		//one more bug: retval should be changed to error code
		goto free_tx_urb;
	}

	//mutex_unlock(&context->ctx_lock); - missing unlock
	//security: affect the main path
	goto driver_unlock;

unregister_lirc:

free_tx_urb:
	//mutex_unlock(&context->ctx_lock);
	//affect an error path
free_rx_urb:

free_lirc_buf:

free_rbuf:

free_driver:
free_context:
	kfree(context);
	context = NULL;

driver_unlock:
	return retval;
}

static void imon_disconnect(struct usb_interface *interface) {
	ldv_mutex_lock_ctx_lock(&interface->ctx_lock);
	kfree(context);
	ldv_mutex_unlock_ctx_lock(&interface->ctx_lock);
}

struct usb_interface *get_interface(void);

void main(void) {
	struct usb_interface *interface = get_interface();
	int ret = imon_probe(interface);
	if(ret==0) {
		imon_disconnect(interface);
	}
}

