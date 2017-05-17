/*
 * linux-3.16-rc1.tar.xz, 32_7a, drivers/net/can/softing/softing.ko, ldv_main0_sequence_infinite_withcheck_stateful
 * non security
 * To reproduce mutex_lock_interruptible should fail.
 * Bug is on failure path of softing_pdev_probe. May fail: sysfs_create_group, softing_netdev_create, softing_netdev_register. 
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

int copy_from_user();
int init(int a);
int f();

void __VERIFIER_error();
int __VERIFIER_nondet_int(void);

struct mutex {
	int a;
};

void mutex_init(struct mutex *lock);

#define ldv_assert(b) if(!(b)) __VERIFIER_error()

static int ldv_mutex_fw_lock = 1;

int ldv_mutex_lock_interruptible_fw_lock(struct mutex *lock) 
{
	int nondetermined;
	ldv_assert(ldv_mutex_fw_lock == 1); 
	nondetermined = __VERIFIER_nondet_int();
	if (nondetermined) {
		ldv_mutex_fw_lock = 2;
		/* LDV_COMMENT_RETURN Finish with success */
		return 0;
	} else {
		/* LDV_COMMENT_RETURN Finish with fail. Mutex 'lock_of_NOT_ARG_SIGN' is keeped unlocked */
		return -4; 
	}
}

void ldv_mutex_unlock_fw_lock(struct mutex *lock) { 
	ldv_assert(ldv_mutex_fw_lock == 2); 
	ldv_mutex_fw_lock = 1;
}

struct softing {
	struct mutex fw_lock;
	int id_freq;
	int fw_up;
};

int sysfs_create_group(void);

static int softing_card_boot(struct softing *card)
{
	if (ldv_mutex_lock_interruptible_fw_lock(&card->fw_lock))
		return -1;
	if (__VERIFIER_nondet_int()) {
		ldv_mutex_unlock_fw_lock(&card->fw_lock);
		return 0;
	}
	ldv_mutex_unlock_fw_lock(&card->fw_lock);
	return 0;
}

static void softing_card_shutdown(struct softing *card) {
	if (ldv_mutex_lock_interruptible_fw_lock(&card->fw_lock))
		/*return -1;*/
	
	if (__VERIFIER_nondet_int()) {
		ldv_mutex_unlock_fw_lock(&card->fw_lock);
	}
	ldv_mutex_unlock_fw_lock(&card->fw_lock);
}

struct softing *pdev_card;

static int softing_pdev_probe(void) {
	int ret;
	struct softing *card;
	card = kzalloc(sizeof(*card));
	if (!card)
		return -1;
	mutex_init(&card->fw_lock);

	/* reset card */
	ret = softing_card_boot(card);
	if (ret < 0) {
		//failed to boot
		goto boot_failed;
	}
	/* only now, the chip's are known */

	ret = sysfs_create_group();
	if (ret < 0) {
		//sysfs failed
		goto sysfs_failed;
	}
	pdev_card = card;
	return 0;
sysfs_failed:
	softing_card_shutdown(card);
boot_failed:
ioremap_failed:
platform_resource_failed:
	kfree(card);
	return ret;
}

static int softing_pdev_remove()
{
	struct softing *card = pdev_card;

	/* first, disable card*/
	softing_card_shutdown(card);

	//sysfs_remove_group(&pdev->dev.kobj, &softing_pdev_group);

	kfree(card);
	return 0;
}

void main(void) {
	int ret = softing_pdev_probe();
	if(ret==0) {
		softing_pdev_remove();
	}
}
