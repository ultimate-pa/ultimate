/*
 * linux-4.2-rc1.tar.xz, 38_7a, drivers/gpio/gpio-grgpio.ko, ldv_main0_sequence_infinite_withcheck_stateful
 * security
 * occurs on all paths
 * depends on condition for the input data: some lirq from priv should have lirq->irq == irq
 * http://linuxtesting.org/pipermail/ldv-project/2015-August/000531.html
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

struct spin_lock {
	int a;
};

#define ldv_assert(b) if(!(b)) __VERIFIER_error()

static int ldv_spin_bgc_lock = 1;

void ldv_spin_lock_bgc_lock(struct spin_lock *lock) 
{
	ldv_assert(ldv_spin_bgc_lock == 1); 
	ldv_spin_bgc_lock = 2;
}

void ldv_spin_unlock_bgc_lock(struct spin_lock *lock) { 
	ldv_assert(ldv_spin_bgc_lock == 2); 
	ldv_spin_bgc_lock = 1;
}

struct grgpio_lirq {
	int index;
	unsigned int irq;
};

#define GRGPIO_MAX_NGPIO 32

struct grgpio_priv {
	struct spin_lock bgc_lock;
	int ngpio;
	unsigned long imask;
	struct grgpio_lirq lirqs[GRGPIO_MAX_NGPIO];
};

unsigned long get_mask(struct grgpio_priv *priv, unsigned int offset);

static void grgpio_set_imask(struct grgpio_priv *priv, unsigned int offset,
			     int val)
{
	unsigned long mask = get_mask(priv, offset);

	//security: double lock occurs on all paths
        ldv_spin_lock_bgc_lock(&priv->bgc_lock);

	if (val)
		priv->imask |= mask;
	else
		priv->imask &= ~mask;

	ldv_spin_unlock_bgc_lock(&priv->bgc_lock);
}

static void grgpio_irq_unmap(struct grgpio_priv *priv, unsigned int irq) 
{
	int index;
	int i;
	struct grgpio_lirq *lirq;
	int ngpio = priv->ngpio;

        ldv_spin_lock_bgc_lock(&priv->bgc_lock);
	/* Free underlying irq if last user unmapped */
	index = -1;
	for (i = 0; i < ngpio; i++) {
		lirq = &priv->lirqs[i];
		if (lirq->irq == irq) {
			grgpio_set_imask(priv, i, 0);
			index = lirq->index;
			break;
		}
	}
	ldv_spin_unlock_bgc_lock(&priv->bgc_lock);
}

struct grgpio_priv *get_grgpio_priv(void);
unsigned int get_irq(void);

void main(void) {
	struct grgpio_priv *priv = get_grgpio_priv();
	unsigned int irq = get_irq();
	grgpio_irq_unmap(priv, irq);
}

