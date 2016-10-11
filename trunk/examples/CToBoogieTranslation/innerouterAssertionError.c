/*
 * DD 2016-10-11
 * AssertionError: this should not be the case as we are in the inner/outermost array right??
 *
 */
typedef unsigned int __u32;
typedef __u32 uint32_t;
typedef uint32_t maskarray_t[0];

static maskarray_t via_pro_group_a_irqs[4U][5U]  = {};

int main() 
{ 
	via_pro_group_a_irqs ;
}