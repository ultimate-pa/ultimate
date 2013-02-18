#include "vcc.h"

struct point {
    int x;
    int y;
};

struct vcc(dynamic_owns) rect {
    struct point ll;
    struct point ur;
	
    invariant( inv_rect(this) )
    invariant( set_in( &ll, owns(this) ) )
    invariant( set_in( &ur, owns(this) ) )
};

spec( ispure bool inv_rect(struct rect * r)
    reads(r, &r->ll, &r->ur)
    returns(r->ll.x <= r->ur.x && r->ll.y <= r->ur.y);
)

spec(ispure bool within_bounds(__in struct rect* r, int dx, int dy)
	 reads(r)
	 returns( 0 <= r->ll.x + dx && r->ll.x + dx < 1024 &&
			  0 <= r->ur.x + dx && r->ur.x + dx < 1024 &&
			  0 <= r->ll.y + dy && r->ll.y + dy < 1024 &&
			  0 <= r->ur.y + dy && r->ur.y + dy < 1024 );
)

void move(__inout struct rect* r, int dx, int dy)
    maintains(wrapped(r))
    requires(within_bounds(r, dx, dy))
	writes(r)
{	
	assert(in_domain(r, r));
	assert(in_domain(&r->ll, r));
	assert(in_domain(&r->ur, r));
	
    unwrap(r);
	unwrap(&r->ll);
    r->ll.x = unchecked(r->ll.x + dx);
    r->ll.y = unchecked(r->ll.y + dy);
	wrap(&r->ll);
    unwrap(&r->ur);
    r->ur.x = unchecked(r->ur.x + dx);
    r->ur.y = unchecked(r->ur.y + dy);
	wrap(&r->ur);
    wrap(r);
}
