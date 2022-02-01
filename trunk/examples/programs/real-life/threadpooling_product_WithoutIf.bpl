//#Safe
/*
 * Date: 2015-04-23
 * Author: Jürgen Christ
 *
 * Variant of threadpooling_product.bpl where four if-then-else code blocks
 * have been removed.
 *
 */

procedure product() {
  var workload : int;
  var next : int;
  var begin0, begin1, end0, end1, working0, working1 : int;
  havoc next;
  assume next >= 0;
  havoc workload;
  assume workload > 0;
  working0 := -1;
  working1 := -1;

l0l0:
  if (*) {
    begin0 := next;
    next := next + workload;
    end0 := next;
    goto l1l0;
  } else {
    begin1 := next;
    next := next + workload;
    end1 := next;
    goto l0l1;
  }
l1l0:
  if (*) {
    working0 := begin0;
    assert working0 != working1;
    begin0 := begin0 + 1;
    if (begin0 < end0) {
      goto l1l0;
    } else {
      goto l0l0;
    }
  } else {
    begin1 := next;
    next := next + workload;
    end1 := next;
    goto l1l1;
  }
l0l1:
  if (*) {
    begin0 := next;
    next := next + workload;
    end0 := next;
    goto l1l1;
  } else {
    working1 := begin1;
    assert working0 != working1;
    begin1 := begin1 + 1;
    if (begin1 < end1) {
      goto l0l1;
    } else {
      goto l0l0;
    }
  }
l1l1:
  if (*) {
    working0 := begin0;
    assert working0 != working1;
    begin0 := begin0 + 1;
    if (begin0 < end0) {
      goto l1l1;
    } else {
      goto l0l1;
    }
  } else {
    working1 := begin1;
    assert working0 != working1;
    begin1 := begin1 + 1;
    if (begin1 < end1) {
      goto l1l1;
    } else {
      goto l1l0;
    }
  }
}


