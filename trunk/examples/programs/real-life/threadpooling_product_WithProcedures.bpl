//#Safe
/*
 * Date: 2015-06-24
 * Author: Jürgen Christ
 *
 * Variant of threadpooling_product.bpl
 *
 */


var begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload : int;

procedure l0l0();
  modifies begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload;

procedure l1l0();
  modifies begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload;

procedure l0l1();
  modifies begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload;

procedure l1l1();
  modifies begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload;

procedure ULTIMATE.start();
  modifies begin0, begin1, end0, end1, working0, working1, iter0, iter1, next, workload;

implementation ULTIMATE.start() {
  havoc next;
  assume next >= 0;
  havoc workload;
  assume workload > 0;
  working0 := -1;
  working1 := -1;

  call l0l0();
}

implementation l0l0() {
  if (*) {
    begin0 := next;
    next := next + workload;
    end0 := next;
    iter0 := begin0;
    if (iter0 < end0) {
      call l1l0();
    } else {
      call l0l0();
    }
  } else {
    begin1 := next;
    next := next + workload;
    end1 := next;
    iter1 := begin1;
    if (iter1 < end1) {
      call l0l1();
    } else {
      call l0l0();
    }
  }
}

implementation l1l0() {
  if (*) {
    working0 := iter0;
    assert working0 != working1;
    iter0 := iter0 + 1;
    if (iter0 < end0) {
      call l1l0();
    } else {
      call l0l0();
    }
  } else {
    begin1 := next;
    next := next + workload;
    end1 := next;
    iter1 := begin1;
    if (iter1 < end1) {
      call l1l1();
    } else {
      call l1l0();
    }
  }
}

implementation l0l1() {
  if (*) {
    begin0 := next;
    next := next + workload;
    end0 := next;
    iter0 := begin0;
    if (iter0 < end0) {
      call l1l1();
    } else {
      call l0l1();
    }
  } else {
    working1 := iter1;
    assert working0 != working1;
    iter1 := iter1 + 1;
    if (iter1 < end1) {
      call l0l1();
    } else {
      call l0l0();
    }
  }
}

implementation l1l1() {
  if (*) {
    working0 := iter0;
    assert working0 != working1;
    iter0 := iter0 + 1;
    if (iter0 < end0) {
      call l1l1();
    } else {
      call l0l1();
    }
  } else {
    working1 := iter1;
    assert working0 != working1;
    iter1 := iter1 + 1;
    if (iter1 < end1) {
      call l1l1();
    } else {
      call l1l0();
    }
  }
}
