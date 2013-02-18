#ifndef STALIN_EXCEPTIONS_HH_
#define STALIN_EXCEPTIONS_HH_

// Include this header so we have a complete exception header
#include <exception>
#include "z3cc.hh"
#include "platformdefs.hh"

/**
 * Class representing an error thrown from Z3. It contains the error code as
 * reported from Z3 (see Z3_error_code enum).
 *
 * This class is flagged with an internal label since it should never leave
 * boundaries of this shared object.
 */
class STALIN_INTERNAL z3error {
  Z3_error_code merrcode;
 public:
  z3error(Z3_error_code errcode) throw();
  ~z3error() throw();
  inline Z3_error_code errorcode() const throw() { return merrcode; }
};

/**
 * Class representing a pending Java Exception or Error. This class does not
 * carry any payload. It is simply used as a replacement for goto or other flow
 * control mechanism.
 *
 * This class is flagged with an internal label since it should never leave
 * boundaries of this shared object.
 */
class STALIN_INTERNAL pendingjavaexc {
 public:
  pendingjavaexc() throw();
  ~pendingjavaexc() throw();
};

#endif
