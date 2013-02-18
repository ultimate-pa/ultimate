#include "exceptions.hh"

z3error::z3error(Z3_error_code errcode) throw() : merrcode(errcode) {}

z3error::~z3error() throw() {}

pendingjavaexc::pendingjavaexc() throw() {}

pendingjavaexc::~pendingjavaexc() throw() {}
