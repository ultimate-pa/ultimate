// #Safe
// Author: Daniel Dietsch
// Function inliner of BoogiePreprocessor produced 
// wrong declaration information for the IdentifierExpression x in the body of the axiom, 
// s.t. the preprocessed version would lead to a type error.
type ref;
const unique $null : ref;
function $refToBool(x : ref) returns ($ret : bool) { (if x == $null then false else true) }
