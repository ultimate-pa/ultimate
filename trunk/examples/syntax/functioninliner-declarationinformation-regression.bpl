// #Safe
// Author: Daniel Dietsch
// Function inliner of BoogiePreprocessor produced 
// wrong declaration information for the IdentifierExpression x in the body of the axiom, 
// s.t. the preprocessed version would lead to a type error.
function $intToBool(x:int) returns ($ret:bool) { (if x == 0 then false else true) }
