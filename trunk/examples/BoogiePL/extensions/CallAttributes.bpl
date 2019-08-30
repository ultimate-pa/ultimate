//#Safe
// Ultimate allows attributes on call statements.
//
// 2019-08-30
// Author: dietsch@informatik.uni-freiburg.de

procedure bar () returns (){}

procedure foo () returns ()
{
  call {:some_id "some_string"} bar();
}