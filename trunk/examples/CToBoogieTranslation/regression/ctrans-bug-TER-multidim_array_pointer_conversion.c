/*
2017-12-11  DD / CR 

Example that produces a type error result during preprocessing due to multi-dimensional array and conversion to pointer. 

 * Results from de.uni_freiburg.informatik.ultimate.boogie.preprocessor:
  - TypeErrorResult [Line: 7]: Type Error
    Wrong parameter type at index 2: CallStatement[false,[],data2hex,[BitvecLiteral[0,32],BitvecLiteral[0,32],ArrayAccessExpression[IdentifierExpression[~str~2,<LOCAL,layoutFirmwareHash>],[BitvecLiteral[0,32]]]]]


*/
extern void data2hex(int  data, int len, int *str);

void main()
{
  int str[1][1];

  data2hex(0, 0, str[0]);
}

