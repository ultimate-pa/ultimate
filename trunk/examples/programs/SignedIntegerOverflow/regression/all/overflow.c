//#Safe
// This program clamps an integer and should not produce an overflow. 
// Nevertheless, we receive a counterexample with 
// -tc AutomizerC.xml 
// -s settings/default/automizer/svcomp-Overflow-32bit-Automizer_Default.epf
// on 0.1.24-b5fb152
// 
// We found a FailurePath: 
// [L5]        x >= 1000000 ? 1000000 : x + 1
//       VAL   [\old(x)=-2147483650, x=-2147483650]
// [L5]        x + 1
//       VAL   [\old(x)=-2147483650, x=-2147483650]
//
// This is probably a bug in library mode where parameters of functions are not assumed to be in range although the option is set. 
//

int foo(int x) { 
  return x >= 1000000 ? 1000000 : x + 1;
}