//#Safe
/**
 * This test program includes a named header file that is searched for in an
 * implementation-defined manner (see C standard, section 6.10.2):
 *
 *   # include <h-char-sequence> new-line
 *   # include "q-char-sequence" new-line
 *
 * The first directive searches a sequence of implementation-defined places for
 * a header identified uniquely by the specified sequence between the '<' and
 * '>' delimiters. The second directive causes the replacement of that
 * directive by the entire contents of the source file identified by the
 * specified sequence between the '"' delimiters. The named source file is
 * searched for in an implementation-defined manner.
 *
 * As usual, a C preprocessor searches for the named source file first in the
 * directory containing the current file, then in the same directories
 * specified with a sequence between the '<' and '>' delimiters.
 */

#include <directoryHeaderOne.h>
#include <directoryHeaderTwo.h>
#include <additionalHeader.h>

int main(void)
{
    ret_t funcOneRet = funcFromDirectoryHeaderOne();
    int funcOneVal = funcOneRet.code;
    //@ assert(funcOneVal == 2);
    int funcTwoVal = funcFromDirectoryHeaderTwo();
    //@ assert(funcTwoVal == 4);
    //@ assert(groundTruth == 17);
    return funcOneVal + funcTwoVal + groundTruth;
}
