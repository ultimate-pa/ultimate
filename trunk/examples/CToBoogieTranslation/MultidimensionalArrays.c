/*
 * DD 2016-10-10: 
 * ArrayHandler.handleArraySubscriptExpression(..) throws AssertionError: not outermost 
 */

int main()
{
    static const unsigned char * const doux_bytes_to_XXX[0] = {};
           doux_bytes_to_XXX[0][0];
}