/*
 * DD 2016-10-10: 
 * ArrayHandler.handleArraySubscriptExpression(..) throws AssertionError: not outermost 
 */

static const char * decode_one_format()
{
    static const unsigned char * const doux_bytes_to_XXX[0] = {};
           doux_bytes_to_XXX[0][0];
}