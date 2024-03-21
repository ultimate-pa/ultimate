//#Safe
/**
 * Bug: Wrong usage of CHandler.assignOrHavocUnionNeighbours(...)
 * 
 * Writing to a non-heap union must manually havoc neighbouring fields 
 * because their values would not be updated correctly. 
 * The bug is that this also happens when the union is on the heap.
 * 
 * 
 * 2020-12-02
 * Author: dietsch@informatik.uni-freiburg.de
 * 
 */


typedef union
{
    double value;
    struct
    {
        unsigned int lsw;
        unsigned int msw;
    } parts;
} ieee_double_shape_type;

void main()
{
    double inx = 0.0;
    ieee_double_shape_type ew_u;
    ieee_double_shape_type iw_u;

    ew_u.value = (inx);
    iw_u.parts.msw = ew_u.parts.msw;
    iw_u.parts.lsw = ew_u.parts.lsw;

    double res = iw_u.value;

    if (res != inx)
    {
        //@assert \false;
    }
}
