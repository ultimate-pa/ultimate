/**
 * Describes a pointer given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CPointer extends CType {
    /**
     * The type, this pointer points to.
     */
    public final CType pointsToType;

    /**
     * Constructor.
     * 
     * @param pointsToType
     *            the type, this pointer points to.
     */
    public CPointer(CType pointsToType) {
//        super();
        super(false, false, false, false); //FIXME: integrate those flags
        this.pointsToType = pointsToType;
    }

    @Override
    public String toString() {
        return SFO.POINTER;
    }
    
    @Override
    public boolean equals(Object o) {
    	if (super.equals(o)) //to break a mutual recursion with CStruct -- TODO: is that a general solution??
    		return true;
        if (!(o instanceof CType)) {
            return false;
        }
        CType oType = ((CType)o).getUnderlyingType();
        if (oType instanceof CPointer) {
            return pointsToType.equals(((CPointer)oType).pointsToType);
        }
        else {
            return false;
        }
    }

	@Override
	public boolean isCompatibleWith(CType o) {
		if (o instanceof CPrimitive &&
				((CPrimitive) o).getType() == PRIMITIVE.VOID)
			return true;

		if (super.equals(o)) //to break a mutual recursion with CStruct -- TODO: is that a general solution??
    		return true;
        CType oType = ((CType)o).getUnderlyingType();
        if (oType instanceof CPointer) {
            return pointsToType.isCompatibleWith(((CPointer)oType).pointsToType);
        }
        else {
            return false;
        }
	}
	
	
	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, pointsToType);
	}
}
