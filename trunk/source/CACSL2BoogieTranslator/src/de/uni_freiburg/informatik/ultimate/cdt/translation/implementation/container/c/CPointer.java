/**
 * Describes a pointer given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

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
        super(pointsToType.cDeclSpec);
        this.pointsToType = pointsToType;
    }

    @Override
    public String toString() {
        return SFO.POINTER;
    }
}
