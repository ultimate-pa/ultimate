/**
 * Describes an enum given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTExpression;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CEnum extends CType {
    /**
     * Field names.
     */
    private final String[] fNames;
    /**
     * Field values.
     */
    private final IASTExpression[] fValues;
    /**
     * The identifier of this enum set.
     */
    private final String identifier;

    /**
     * Constructor.
     * 
     * @param fNames
     *            field names.
     * @param fValues
     *            field values.
     * @param cDeclSpec
     *            the C declaration used.
     * @param id
     *            this enums identifier.
     */
    public CEnum(IASTDeclSpecifier cDeclSpec, String id, String[] fNames,
            IASTExpression[] fValues) {
        super(cDeclSpec);
        assert fNames.length == fValues.length;
        this.identifier = id;
        this.fNames = fNames;
        this.fValues = fValues;
    }

    /**
     * Get the number of fields in this enum.
     * 
     * @return the number of fields.
     */
    public int getFieldCount() {
        return fNames.length;
    }

    /**
     * Returns the field value.
     * 
     * @param id
     *            the fields id.
     * @return the fields value.
     */
    public IASTExpression getFieldValue(String id) {
        int idx = Arrays.asList(fNames).indexOf(id);
        if (idx < 0) {
            throw new IllegalArgumentException("Field '" + id
                    + "' not in struct!");
        }
        return fValues[idx];
    }

    /**
     * Returns the set of fields in this enum.
     * 
     * @return the set of fields in this enum.
     */
    public String[] getFieldIds() {
        return fNames.clone();
    }

    /**
     * Getter for this enums identifier.
     * 
     * @return this enums identifier.
     */
    public String getIdentifier() {
        return identifier;
    }

    @Override
    public String toString() {
        StringBuilder id = new StringBuilder("ENUM#");
        for (int i = 0; i < getFieldCount(); i++) {
            id.append("?");
            id.append(fNames[i]);
        }
        id.append("#");
        return id.toString();
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CType)) {
            return false;
        }
        CType oType = ((CType)o).getUnderlyingType();
        if (!(oType instanceof CEnum)) {
            return false;
        }
        
        CEnum oEnum = (CEnum)oType;
        if (!(identifier.equals(oEnum.identifier))) {
            return false;
        }
        if (fNames.length != oEnum.fNames.length) {
            return false;
        }
        for (int i = fNames.length - 1; i >= 0; --i) {
            if (!(fNames[i].equals(oEnum.fNames[i]))) {
                return false;
            }
        }
        if (fValues.length != oEnum.fValues.length) {
            return false;
        }
        for (int i = fValues.length - 1; i >= 0; --i) {
            if (!(fValues[i].equals(oEnum.fValues[i]))) {
                return false;
            }
        }
        return true;
    }
}
