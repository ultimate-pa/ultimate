/**
 * Describes a struct given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Arrays;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CStruct extends CType {
    /**
     * Field names.
     */
    private final String[] fNames;
    /**
     * Field types.
     */
    private final CType[] fTypes;
    
    /**
     * Indicates if this represents an incomplete type.
     */
    private final boolean isIncomplete;

    public boolean isIncomplete() {
		return isIncomplete;
	}

	/**
     * Constructor.
     * 
     * @param fNames
     *            field names.
     * @param fTypes
     *            field types.
     * @param cDeclSpec
     *            the C declaration used.
     */
    public CStruct(IASTDeclSpecifier cDeclSpec, String[] fNames,
            CType[] fTypes) {
        super(cDeclSpec);
        this.fNames = fNames;
        this.fTypes = fTypes;
        this.isIncomplete = false;
    }
    
    public CStruct(IASTDeclSpecifier cDeclSpec, boolean isIncomplete) {
        super(cDeclSpec);
        if (!isIncomplete) {
        	throw new AssertionError("use different constructor for non-incomplete types");
        }
        this.fNames = null;
        this.fTypes = null;
        this.isIncomplete = isIncomplete;
    }

    /**
     * Get the number of fields in this struct.
     * 
     * @return the number of fields.
     */
    public int getFieldCount() {
        return fNames.length;
    }

    /**
     * Returns the field type, i.e. the type of the field at the given index.
     * 
     * @param id
     *            the fields id.
     * @return the field type.
     */
    public CType getFieldType(String id) {
        int idx = Arrays.asList(fNames).indexOf(id);
        if (idx < 0) {
            throw new IllegalArgumentException("Field '" + id
                    + "' not in struct!");
        }
        return fTypes[idx];
    }

    /**
     * Getter for all field types, orderd according to occurance in C code!
     * 
     * @return the types of this strut's fields.
     */
    public CType[] getFieldTypes() {
        return fTypes;
    }

    /**
     * Returns the set of fields in this struct.
     * 
     * @return the set of fields in this struct.
     */
    public String[] getFieldIds() {
        return fNames.clone();
    }

    @Override
    public String toString() {
    	if (isIncomplete) {
    		return "STRUCT#~incomplete";
    	} else {
    		StringBuilder id = new StringBuilder("STRUCT#");
    		for (int i = 0; i < getFieldCount(); i++) {
    			id.append("?");
    			id.append(fNames[i]);
    			id.append("~");
    			id.append(fTypes[i].toString());
    		}
    		id.append("#");
    		return id.toString();
    	}
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CType)) {
            return false;
        }
        CType oType = ((CType)o).getUnderlyingType();
        if (!(oType instanceof CStruct)) {
            return false;
        }
        
        CStruct oStruct = (CStruct)oType;
        if (fNames.length != oStruct.fNames.length) {
            return false;
        }
        for (int i = fNames.length - 1; i >= 0; ++i) {
            if (!(fNames[i].equals(oStruct.fNames[i]))) {
                return false;
            }
        }
        if (fTypes.length != oStruct.fTypes.length) {
            return false;
        }
        for (int i = fTypes.length - 1; i >= 0; ++i) {
            if (!(fTypes[i].equals(oStruct.fTypes[i]))) {
                return false;
            }
        }
        return true;
    }
}
