/**
 * Class representing a struct type in Boogie.
 */
package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Class representing a struct type.
 * 
 * @author Markus Lindenmann
 * @date 11.09.2012
 */
public class StructType extends BoogieType {
    /**
     * Serial unique identifier.
     */
    private static final long serialVersionUID = -1467920629539012234L;
    /**
     * Whether this type is finite or not.
     */
    private final boolean isFinite;
    /**
     * Field names.
     */
    private final String[] fNames;
    /**
     * Field types.
     */
    private final BoogieType[] fTypes;
    /**
     * The underlying real type.
     */
    private final BoogieType realType;

    /**
     * Constructor.
     * 
     * @param fNames
     *            a list of field names.
     * @param fTypes
     *            a list of type names.
     */
    public StructType(String[] fNames, BoogieType[] fTypes) {
        assert fNames.length == fTypes.length;
        this.fNames = fNames;
        this.fTypes = fTypes;
        boolean changed = false;
        boolean finite = true;
        BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].getUnderlyingType();
            if (newFTypes[i] != fTypes[i])
                changed = true;
            if (finite && fTypes[i].isFinite())
                finite = false;
        }
        if (changed)
            realType = createStructType(fNames, newFTypes);
        else
            realType = this;
        this.isFinite = finite;
    }

    @Override
    protected BoogieType substitutePlaceholders(int depth,
            BoogieType[] substType) {
        if (getFieldCount() == 0)
            return this;
        BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        boolean changed = false;
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].substitutePlaceholders(depth, substType);
            if (newFTypes[i] != fTypes[i])
                changed = true;
        }
        if (!changed)
            return this;
        return createStructType(fNames, newFTypes);
    }

    @Override
    protected BoogieType incrementPlaceholders(int depth, int incDepth) {
        if (getFieldCount() == 0)
            return this;
        BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        boolean changed = false;
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].incrementPlaceholders(depth, incDepth);
            if (newFTypes[i] != fTypes[i])
                changed = true;
        }
        if (!changed)
            return this;
        return createStructType(fNames, fTypes);
    }

    @Override
    public BoogieType getUnderlyingType() {
        return realType;
    }

    @Override
    protected boolean unify(int depth, BoogieType other,
            BoogieType[] substitution) {
        if (!(other instanceof StructType))
            return false;
        StructType type = (StructType) other;
        if (isFinite() != type.isFinite())
            return false;
        for (String f : fNames) {
            if (!getFieldType(f).unify(depth, type.getFieldType(f),
                    substitution))
                return false;
        }
        return true;
    }

    @Override
    protected boolean hasPlaceholder(int minDepth, int maxDepth) {
        for (BoogieType t : fTypes) {
            if (t.hasPlaceholder(minDepth, maxDepth))
                return true;
        }
        return false;
    }

    @Override
    protected boolean isUnifiableTo(int depth, BoogieType other,
            ArrayList<BoogieType> subst) {
        if (this == other || other == errorType)
            return true;
        if (!(other instanceof StructType))
            return false;
        StructType type = (StructType) other;
        if (isFinite() != type.isFinite())
            return false;
        for (String f : fNames) {
            if (!getFieldType(f).isUnifiableTo(depth, type.getFieldType(f),
                    subst))
                return false;
        }
        return true;
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
    public BoogieType getFieldType(String id) {
        int idx = Arrays.asList(fNames).indexOf(id);
        if (idx < 0) {
            throw new IllegalArgumentException("Field '" + id
                    + "' not in struct!");
        }
        return fTypes[idx];
    }

    /**
     * Returns the set of fields in this struct.
     * 
     * @return the set of fields in this struct.
     */
    public String[] getFieldIds() {
        return fNames.clone();
    }

    /**
     * Returns the set of types in this struct.
     * 
     * @return the set of types in this struct.
     */
    public BoogieType[] getFieldTypes() {
        return fTypes.clone();
    }
    
    @Override
    protected String toString(int depth, boolean needParentheses) {
        StringBuilder sb = new StringBuilder();
        if (needParentheses)
            sb.append("(");
        sb.append("{ ");
        String comma = "";
        for (int i = 0; i < getFieldCount(); i++) {
            sb.append(comma);
            sb.append(fNames[i]).append(":");
            sb.append(fTypes[i].toString(depth + 1, false));
            comma = ", ";
        }
        sb.append(" }");
        if (needParentheses)
            sb.append(")");
        return sb.toString();
    }

    @Override
    public boolean isFinite() {
        if (realType != this)
            return realType.isFinite();
        return this.isFinite;
    }
}
