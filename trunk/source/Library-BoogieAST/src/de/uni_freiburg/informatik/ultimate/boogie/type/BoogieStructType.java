/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Class representing a struct type in Boogie.
 */
package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Class representing a struct type.
 * 
 * @author Markus Lindenmann
 * @date 11.09.2012
 */
public class BoogieStructType extends BoogieType {
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
    public BoogieStructType(String[] fNames, BoogieType[] fTypes) {
        assert fNames.length == fTypes.length;
        this.fNames = fNames;
        this.fTypes = fTypes;
        boolean changed = false;
        boolean finite = true;
        final BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].getUnderlyingType();
            if (newFTypes[i] != fTypes[i]) {
				changed = true;
			}
            if (finite && fTypes[i].isFinite()) {
				finite = false;
			}
        }
        if (changed) {
			realType = createStructType(fNames, newFTypes);
		} else {
			realType = this;
		}
        isFinite = finite;
    }

    @Override
    protected BoogieType substitutePlaceholders(int depth,
            BoogieType[] substType) {
        if (getFieldCount() == 0) {
			return this;
		}
        final BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        boolean changed = false;
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].substitutePlaceholders(depth, substType);
            if (newFTypes[i] != fTypes[i]) {
				changed = true;
			}
        }
        if (!changed) {
			return this;
		}
        return createStructType(fNames, newFTypes);
    }

    @Override
    protected BoogieType incrementPlaceholders(int depth, int incDepth) {
        if (getFieldCount() == 0) {
			return this;
		}
        final BoogieType[] newFTypes = new BoogieType[getFieldCount()];
        boolean changed = false;
        for (int i = 0; i < getFieldCount(); i++) {
            newFTypes[i] = fTypes[i].incrementPlaceholders(depth, incDepth);
            if (newFTypes[i] != fTypes[i]) {
				changed = true;
			}
        }
        if (!changed) {
			return this;
		}
        return createStructType(fNames, fTypes);
    }

    @Override
    public BoogieType getUnderlyingType() {
        return realType;
    }

    @Override
    protected boolean unify(int depth, BoogieType other,
            BoogieType[] substitution) {
        if (!(other instanceof BoogieStructType)) {
			return false;
		}
        final BoogieStructType type = (BoogieStructType) other;
        if (isFinite() != type.isFinite()) {
			return false;
		}
        for (final String f : fNames) {
            if (!getFieldType(f).unify(depth, type.getFieldType(f),
                    substitution)) {
				return false;
			}
        }
        return true;
    }

    @Override
    protected boolean hasPlaceholder(int minDepth, int maxDepth) {
        for (final BoogieType t : fTypes) {
            if (t.hasPlaceholder(minDepth, maxDepth)) {
				return true;
			}
        }
        return false;
    }

    @Override
    protected boolean isUnifiableTo(int depth, BoogieType other,
            ArrayList<BoogieType> subst) {
        if (this == other || other == TYPE_ERROR) {
			return true;
		}
        if (!(other instanceof BoogieStructType)) {
			return false;
		}
        final BoogieStructType type = (BoogieStructType) other;
        if (isFinite() != type.isFinite()) {
			return false;
		}
        for (final String f : fNames) {
            if (!getFieldType(f).isUnifiableTo(depth, type.getFieldType(f),
                    subst)) {
				return false;
			}
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
        final int idx = Arrays.asList(fNames).indexOf(id);
        if (idx < 0) {
            throw new IllegalArgumentException("Field '" + id
                    + "' not in struct!");
        }
        return fTypes[idx];
    }

    /**
     * Returns the type of the field at the given index.
     * 
     * @param idx
     *            the fields index.
     * @return the field type.
     */
    public BoogieType getFieldType(int idx) {
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
        final StringBuilder sb = new StringBuilder();
        if (needParentheses) {
			sb.append("(");
		}
        sb.append("{ ");
        String comma = "";
        for (int i = 0; i < getFieldCount(); i++) {
            sb.append(comma);
            sb.append(fNames[i]).append(":");
            sb.append(fTypes[i].toString(depth + 1, false));
            comma = ", ";
        }
        sb.append(" }");
        if (needParentheses) {
			sb.append(")");
		}
        return sb.toString();
    }
    
	@Override
	protected ASTType toASTType(ILocation loc, int depth) {
		final VarList[] varlist = new VarList[fNames.length];
		for (int i = 0; i < fNames.length; i++) {
			varlist[i] = new VarList(loc, new String[] { fNames[i] }, 
					fTypes[i].toASTType(loc, depth));
		}
		return new de.uni_freiburg.informatik.ultimate.boogie.ast.
			StructType(loc, this, varlist);
	}
	
    @Override
    public boolean isFinite() {
        if (realType != this) {
			return realType.isFinite();
		}
        return isFinite;
    }
}
