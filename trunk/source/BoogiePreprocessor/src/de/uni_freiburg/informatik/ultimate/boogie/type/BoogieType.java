/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * The base class for all Boogie types. The type instances are immutable.
 * 
 * @author hoenicke
 * 
 */
public abstract class BoogieType implements IBoogieType {
    /**
     * long serialVersionUID
     */
    private static final long serialVersionUID = -1366978000551630241L;
    private final static ArrayList<PlaceholderType> PLACEHOLDER_TYPES = new ArrayList<PlaceholderType>();
    private final static ArrayList<PrimitiveType> BITVECTOR_TYPES = new ArrayList<PrimitiveType>();
    private final static UnifyHash<BoogieType> GLOBAL_TYPES = new UnifyHash<BoogieType>();
    
    public final static PrimitiveType TYPE_INT = new PrimitiveType(
            PrimitiveType.INT);
    public final static PrimitiveType TYPE_REAL = new PrimitiveType(
            PrimitiveType.REAL);
    public final static PrimitiveType TYPE_BOOL = new PrimitiveType(
            PrimitiveType.BOOL);
    public final static PrimitiveType TYPE_ERROR = new PrimitiveType(
            PrimitiveType.ERROR);

    /**
     * Create a bit vector type; reuses an old instance if it already exists.
     * 
     * @param len
     *            the number of bits in this type
     * @return the bit vector type.
     */
    public static BoogieType createBitvectorType(int len) {
        for (int j = BITVECTOR_TYPES.size(); j <= len; j++) {
            BITVECTOR_TYPES.add(new PrimitiveType(j));
        }
        return BITVECTOR_TYPES.get(len);
    }

    /**
     * Create a new placeholder type; reuses an old instance if it already
     * exists. A placeholder is a type variable and is represented by the number
     * giving the position of the scope (de Bruijn's normal form). The
     * placeholders are numbered from inside to outside and in the same scope
     * from left to right. For example the type <code>
     * 	  &lt;x,y&gt;[&lt;z&gt;[x, y, z]y, x, y]x
     * </code> is represented as <code>
     *    &lt;2&gt;[&lt;1&gt;[1,2,0]2, 0, 1]0
     * </code> This weird numbering makes it easy to substitute the outermost
     * placeholders.
     * 
     * @param i
     *            the index of the typevar argument.
     * @return the placeholder type.
     */
    public static BoogieType createPlaceholderType(int i) {
        for (int j = PLACEHOLDER_TYPES.size(); j <= i; j++) {
            PLACEHOLDER_TYPES.add(new PlaceholderType(j));
        }
        return PLACEHOLDER_TYPES.get(i);
    }

    /**
     * Create a new constructed type; reuses an old instance if it already
     * exists. A constructed type is build from a TypeConstructor and some type
     * arguments.
     * 
     * @param constr
     *            the type constructor.
     * @param params
     *            the arguments. The length must be equal to
     *            constr.getParamCount().
     * @return The constructed type.
     */
    /*
     * @ requires constr.getParamCount() == params.length;
     * 
     * @
     */
    public static ConstructedType createConstructedType(TypeConstructor constr,
            BoogieType... params) {
        assert (constr.getParamCount() == params.length);
        int hashcode = constr.hashCode();
        for (int i = 0; i < params.length; i++) {
            hashcode = hashcode * 31 + params[i].hashCode();
        }
        for (final BoogieType t : GLOBAL_TYPES.iterateHashCode(hashcode)) {
            if (!(t instanceof ConstructedType)) {
				continue;
			}
            final ConstructedType c = (ConstructedType) t;
            if (c.getConstr() != constr) {
				continue;
			}
            for (int i = 0; true; i++) {
                if (i == params.length) {
					return c;
				}
                if (params[i] != c.getParameter(i)) {
					break;
				}
            }
        }
        final ConstructedType newType = new ConstructedType(constr, params);
        GLOBAL_TYPES.put(hashcode, newType);
        return newType;
    }

    private static BoogieType[] EMPTY = new BoogieType[0];

    /**
     * Creates a new constructed type without parameters; reuses an old instance
     * if it already exists. A constructed type is build from a TypeConstructor
     * and some type arguments.
     * 
     * @param constr
     *            the type constructor, constr.getParamCount() must be 0.
     * @return The constructed type.
     */
    public static ConstructedType createConstructedType(TypeConstructor constr) {
        return createConstructedType(constr, EMPTY);
    }

    /**
     * Creates a new array type; reuses an old instance if it already exists. An
     * array has a number of placeholders (type variables), some index types and
     * a value type.
     * 
     * @param numPlaceholders
     *            number of declared placeholders
     * @param indexTypes
     *            the types used in the array indices. One entry for each
     *            dimension of the array.
     * @param valueType
     *            the type of the values stored in the array.
     * @return The array type.
     */
    public static ArrayType createArrayType(int numPlaceholders,
            BoogieType[] indexTypes, BoogieType valueType) {
        int hashcode = numPlaceholders;
        for (int i = 0; i < indexTypes.length; i++) {
            hashcode = hashcode * 31 + indexTypes[i].hashCode();
        }
        hashcode = hashcode * 31 + valueType.hashCode();
        for (final BoogieType t : GLOBAL_TYPES.iterateHashCode(hashcode)) {
            if (!(t instanceof ArrayType)) {
				continue;
			}
            final ArrayType arrType = (ArrayType) t;
            if (arrType.getNumPlaceholders() != numPlaceholders
                    || arrType.getIndexCount() != indexTypes.length
                    || arrType.getValueType() != valueType) {
				continue;
			}
            for (int i = 0; true; i++) {
                if (i == indexTypes.length) {
					return arrType;
				}
                if (indexTypes[i] != arrType.getIndexType(i)) {
					break;
				}
            }
        }
        final ArrayType newType = new ArrayType(numPlaceholders, indexTypes,
                valueType);
        GLOBAL_TYPES.put(hashcode, newType);
        return newType;
    }

    /**
     * Creates a new struct type; reuses an old instance if it already exists.
     * 
     * @param fNames
     *            Field names.
     * @param fTypes
     *            Field types.
     * @return The struct type.
     */
    public static StructType createStructType(String[] fNames,
            BoogieType[] fTypes) {
        assert fNames.length == fTypes.length;
        int hashCode = 1031;
        for (int i = 0; i < fNames.length; i++) {
            hashCode = hashCode * 31 + fTypes[i].hashCode();
            hashCode = hashCode * 31 + fNames[i].hashCode();
        }
        outer: for (final BoogieType t : GLOBAL_TYPES.iterateHashCode(hashCode)) {
            if (!(t instanceof StructType)) {
				continue;
			}
            final StructType strType = (StructType) t;
            if (strType.getFieldCount() != fNames.length) {
				continue;
			}
            if (!Arrays.equals(fNames, strType.getFieldIds())) {
				break;
			}
            for (int i = 0; i < fNames.length; i++) {
                if (fTypes[i] != strType.getFieldType(fNames[i])) {
					break outer;
				}
            }
            return strType;
        }
        // no match found -> create a new one
        final StructType newType = new StructType(fNames, fTypes);
        GLOBAL_TYPES.put(hashCode, newType);
        return newType;
    }

    /**
     * Substitute placeholders in given type. This is called recursively to
     * substitute.
     * 
     * @param depth
     *            the depth into the type to substitute. Normally 0.
     * @param substType
     *            The types to substitute.
     * @return The substituted type
     */
    protected abstract BoogieType substitutePlaceholders(int depth,
            BoogieType[] substType);

    /**
     * Increment all placeholders in given type. This is used to adapt the place
     * holders in a substitution if it is applied deep inside another type.
     * 
     * @param depth
     *            the depth into the type to substitute. Normally 0.
     * @param incDepth
     *            the depth by which to increment placeholders.
     * @return The type with incremented placeholders.
     */
    protected abstract BoogieType incrementPlaceholders(int depth, int incDepth);

    /**
     * Substitute placeholders in given type. This is called recursively to
     * substitute.
     * 
     * @param substType
     *            The types to substitute.
     * @return The substituted type
     */
    public BoogieType substitutePlaceholders(BoogieType[] substType) {
        return substitutePlaceholders(0, substType);
    }

    /**
     * Returns the type as which this type was ultimately defined.
     * 
     * @return The underlying type (this if it is a basic or a free type).
     */
    public abstract BoogieType getUnderlyingType();

    /**
     * Returns true if this type is a synonym of the give object o. This can
     * only be the case if o is a BoogieType.
     */
    @Override
	public boolean equals(Object o) {
        return (o instanceof BoogieType)
                && getUnderlyingType() == ((BoogieType) o).getUnderlyingType();
    }

    /**
     * Unify the this type (which contains Placeholders) with another type
     * (which doesn't) and compute a suitable substitution.
     * 
     * @param depth
     *            the depth into the type to unify. Normally 0.
     * @param other
     *            the other type
     * @param substitution
     *            the substitution array. should be initialized to null and
     *            contains a suitable substitution.
     * @returns true if unification was successful, false on type mismatch.
     */
    protected abstract boolean unify(int depth, BoogieType other,
            BoogieType[] substitution);

    /**
     * Unify the this type (which contains Placeholders) with another type
     * (which doesn't) and compute a suitable substitution.
     * 
     * @param other
     *            the other type
     * @param substitution
     *            the substitution array. should be initialized to null and
     *            contains a suitable substitution.
     * @returns true if unification was successful, false on type mismatch.
     */
    public boolean unify(BoogieType other, BoogieType[] substitution) {
        return getUnderlyingType().unify(0, other.getUnderlyingType(),
                substitution);
    }

    /**
     * Determines if this type contains a placeholder to the given depth range.
     * Needed for the occur check in unification.
     * 
     * @param minDepth
     *            the minimum index of the placeholder. Measured from the start
     *            of this type.
     * @param maxDepth
     *            the maximum index of the placeholder.
     * @return true if placeholder with given depth occurs in this type.
     */
    protected abstract boolean hasPlaceholder(int minDepth, int maxDepth);

    /**
     * Check whether this and the other type are unifiable by replacing
     * Placeholders. This is symmetric, i.e. place holders are considered in
     * both types.
     * 
     * @param depth
     *            the depth
     * @param other
     *            the other type
     * @param subst
     *            the partial substitution
     * @returns true if unification was successful, false on type mismatch.
     */
    protected abstract boolean isUnifiableTo(int depth, BoogieType other,
            ArrayList<BoogieType> subst);

    /**
     * Check whether this and the other type are unifiable by replacing
     * Placeholders. This is symmetric, i.e. place holders are considered in
     * both types.
     * 
     * @param other
     *            the other type
     * @returns true if unification was successful, false on type mismatch.
     */
    public boolean isUnifiableTo(BoogieType other) {
        final BoogieType realThis = getUnderlyingType();
        final BoogieType realOther = other.getUnderlyingType();
        return (realThis.isUnifiableTo(0, realOther,
                new ArrayList<BoogieType>()));
    }

    /**
     * Computes a string representation. It uses depth to compute artificial
     * names for the placeholders.
     * 
     * @param depth
     *            the number of placeholders outside this expression.
     * @param needParentheses
     *            true if parentheses should be set for constructed types
     * @return a string representation of this type.
     */
    protected abstract String toString(int depth, boolean needParentheses);

    /**
     * Computes an AST type representation. It uses depth to compute artificial
     * names for the placeholders.
     * 
     * @param depth
     *            the number of placeholders outside this expression.
     * @param needParentheses
     *            true if parentheses should be set for constructed types
     * @return a string representation of this type.
     */
    protected abstract ASTType toASTType(ILocation loc, int depth);

    /**
     * Computes a string representation.
     * 
     * @return a string representation of this type.
     */
    @Override
	public String toString() {
        return toString(0, false);
    }

    /**
     * Computes an AST type representation.
     * 
     * @return the AST type representation of this type.
     */
    public ASTType toASTType(ILocation loc) {
        return toASTType(loc, 0);
    }

    /**
     * Returns whether the type has finitely many elements.
     * 
     * @return true if this type has finitely many elements, or if it is
     *         unknown.
     */
    public abstract boolean isFinite();
}
