/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * @author Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ArrayBoogieType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8089266195576415316L;
	private final int mNumPlaceholders;
	private final BoogieType[] mIndexTypes;
	private final BoogieType mValueType;
	private final BoogieType mRealType;
	private final boolean mIsFinite;

	ArrayBoogieType(final int numPlaceholders, final BoogieType[] indexTypes, final BoogieType valueType) {
		mNumPlaceholders = numPlaceholders;
		mIndexTypes = indexTypes;
		mValueType = valueType;

		boolean changed = false;
		final BoogieType realValueType = valueType.getUnderlyingType();
		if (realValueType != valueType) {
			changed = true;
		}
		BoogieType[] realIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < realIndexTypes.length; i++) {
			realIndexTypes[i] = indexTypes[i].getUnderlyingType();
			if (realIndexTypes[i] != indexTypes[i])
				changed = true;
		}
		if (changed) {
			mRealType = createArrayType(numPlaceholders, realIndexTypes, realValueType);
		} else {
			mRealType = this;
		}
		boolean finite = realValueType.isFinite();
		for (final BoogieType indexType : realIndexTypes) {
			finite &= indexType.isFinite();
		}
		mIsFinite = finite;
	}

	@Override
	protected BoogieType substitutePlaceholders(int depth, BoogieType[] substType) {
		depth += mNumPlaceholders;
		boolean changed = false;
		BoogieType newValueType = mValueType.substitutePlaceholders(depth, substType);
		if (newValueType != mValueType)
			changed = true;
		BoogieType[] newIndexTypes = new BoogieType[mIndexTypes.length];
		for (int i = 0; i < mIndexTypes.length; i++) {
			newIndexTypes[i] = mIndexTypes[i].substitutePlaceholders(depth, substType);
			if (newIndexTypes[i] != mIndexTypes[i])
				changed = true;
		}
		if (changed)
			return createArrayType(mNumPlaceholders, newIndexTypes, newValueType);
		return this;
	}

	@Override
	protected BoogieType incrementPlaceholders(int depth, int incDepth) {
		depth += mNumPlaceholders;
		boolean changed = false;
		BoogieType newValueType = mValueType.incrementPlaceholders(depth, incDepth);
		if (newValueType != mValueType)
			changed = true;
		BoogieType[] newIndexTypes = new BoogieType[mIndexTypes.length];
		for (int i = 0; i < mIndexTypes.length; i++) {
			newIndexTypes[i] = mIndexTypes[i].incrementPlaceholders(depth, incDepth);
			if (newIndexTypes[i] != mIndexTypes[i])
				changed = true;
		}
		if (changed)
			return createArrayType(mNumPlaceholders, newIndexTypes, newValueType);
		return this;
	}

	@Override
	public BoogieType getUnderlyingType() {
		return mRealType;
	}

	/**
	 * Get the number of placeholder (type variables) used in this array type.
	 * 
	 * @return the number of placeholder.
	 */
	public int getNumPlaceholders() {
		return mNumPlaceholders;
	}

	/**
	 * Get the number of indices, i.e. the dimension of the array.
	 * 
	 * @return the number of indices.
	 */
	public int getIndexCount() {
		return mIndexTypes.length;
	}

	/**
	 * Returns the index type, i.e. the type of the index arguments at the given
	 * dimension.
	 * 
	 * @param dim
	 *            the dimension. We must have 0 <= dim < getIndexCount().
	 * @return the index type.
	 */
	public BoogieType getIndexType(int dim) {
		return mIndexTypes[dim];
	}

	/**
	 * Returns the value type of the array, i.e. the type of the elements stored
	 * in the arrray.
	 * 
	 * @return the value type.
	 */
	public BoogieType getValueType() {
		return mValueType;
	}

	/**
	 * Instantiates a generic array type with the given types to produce a
	 * non-generic array type.
	 */
	public ArrayBoogieType instantiate(final BoogieType[] idxTypeInstances, final BoogieType idxValueInstance) {
		assert idxTypeInstances != null;
		assert idxTypeInstances.length == mIndexTypes.length;
		assert idxValueInstance != null;

		final List<BoogieType> newIdxTypes = new ArrayList<BoogieType>();
		final BoogieType[] subst = new BoogieType[getNumPlaceholders()];

		for (int i = 0; i < mIndexTypes.length; ++i) {
			mIndexTypes[i].unify(idxTypeInstances[i], subst);
			newIdxTypes.add(mIndexTypes[i].substitutePlaceholders(subst));
		}
		getValueType().unify(idxValueInstance, subst);
		final BoogieType newValueType = getValueType().substitutePlaceholders(subst);
		return BoogieType.createArrayType(0, newIdxTypes.toArray(new BoogieType[newIdxTypes.size()]), newValueType);
	}

	@Override
	protected boolean unify(int depth, BoogieType other, BoogieType[] substitution) {
		if (other == errorType)
			return true;
		if (!(other instanceof ArrayBoogieType))
			return false;
		ArrayBoogieType type = (ArrayBoogieType) other;
		if (type.mNumPlaceholders != mNumPlaceholders || type.mIndexTypes.length != mIndexTypes.length)
			return false;
		depth += mNumPlaceholders;
		for (int i = 0; i < mIndexTypes.length; i++) {
			if (!mIndexTypes[i].unify(depth, type.mIndexTypes[i], substitution))
				return false;
		}
		return mValueType.unify(depth, type.mValueType, substitution);
	}

	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		minDepth += mNumPlaceholders;
		maxDepth += mNumPlaceholders;
		for (BoogieType t : mIndexTypes) {
			if (t.hasPlaceholder(minDepth, maxDepth))
				return true;
		}
		return mValueType.hasPlaceholder(minDepth, maxDepth);
	}

	@Override
	protected boolean isUnifiableTo(int depth, BoogieType other, ArrayList<BoogieType> subst) {
		if (this == other || other == errorType)
			return true;
		if (other instanceof PlaceholderBoogieType)
			return other.isUnifiableTo(depth, this, subst);
		if (!(other instanceof ArrayBoogieType))
			return false;
		ArrayBoogieType type = (ArrayBoogieType) other;
		if (type.mNumPlaceholders != mNumPlaceholders || type.mIndexTypes.length != mIndexTypes.length)
			return false;
		depth += mNumPlaceholders;
		for (int i = 0; i < mIndexTypes.length; i++) {
			if (!mIndexTypes[i].isUnifiableTo(depth, type.mIndexTypes[i], subst))
				return false;
		}
		return mValueType.isUnifiableTo(depth, type.mValueType, subst);
	}

	/**
	 * Computes a string representation. It uses depth to compute artificial
	 * names for the placeholders.
	 * 
	 * @param depth
	 *            the number of placeholders outside this expression.
	 * @param needParentheses
	 *            true if parentheses should be set for constructed types
	 * @return a string representation of this array type.
	 */
	protected String toString(int depth, boolean needParentheses) {
		StringBuilder sb = new StringBuilder();
		String delim;
		if (needParentheses)
			sb.append("(");
		if (mNumPlaceholders > 0) {
			sb.append("<");
			delim = "";
			for (int i = 0; i < mNumPlaceholders; i++) {
				sb.append(delim).append("$" + (depth + i));
				delim = ",";
			}
			sb.append(">");
		}
		sb.append("[");
		delim = "";
		for (BoogieType iType : mIndexTypes) {
			sb.append(delim).append(iType.toString(depth + mNumPlaceholders, false));
			delim = ",";
		}
		sb.append("]");
		sb.append(mValueType.toString(depth + mNumPlaceholders, false));
		if (needParentheses)
			sb.append(")");
		return sb.toString();
	}

	@Override
	protected ASTType toASTType(ILocation loc, int depth) {
		String[] typeParams = new String[mNumPlaceholders];
		for (int i = 0; i < mNumPlaceholders; i++)
			typeParams[i] = "$" + (depth + i);
		ASTType[] astIndexTypes = new ASTType[mIndexTypes.length];
		for (int i = 0; i < mIndexTypes.length; i++)
			astIndexTypes[i] = mIndexTypes[i].toASTType(loc, depth + mNumPlaceholders);
		ASTType astValueType = mValueType.toASTType(loc, depth + mNumPlaceholders);
		return new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType(loc, this, typeParams, astIndexTypes,
				astValueType);
	}

	@Override
	public boolean isFinite() {
		return mIsFinite;
	}
}
