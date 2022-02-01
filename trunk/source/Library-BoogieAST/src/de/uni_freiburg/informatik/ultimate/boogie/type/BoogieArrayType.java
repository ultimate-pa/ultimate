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

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class BoogieArrayType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -8089266195576415316L;
	private final int numPlaceholders;
	private final BoogieType[] indexTypes;
	private final BoogieType valueType;
	private final BoogieType realType;
	private final boolean isFinite;

	BoogieArrayType(final int numPlaceholders, final BoogieType[] indexTypes,
			final BoogieType valueType) {
		this.numPlaceholders = numPlaceholders;
		this.indexTypes = indexTypes;
		this.valueType = valueType;

		boolean changed = false;
		final BoogieType   realValueType = valueType.getUnderlyingType();
		if (realValueType != valueType) {
			changed = true;
		}
		final BoogieType[] realIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < realIndexTypes.length; i++) {
			realIndexTypes[i] = indexTypes[i].getUnderlyingType();
			if (realIndexTypes[i] != indexTypes[i]) {
				changed = true;
			}
		}
		if (changed) {
			realType = createArrayType(numPlaceholders, realIndexTypes, realValueType);
		} else {
			realType = this;
		}
		boolean finite = realValueType.isFinite();
		for (final BoogieType indexType : realIndexTypes) {
			finite &= indexType.isFinite();
		}
		isFinite = finite;
	}


	//@Override
	@Override
	protected BoogieType substitutePlaceholders(int depth, final BoogieType[] substType) {
		depth += numPlaceholders;
		boolean changed = false;
		final BoogieType newValueType = valueType.substitutePlaceholders(depth, substType);
		if (newValueType != valueType) {
			changed = true;
		}
		final BoogieType[] newIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < indexTypes.length; i++) {
			newIndexTypes[i] = indexTypes[i].substitutePlaceholders(depth, substType);
			if (newIndexTypes[i] != indexTypes[i]) {
				changed = true;
			}
		}
		if (changed) {
			return createArrayType(numPlaceholders, newIndexTypes, newValueType);
		}
		return this;
	}

	//@Override
	@Override
	protected BoogieType incrementPlaceholders(int depth, final int incDepth) {
		depth += numPlaceholders;
		boolean changed = false;
		final BoogieType newValueType = valueType.incrementPlaceholders(depth, incDepth);
		if (newValueType != valueType) {
			changed = true;
		}
		final BoogieType[] newIndexTypes = new BoogieType[indexTypes.length];
		for (int i = 0; i < indexTypes.length; i++) {
			newIndexTypes[i] = indexTypes[i].incrementPlaceholders(depth, incDepth);
			if (newIndexTypes[i] != indexTypes[i]) {
				changed = true;
			}
		}
		if (changed) {
			return createArrayType(numPlaceholders, newIndexTypes, newValueType);
		}
		return this;
	}

	//@Override
	@Override
	public BoogieType getUnderlyingType() {
		return realType;
	}


	/**
	 * Get the number of placeholder (type variables) used in this array type.
	 * @return the number of placeholder.
	 */
	public int getNumPlaceholders() {
		return numPlaceholders;
	}

	/**
	 * Get the number of indices, i.e. the dimension of the array.
	 * @return the number of indices.
	 */
	public int getIndexCount() {
		return indexTypes.length;
	}

	/**
	 * Returns the index type, i.e. the type of the index
	 * arguments at the given dimension.
	 * @param dim the dimension. We must have 0 <= dim < getIndexCount().
	 * @return the index type.
	 */
	public BoogieType getIndexType(final int dim) {
		return indexTypes[dim];
	}

	/**
	 * Returns the value type of the array, i.e. the type of the elements stored
	 * in the arrray.
	 * @return the value type.
	 */
	public BoogieType getValueType() {
		return valueType;
	}


	//@Override
	@Override
	protected boolean unify(int depth, final BoogieType other, final BoogieType[] substitution) {
		if (other == TYPE_ERROR) {
			return true;
		}
		if (!(other instanceof BoogieArrayType)) {
			return false;
		}
		final BoogieArrayType type = (BoogieArrayType) other;
		if (type.numPlaceholders != numPlaceholders
			|| type.indexTypes.length != indexTypes.length) {
			return false;
		}
		depth += numPlaceholders;
		for (int i = 0; i < indexTypes.length; i++) {
			if (!indexTypes[i].unify(depth, type.indexTypes[i], substitution)) {
				return false;
			}
		}
		return valueType.unify(depth, type.valueType, substitution);
	}

	@Override
	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		minDepth += numPlaceholders;
		maxDepth += numPlaceholders;
		for (final BoogieType t : indexTypes) {
			if (t.hasPlaceholder(minDepth, maxDepth)) {
				return true;
			}
		}
		return valueType.hasPlaceholder(minDepth, maxDepth);
	}

	//@Override
	@Override
	protected boolean isUnifiableTo(int depth, final BoogieType other, final ArrayList<BoogieType> subst) {
		if (this == other || other == TYPE_ERROR) {
			return true;
		}
		if (other instanceof BoogiePlaceholderType) {
			return other.isUnifiableTo(depth, this, subst);
		}
		if (!(other instanceof BoogieArrayType)) {
			return false;
		}
		final BoogieArrayType type = (BoogieArrayType) other;
		if (type.numPlaceholders != numPlaceholders
			|| type.indexTypes.length != indexTypes.length) {
			return false;
		}
		depth += numPlaceholders;
		for (int i = 0; i < indexTypes.length; i++) {
			if (!indexTypes[i].isUnifiableTo(depth, type.indexTypes[i], subst)) {
				return false;
			}
		}
		return valueType.isUnifiableTo(depth, type.valueType, subst);
	}

	/**
	 * Computes a string representation.  It uses depth to compute artificial
	 * names for the placeholders.
	 * @param depth the number of placeholders outside this expression.
	 * @param needParentheses true if parentheses should be set for constructed types
	 * @return a string representation of this array type.
	 */
	@Override
	protected String toString(final int depth, final boolean needParentheses) {
		final StringBuilder sb = new StringBuilder();
		String delim;
		if (needParentheses) {
			sb.append("(");
		}
		if (numPlaceholders > 0) {
			sb.append("<");
			delim ="";
			for (int i = 0; i < numPlaceholders; i++) {
				sb.append(delim).append("$"+(depth+i));
				delim = ",";
			}
			sb.append(">");
		}
		sb.append("[");
		delim = "";
		for (final BoogieType iType : indexTypes) {
			sb.append(delim).append(iType.toString(depth+numPlaceholders, false));
			delim = ",";
		}
		sb.append("]");
		sb.append(valueType.toString(depth+numPlaceholders, false));
		if (needParentheses) {
			sb.append(")");
		}
		return sb.toString();
	}

	@Override
	protected ASTType toASTType(final ILocation loc, final int depth) {
		final String[] typeParams = new String[numPlaceholders];
		for (int i = 0; i < numPlaceholders; i++) {
			typeParams[i] = "$"+(depth+i);
		}
		final ASTType[] astIndexTypes = new ASTType[indexTypes.length];
		for (int i = 0; i < indexTypes.length; i++) {
			astIndexTypes[i] = indexTypes[i].toASTType(loc, depth + numPlaceholders);
		}
		final ASTType astValueType = valueType.toASTType(loc, depth + numPlaceholders);
		return new de.uni_freiburg.informatik.ultimate.boogie.ast.
			ArrayType(loc, this, typeParams, astIndexTypes, astValueType);
	}

	//@Override
	@Override
	public boolean isFinite() {
		return isFinite;
	}
}
