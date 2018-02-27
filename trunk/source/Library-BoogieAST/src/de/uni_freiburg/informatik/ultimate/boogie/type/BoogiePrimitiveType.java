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

public class BoogiePrimitiveType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -1842658349197318623L;
	public static final int BOOL  = -1;
	public static final int INT   = -2;
	public static final int REAL  = -3;
	public static final int ERROR = -42;

	/**
	 * The type code.  If this is >= 0, this is the length and the class
	 * represents a bit vector type of this length.  Otherwise, this is
	 * one of BOOL, INT, REAL, or ERROR.
	 */
	private final int type;

	BoogiePrimitiveType(final int type) {
		this.type = type;
	}

	//@Override
	@Override
	public BoogieType getUnderlyingType() {
		return this;
	}

	//@Override
	@Override
	protected boolean hasPlaceholder(final int minDepth, final int maxDepth) {
		return false;
	}

	//@Override
	@Override
	protected BoogieType incrementPlaceholders(final int depth, final int incDepth) {
		return this;
	}

	//@Override
	@Override
	protected boolean isUnifiableTo(final int depth, final BoogieType other,
			final ArrayList<BoogieType> subst) {
		if (other instanceof BoogiePlaceholderType) {
			return other.isUnifiableTo(depth, this, subst);
		}
		return this == TYPE_ERROR || other == TYPE_ERROR || this == other;
	}

	//@Override
	@Override
	protected BoogieType substitutePlaceholders(final int depth,
			final BoogieType[] substType) {
		return this;
	}

	//@Override
	@Override
	protected String toString(final int depth, final boolean needParentheses) {
		switch (type) {
		case INT:
			return "int";
		case BOOL:
			return "bool";
		case REAL:
		    return "real";
		case ERROR:
			return "*type-error*";
		default:
			return "bv"+type;

		}
	}

	@Override
	protected ASTType toASTType(final ILocation loc, final int depth) {
		return new de.uni_freiburg.informatik.ultimate.boogie.ast.
			PrimitiveType(loc, this, toString(depth, false));
	}

	//@Override
	@Override
	protected boolean unify(final int depth, final BoogieType other,
			final BoogieType[] substitution) {
		return this == TYPE_ERROR || other == TYPE_ERROR || this == other;
	}

	public int getTypeCode() {
		return type;
	}

	@Override
	public boolean isFinite() {
		/* Everything except INT may be finite */
		return type != INT;
	}

}
