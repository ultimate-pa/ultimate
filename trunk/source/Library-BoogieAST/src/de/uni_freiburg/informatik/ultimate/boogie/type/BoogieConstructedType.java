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
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A Constructed type is a
 * @author hoenicke
 *
 */
public class BoogieConstructedType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -2227100606701950977L;
	private final BoogieTypeConstructor constr;
	private final BoogieType[] parameters;
	private final BoogieType realType;

	BoogieConstructedType(final BoogieTypeConstructor c, final BoogieType[] parameters) {
		constr = c;
		this.parameters = parameters;

		boolean changed = false;
		final BoogieType[] realParameters = new BoogieType[parameters.length];
		for (int i = 0; i < realParameters.length; i++) {
			realParameters[i] = parameters[i].getUnderlyingType();
			if (realParameters[i] != parameters[i]) {
				changed = true;
			}
		}
		final BoogieType t = c.getSynonym();
		if (t == null) {
			if (changed) {
				realType = createConstructedType(constr, realParameters);
			} else {
				realType = this;
			}
		} else {
			realType = t.getUnderlyingType().substitutePlaceholders(0, realParameters);
		}
	}

	//@Override
	@Override
	protected BoogieType substitutePlaceholders(final int depth, final BoogieType[] substType) {
		if (parameters.length == 0) {
			return this;
		}
		final BoogieType[] newParam = new BoogieType[parameters.length];
		boolean changed = false;
		for (int i = 0; i < parameters.length; i++) {
			newParam[i] = parameters[i].substitutePlaceholders(depth, substType);
			if (newParam[i] != parameters[i]) {
				changed = true;
			}
		}
		if (!changed) {
			return this;
		}
		return createConstructedType(constr, newParam);
	}

	//@Override
	@Override
	protected BoogieType incrementPlaceholders(final int depth, final int incDepth) {
		if (parameters.length == 0) {
			return this;
		}
		final BoogieType[] newParam = new BoogieType[parameters.length];
		boolean changed = false;
		for (int i = 0; i < parameters.length; i++) {
			newParam[i] = parameters[i].incrementPlaceholders(depth, incDepth);
			if (newParam[i] != parameters[i]) {
				changed = true;
			}
		}
		if (!changed) {
			return this;
		}
		return createConstructedType(constr, newParam);
	}

	//@Override
	@Override
	protected boolean unify(final int depth, final BoogieType other, final BoogieType[] substitution) {
		if (!(other instanceof BoogieConstructedType)) {
			return false;
		}
		final BoogieConstructedType type = (BoogieConstructedType) other;
		if (constr != type.constr) {
			return false;
		}
		for (int i = 0; i < parameters.length; i++) {
			if (!parameters[i].unify(depth, type.parameters[i], substitution)) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected boolean hasPlaceholder(final int minDepth, final int maxDepth) {
		for (final BoogieType t : parameters) {
			if (t.hasPlaceholder(minDepth, maxDepth)) {
				return true;
			}
		}
		return false;
	}

	//@Override
	@Override
	protected boolean isUnifiableTo(final int depth, final BoogieType other, final ArrayList<BoogieType> subst) {
		if (this == other || other == TYPE_ERROR) {
			return true;
		}
		if (!(other instanceof BoogieConstructedType)) {
			return false;
		}
		final BoogieConstructedType type = (BoogieConstructedType) other;
		if (constr != type.constr) {
			return false;
		}
		for (int i = 0; i < parameters.length; i++) {
			if (!parameters[i].isUnifiableTo(depth, type.parameters[i], subst)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public BoogieType getUnderlyingType() {
		return realType;
	}

	public BoogieTypeConstructor getConstr() {
		return constr;
	}
	public BoogieType getParameter(final int i) {
		return parameters[i];
	}

	public int getParameterCount() {
		return parameters.length;
	}

	/**
	 * Computes a string representation.  It uses depth to compute artificial
	 * names for the placeholders.
	 * @param depth the number of placeholders outside this expression.
	 * @param needParentheses true if parentheses should be set for constructed types
	 * @return a string representation of this type.
	 */
	@Override
	protected String toString(final int depth, final boolean needParentheses) {
		if (parameters.length == 0) {
			return constr.getName();
		}

		final StringBuilder sb = new StringBuilder();
		if (needParentheses) {
			sb.append("(");
		}
		sb.append(constr.getName());
		for (final BoogieType pType: parameters) {
			sb.append(" ").append(pType.toString(depth, true));
		}
		if (needParentheses) {
			sb.append(")");
		}
		return sb.toString();
	}

	@Override
	protected ASTType toASTType(final ILocation loc, final int depth) {
		final ASTType[] astParamTypes = new ASTType[parameters.length];
		for (int i = 0; i < parameters.length; i++) {
			astParamTypes[i] = parameters[i].toASTType(loc, depth);
		}
		return new de.uni_freiburg.informatik.ultimate.boogie.ast.
			NamedType(loc, this, constr.getName(), astParamTypes);
	}

	//@Override
	@Override
	public boolean isFinite() {
		if (realType != this) {
			return realType.isFinite();
		}
		return constr.isFinite();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((constr == null) ? 0 : constr.hashCode());
		result = prime * result + Arrays.hashCode(parameters);
		result = prime * result + ((realType == null) ? 0 : realType.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final BoogieConstructedType other = (BoogieConstructedType) obj;
		if (constr == null) {
			if (other.constr != null) {
				return false;
			}
		} else if (!constr.equals(other.constr)) {
			return false;
		}
		if (!Arrays.equals(parameters, other.parameters)) {
			return false;
		}
		if (realType == null) {
			if (other.realType != null) {
				return false;
			}
		} else if (!realType.equals(other.realType)) {
			return false;
		}
		return true;
	}


}
