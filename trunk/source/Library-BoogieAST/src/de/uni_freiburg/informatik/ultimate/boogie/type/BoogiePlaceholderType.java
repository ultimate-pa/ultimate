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

/**
 * A placeholder type represents a type bounded by some outer type parameters, 
 * like by an ArrayType, by a function signature, a procedure signature or a
 * forall/exists quantifier.
 * 
 * The type args are represented in de Bruijn style, giving only the number of
 * type parameter declarations between the placeholder and its binder.
 *  
 * @author hoenicke
 *
 */
public class BoogiePlaceholderType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 3301828910886451978L;
	private final int depth;

	public BoogiePlaceholderType(int depth) {
		this.depth = depth;
	}

	/**
	 * Get the depth of the declaration where this placeholder points to.
	 * @return the depth.
	 */
	public int getDepth() {
		return depth;
	}

	//@Override
	@Override
	protected BoogieType substitutePlaceholders(int deltaDepth, BoogieType[] substType) {
		final int relDepth = depth - deltaDepth;
		if (relDepth < 0) {
			/* Placeholder matches some inner scope*/
			return this;
		} else if (relDepth < substType.length) {
			/* Substitute this placeholder */
			BoogieType subst = substType[relDepth];
			/* This should only happen if error type was involved when computing
			 * substitution.
			 */
			if (subst == null) {
				return TYPE_ERROR;
			}
			if (deltaDepth > 0) {
				subst = subst.incrementPlaceholders(0, deltaDepth);
			}
			return subst;
		} else {
			/* Placeholder matches some outer scope; but this scope moves */
			return createPlaceholderType(depth - substType.length);
		}
	}

	//@Override
	@Override
	protected BoogieType incrementPlaceholders(int deltaDepth, int incDepth) {
		final int relDepth = depth - deltaDepth;
		if (relDepth < 0) {
			/* Placeholder matches some inner scope*/
			return this;
		} else { 
			/* Substitute this placeholder */
			return createPlaceholderType(depth + incDepth);
		}
	}

	//@Override
	@Override
	protected boolean unify(int deltaDepth, BoogieType other, BoogieType[] substitution) {
		if (other == TYPE_ERROR) {
			return true;
		}
		final int relDepth = depth - deltaDepth;
		if (relDepth < 0 || relDepth >= substitution.length) {
			/* This placeholder is not substituted */
			if (!(other instanceof BoogiePlaceholderType)) {
				return false;
			}
			final BoogiePlaceholderType type = (BoogiePlaceholderType) other;
			return (type.depth == (relDepth < 0 ? depth : depth - substitution.length));
		} else {
			/* Check freedom of inner bounded variable */
			if (other.hasPlaceholder(0, deltaDepth-1)) {
				return false;
			}
			if (deltaDepth != 0) {
				other = other.incrementPlaceholders(0, -deltaDepth);
			}
			/* Substitute this placeholder */
			if (substitution[relDepth] == null) {
				substitution[relDepth] = other;
				return true;
			}
			return substitution[relDepth] == other;
		}
	}
	
	@Override
	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		return depth >= minDepth && depth <= maxDepth;
	}

	//@Override
	@Override
	protected boolean isUnifiableTo(int deltaDepth, BoogieType other, 
									ArrayList<BoogieType> substitution) {
		/* fast path first */
		if (other == this || other == TYPE_ERROR) {
			return true;
		}
		
		int relDepth = depth - deltaDepth;
		if (relDepth < 0) {
			/* This placeholder is not substituted */
			return false;
		} else {
			/* Get the real types */
			final BoogieType[] subst = 
				substitution.toArray(new BoogieType[substitution.size()]);
			final BoogieType me = substitutePlaceholders(deltaDepth, subst);
			other = other.substitutePlaceholders(deltaDepth, subst);
			if (me == other) {
				return true;
			}
			if (!(me instanceof BoogiePlaceholderType)) {
				/* we are no longer a placeholder type, let the unification
				 * process continue;
				 */
				return other.isUnifiableTo(deltaDepth, me, substitution);
			}
			/* We are a currently unsubstituted placeholder */
			relDepth = ((BoogiePlaceholderType) me).depth - deltaDepth;
			/* Inner placeholders cannot be substituted */
			if (relDepth < 0) {
				return false;
			}
			
			/* Check that other is free of inner bounded variable */
			if (other.hasPlaceholder(0, deltaDepth-1)) {
				return false;
			}

			/* Bring other to the right depth */
			if (deltaDepth != 0) {
				other = other.incrementPlaceholders(0, -deltaDepth);
			}
		
			/* Occur check */
			if (other.hasPlaceholder(relDepth, relDepth)) {
				return false;
			}

			while (relDepth >= substitution.size()) {
				substitution.add(null);
			}
			substitution.set(relDepth, other);
			return true;
		}
	}

	@Override
	public BoogieType getUnderlyingType() {
		return this;
	}
	
	/**
	 * Computes a string representation.  It uses depth to compute artificial
	 * names for the placeholders.
	 * @param depth the number of placeholders outside this expression.
	 * @param needParentheses true if parentheses should be set for constructed types
	 * @return a string representation of this type.
	 */
	@Override
	protected String toString(int depth, boolean needParentheses) {
		final int paramNumber = depth - this.depth - 1;
		
		if (paramNumber >= 0) {
			return "$"+paramNumber;
		} else {
			return "$_"+(-paramNumber);
		}
	}
	
	@Override
	protected ASTType toASTType(ILocation loc, int depth) {
		return new de.uni_freiburg.informatik.ultimate.boogie.ast.
			NamedType(loc, this, toString(depth, false), new ASTType[0]);
	}
	
	//@Override
	@Override
	public boolean isFinite() {
		return true;
	}
}
