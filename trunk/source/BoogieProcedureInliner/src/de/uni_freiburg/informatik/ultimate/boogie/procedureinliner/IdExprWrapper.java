/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;

/**
 * Wrapper class for IdentifierExpression to be used, when equals() and hashCode() are needed.
 * Warning: The wrapper relies only on the identifier. Two wrapped IdentifierExpressions are equal, iff they have the
 * same name/identifier. Their types and payloads aren't taken into account.
 * 
 * This class forbids null values for IdentfierExpressions and their identifier attribute.
 * Simply use null instead of a wrapper instance, containing null.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class IdExprWrapper {

	/** The wrapped object. */
	private final IdentifierExpression mIdExpr;
	
	/**
	 * Creates a new wrapper instance for IdentifierExpressions.
	 * @param idExpr IdentifierExpression, must not be null and must have an identifier that isn't null.
	 */
	public IdExprWrapper(IdentifierExpression idExpr) {
		if (idExpr == null || idExpr.getIdentifier() == null) {
			throw new IllegalArgumentException("Wrappers aren't allowed for null values. Use null wrapper instead.");
		}
		mIdExpr = idExpr;
	}
	
	/** @return The wrapped IdentifierExpression. Is guaranteed to be not null. */
	public IdentifierExpression getIdExpr() {
		return mIdExpr;
	}

	/** @return HashCode from {@link IdentifierExpression#getIdentifier()}. */
	@Override
	public int hashCode() {
		return mIdExpr.getIdentifier().hashCode();
	}
	

	/**
	 * Checks equality.
	 * Warning: Relies only on the identifier. Two wrapped IdentifierExpressions are equal, iff they have the
	 * same name/identifier. Their types and payloads aren't taken into account
	 * @param obj Object
	 * @return obj is an IdExprWrapper with an equal {@link IdentifierExpression#getIdentifier()}.
	 * 
	 * @see Object#equals(Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final String otherIdentifer = ((IdExprWrapper) obj).mIdExpr.getIdentifier();
		return mIdExpr.getIdentifier().equals(otherIdentifer);
	}

}
