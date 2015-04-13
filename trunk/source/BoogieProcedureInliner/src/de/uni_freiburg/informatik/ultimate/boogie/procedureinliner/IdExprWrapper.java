package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;

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
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		String otherIdentifer = ((IdExprWrapper) obj).mIdExpr.getIdentifier();
		return mIdExpr.getIdentifier().equals(otherIdentifer);
	}

}
