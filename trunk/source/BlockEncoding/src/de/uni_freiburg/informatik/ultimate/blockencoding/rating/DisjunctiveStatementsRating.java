/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating;

import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;

/**
 * Here we store the amount of disjunctions on one edge and additionally store
 * for each disjunction the amount of statements inside.
 * 
 * @author Stefan Wissert
 * 
 */
public class DisjunctiveStatementsRating implements IRating {

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(IRating arg0) {
		// TODO Auto-generated method stub
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating
	 * #getRatingValue()
	 */
	@Override
	public RatingValue<?> getRatingValue() {
		// TODO Auto-generated method stub
		return null;
	}

}
