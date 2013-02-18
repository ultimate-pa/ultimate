package local.stalin.smt.theory.linar;

import java.util.TreeMap;
import java.util.Map;

/**
 * Class representing a linear term c1*x1+...+cn*xn
 * 
 * @author Juergen Christ
 */
public class LinTerm {
	// coefficient map has to be initialized before mvar!!!
	Map<LinVar,Rational> mcoeffs;
	/**
	 * Generate an empty linear term.
	 */
	LinTerm() {
		mcoeffs = new TreeMap<LinVar,Rational>();
	}
	/**
	 * Generate a new linear term. Note that we do not make a copy of the given
	 * map. 
	 * @param coeffmap Coefficient map to use.
	 */
	LinTerm(Map<LinVar,Rational> coeffmap) {
		mcoeffs = coeffmap;
	}
	public String toString() {
		return new AffinTerm(this, false).toString();
	}
	public int hashCode() {
		return mcoeffs.hashCode();
	}
	public boolean equals(Object o) {
		if( o instanceof LinTerm )
			return mcoeffs.equals(((LinTerm)o).mcoeffs);
		return false;
	}	
}
