package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * This represents a linear supporting invariant of the form
 * <pre>Σ c_i x_i + c ⊳ 0</pre>
 * where ⊳ is > or ≥.
 * 
 * @author Jan Leike
 */
public class SupportingInvariant extends AffineFunction {
	private static final long serialVersionUID = -8409937196513651751L;
	
	/**
	 * Whether the invariant is strict (">") versus non-strict ("≥")
	 */
	public boolean strict;
	
	public SupportingInvariant() {
		super();
	}
	
	/**
	 * Construct a supporting invariant from an AffineFunction
	 */
	public SupportingInvariant(AffineFunction f) {
		m_coefficients = f.m_coefficients;
		m_constant = f.m_constant;
	}
	
	/**
	 * Check whether this supporting invariant is equivalent to false.
	 */
	public boolean isFalse() {
		if (!m_coefficients.isEmpty()) {
			return false;
		}
		int cmp = m_constant.compareTo(BigInteger.ZERO);
		return (cmp <= 0 && strict) || (cmp < 0 && !strict);
	}
	
	/**
	 * Check whether this supporting invariant is equivalent to true.
	 */
	public boolean isTrue() {
		if (!m_coefficients.isEmpty()) {
			return false;
		}
		int cmp = m_constant.compareTo(BigInteger.ZERO);
		return (cmp > 0 && strict) || (cmp >= 0 && !strict);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(super.toString());
		sb.append(strict ? " > 0" : " >= 0");
		return sb.toString();
	}
	
	@Override
	public Term asTerm(Script script) throws SMTLIBException {
		Term t = super.asTerm(script);
		return script.term(strict ? ">" : ">=", t,
				script.numeral(BigInteger.ZERO));
	}
}