/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
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
	public SupportingInvariant(final AffineFunction f) {
		mCoefficients.putAll(f.mCoefficients);
		mConstant = f.mConstant;
	}
	
	/**
	 * Check whether this supporting invariant is equivalent to false.
	 */
	public boolean isFalse() {
		if (!mCoefficients.isEmpty()) {
			return false;
		}
		final int cmp = mConstant.compareTo(BigInteger.ZERO);
		return (cmp <= 0 && strict) || (cmp < 0 && !strict);
	}
	
	/**
	 * Check whether this supporting invariant is equivalent to true.
	 */
	public boolean isTrue() {
		if (!mCoefficients.isEmpty()) {
			return false;
		}
		final int cmp = mConstant.compareTo(BigInteger.ZERO);
		return (cmp > 0 && strict) || (cmp >= 0 && !strict);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(super.toString());
		sb.append(strict ? " > 0" : " >= 0");
		return sb.toString();
	}
	
	@Override
	public Term asTerm(final Script script) throws SMTLIBException {
		final Term t = super.asTerm(script);
		return script.term(strict ? ">" : ">=", t,
				SmtUtils.constructIntValue(script, BigInteger.ZERO));
	}
}
