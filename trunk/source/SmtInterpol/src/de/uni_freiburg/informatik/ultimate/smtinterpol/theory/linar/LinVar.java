/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;


/**
 * Class representing a variable in a linear combination. This might either be
 * a slack variable or a real variable as introduced by the problem. For slack
 * variables we use the object name to refer to the corresponding linear term.
 * 
 * Natural order depends on the order of creation of variables. That is every
 * variable is ordered according to their creation time. Ordering on the
 * variables is one requirement to be able to prove termination of the
 * algorithm.
 * 
 * Every variable knows all possible bound constraints referring to it. This
 * way, bound propagations can easily be implemented.
 * 
 * @author Juergen Christ
 */
public class LinVar implements Comparable<LinVar> {
	/**
	 * Name of the variable.  This is either a SharedTermOld for initially
	 * non-basic variables or a LinTerm for initially basic variables.
	 */
	Object m_name;
	
	/** Current upper bound and its reason. null if no upper bound. */
	LAReason m_upper;
	/** Current lower bound and its reason. null if no lower bound. */
	LAReason m_lower;
	/** Current value. */
	InfinitNumber m_curval;
	// Is value required to be integer?
	boolean misint;
	// List of all bounds on this variable
	NavigableMap<InfinitNumber, BoundConstraint> mconstraints = 
		new TreeMap<InfinitNumber, BoundConstraint>();
	// List of all equalities known for this variable
	NavigableMap<InfinitNumber, LAEquality> mequalities =
		new TreeMap<InfinitNumber, LAEquality>();
	
	/**
	 * All disequalities asserted on this variable.
	 */
	Map<Rational,LAEquality> mdisequalities;
	// Is this variable currently basic? NOTE: THIS IS THE CURRENT STATUS
	boolean mbasic;
	// Number to sort this variable in the sparse matrix
	final int matrixpos;
	int numcuts = 0;
	/**
	 * The dummy entry that starts the list for this linvar. 
	 * The list follows nextInRow if this is a basic variable,
	 * nextInCol if this is a non-basic variable.
	 */
	MatrixEntry headEntry;
	
	/**
	 * Number of infinities currently contributing to the upper bound.
	 */
	int m_numUpperInf;
	/**
	 * Number of infinities currently contributing to the lower bound.
	 */
	int m_numLowerInf;
	/**
	 * Number of epsilons currently contributing to the upper bound.
	 */
	int m_numUpperEps;
	/**
	 * Number of epsilons currently contributing to the lower bound.
	 */
	int m_numLowerEps;
	/**
	 * Rational part of upper bound.
	 * This still has to be divided by the head coeff (and may also be a
	 * lower bound if head coeff is negative).
	 */
	private MutableRational m_upperComposite = new MutableRational(Rational.ZERO);
	/**
	 * Rational part of lower bound.
	 * This still has to be divided by the head coeff (and may also be a
	 * upper bound if head coeff is negative).
	 */
	private MutableRational m_lowerComposite = new MutableRational(Rational.ZERO);
	LinVar[] m_cachedRowVars;
	Rational[] m_cachedRowCoeffs;
	
	int assertionstacklevel;
	boolean dead = false;

	int chainlength;
	
	/// --- Construction ---
	/**
	 * Constructs a dummy linear variable.
	 */
	private LinVar() {
		m_name = "Dummy";
		matrixpos = Integer.MAX_VALUE;
	}
	/**
	 * Constructor for a variable.
	 * @param name  Name of the variable (Needed for printout).
	 * @param isint Is the variable required to be integral valued?
	 * @param assertionstacklevel The number of pushes succeeded before this
	 * 							  variable has been created.
	 * @param num The count for this variable.
	 */
	public LinVar(Object name,boolean isint, int assertionstacklevel, int num) {
		m_name = name;
		m_curval = InfinitNumber.ZERO;
		misint = isint;
		mbasic = false;
		matrixpos = num;

		headEntry = new MatrixEntry();
		headEntry.column = this;
		headEntry.row = dummylinvar;
		headEntry.prevInCol = headEntry;
		headEntry.nextInCol = headEntry;
		this.assertionstacklevel = assertionstacklevel;
		chainlength = 0;
	}
	/**
	 * Get the upper bound.
	 * @return Upper bound.
	 */
	public final InfinitNumber getUpperBound() {
		return m_upper == null ? InfinitNumber.POSITIVE_INFINITY :
			m_upper.getBound();
	}
	/**
	 * Get the lower bound.
	 * @return Lower bound.
	 */
	public final InfinitNumber getLowerBound() {
		return m_lower == null ? InfinitNumber.NEGATIVE_INFINITY :
			m_lower.getBound();
	}
	public InfinitNumber getExactUpperBound() {
		return m_upper == null ? InfinitNumber.POSITIVE_INFINITY :
			m_upper.getExactBound();
	}
	public InfinitNumber getExactLowerBound() {
		return m_lower == null ? InfinitNumber.NEGATIVE_INFINITY :
			m_lower.getExactBound();
	}
	/**
	 * Check whether the upper bound is set.
	 * @return <code>true</code> iff upper bound is finite.
	 */
	public final boolean hasUpperBound() {
		return m_upper != null;
	}
	/**
	 * Check whether the lower bound is set.
	 * @return <code>true</code> iff lower bound is finite.
	 */
	public final boolean hasLowerBound() {
		return m_lower != null;
	}
	/// --- Bound testing ---
	/**
	 * Check whether we can increment the value of this variable
	 * @return <code>true</code> iff value of this variable is below its upper
	 * 		   bound
	 */
	public final boolean isIncrementPossible() {
		assert !mbasic;
		return m_curval.less(getUpperBound());
	}
	/**
	 * Check whether we can decrement the value of this variable.
	 * @return <code>true</code> iff value of this variable is above its lower
	 * 		   bound.
	 */
	public final boolean isDecrementPossible() {
		assert !mbasic;
		return getLowerBound().less(m_curval);
	}
	/// --- Name stuff ---
	public String toString() {
		return m_name.toString();
	}
	/// --- Initially basic testing ---
	/**
	 * Check whether this variable is initially basic.
	 * @return <code>true</code> iff this variable corresponds to a linear term
	 */
	public boolean isInitiallyBasic() {
		return m_name instanceof LinTerm;
	}
	
	@Override
	public int hashCode() {
		return matrixpos;
	}
	
	@Override
	public final int compareTo(LinVar o) {
		return matrixpos - o.matrixpos;
	}
	/**
	 * Check whether this variable has a value outside its bounds.
	 * @return <code>false</code> iff <code>mlbound<=mcurval<=mubound</code>. 
	 */
	public boolean outOfBounds() {
		if (m_upper instanceof LiteralReason
			|| (isInt() && m_upper != null)) {
			if (m_curval.ma.equals(m_upper.getExactBound().ma))
				fixEpsilon();
			if (m_upper.getExactBound().less(m_curval))
				return true;
		}
		if (m_lower instanceof LiteralReason
			|| (isInt() && m_lower != null)) {
			if (m_curval.ma.equals(m_lower.getExactBound().ma))
				fixEpsilon();
			if (m_curval.less(m_lower.getExactBound()))
				return true;
		}
		return false;
	}
	
	/**
	 * Dummy linear variable marking end of a non-basic chain.
	 */
	final static LinVar dummylinvar = new LinVar();
	
	void addDiseq(LAEquality ea) {
		if (mdisequalities == null)
			mdisequalities = new HashMap<Rational,LAEquality>();
		// we only remember the first disequality.  We only care if there
		// is a disequality not which exactly.  The first is also better
		// to explain a conflict.
		if (!mdisequalities.containsKey(ea.getBound()))
			mdisequalities.put(ea.getBound(),ea);
	}
	void removeDiseq(LAEquality ea) {
		// only remove the disequality if it is the right one.
		// chronological backtracking will ensure that if we remove
		// the disequality there is no other disequality with the 
		// same bound missing.
		// mdisequalities can be null, if the literal was not set, because
		// it already produced a conflict in another theory.
		if (mdisequalities != null
			&& mdisequalities.get(ea.getBound()) == ea)
			mdisequalities.remove(ea.getBound());
	}
	LAEquality getDiseq(Rational bound) {
		if (mdisequalities != null)
			return mdisequalities.get(bound);
		return null;
	}
	public void addEquality(LAEquality ea) {
		mequalities.put(new InfinitNumber(ea.getBound(), 0), ea);
	}
	boolean unconstrained() {
		return mconstraints.isEmpty() && mequalities.isEmpty();
	}
	boolean isCurrentlyUnconstrained() {
		return m_lower == null && m_upper == null;
	}
	public boolean isInt() {
		return misint;
	}
	public InfinitNumber getEpsilon() {
		return misint ? InfinitNumber.ONE : InfinitNumber.EPSILON;
	}
	
	public final void moveBounds(LinVar other) {
		m_numUpperInf = other.m_numUpperInf;
		m_numLowerInf = other.m_numLowerInf;
		m_numUpperEps = other.m_numUpperEps;
		m_numLowerEps = other.m_numLowerEps;
		m_upperComposite = other.m_upperComposite; 
		m_lowerComposite = other.m_lowerComposite;
		other.m_upperComposite = null;
		other.m_lowerComposite = null;
	}
	
	public void mulUpperLower(Rational r) {
		m_upperComposite.mul(r);
		m_lowerComposite.mul(r);
	}

	public final void updateUpper(BigInteger coeff, InfinitNumber oldBound, InfinitNumber newBound) {
		if (oldBound.isInfinity()) {
			if (newBound.isInfinity())
				return;
			m_numUpperInf--;
			m_upperComposite.addmul(newBound.ma, coeff);
		} else if (newBound.isInfinity()) {
			m_numUpperInf++;
			m_upperComposite.addmul(oldBound.ma.negate(), coeff);
		} else {
			m_upperComposite.addmul(newBound.ma.sub(oldBound.ma), coeff);
		}
		m_numUpperEps += (newBound.meps - oldBound.meps) * coeff.signum();
	}
	
	public final void updateLower(BigInteger coeff, InfinitNumber oldBound, InfinitNumber newBound) {
		if (oldBound.isInfinity()) {
			if (newBound.isInfinity())
				return;
			m_numLowerInf--;
			m_lowerComposite.addmul(newBound.ma, coeff);
		} else if (newBound.isInfinity()) {
			m_numLowerInf++;
			m_lowerComposite.addmul(oldBound.ma.negate(), coeff);
		} else {
			m_lowerComposite.addmul(newBound.ma.sub(oldBound.ma), coeff);
		}
		m_numLowerEps += (newBound.meps - oldBound.meps) * coeff.signum();
	}
	
	public void updateUpperLowerSet(BigInteger coeff, LinVar nb) {
		InfinitNumber ubound = nb.getUpperBound();
		InfinitNumber lbound = nb.getLowerBound();
		if (coeff.signum() < 0) {
			InfinitNumber swap = ubound;
			ubound = lbound;
			lbound = swap;
		}
		if (ubound.isInfinity()) {
			m_numUpperInf++;
		} else {
			m_upperComposite.addmul(ubound.ma, coeff);
		}
		m_numUpperEps += ubound.meps * coeff.signum();
		if (lbound.isInfinity()) {
			m_numLowerInf++;
		} else {
			m_lowerComposite.addmul(lbound.ma, coeff);
		}
		m_numLowerEps += lbound.meps * coeff.signum();
	}
	public void updateUpperLowerClear(BigInteger coeff, LinVar nb) {
		InfinitNumber ubound = nb.getUpperBound().negate();
		InfinitNumber lbound = nb.getLowerBound().negate();
		if (coeff.signum() < 0) {
			InfinitNumber swap = ubound;
			ubound = lbound;
			lbound = swap;
		}
		if (ubound.isInfinity()) {
			m_numUpperInf--;
		} else {
			m_upperComposite.addmul(ubound.ma, coeff);
		}
		m_numUpperEps += ubound.meps * coeff.signum();
		if (lbound.isInfinity()) {
			m_numLowerInf--;
		} else {
			m_lowerComposite.addmul(lbound.ma, coeff);
		}
		m_numLowerEps += lbound.meps * coeff.signum();
	}
	public InfinitNumber getUpperComposite() {
		if (headEntry.coeff.signum() < 0) {
			if (m_numUpperInf != 0)
				return InfinitNumber.POSITIVE_INFINITY;
			Rational denom = m_upperComposite.toRational()
				.mul(Rational.valueOf(BigInteger.valueOf(-1), headEntry.coeff));
			return new InfinitNumber(denom, InfinitNumber.normEpsilon(m_numUpperEps));
		} else {
			if (m_numLowerInf != 0)
				return InfinitNumber.POSITIVE_INFINITY;
			Rational denom = m_lowerComposite.toRational()
				.mul(Rational.valueOf(BigInteger.valueOf(-1), headEntry.coeff));
			return new InfinitNumber(denom, -InfinitNumber.normEpsilon(m_numLowerEps));
		}
	}
	
	public InfinitNumber getLowerComposite() {
		if (headEntry.coeff.signum() < 0) {
			if (m_numLowerInf != 0)
				return InfinitNumber.NEGATIVE_INFINITY;
			Rational denom = m_lowerComposite.toRational()
				.mul(Rational.valueOf(BigInteger.valueOf(-1), headEntry.coeff));
			return new InfinitNumber(denom, InfinitNumber.normEpsilon(m_numLowerEps));
		} else {
			if (m_numUpperInf != 0)
				return InfinitNumber.NEGATIVE_INFINITY;
			Rational denom = m_upperComposite.toRational()
				.mul(Rational.valueOf(BigInteger.valueOf(-1), headEntry.coeff));
			return new InfinitNumber(denom, -InfinitNumber.normEpsilon(m_numUpperEps));
		}
	}
	
	void resetComposites() {
		m_lowerComposite.setValue(Rational.ZERO);
		m_upperComposite.setValue(Rational.ZERO);
		m_numUpperInf = 0;
		m_numLowerInf = 0;
		m_numUpperEps = 0;
		m_numLowerEps = 0;
		m_cachedRowCoeffs = null;
		m_cachedRowVars = null;
	}
	
	/**
	 * Get the linear term from which this basic linvar was created.
	 * @throws ClassCastException if this is not an initially basic variable.
	 * @return the LinTerm.
	 */
	public Map<LinVar,BigInteger> getLinTerm() {
		return ((LinTerm) m_name).mcoeffs;
	}
	
	/**
	 * Get the shared term from which this non-basic linvar was created.
	 * @throws ClassCastException if this is not an initially non-basic variable.
	 * @return the shared term.
	 */
	public SharedTerm getSharedTerm() {
		return (SharedTerm) m_name;
	}
	
	public int getAssertionStackLevel() {
		return assertionstacklevel;
	}
	public boolean checkBrpCounters() {
		assert (mbasic);
		int cntLower = 0, cntLowerEps = 0;
		int cntUpper = 0, cntUpperEps = 0;
		MutableInfinitNumber value = new MutableInfinitNumber();
		MutableInfinitNumber lbound = new MutableInfinitNumber();
		MutableInfinitNumber ubound = new MutableInfinitNumber();
		for (MatrixEntry entry = headEntry.nextInRow;
			 entry != headEntry; entry = entry.nextInRow) {
			value.addmul(entry.column.m_curval, entry.coeff);
			if (entry.coeff.signum() < 0) {
				if (!entry.column.hasUpperBound())
					cntLower++;
				else
					lbound.addmul(entry.column.getUpperBound(), entry.coeff);
				cntLowerEps -= entry.column.getUpperBound().meps;
				if (!entry.column.hasLowerBound())
					cntUpper++;
				else
					ubound.addmul(entry.column.getLowerBound(), entry.coeff);
				cntUpperEps -= entry.column.getLowerBound().meps;
			} else {
				if (!entry.column.hasUpperBound())
					cntUpper++;
				else
					ubound.addmul(entry.column.getUpperBound(), entry.coeff);
				cntUpperEps += entry.column.getUpperBound().meps;
				if (!entry.column.hasLowerBound())
					cntLower++;
				else
					lbound.addmul(entry.column.getLowerBound(), entry.coeff);
				cntLowerEps += entry.column.getLowerBound().meps;
			}
		}
		value = value.div(Rational.valueOf(headEntry.coeff.negate(), BigInteger.ONE));
		assert (cntLower == m_numLowerInf && cntUpper == m_numUpperInf);
		assert (lbound.ma.equals(m_lowerComposite));
		assert (lbound.meps == InfinitNumber.normEpsilon(m_numLowerEps));
		assert (cntLowerEps == m_numLowerEps);
		assert (ubound.ma.equals(m_upperComposite));
		assert (ubound.meps == InfinitNumber.normEpsilon(m_numUpperEps));
		assert (cntUpperEps == m_numUpperEps);
		assert (value.ma.equals(m_curval.ma));
		return true;
	}
	public boolean checkCoeffChain() {
		if (!mbasic)
			return true;
		assert headEntry.row == headEntry.column;
		//assert headEntry.nextInCol == headEntry;
		//assert headEntry.nextInCol == headEntry.prevInCol;
		MutableAffinTerm mat = new MutableAffinTerm();
		MatrixEntry entry = headEntry;
		do {
			assert entry.row == this;
			assert entry.row == entry.column || !entry.column.mbasic;
			assert entry.nextInRow.prevInRow == entry;
			mat.add(Rational.valueOf(entry.coeff, BigInteger.ONE), entry.column);
			entry = entry.nextInRow;
		} while (entry != headEntry);
		assert mat.isConstant() && mat.getConstant().equals(InfinitNumber.ZERO);
		return true;
	}
	public boolean isFixed() {
		return m_upper != null && m_lower != null &&
			m_upper.getBound().equals(m_lower.getBound());
	}
	
	boolean checkChainlength() {
		if (mbasic) {
			int length = 0;
			for (MatrixEntry entry = headEntry.nextInRow; entry != headEntry;
			entry = entry.nextInRow) {
				++length;
			}
			assert(length == chainlength);
		} else {
			int length = 0;
			for (MatrixEntry entry = headEntry.nextInCol; entry != headEntry;
			entry = entry.nextInCol) {
				++length;
			}
			assert(length == chainlength);
		}
		return true;
	}
	
	public Rational computeEpsilon() {
		if (!mbasic) {
			return Rational.valueOf(m_curval.meps, 1);
		}
		BigInteger epsilons = BigInteger.ZERO;
		for (MatrixEntry entry = headEntry.nextInRow; entry != headEntry;
				entry = entry.nextInRow) {
			int eps = entry.column.m_curval.meps;
			if (eps > 0)
				epsilons = epsilons.subtract(entry.coeff);
			else if (eps < 0)
				epsilons = epsilons.add(entry.coeff);
		}
		return Rational.valueOf(epsilons, headEntry.coeff);
	}

	public void fixEpsilon() {
		if (mbasic) {
			BigInteger epsilons = BigInteger.ZERO;
			for (MatrixEntry entry = headEntry.nextInRow; entry != headEntry;
				entry = entry.nextInRow) {
				int eps = entry.column.m_curval.meps;
				if (eps > 0)
					epsilons = epsilons.subtract(entry.coeff);
				else if (eps < 0)
					epsilons = epsilons.add(entry.coeff);
			}
			m_curval = new InfinitNumber(m_curval.ma, 
					epsilons.signum() * headEntry.coeff.signum());
		}
	}
	public LAEquality getEquality(InfinitNumber bound) {
		return mequalities.get(bound);
	}
	public boolean isAlive() {
		return !dead;
	}
}
