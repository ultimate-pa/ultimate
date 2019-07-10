/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * A CDD (constraint decision diagram) represents a logical quantifier free formula in a BDD like structure. This
 * formula can have arbitrary atomic propositions that are represented by subclasses of the Decision class. Each of this
 * decision can have an arbitrary (but finite) number of branches, e.g. an enumeration type of n values can be
 * represented by a decision with n childs. In the BDD case a decision has just two childs, one for true, one for false.
 *
 * All decisions need to be comparable to each other, and this determines the variable order. This class implements
 * logical operations like and/or/negate, however the decision needs to implement and/or for two CDD with the same
 * decision at the top node.
 *
 * The normal unification process of BDDs is also done for CDDs: Whenever a new CDD is needed that equals a previously
 * created one, the previous CDD is reused. If two CDDs represent the same formula, they are always identical. A CDD
 * that does not equal FALSE is always satisfiable (provided that the decisions are implemented correctly).
 *
 * Note to maintainers: {@link CDD}s depend on Java's {@link #hashCode()} and {@link #equals(Object)} method. Do not
 * overwrite it. Look at {@link #create(Decision, CDD[])} to see what the dependency is.
 *
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Decision
 *
 */
public final class CDD {
	/**
	 * The formula TRUE.
	 */
	public static final CDD TRUE = new CDD(null, null);

	/**
	 * The formula FALSE.
	 */
	public static final CDD FALSE = new CDD(null, null);

	/**
	 * Useful child array to create a boolean decision.
	 */
	public static final CDD[] TRUE_CHILDS = new CDD[] { CDD.TRUE, CDD.FALSE };

	/**
	 * Useful child array to create a negated boolean decision.
	 */
	public static final CDD[] FALSE_CHILDS = new CDD[] { CDD.FALSE, CDD.TRUE };

	/**
	 * Hash to keep all equal CDDs identical.
	 */
	private static final UnifyHash<CDD> UNIFY_HASH = new UnifyHash<>();

	private static final Comparator<Decision<?>> DECISION_COMPARATOR = Decision.getComparator();

	private final Decision<?> mDecision;
	private final int mDepth;
	private final CDD[] mChilds;
	private final boolean mTimed;

	private CDD mPrimeCache;

	/**
	 * Create a new CDD with the given decision and sub diagrams.
	 */
	private CDD(final Decision<?> decision, final CDD[] childs) {
		mDecision = decision;
		mChilds = childs;

		boolean timed = decision instanceof RangeDecision;
		int depth = 0;

		if (childs != null) {
			for (int i = 0; i < childs.length; i++) {
				depth = max(depth, childs[i].mDepth + 1);
				timed = timed || childs[i].isTimed();
			}
		}
		mDepth = depth;
		mTimed = timed;
	}

	private static int min(final int a, final int b) {
		return ((a < b) ? a : b);
	}

	private static int max(final int a, final int b) {
		return ((a > b) ? a : b);
	}

	public int getDepth() {
		return mDepth;
	}

	public boolean isTimed() {
		return mTimed;
	}

	/**
	 * Create a new CDD with the given decision and sub diagrams.
	 *
	 * @param decision
	 *            the decision.
	 * @param childs
	 *            the child formulae for the sub-decisions.
	 */
	public static CDD create(final Decision<?> decision, final CDD[] childs) {
		final CDD cdd = new CDD(decision, childs);
		int hashcode = decision.hashCode();

		for (int i = 0; i < childs.length; i++) {
			hashcode = (hashcode * (11 + i)) ^ childs[i].hashCode();
		}
		final Iterator<CDD> iter = UNIFY_HASH.iterateHashCode(hashcode).iterator();

		while (iter.hasNext()) {
			final CDD current = iter.next();
			if (current.isEqual(cdd)) {
				return current;
			}
		}

		UNIFY_HASH.put(hashcode, cdd);
		return cdd;
	}

	public boolean isEqual(final CDD cdd) {
		if (mDecision.equals(cdd.mDecision)) {
			return Arrays.equals(mChilds, cdd.mChilds);
		}
		return false;
	}

	/**
	 * Check if other CDD is implied by this one. This is equivalent to &quot;
	 * <code>this.negate().or(other) == CDD.TRUE</code>&quot; but more efficient.
	 *
	 * @param other
	 *            the other CDD.
	 * @return true iff other CDD is implied by this one.
	 */
	public boolean implies(final CDD other) {
		if ((this == FALSE) || (other == TRUE)) {
			return true;
		}

		if ((this == TRUE) || (other == FALSE)) {
			return false;
		}

		final int cmpTo = DECISION_COMPARATOR.compare(mDecision, other.mDecision);

		if (cmpTo < 0) {
			for (int i = 0; i < mChilds.length; i++) {
				if (!mChilds[i].implies(other)) {
					return false;
				}
			}

			return true;
		} else if (cmpTo > 0) {
			for (int i = 0; i < other.mChilds.length; i++) {
				if (!implies(other.mChilds[i])) {
					return false;
				}
			}

			return true;
		} else {
			return mDecision.implies(other.mDecision, mChilds, other.mChilds);
		}
	}

	/**
	 * Negate the current CDD. This means to recursively swap the TRUE and FALSE leafs.
	 *
	 * @return the negation of the current CDD.
	 */
	public CDD negate() {
		if (mChilds == null) {
			if (this == TRUE) {
				return FALSE;
			}
			return TRUE;
		}

		final CDD[] newchilds = new CDD[mChilds.length];

		for (int i = 0; i < mChilds.length; i++) {
			newchilds[i] = mChilds[i].negate();
		}

		return create(mDecision, newchilds);
	}

	/**
	 * Calculate logical conjunction of this and other CDD.
	 *
	 * @param other
	 *            the other CDD.
	 * @return the conjunction of the CDDs.
	 */
	public CDD and(final CDD other) {
		if ((other == CDD.FALSE) || (this == CDD.TRUE)) {
			return other;
		}

		if ((other == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}

		return and(other, new HashMap<>());
	}

	/**
	 * Calculate logical conjunction of this and other CDD.
	 *
	 * @param other
	 *            the other CDD.
	 * @return the conjunction of the CDDs.
	 */
	public CDD and(final CDD other, final Map<CDD, Map<CDD, CDD>> cache) {
		if ((other == CDD.FALSE) || (this == CDD.TRUE)) {
			return other;
		}

		if ((other == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}

		Map<CDD, CDD> cache2 = cache.get(this);
		if (cache2 == null) {
			cache2 = new HashMap<>();
			cache.put(this, cache2);
		}
		CDD result = cache2.get(other);
		if (result != null) {
			return result;
		}
		CDD[] newchilds;
		final int cmpTo = DECISION_COMPARATOR.compare(mDecision, other.mDecision);

		if (cmpTo == 0) {
			result = mDecision.and(other.mDecision, mChilds, other.mChilds, cache);
		} else if (cmpTo < 0) {
			newchilds = new CDD[mChilds.length];

			for (int i = 0; i < mChilds.length; i++) {
				newchilds[i] = mChilds[i].and(other, cache);
			}

			result = mDecision.simplify(newchilds);
		} else {
			newchilds = new CDD[other.mChilds.length];

			for (int i = 0; i < other.mChilds.length; i++) {
				newchilds[i] = this.and(other.mChilds[i], cache);
			}

			result = other.mDecision.simplify(newchilds);
		}
		cache2.put(other, result);
		return result;
	}

	/**
	 * Calculate logical disjunction of this and other CDD.
	 *
	 * @param other
	 *            the other CDD.
	 * @return the disjunction of the CDDs.
	 */
	public CDD or(final CDD other) {
		if ((other == CDD.FALSE) || (this == CDD.TRUE)) {
			return this;
		}

		if ((other == CDD.TRUE) || (this == CDD.FALSE)) {
			return other;
		}

		final Map<CDD, Map<CDD, CDD>> cache = new HashMap<>();
		return or(other, cache);
	}

	public CDD or(final CDD other, final Map<CDD, Map<CDD, CDD>> cache) {
		if ((other == CDD.FALSE) || (this == CDD.TRUE)) {
			return this;
		}

		if ((other == CDD.TRUE) || (this == CDD.FALSE)) {
			return other;
		}

		Map<CDD, CDD> innerCache = cache.get(this);
		if (innerCache == null) {
			innerCache = new HashMap<>();
			cache.put(this, innerCache);
		}
		final CDD cachedResult = innerCache.get(other);
		if (cachedResult != null) {
			return cachedResult;
		}

		CDD[] newchilds;
		final int cmpTo = DECISION_COMPARATOR.compare(mDecision, other.mDecision);

		final CDD result;
		if (cmpTo == 0) {
			result = mDecision.or(other.mDecision, mChilds, other.mChilds, cache);
		} else if (cmpTo < 0) {
			newchilds = new CDD[mChilds.length];

			for (int i = 0; i < mChilds.length; i++) {
				newchilds[i] = mChilds[i].or(other, cache);
			}

			result = mDecision.simplify(newchilds);
		} else {
			newchilds = new CDD[other.mChilds.length];

			for (int i = 0; i < other.mChilds.length; i++) {
				newchilds[i] = or(other.mChilds[i], cache);
			}

			result = other.mDecision.simplify(newchilds);
		}
		final CDD old = innerCache.put(other, result);
		assert old == null;
		return result;
	}

	/**
	 * Simplify the current CDD under the given assumption. This should remove all parts that are already implied by the
	 * assumption. The correctness criteria is
	 *
	 * <pre>
	 * this.assume(assumption).and(assumption) == this.and(assumption)
	 * </pre>
	 *
	 * @param assumption
	 *            the assumption.
	 * @return the simplified CDDs.
	 */
	public CDD assume(CDD assumption) {
		while (true) {
			if ((this == TRUE) || (assumption == FALSE)) {
				return TRUE;
			}

			if ((this == FALSE) || (assumption == TRUE)) {
				return this;
			}

			final int cmp = DECISION_COMPARATOR.compare(assumption.mDecision, mDecision);

			if (cmp < 0) {
				CDD newass = assumption.mChilds[0];

				for (int i = 1; i < assumption.mChilds.length; i++) {
					newass = newass.or(assumption.mChilds[i]);
				}

				assumption = newass;
			} else if (cmp == 0) {
				return mDecision.assume(assumption.mDecision, mChilds, assumption.mChilds);
			} else {
				CDD[] newChilds = null;

				for (int i = 0; i < mChilds.length; i++) {
					final CDD newC = mChilds[i].assume(assumption);

					if ((newChilds == null) && (newC != mChilds[i])) {
						newChilds = new CDD[mChilds.length];
						System.arraycopy(mChilds, 0, newChilds, 0, i);
					}

					if (newChilds != null) {
						newChilds[i] = newC;
					}
				}

				if (newChilds == null) {
					return this;
				}

				return mDecision.simplify(newChilds);
			}
		}
	}

	/**
	 * Generates the disjunctive normal form of a CDD.
	 *
	 * @return It returns an array with CDDs for each conjunction term of the normal form.
	 */
	public CDD[] toDNF() {
		if (this == TRUE) {
			return new CDD[] { this };
		}

		if (this == FALSE) {
			return new CDD[] {};
		}

		final ArrayList<CDD> dnf = new ArrayList<>();

		for (int i = 0; i < mChilds.length; i++) {
			final CDD[] cdnf = mChilds[i].toDNF();

			// isDominated optimization as in toString
			if (childDominates(i)) {
				for (int j = 0; j < cdnf.length; j++) {
					if (!dnf.contains(cdnf[j])) {
						dnf.add(cdnf[j]);
					}
				}
			} else {
				for (int j = 0; j < cdnf.length; j++) {
					// extended isDominated check:
					// checks whether a single conjunction term of the DNF dominates
					// all childs. In this case we do not need to consider the current decision.
					if (cddDominates(i, cdnf[j])) {
						if (!dnf.contains(cdnf[j])) {
							dnf.add(cdnf[j]);
						}
					} else {
						final CDD[] newchilds = new CDD[mChilds.length];

						for (int k = 0; k < newchilds.length; k++) {
							newchilds[k] = FALSE;
						}

						newchilds[i] = cdnf[j];

						final CDD newCDD = create(mDecision, newchilds);

						if (!dnf.contains(newCDD)) {
							dnf.add(newCDD);
						}
					}
				}
			}
		}

		return dnf.toArray(new CDD[dnf.size()]);
	}

	public CDD toDNF_CDD() {
		final CDD[] dnfList = toDNF();
		CDD result = CDD.FALSE;

		for (int i = 0; i < dnfList.length; i++) {
			final CDD literal = dnfList[i];
			result = result.or(literal);
		}

		return result;
	}

	/**
	 * Generates the conjunctive normal form of a CDD.
	 *
	 * @return It returns an array with CDDs for each disjunction term of the normal form.
	 */
	public CDD[] toCNF() {
		if (this == TRUE) {
			return new CDD[] {};
		}

		if (this == FALSE) {
			return new CDD[] { this };
		}

		final ArrayList<CDD> cnf = new ArrayList<>();

		for (int i = 0; i < mChilds.length; i++) {
			final CDD[] ccnf = mChilds[i].toCNF();

			// isDominated optimization similar to toString and toCDD
			if (childIsDominated(i)) {
				for (int j = 0; j < ccnf.length; j++) {
					if (!cnf.contains(ccnf[j])) {
						cnf.add(ccnf[j]);
					}
				}
			} else {
				for (int j = 0; j < ccnf.length; j++) {
					// extended isDominated check:
					// checks whether a single disjunction term of the CNF is dominated
					// by all childs. In this case we do not need to consider the current decision.
					if (cddIsDominated(i, ccnf[j])) {
						if (!cnf.contains(ccnf[j])) {
							cnf.add(ccnf[j]);
						}
					} else {
						// we construct a CDD for the disjunction of this decision and the
						// disjunction term ccnf[i].
						final CDD[] newchilds = new CDD[mChilds.length];

						for (int k = 0; k < newchilds.length; k++) {
							newchilds[k] = TRUE;
						}

						newchilds[i] = ccnf[j];

						final CDD newCDD = create(mDecision, newchilds);

						if (!cnf.contains(newCDD)) {
							cnf.add(newCDD);
						}
					}
				}
			}
		}

		return cnf.toArray(new CDD[cnf.size()]);
	}

	public CDD toCNF_CDD() {
		final CDD[] cnfList = toCNF();
		CDD result = CDD.TRUE;

		for (int i = 0; i < cnfList.length; i++) {
			final CDD literal = cnfList[i];
			result = result.and(literal);
		}

		return result;
	}

	/**
	 * Check whether a given childs in the current node dominates (i.e. logically implies) all sub-childs. This function
	 * should only be called by subclasses of Decision.
	 *
	 * @param i
	 *            the index of the child to check.
	 * @return true, if childs[i] implies childs[j] for all j.
	 */
	public boolean childDominates(final int i) {
		return cddDominates(i, mChilds[i]);
	}

	/**
	 * Check whether a given childs in the current node is dominated (i.e. logically implied) by all other childs. This
	 * function should only be called by subclasses of Decision.
	 *
	 * @param i
	 *            the index of the child to check.
	 * @return true, if childs[j] implies childs[i] for all j.
	 */
	public boolean childIsDominated(final int i) {
		return cddIsDominated(i, mChilds[i]);
	}

	/**
	 * Check whether a given CDD dominates (i.e. logically implies) all childs (besides the child given by i) of this
	 * CDD.
	 *
	 * @param i
	 *            the index of the child to be excluded from the check.
	 * @param cdd
	 *            the constraint to check the dominates relation
	 * @return true, if cdd implies childs[j] for all j != i.
	 */
	private boolean cddDominates(final int i, final CDD cdd) {
		for (int j = 0; j < mChilds.length; j++) {
			if ((j != i) && !cdd.implies(mChilds[j])) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Check whether a given CDD is dominated (i.e. logically implied) by all childs (besides the child given by i) of
	 * this CDD.
	 *
	 * @param i
	 *            the index of the child to be excluded from the check.
	 * @param cdd
	 *            the constraint to check the dominates relation
	 * @return true, if cdd implies childs[j] for all j != i.
	 */
	private boolean cddIsDominated(final int i, final CDD cdd) {
		for (int j = 0; j < mChilds.length; j++) {
			if ((j != i) && !mChilds[j].implies(cdd)) {
				return false;
			}
		}

		return true;
	}

	public CDD[] getChilds() {
		return mChilds;
	}

	public Decision<?> getDecision() {
		return mDecision;
	}

	public CDD prime(final Set<String> ignoredIds) {
		if ((this == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}
		if (mPrimeCache != null) {
			return mPrimeCache;
		}

		final Decision<?> ldecision = mDecision;
		Decision<?> newDecision;

		final CDD[] children = mChilds;
		final CDD[] newChildren = new CDD[children.length];

		for (int i = 0; i < children.length; i++) {
			newChildren[i] = children[i].prime(ignoredIds);
		}

		newDecision = ldecision.prime(ignoredIds);

		mPrimeCache = CDD.create(newDecision, newChildren);
		return mPrimeCache;
	}

	/**
	 * @return whether a CDD is an atomic proposition (like A, !A) or a proposition composed of several variables (e.g.,
	 *         A&B, A||B)
	 */
	public boolean isAtomic() {
		return ((getChilds()[0] == CDD.TRUE) || (getChilds()[0] == CDD.FALSE))
				&& ((getChilds()[1] == CDD.TRUE) || (getChilds()[1] == CDD.FALSE));
	}

	public CDD unprime(final Set<String> ignoredIds) {
		if ((this == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}

		final Decision<?> decision = mDecision;
		Decision<?> newDecision;

		final CDD[] children = mChilds;
		final CDD[] newChildren = new CDD[children.length];

		for (int i = 0; i < children.length; i++) {

			newChildren[i] = children[i].unprime(ignoredIds);
		}

		newDecision = decision.unprime(ignoredIds);

		return CDD.create(newDecision, newChildren);
	}

	/**
	 * Creates a string representation of the CDD.
	 */
	@Override
	public String toString() {
		return toString(false);
	}

	public String toTexString() {
		return toString("tex", false);
	}

	/**
	 * Creates a string representation of the CDD.
	 *
	 * @param needsParens
	 *            true, if disjunctions need to be parenthesised.
	 */
	public String toString(final boolean needsParens) {
		return toString("general", needsParens);
	}

	/**
	 * Creates a string representation of the CDD in tex-format.
	 *
	 * @param format
	 *            in {tex, uppaal, general}
	 * @param needsParens
	 *            true, if disjunctions need to be parenthesised.
	 */
	public String toString(final String format, final boolean needsParens) {
		if (this == CDD.TRUE) {
			return "true";
		}

		if (this == CDD.FALSE) {
			return "false";
		}

		final Function<CDD, String> funCdd2Str;
		final Function<Integer, String> funDecision2Str;
		final String orStr;
		final String andStr;
		final boolean isInfix;
		if ("tex".equalsIgnoreCase(format)) {
			funCdd2Str = a -> a.toString("tex", needsParens);
			funDecision2Str = i -> mDecision.toTexString(i);
			orStr = " \\vee ";
			andStr = " \\wedge ";
			isInfix = true;
		} else if ("uppaal".equalsIgnoreCase(format)) {
			funCdd2Str = a -> a.toString("uppaal", needsParens);
			funDecision2Str = i -> mDecision.toUppaalString(i);
			orStr = " || ";
			andStr = " && ";
			isInfix = true;
		} else if ("boogie".equalsIgnoreCase(format)) {
			funCdd2Str = a -> a.toString("boogie", needsParens);
			funDecision2Str = i -> mDecision.toBoogieString(i);
			orStr = " || ";
			andStr = " && ";
			isInfix = true;
		} else if ("general".equalsIgnoreCase(format)) {
			funCdd2Str = a -> a.toString("general", needsParens);
			funDecision2Str = i -> mDecision.toString(i);
			orStr = " \u2228 ";
			andStr = " \u2227 ";
			isInfix = true;
		} else if ("smt".equalsIgnoreCase(format)) {
			funCdd2Str = a -> a.toString("smt", needsParens);
			funDecision2Str = i -> mDecision.toSmtString(i);
			orStr = "(or ";
			andStr = "(and ";
			isInfix = false;
		} else {
			throw new UnsupportedOperationException("Unknown format: " + format);
		}
		if (isInfix) {
			return toStringInfix(funCdd2Str, funDecision2Str, orStr, andStr);
		}
		return toStringPrefix(funCdd2Str, funDecision2Str, orStr, andStr);
	}

	public String toSmtString() {
		return toString("smt", true);
	}

	public String toBoogieString() {
		return toString("boogie", true);
	}

	public String toUppaalString() {
		return toString("uppaal", true);
	}

	private String toStringPrefix(final Function<CDD, String> funCdd2Str,
			final Function<Integer, String> funDecision2Str, final String orStr, final String andStr) {

		final long childCount = Arrays.stream(mChilds).filter(a -> a != CDD.FALSE).count();
		final StringBuilder sb = new StringBuilder();
		if (childCount > 1) {
			sb.append(orStr);
		}

		for (int i = 0; i < mChilds.length; i++) {
			if (mChilds[i] == CDD.FALSE) {
				continue;
			}

			if (childDominates(i)) {
				sb.append(funCdd2Str.apply(mChilds[i]));
			} else {
				if (mChilds[i].getChilds() != null) {
					sb.append(andStr);
				}
				sb.append(funDecision2Str.apply(i));

				if (mChilds[i] != CDD.TRUE) {
					sb.append(funCdd2Str.apply(mChilds[i]));
				}

				if (mChilds[i].getChilds() != null) {
					sb.append(") ");
				}
			}
		}
		return sb.toString();
	}

	private String toStringInfix(final Function<CDD, String> funCdd2Str,
			final Function<Integer, String> funDecision2Str, final String orStr, final String andStr) {
		final List<String> disjuncts = new ArrayList<>();
		for (int i = 0; i < mChilds.length; i++) {
			if (mChilds[i] == CDD.FALSE) {
				continue;
			}

			if (childDominates(i)) {
				disjuncts.add(funCdd2Str.apply(mChilds[i]));
			} else {
				if (mChilds[i] != CDD.TRUE) {
					disjuncts.add("(" + funDecision2Str.apply(i) + andStr + funCdd2Str.apply(mChilds[i]) + ")");
				} else {
					disjuncts.add(funDecision2Str.apply(i));
				}
			}
		}
		if (disjuncts.size() == 1) {
			return disjuncts.get(0);
		}
		final StringBuilder sb = new StringBuilder();
		final Iterator<String> iter = disjuncts.iterator();
		sb.append("(");
		sb.append(iter.next());
		while (iter.hasNext()) {
			sb.append(orStr);
			sb.append(iter.next());
		}
		sb.append(")");
		return sb.toString();
	}

}
