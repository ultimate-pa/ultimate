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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

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
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.Decision
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
	public static CDD[] trueChilds = new CDD[] { CDD.TRUE, CDD.FALSE };

	/**
	 * Useful child array to create a negated boolean decision.
	 */
	public static CDD[] falseChilds = new CDD[] { CDD.FALSE, CDD.TRUE };

	/**
	 * Hash to keep all equal CDDs identical.
	 */
	private static UnifyHash<CDD> unifyHash = new UnifyHash<>();
	public Decision decision;
	int depth;
	CDD[] childs;
	boolean timed = false;

	/**
	 * Create a new CDD with the given decision and sub diagrams.
	 */
	private CDD(final Decision decision, final CDD[] childs) {
		this.decision = decision;
		this.childs = childs;
		timed = decision instanceof RangeDecision;

		int i;
		depth = 0;

		if (childs != null) {
			for (i = 0; i < childs.length; i++) {
				depth = max(depth, childs[i].depth + 1);
				timed = timed || childs[i].isTimed();
			}
		}
	}

	private static int min(final int a, final int b) {
		return ((a < b) ? a : b);
	}

	private static int max(final int a, final int b) {
		return ((a > b) ? a : b);
	}

	public int getDepth() {
		return depth;
	}

	public boolean isTimed() {
		return timed;
	}

	/**
	 * Create a new CDD with the given decision and sub diagrams.
	 * 
	 * @param decision
	 *            the decision.
	 * @param childs
	 *            the child formulae for the sub-decisions.
	 */
	public static CDD create(final Decision decision, final CDD[] childs) {
		int hashcode = decision.hashCode();

		for (int i = 0; i < childs.length; i++) {
			hashcode = (hashcode * (11 + i)) ^ childs[i].hashCode();
		}

		final Iterator<CDD> it = unifyHash.iterateHashCode(hashcode);
		CDD cdd;

		try_next: while (it.hasNext()) {
			cdd = it.next();

			if (decision.equals(cdd.decision)) {
				for (int i = 0; i < childs.length; i++) {
					if (cdd.childs[i] != childs[i]) {
						continue try_next;
					}
				}

				return cdd;
			}
		}

		cdd = new CDD(decision, childs);
		unifyHash.put(hashcode, cdd);

		return cdd;
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

		final int cmpTo = decision.compareTo(other.decision);

		if (cmpTo < 0) {
			for (int i = 0; i < childs.length; i++) {
				if (!childs[i].implies(other)) {
					return false;
				}
			}

			return true;
		} else if (cmpTo > 0) {
			for (int i = 0; i < other.childs.length; i++) {
				if (!implies(other.childs[i])) {
					return false;
				}
			}

			return true;
		} else {
			return decision.implies(other.decision, childs, other.childs);
		}
	}

	/**
	 * Negate the current CDD. This means to recursively swap the TRUE and FALSE leafs.
	 * 
	 * @return the negation of the current CDD.
	 */
	public CDD negate() {
		if (childs == null) {
			if (this == TRUE) {
				return FALSE;
			}
			return TRUE;
		}

		final CDD[] newchilds = new CDD[childs.length];

		for (int i = 0; i < childs.length; i++) {
			newchilds[i] = childs[i].negate();
		}

		return create(decision, newchilds);
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

		final HashMap<CDD, HashMap<CDD, CDD>> cache = new HashMap<>();
		return and(other, cache);
	}

	/**
	 * Calculate logical conjunction of this and other CDD.
	 * 
	 * @param other
	 *            the other CDD.
	 * @return the conjunction of the CDDs.
	 */
	public CDD and(final CDD other, final HashMap<CDD, HashMap<CDD, CDD>> cache) {
		if ((other == CDD.FALSE) || (this == CDD.TRUE)) {
			return other;
		}

		if ((other == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}

		HashMap<CDD, CDD> cache2 = cache.get(this);
		if (cache2 == null) {
			cache2 = new HashMap<>();
			cache.put(this, cache2);
		}
		CDD result = cache2.get(other);
		if (result != null) {
			return result;
		}
		CDD[] newchilds;
		final int cmpTo = decision.compareTo(other.decision);

		if (cmpTo == 0) {
			result = decision.and(other.decision, childs, other.childs, cache);
		} else if (cmpTo < 0) {
			newchilds = new CDD[childs.length];

			for (int i = 0; i < childs.length; i++) {
				newchilds[i] = childs[i].and(other, cache);
			}

			result = decision.simplify(newchilds);
		} else {
			newchilds = new CDD[other.childs.length];

			for (int i = 0; i < other.childs.length; i++) {
				newchilds[i] = this.and(other.childs[i], cache);
			}

			result = other.decision.simplify(newchilds);
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

		CDD[] newchilds;
		final int cmpTo = decision.compareTo(other.decision);

		if (cmpTo == 0) {
			return decision.or(other.decision, childs, other.childs);
		} else if (cmpTo < 0) {
			newchilds = new CDD[childs.length];

			for (int i = 0; i < childs.length; i++) {
				newchilds[i] = childs[i].or(other);
			}

			return decision.simplify(newchilds);
		} else {
			newchilds = new CDD[other.childs.length];

			for (int i = 0; i < other.childs.length; i++) {
				newchilds[i] = or(other.childs[i]);
			}

			return other.decision.simplify(newchilds);
		}
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

			if (assumption.decision.compareTo(decision) < 0) {
				CDD newass = assumption.childs[0];

				for (int i = 1; i < assumption.childs.length; i++) {
					newass = newass.or(assumption.childs[i]);
				}

				assumption = newass;
			} else if (assumption.decision.compareTo(decision) == 0) {
				return decision.assume(assumption.decision, childs, assumption.childs);
			} else {
				CDD[] newChilds = null;

				for (int i = 0; i < childs.length; i++) {
					final CDD newC = childs[i].assume(assumption);

					if ((newChilds == null) && (newC != childs[i])) {
						newChilds = new CDD[childs.length];
						System.arraycopy(childs, 0, newChilds, 0, i);
					}

					if (newChilds != null) {
						newChilds[i] = newC;
					}
				}

				if (newChilds == null) {
					return this;
				}

				return decision.simplify(newChilds);
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

		for (int i = 0; i < childs.length; i++) {
			final CDD[] cdnf = childs[i].toDNF();

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
						final CDD[] newchilds = new CDD[childs.length];

						for (int k = 0; k < newchilds.length; k++) {
							newchilds[k] = FALSE;
						}

						newchilds[i] = cdnf[j];

						final CDD newCDD = create(decision, newchilds);

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

		for (int i = 0; i < childs.length; i++) {
			final CDD[] ccnf = childs[i].toCNF();

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
						final CDD[] newchilds = new CDD[childs.length];

						for (int k = 0; k < newchilds.length; k++) {
							newchilds[k] = TRUE;
						}

						newchilds[i] = ccnf[j];

						final CDD newCDD = create(decision, newchilds);

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
		return cddDominates(i, childs[i]);
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
		return cddIsDominated(i, childs[i]);
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
		for (int j = 0; j < childs.length; j++) {
			if ((j != i) && !cdd.implies(childs[j])) {
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
		for (int j = 0; j < childs.length; j++) {
			if ((j != i) && !childs[j].implies(cdd)) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Creates a string representation of the CDD.
	 */
	@Override
	public String toString() {
		return toString(false);
	}

	public String toTexString() {
		return toTexString(false);
	}

	/**
	 * Creates a string representation of the CDD.
	 * 
	 * @param needsParens
	 *            true, if disjunctions need to be parenthesised.
	 */
	public String toString(final boolean needsParens) {
		final StringBuffer sb = new StringBuffer();
		String ordelim = "";
		int clauses = 0;

		if (this == CDD.TRUE) {
			return "TRUE";
		}

		if (this == CDD.FALSE) {
			return "FALSE";
		}

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			sb.append(ordelim);

			if (childDominates(i)) {
				sb.append(childs[i]);
			} else {
				sb.append(decision.toString(i));

				if (childs[i] != CDD.TRUE) {
					sb.append(" \u2227 ").append(childs[i].toString(true));
				}
			}

			ordelim = " \u2228 ";
			clauses++;
		}

		if (needsParens && (clauses > 1)) {
			return "(" + sb + ")";
		}
		return sb.toString();
	}

	public String toSmtString(final boolean needsParens, final int index) {
		final StringBuffer sb = new StringBuffer();
		final String ordelim = "(or ";
		int clauses = 0;

		if (this == CDD.TRUE) {
			return "true";
		}

		if (this == CDD.FALSE) {
			return "false";
		}

		int cnt = 0;

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			sb.append(ordelim);
			cnt++;

			if (childDominates(i)) {
				sb.append(childs[i].toSmtString(true, index));
			} else {
				if (childs[i].getChilds() != null) {
					sb.append("(and ");
				}

				sb.append(decision.toSmtString(i, index));

				if (childs[i] != CDD.TRUE) {
					sb.append(childs[i].toSmtString(true, index));
				}

				if (childs[i].getChilds() != null) {
					sb.append(") ");
				}
			}

			clauses++;
		}

		for (int i = 0; i < cnt; i++) {
			sb.append(") ");
		}

		// if (needsParens && clauses > 1)
		// return "(" + sb + ")";
		// else
		return sb.toString();
	}

	/* bei range decisions wird der value der bound zur�ckgegeben - nur f�r einfache decisions */
	public int getValue() {
		if (!(decision instanceof RangeDecision)) {
			return 0;
		}

		int val = 0;

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			val = ((RangeDecision) decision).getVal(i);

			if (val > 0) {
				return val;
			}
		}

		return val;
	}

	public int getOp() {
		if (!(decision instanceof RangeDecision)) {
			return RangeDecision.OP_INVALID;
		}

		int val = RangeDecision.OP_INVALID;

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			val = ((RangeDecision) decision).getOp(i);

			if (val != RangeDecision.OP_INVALID) {
				return val;
			}
		}

		return RangeDecision.OP_INVALID;
	}

	/**
	 * Creates a string representation of the CDD in tex-format.
	 * 
	 * @param needsParens
	 *            true, if disjunctions need to be parenthesised.
	 */
	public String toTexString(final boolean needsParens) {
		final StringBuffer sb = new StringBuffer();
		String ordelim = "";
		int clauses = 0;

		if (this == CDD.TRUE) {
			return "TRUE";
		}

		if (this == CDD.FALSE) {
			return "FALSE";
		}

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			sb.append(ordelim);

			if (childDominates(i)) {
				sb.append(childs[i].toTexString(true));
			} else {
				sb.append(decision.toTexString(i));

				if (childs[i] != CDD.TRUE) {
					sb.append(" \\wedge ").append(childs[i].toTexString(true));
				}
			}

			ordelim = " \\vee ";
			clauses++;
		}

		if (needsParens && (clauses > 1)) {
			return "(" + sb + ")";
		}
		return sb.toString();
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
		final StringBuffer sb = new StringBuffer();
		String ordelim = "";
		int clauses = 0;

		if (this == CDD.TRUE) {
			return "TRUE";
		}

		if (this == CDD.FALSE) {
			return "FALSE";
		}

		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}

			sb.append(ordelim);

			if (childDominates(i)) {
				if (format.matches("tex")) {
					sb.append(childs[i].toString("tex", true));
				}

				if (format.matches("uppaal")) {
					sb.append(childs[i].toString("uppaal", true));
				}

				if (format.matches("general")) {
					sb.append(childs[i].toString("general", true));
				}
			} else {
				if (format.matches("tex")) {
					sb.append(decision.toTexString(i));

					if (childs[i] != CDD.TRUE) {
						sb.append(" \\wedge ").append(childs[i].toString("tex", true));
					}
				}

				if (format.matches("uppaal")) {
					sb.append(decision.toString(i));

					if (childs[i] != CDD.TRUE) {
						sb.append(" && ").append(childs[i].toString("uppaal", true));
					}
				}

				if (format.matches("general")) {
					sb.append(decision.toString(i));

					if (childs[i] != CDD.TRUE) {
						sb.append(" \u2227 ").append(childs[i].toString("general", true));
					}
				}
			}

			if (format.matches("tex")) {
				ordelim = " \\vee ";
			}

			if (format.matches("uppaal")) {
				ordelim = " || ";
			}

			if (format.matches("general")) {
				ordelim = " \u2228 ";
			}

			clauses++;
		}

		if (needsParens && (clauses > 1)) {
			return "(" + sb + ")";
		}
		return sb.toString();
	}

	public void printCDD(final int i) {
		if (this == CDD.TRUE) {
			System.out.println("CDD=TRUE");

			return;
		} else if (this == CDD.FALSE) {
			System.out.println("CDD=FALSE");

			return;
		}

		System.out.println("Decision=" + decision.toString(i));

		for (int j = 0; j < childs.length; j++) {
			childs[j].printCDD(j);
		}
	}

	/**
	 * @return Returns the childs.
	 */
	public CDD[] getChilds() {
		return childs;
	}

	/**
	 * @return Returns the decision.
	 */
	public Decision getDecision() {
		return decision;
	}

	private CDD primeCache;

	public CDD prime() {
		return this.prime(null);
	}

	public CDD prime(final String ignore) {
		if ((this == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}
		if (primeCache != null) {
			return primeCache;
		}

		final Decision decision = this.decision;
		Decision newDecision;

		final CDD[] children = childs;
		final CDD[] newChildren = new CDD[children.length];

		for (int i = 0; i < children.length; i++) {
			newChildren[i] = children[i].prime();
		}

		newDecision = decision.prime(ignore);

		primeCache = CDD.create(newDecision, newChildren);
		return primeCache;
	}

	// Change by Ami
	// the function returns whether a CDD is an atomic proposition (like A, !A) or a
	// proposition composed of several variables (e.g., A&B, A||B)
	public boolean isAtomic() {
		return ((getChilds()[0] == CDD.TRUE) || (getChilds()[0] == CDD.FALSE))
				&& ((getChilds()[1] == CDD.TRUE) || (getChilds()[1] == CDD.FALSE));
	}

	private static void testIsAtomic(final CDD cdd) {
		System.out.println("The formula " + cdd.toString() + " is atomic: " + cdd.isAtomic());
	}

	public CDD unprime() {
		return this.unprime(null);
	}

	public CDD unprime(final String ignore) {
		if ((this == CDD.TRUE) || (this == CDD.FALSE)) {
			return this;
		}

		final Decision decision = this.decision;
		Decision newDecision;

		final CDD[] children = childs;
		final CDD[] newChildren = new CDD[children.length];

		for (int i = 0; i < children.length; i++) {

			newChildren[i] = children[i].unprime();
		}

		newDecision = decision.unprime(ignore);

		return CDD.create(newDecision, newChildren);
	}

	/***
	 * Collect Identifiers from the whole CDD
	 * 
	 * @return set containing all variables in the CDD
	 */
	public Set<String> getIdents() {
		final Set<String> idents = new HashSet<String>();
		if (childs == null) { // empty cdds may happen
			return idents;
		}
		for (final CDD child : getChilds()) {
			if (child != null) {
				idents.addAll(child.getIdents());
			}
		}
		if (decision == null) {
			return idents;
		} else if (decision instanceof BoogieBooleanExpressionDecision) {
			idents.addAll(((BoogieBooleanExpressionDecision) decision).getVars().keySet());
		} else {
			idents.add(decision.getVar());
		}
		return idents;
	}

	// XXX: Testing
	public static void main(final String[] args) {
		final CDD a = BooleanDecision.create("a");
		final CDD b = BooleanDecision.create("b");
		final CDD c = BooleanDecision.create("c");
		final CDD d = BooleanDecision.create("d");

		// CDD main = ((a.and(b)).and(c.or(d))).or(e).or(f.negate());
		// CDD main2 = ((a.and(b)).or(a.negate().and(b.negate())));
		// CDD main = main2.or(c.and(d));
		// CDD main = c.or(main2);

		// CDD teil1 = a.negate().and(b).and(c);
		// CDD teil2 = a.and(b);
		// CDD main = teil1.or(teil2);

		// CDD links = a.negate().or(b.or(c));
		// CDD rechts = a.or(b);
		// CDD main = links.and(rechts);
		// CDD links = a.negate().and(b.and(c));
		// CDD rechts = a.and(d);
		// CDD main = links.or(rechts);
		final CDD links = a.negate().and(b);
		final CDD rechts = a.and(b.or(c)).and(d);
		final CDD main = links.or(rechts);

		final CDD test = a.negate();
		final CDD test2 = a.or(b);

		System.out.println("********************************* CDD ********************************* ");
		System.out.println(main.toString());
		System.out.println(main.toTexString());
		testIsAtomic(test);
		testIsAtomic(test2);
		testIsAtomic(links);
		testIsAtomic(main);
		testIsAtomic(a);

		final CDD[] dnf = main.toDNF();
		System.out.println("********************************* DNF ********************************* ");

		for (int i = 0; i < dnf.length; i++) {
			System.out.println("*** Conjunctive term " + i + ": ");
			System.out.println(dnf[i].toString());
		}

		final CDD[] cnf = main.toCNF();
		System.out.println("********************************* CNF ********************************* ");

		for (int i = 0; i < cnf.length; i++) {
			System.out.println("*** Disjunctive term " + i + ": ");
			System.out.println(cnf[i].toString());
		}

		System.out.println("*********************************************************************** ");
	}

	private int getDecHash() {
		if (decision == null) {
			return 0;
		}

		return decision.getVar().hashCode();
	}

	private int getDecHash2() {
		if (decision == null) {
			return 0;
		}

		int i;
		int res = 0;
		final char[] chs = decision.getVar().toCharArray();

		for (i = 0; i < decision.getVar().length(); i++) {
			res += (chs[i] * (((i & 1) == 0) ? 7 : 11));
		}

		return res;
	}

	public Vector<Integer> getElemHashes() {
		int i;
		final Vector<Integer> res = new Vector<>();

		if (decision != null) {
			res.add(getDecHash());
			res.add(getDecHash2());
		}

		if (childs != null) {
			for (i = 0; i < childs.length; i++) {
				res.addAll(childs[i].getElemHashes());
			}
		}

		return res;
	}
}
