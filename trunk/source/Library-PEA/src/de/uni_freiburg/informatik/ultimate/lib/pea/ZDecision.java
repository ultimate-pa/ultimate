/* $Id: ZDecision.java 399 2009-06-26 16:01:20Z jfaber $
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 *
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.PrimeVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZTerm;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZWrapper;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.z.util.ZString;

/**
 * ZDecision is used to create CDDs containing Z terms. Please note that these terms may contain quantifiers. Currently
 * predicates below quantifiers are only represented as unicode strings and not as CDDs again. This may change in the
 * future.
 *
 * @author jdq, ulli, jfaber
 *
 */
public final class ZDecision extends Decision<ZDecision> {
	private String mPredicate;

	/**
	 *
	 */
	private ZDecision(final String predicate) {
		super();
		mPredicate = predicate;
	}

	/**
	 * Creates a CDD for a Z predicate given as Unicode String. It simplifies the predicate according to very simple
	 * rules, assuming that the Z predicate has a simple pattern (similar to the pattern allowed in boolean
	 * expressions). Please use this method only if you know what you are doing.
	 *
	 * @param predicate
	 *            the Z predicate as Unicode String to represent as CDD
	 * @return a CDD for the given predicate
	 */
	@Deprecated
	public static CDD createSimplified(final String predicate) {
		return getSimplifiedCDD(predicate);
	}

	/**
	 * Creates a CDD without simplifying the predicate any further
	 */
	public static CDD create(final String predicate) {
		return ZDecision.createWithChildren(predicate, CDD.TRUE_CHILDS);
	}

	public static CDD createWithChildren(final String predicate, final CDD[] children) {
		if (predicate.trim().equals(ZString.TRUE)) {
			return CDD.TRUE;
		}

		if (predicate.trim().equals(ZString.FALSE)) {
			return CDD.FALSE;
		}

		return CDD.create(new ZDecision(predicate), children);
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof ZDecision)) {
			return false;
		}

		final ZDecision zd = (ZDecision) o;

		return zd.mPredicate.equals(mPredicate);
	}

	@Override
	public int hashCode() {
		return mPredicate.hashCode();
	}

	public String getPredicate() {
		return mPredicate;
	}

	@Override
	public String toString(final int child) {
		return (child == 0) ? mPredicate : (ZString.NOT + mPredicate);
	}

	@Override
	public String toTexString(final int child) {
		return toString(child);
	}

	@Override
	public String toBoogieString(final int child) {
		return (child == 0) ? mPredicate : ("!" + mPredicate);
	}

	@Override
	public String toSmtString(final int child) {
		return toString(child);
	}

	@Override
	public String toUppaalString(final int child) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		throw new UnsupportedOperationException();
	}

	/**
	 * @return Returns the predicate encoded in ZML.
	 * @throws ParseException
	 *             if the Unicode String could not be parsed.
	 * @throws InstantiationException
	 */
	public String getZML() throws ParseException, InstantiationException {
		return ZWrapper.INSTANCE.predicateToZml(mPredicate);
	}

	public boolean equals(final ZDecision z) {
		// TODO: compare term objects
		return mPredicate.equals(z.mPredicate);
	}

	public ZDecision negate() {
		final StringBuilder neg = new StringBuilder(ZString.NOT);
		neg.append(ZString.LPAREN);
		neg.append(mPredicate);
		neg.append(ZString.RPAREN);

		return new ZDecision(neg.toString());
	}

	/**
	 * @return if a CDD contains a ZDecision containing the given text. Since this method isn't for general CDDs, it
	 *         resides in this class
	 */
	public static boolean cddContainsZDecisionWith(final CDD cdd, final String text) {
		if ((cdd == CDD.TRUE) || (cdd == CDD.FALSE)) {
			return false;
		}

		if (cdd.getDecision() instanceof ZDecision && ((ZDecision) cdd.getDecision()).mPredicate.contains(text)) {
			return true;
		}

		for (final CDD child : cdd.getChilds()) {
			if (cddContainsZDecisionWith(child, text)) {
				return true;
			}
		}

		return false;
	}

	/** rename a variable inside ZDecisions in a CDD */
	public static void renameVariableInCDD(final CDD cdd, final String oldVar, final String newVar) {
		if ((cdd == CDD.TRUE) || (cdd == CDD.FALSE)) {
			return;
		}

		if (cdd.getDecision() instanceof ZDecision) {
			final ZDecision zd = (ZDecision) cdd.getDecision();
			zd.mPredicate = zd.mPredicate.replace(oldVar, newVar);
		}

		for (final CDD child : cdd.getChilds()) {
			renameVariableInCDD(child, oldVar, newVar);
		}
	}

	/* Methods to simplify and normalize ZDecisions on creation */

	/*
	 * try to rewrite all decisions in terms of < or <= this might enable further CDD simplifications down the road we
	 * also remove spaces around the operator for that reason
	 */
	@Deprecated
	static CDD simplifyDecision(String s) {
		s = s.trim();

		if (s.contains(ZString.GEQ)) {
			final String[] terms = s.split(ZString.GEQ);

			return ZDecision.create(terms[0].trim() + "<" + terms[1].trim()).negate();
		}

		if (s.contains(">=")) {
			final String[] terms = s.split(">=");

			return ZDecision.create(terms[0].trim() + "<" + terms[1].trim()).negate();
		}

		if (s.contains(">")) {
			final String[] terms = s.split(">");

			return ZDecision.create(terms[0].trim() + ZString.LEQ + terms[1].trim()).negate();
		}

		/* remove spaces */
		s = s.replaceAll("(\\s*)<(\\s*)", "<");
		s = s.replaceAll("(\\s*)" + ZString.LEQ + "(\\s*)", ZString.LEQ);
		s = s.replaceAll("(\\s*)<=(\\s*)", ZString.LEQ);

		return ZDecision.create(s);
	}

	@Deprecated
	static CDD parseAND(final String term) {
		final String[] tt = term.split(ZString.AND);
		CDD cdd = simplifyDecision(tt[0]);

		for (int i = 1; i < tt.length; i++) {
			cdd = cdd.and(simplifyDecision(tt[i]));
		}

		return cdd;
	}

	@Deprecated
	static CDD parseOR(final String term) {
		final String[] tt = term.split(ZString.OR);
		CDD cdd = parseAND(tt[0]);

		for (int i = 1; i < tt.length; i++) {
			cdd = cdd.or(parseAND(tt[i]));
		}

		return cdd;
	}

	@Deprecated
	static CDD resolveImpls(final String term) {
		final String[] tt = term.split(ZString.IMP);

		if (tt.length == 1) {
			return parseOR(tt[0]);
		}

		if (tt.length == 2) {
			/* implication: a => b ~~ !a \/ b */
			CDD cdd = parseOR(tt[0]).negate();
			cdd = cdd.or(parseOR(tt[1]));

			return cdd;
		}

		throw new RuntimeException("implication with more than two parts"); //$NON-NLS-1$
	}

	/* return the simplified CDD for the given term */
	@Deprecated
	static CDD getSimplifiedCDD(final String term) {
		/*
		 * split into conjugated subterms; for some reason we can't split using ZString.NL, but "\n" works
		 */
		final String[] tt = term.split("\n");
		CDD cdd = resolveImpls(tt[0]);

		for (int i = 1; i < tt.length; i++) {
			cdd = cdd.and(resolveImpls(tt[i]));
		}

		return cdd;
	}

	@Override
	public ZDecision prime(final Set<String> ignoreIds) {
		// TODO: Totally ignores all the parameters
		// String decision = predicate.replaceAll("([a-zA-Z_])(\\w*)", "$1$2'");
		String decision = mPredicate;

		try {
			// decision = OZUtils.computePrimedPredicate(predicate);
			final ZTerm predTerm = ZWrapper.INSTANCE.predicateToTerm(mPredicate);
			final PrimeVisitor visitor = new PrimeVisitor();
			// PrimeVisitor visitor = new PrimeVisitor();
			// //visitor.accept(predTerm.getTerm());
			predTerm.getTerm().accept(visitor);

			decision = ZWrapper.INSTANCE.termToUnicode(predTerm);
		} catch (final ParseException e) {
			e.printStackTrace();
		} catch (final InstantiationException e) {
			e.printStackTrace();
		}

		return new ZDecision(decision);
	}

	@Override
	public ZDecision unprime(final Set<String> ignoreIds) {
		// String decision = predicate.replaceAll("([a-zA-Z_])(\\w*)", "$1$2'");
		String decision = mPredicate;

		try {
			// decision = OZUtils.computePrimedPredicate(predicate);
			final ZTerm predTerm = ZWrapper.INSTANCE.predicateToTerm(mPredicate);
			final PrimeVisitor visitor = new PrimeVisitor();
			// PrimeVisitor visitor = new PrimeVisitor();
			// //visitor.accept(predTerm.getTerm());
			predTerm.getTerm().accept(visitor);

			decision = ZWrapper.INSTANCE.termToUnicode(predTerm);
		} catch (final ParseException e) {
			e.printStackTrace();
		} catch (final InstantiationException e) {
			e.printStackTrace();
		}

		return new ZDecision(decision);
	}

	@Override
	public String getVar() {
		return "";
	}

	@Override
	public int compareToSimilar(final Decision<?> other) {
		return mPredicate.compareTo(((ZDecision) other).mPredicate);
	}

}
