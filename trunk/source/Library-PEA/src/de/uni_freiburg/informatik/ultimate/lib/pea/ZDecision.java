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
public final class ZDecision extends Decision {
	// private Term term;
	private String predicate;

	/**
	 *
	 */
	private ZDecision(final String predicate) {
		super();
		this.predicate = predicate;
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
		return ZDecision.createWithChildren(predicate, CDD.trueChilds);
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see pea.Decision#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(final Object o) {
		/* we're 'bigger' than Ranges and Events */
		if (o instanceof RangeDecision || o instanceof EventDecision) {
			return 1;
		}

		/* we're 'smaller' than other decisions */
		if (!(o instanceof ZDecision)) {
			return -1;
		}

		final ZDecision zd = (ZDecision) o;

		return predicate.compareTo(zd.predicate);
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof ZDecision)) {
			return false;
		}

		final ZDecision zd = (ZDecision) o;

		return zd.predicate.equals(predicate);
	}

	@Override
	public int hashCode() {
		return predicate.hashCode();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see pea.Decision#prime()
	 */
	@SuppressWarnings("unchecked")
	@Override
	public Decision prime() {
		// String decision = predicate.replaceAll("([a-zA-Z_])(\\w*)", "$1$2'");
		String decision = predicate;

		try {
			// decision = OZUtils.computePrimedPredicate(predicate);
			final ZTerm predTerm = ZWrapper.INSTANCE.predicateToTerm(predicate);
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

	public String getPredicate() {
		return predicate;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see pea.Decision#toString(int)
	 */
	@Override
	public String toString(final int child) {
		return (child == 0) ? predicate : (ZString.NOT + predicate);
	}

	@Override
	public String toSmtString(final int child) {
		return toString(child);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see pea.Decision#toUppaalString(int)
	 */
	@Override
	public String toUppaalString(final int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @return Returns the term.
	 */

	/*
	 * public Term getTerm() { return term; }
	 */

	/**
	 * @return Returns the predicate encoded in ZML.
	 * @throws ParseException
	 *             if the Unicode String could not be parsed.
	 * @throws InstantiationException
	 */
	public String getZML() throws ParseException, InstantiationException {
		return ZWrapper.INSTANCE.predicateToZml(predicate);
	}

	/**
	 * @param term
	 *            The term to set.
	 */

	/*
	 * public void setTerm(Term term) { this.term = term; }
	 */

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(final ZDecision z) {
		// TODO: compare term objects
		return predicate.equals(z.predicate);
	}

	public ZDecision negate() {
		final StringBuilder neg = new StringBuilder(ZString.NOT);
		neg.append(ZString.LPAREN);
		neg.append(predicate);
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

		if (cdd.decision instanceof ZDecision && ((ZDecision) cdd.decision).predicate.contains(text)) {
			return true;
		}

		for (final CDD child : cdd.childs) {
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

		if (cdd.decision instanceof ZDecision) {
			final ZDecision zd = (ZDecision) cdd.decision;
			zd.predicate = zd.predicate.replace(oldVar, newVar);
		}

		for (final CDD child : cdd.childs) {
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
	public String toTexString(final int child) {
		return (child == 0) ? predicate : (ZString.NOT + predicate);
	}

	@Override
	public Decision unprime(final String ignore) {
		return this.unprime();
	}

	@Override
	public Decision prime(final String ignore) {
		return this.prime();
	}

	@Override
	public Decision unprime() {
		// String decision = predicate.replaceAll("([a-zA-Z_])(\\w*)", "$1$2'");
		String decision = predicate;

		try {
			// decision = OZUtils.computePrimedPredicate(predicate);
			final ZTerm predTerm = ZWrapper.INSTANCE.predicateToTerm(predicate);
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
}
