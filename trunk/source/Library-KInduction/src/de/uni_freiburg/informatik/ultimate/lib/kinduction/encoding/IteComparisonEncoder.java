/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Encodes an equality over an ite term as Boolean structure if every leaf of the ite decides the equality. C has no
 * Boolean type, so its conditions reach us as e.g. {@code (= (ite phi 1 0) 0)}, which is just {@code (not phi)}, and
 * {@code (= 0 (ite c (ite p 1 0) 1))}, which is {@code (and c (not p))}.
 * <p>
 * Without this, a condition like {@code phi} stays hidden inside a non-Boolean equality, which is one atom for
 * everybody who splits a formula along its Boolean structure. IteRemover, which the quantifier elimination uses,
 * doubles an atom per ite in it, so a whole C condition in one atom makes it run into its timeout.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class IteComparisonEncoder extends TermTransformer {
	private final Script mScript;

	private IteComparisonEncoder(final Script script) {
		mScript = script;
	}

	/**
	 * Returns a term that is equivalent to {@code term}.
	 *
	 * @param script
	 *            the script all terms belong to
	 * @param term
	 *            the term to encode
	 * @return a term that is equivalent to {@code term}
	 */
	public static Term apply(final Script script, final Term term) {
		return new IteComparisonEncoder(script).transform(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final Term converted = SmtUtils.convertApplicationTerm(appTerm, newArgs, mScript);
		setResult(encodeEquality(converted));
	}

	private Term encodeEquality(final Term term) {
		if (!(term instanceof ApplicationTerm)) {
			return term;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;
		if (!"=".equals(appTerm.getFunction().getName()) || appTerm.getParameters().length != 2) {
			return term;
		}
		final Term lhs = appTerm.getParameters()[0];
		final Term rhs = appTerm.getParameters()[1];
		Term result = isIte(lhs) ? decide(lhs, rhs, new HashMap<>()) : null;
		if (result == null && isIte(rhs)) {
			result = decide(rhs, lhs, new HashMap<>());
		}
		return result == null ? term : result;
	}

	/**
	 * Decides a comparison of an ite term with {@code other} on the leaves of the ite term.
	 *
	 * @param decided
	 *            the results so far: ite terms share subterms, whose repeated visits would take exponentially long
	 * @return a Boolean term equivalent to {@code (= term other)} without this equality, or null if some leaf of
	 *         {@code term} does not decide it
	 */
	private Term decide(final Term term, final Term other, final Map<Term, Term> decided) {
		final Term known = decided.get(term);
		if (known != null) {
			return known;
		}
		final Term result;
		if (isIte(term)) {
			final Term[] params = ((ApplicationTerm) term).getParameters();
			final Term ifDecided = decide(params[1], other, decided);
			if (ifDecided == null) {
				return null;
			}
			final Term elseDecided = decide(params[2], other, decided);
			if (elseDecided == null) {
				return null;
			}
			result = SmtUtils.or(mScript, SmtUtils.and(mScript, params[0], ifDecided),
					SmtUtils.and(mScript, SmtUtils.not(mScript, params[0]), elseDecided));
		} else {
			final Term equality = SmtUtils.binaryEquality(mScript, term, other);
			if (!SmtUtils.isTrueLiteral(equality) && !SmtUtils.isFalseLiteral(equality)) {
				return null;
			}
			result = equality;
		}
		decided.put(term, result);
		return result;
	}

	private static boolean isIte(final Term term) {
		return term instanceof ApplicationTerm && "ite".equals(((ApplicationTerm) term).getFunction().getName());
	}
}
