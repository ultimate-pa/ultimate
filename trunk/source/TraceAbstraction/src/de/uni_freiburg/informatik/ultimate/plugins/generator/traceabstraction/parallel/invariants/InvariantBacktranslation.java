/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * The backtranslation of the invariants of k-induction to C, for the correctness witnesses of
 * {@code ParallelNwaCegarLoop} and {@code NwaCegarLoopWithKInduction}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantBacktranslation {
	/**
	 * FloydHoareUtils.createInvariantResults leaves out the whole invariant of a location if a part of it cannot be
	 * backtranslated to C: variables without a C counterpart (#memory_int, the !base of an array, currentRoundingMode),
	 * a variable out of the C block scope at the loop head, bit-vector extracts or quantifiers. In the 11-10 run 50
	 * k-induction proofs lost invariants that way, 36 of them all. Instead, every literal of the and/or structure that
	 * cannot be backtranslated is replaced by true. This weakens the invariant, so it still holds at its location, and
	 * since the backtranslation is compositional over and/or, the rest translates as a whole.
	 * <p>
	 * Each literal that cannot be backtranslated reports one "Unfinished Backtranslation" result, as the whole
	 * invariant did before.
	 *
	 * @return {@code invariant} with every literal that cannot be backtranslated at {@code loc} replaced by true
	 */
	public static Term weakenToBacktranslatable(final Term invariant, final IcfgLocation loc, final Script script,
			final IBacktranslationService backtranslation, final ILogger logger) {
		final ILocation context = ILocation.getAnnotation(loc);
		final Map<Term, Boolean> translatable = new HashMap<>();
		final Term result = weakenToBacktranslatable(invariant, context, translatable, script, backtranslation, logger);
		final long dropped = translatable.values().stream().filter(ok -> !ok).count();
		if (dropped > 0) {
			logger.info("Main: k-induction invariant at %s: %d of %d literal(s) cannot be backtranslated, replaced by "
					+ "true", loc, dropped, translatable.size());
		}
		return result;
	}

	private static Term weakenToBacktranslatable(final Term term, final ILocation context,
			final Map<Term, Boolean> translatable, final Script script, final IBacktranslationService backtranslation,
			final ILogger logger) {
		if (term instanceof final ApplicationTerm appTerm) {
			final String connective = appTerm.getFunction().getName();
			if ("and".equals(connective) || "or".equals(connective)) {
				final List<Term> weakened = new ArrayList<>();
				for (final Term param : appTerm.getParameters()) {
					weakened.add(
							weakenToBacktranslatable(param, context, translatable, script, backtranslation, logger));
				}
				return "and".equals(connective) ? SmtUtils.and(script, weakened) : SmtUtils.or(script, weakened);
			}
		}
		if (SmtUtils.isTrueLiteral(term) || SmtUtils.isFalseLiteral(term)) {
			return term;
		}
		return translatable.computeIfAbsent(term,
				literal -> canBacktranslate(literal, context, backtranslation, logger)) ? term : script.term("true");
	}

	/**
	 * The same backtranslation as FloydHoareUtils.createInvariantResults, which reports and returns null on failure.
	 */
	private static boolean canBacktranslate(final Term literal, final ILocation context,
			final IBacktranslationService backtranslation, final ILogger logger) {
		try {
			final var translated = backtranslation.translateExpressionWithContext(literal, context, Term.class);
			return translated != null && backtranslation.targetExpressionToString(translated) != null;
		} catch (final RuntimeException e) {
			logger.warn("Main: backtranslating the k-induction invariant literal %s failed: %s", literal, e);
			return false;
		}
	}

	private InvariantBacktranslation() {
		// static methods only
	}
}
