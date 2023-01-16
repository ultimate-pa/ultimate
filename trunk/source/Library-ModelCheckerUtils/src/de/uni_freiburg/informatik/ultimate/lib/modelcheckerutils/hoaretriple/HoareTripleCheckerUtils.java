/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;

/**
 * Provides helper methods for {@link IHoareTripleChecker}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class HoareTripleCheckerUtils {

	private static final boolean REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED = true;
	private static final boolean REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED = true;

	/**
	 * Let Hoare triple checker immediately say `unknown` if one of the predicates is quantified.
	 */
	private static final boolean UNKNOWN_FOR_ALL_QUANTIFIED_PREDICATES = false;
	/**
	 * Let Hoare triple checker immediately say `unknown` if the action is quantified.
	 */
	private static final boolean UNKNOWN_FOR_ALL_QUANTIFIED_TRANSFORMULAS = false;

	private HoareTripleCheckerUtils() {
		// do not instantiate utility class
	}

	/**
	 *
	 * @param services
	 * @param hoareTripleChecks
	 * @param csToolkit
	 * @param unifier
	 * @return
	 * @throws AssertionError
	 */
	public static ChainingHoareTripleChecker constructEfficientHoareTripleChecker(
			final IUltimateServiceProvider services, final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier unifier) {
		final ILogger logger = services.getLoggingService().getLogger(HoareTripleCheckerUtils.class);
		final ChainingHoareTripleChecker sdHtc = constructSdHoareTripleChecker(logger, csToolkit, unifier);
		final ChainingHoareTripleChecker solverHtc =
				constructSmtHoareTripleChecker(logger, hoareTripleChecks, csToolkit, unifier);
		return sdHtc.andThen(solverHtc);
	}

	public static ChainingHoareTripleChecker constructSdHoareTripleChecker(final ILogger logger,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier unifier) {
		ChainingHoareTripleChecker chain =
				ChainingHoareTripleChecker.with(logger, new SdHoareTripleChecker(csToolkit, unifier));
		if (REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED) {
			chain = chain.reviewWith(new MonolithicHoareTripleChecker(csToolkit));
		}
		return chain;
	}

	public static ChainingHoareTripleChecker constructSmtHoareTripleChecker(final ILogger logger,
			final HoareTripleChecks hoareTripleChecks, final CfgSmtToolkit csToolkit, final IPredicateUnifier unifier) {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = new MonolithicHoareTripleChecker(csToolkit);
			break;
		case INCREMENTAL:
			solverHtc = new IncrementalHoareTripleChecker(csToolkit, false);
			break;
		default:
			throw new UnsupportedOperationException("unknown value " + hoareTripleChecks);
		}

		ChainingHoareTripleChecker chain = ChainingHoareTripleChecker.with(logger, solverHtc);
		// protect against quantified transition formulas and intricate predicates
		final SubtermPropertyChecker quantifierFinder = new SubtermPropertyChecker(QuantifiedFormula.class::isInstance);
		final Predicate<IPredicate> quantifierProtectionForPredicates;
		if (UNKNOWN_FOR_ALL_QUANTIFIED_PREDICATES) {
			quantifierProtectionForPredicates = (p -> unifier.isIntricatePredicate(p)
					|| quantifierFinder.isSatisfiedBySomeSubterm(p.getFormula()));
		} else {
			quantifierProtectionForPredicates = (p -> unifier.isIntricatePredicate(p));
		}
		chain = chain.predicatesProtectedBy(quantifierProtectionForPredicates);
		if (UNKNOWN_FOR_ALL_QUANTIFIED_TRANSFORMULAS) {
			final Predicate<IAction> noQuantifier =
					a -> quantifierFinder.isSatisfiedBySomeSubterm(a.getTransformula().getFormula());
			chain = chain.actionsProtectedBy(noQuantifier);
		}
		if (REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED) {
			chain = chain.reviewWith(new MonolithicHoareTripleChecker(csToolkit));
		}
		return chain;
	}

	public static IHoareTripleChecker constructEfficientHoareTripleCheckerWithCaching(
			final IUltimateServiceProvider services, final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier) {
		// TODO: Cache support in ChainingHtc
		return new CachingHoareTripleChecker(services,
				constructEfficientHoareTripleChecker(services, hoareTripleChecks, csToolkit, predicateUnifier),
				predicateUnifier);
	}

	public static IHoareTripleChecker constructEfficientHoareTripleCheckerWithCaching(
			final IUltimateServiceProvider services, final HoareTripleChecks hoareTripleChecks,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier,
			final HoareTripleCheckerCache initialCache) {
		// TODO: Cache support in ChainingHtc
		return new CachingHoareTripleChecker(services,
				constructEfficientHoareTripleChecker(services, hoareTripleChecks, csToolkit, predicateUnifier),
				predicateUnifier, initialCache);
	}

	/**
	 * Hoare triple check mode.
	 */
	public enum HoareTripleChecks {
		MONOLITHIC, INCREMENTAL
	}

}
