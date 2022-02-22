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
public final class HoareTripleCheckerBuilder {

	private static final boolean REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED = true;
	private static final boolean REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final IPredicateUnifier mUnifier;

	public HoareTripleCheckerBuilder(final IUltimateServiceProvider services, final CfgSmtToolkit toolkit,
			final IPredicateUnifier unifier) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(HoareTripleCheckerBuilder.class);
		mCsToolkit = toolkit;
		mUnifier = unifier;
	}

	public ChainingHoareTripleChecker constructEfficientHoareTripleChecker(final HoareTripleChecks hoareTripleChecks) {
		final ChainingHoareTripleChecker sdHtc = constructSdHoareTripleChecker();
		final ChainingHoareTripleChecker solverHtc = constructSmtHoareTripleChecker(hoareTripleChecks);
		return sdHtc.andThen(solverHtc);
	}

	public ChainingHoareTripleChecker constructSdHoareTripleChecker() {
		ChainingHoareTripleChecker chain = ChainingHoareTripleChecker.with(mServices.getStorage(), mLogger,
				new SdHoareTripleChecker(mServices.getStorage(), mCsToolkit, mUnifier));
		if (REVIEW_SD_RESULTS_IF_ASSERTIONS_ENABLED) {
			chain = chain.reviewWith(constructMonolithicHoareTripleChecker());
		}
		return chain;
	}

	public IncrementalHoareTripleChecker constructIncrementalHoareTripleChecker() {
		return new IncrementalHoareTripleChecker(mServices.getStorage(), mCsToolkit, false);
	}

	public MonolithicHoareTripleChecker constructMonolithicHoareTripleChecker() {
		return new MonolithicHoareTripleChecker(mServices.getStorage(), mCsToolkit);
	}

	public ChainingHoareTripleChecker constructSmtHoareTripleChecker(final HoareTripleChecks hoareTripleChecks) {
		final IHoareTripleChecker solverHtc;
		switch (hoareTripleChecks) {
		case MONOLITHIC:
			solverHtc = constructMonolithicHoareTripleChecker();
			break;
		case INCREMENTAL:
			solverHtc = constructIncrementalHoareTripleChecker();
			break;
		default:
			throw new UnsupportedOperationException("unknown value " + hoareTripleChecks);
		}

		ChainingHoareTripleChecker chain = ChainingHoareTripleChecker.with(mServices.getStorage(), mLogger, solverHtc);
		// protect against quantified transition formulas and intricate predicates
		final SubtermPropertyChecker quantifierFinder = new SubtermPropertyChecker(QuantifiedFormula.class::isInstance);
		final Predicate<IPredicate> noIntricateNoQuantifier =
				p -> mUnifier.isIntricatePredicate(p) || quantifierFinder.isSatisfiedBySomeSubterm(p.getFormula());
		final Predicate<IAction> noQuantifier =
				a -> quantifierFinder.isSatisfiedBySomeSubterm(a.getTransformula().getFormula());
		chain = chain.predicatesProtectedBy(noIntricateNoQuantifier).actionsProtectedBy(noQuantifier);
		if (REVIEW_SMT_RESULTS_IF_ASSERTIONS_ENABLED) {
			chain = chain.reviewWith(constructMonolithicHoareTripleChecker());
		}
		return chain;
	}

	public IHoareTripleChecker
			constructEfficientHoareTripleCheckerWithCaching(final HoareTripleChecks hoareTripleChecks) {
		// TODO: Cache support in ChainingHtc
		return new CachingHoareTripleCheckerMap(mServices, constructEfficientHoareTripleChecker(hoareTripleChecks),
				mUnifier);
	}

	/**
	 * Hoare triple check mode.
	 */
	public enum HoareTripleChecks {
		MONOLITHIC, INCREMENTAL
	}

}
