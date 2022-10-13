/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Collections;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.ChainingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.UnionPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ILooperCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.LooperIndependenceRelation;

class IndependenceProviderForLoopers<L extends IIcfgTransition<?>> implements IRefinableIndependenceProvider<L> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final IndependenceSettings.IndependenceType mType;

	private Set<IPredicate> mAbstractionLevel;

	private ChainingHoareTripleChecker mHtc;
	private UnionPredicateCoverageChecker mCoverage;

	public IndependenceProviderForLoopers(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IndependenceSettings.IndependenceType type) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(IndependenceProviderForLoopers.class);
		mCsToolkit = csToolkit;
		mType = type;
	}

	@Override
	public void initialize() {
		mAbstractionLevel = Collections.emptySet();
		if (mType != IndependenceType.SYNTACTIC) {
			mHtc = ChainingHoareTripleChecker.empty(mLogger);
			mCoverage = UnionPredicateCoverageChecker.empty();
		}
	}

	@Override
	public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
		mAbstractionLevel = LooperIndependenceRelation.refine(mAbstractionLevel, refinement);
		if (mType != IndependenceType.SYNTACTIC) {
			final Predicate<IPredicate> protection = p -> !refinement.getPredicateUnifier().isRepresentative(p);
			mHtc = mHtc.andThen(getHoareTripleChecker(refinement)).predicatesProtectedBy(protection);
			mCoverage = mCoverage.with(refinement.getPredicateUnifier().getCoverageRelation(), protection);
		}
	}

	@Override
	public IIndependenceRelation<IPredicate, L> retrieveIndependence() {
		return IndependenceBuilder
				.fromPredicateActionIndependence(new LooperIndependenceRelation<>(mAbstractionLevel, constructCheck()))
				.threadSeparated().build();
	}

	private IHoareTripleChecker getHoareTripleChecker(final IRefinementEngineResult<L, ?> refinement) {
		final IHoareTripleChecker refinementHtc = refinement.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				HoareTripleChecks.MONOLITHIC, mCsToolkit, refinement.getPredicateUnifier());
	}

	private ILooperCheck<L> constructCheck() {
		switch (mType) {
		case SEMANTIC:
			return new ILooperCheck.HoareLooperCheck<>(mHtc, mCoverage);
		case SYNTACTIC:
			return new ILooperCheck.IndependentLooperCheck<>();
		default:
			throw new UnsupportedOperationException("Unknown independence type " + mType);
		}
	}
}
