/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder.SifaComponents;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * {@link IInterpolatingTraceCheck} that performs symbolic interpretation with fluid abstractions (SIFA).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class SifaRunner<L extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<L> {

	private final SifaStats mStats;
	private final IPredicate[] mInterpolants;
	private final LBool mIsCorrect;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final boolean mTracecheckFinishedNormally;
	private final TraceCheckReasonUnknown mTraceCheckReasonUnknown;
	private final List<L> mTrace;
	private final IPredicateUnifier mPredicateUnifier;
	private final InterpolantComputationStatus mInterpolantComputationStatus;

	public SifaRunner(final IUltimateServiceProvider services, final ILogger logger, final IIcfg<?> icfg,
			final IRun<L, ?> currentCex, final IPredicateUnifier unifier) {
		mTrace = currentCex.getWord().asList();
		mPredicateUnifier = unifier;
		mPrecondition = mPredicateUnifier.getTruePredicate();
		final Set<L> pathProgramSet = currentCex.getWord().asSet();
		final PathProgramConstructionResult ppConstructionResult = PathProgram.constructPathProgram("sifa-path-program",
				icfg, pathProgramSet, Collections.emptySet());
		final PathProgram pp = ppConstructionResult.getPathProgram();

		final List<IcfgLocation> locationOfInterestList =
				TraceCheckUtils.getSequenceOfProgramPoints(currentCex.getWord()).stream()
						.map(a -> ppConstructionResult.getLocationMapping().get(a)).collect(Collectors.toList());
		final Collection<IcfgLocation> locationOfInterestSet = new HashSet<>(locationOfInterestList);
		final SifaComponents sifaComponents = new SifaBuilder(services, logger).construct(pp,
				services.getProgressMonitorService(), locationOfInterestSet);
		final Map<IcfgLocation, IPredicate> predicates;
		try {
			predicates = sifaComponents.getIcfgInterpreter().interpret();
		} catch (final ToolchainCanceledException tce) {
			mTracecheckFinishedNormally = false;
			mPostcondition = null;
			mInterpolants = null;
			mStats = null;
			mIsCorrect = LBool.UNKNOWN;
			mTraceCheckReasonUnknown =
					new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, tce, ExceptionHandlingCategory.KNOWN_IGNORE);
			mInterpolantComputationStatus = new InterpolantComputationStatus(ItpErrorStatus.OTHER, tce);
			return;
		}

		final IcfgLocation errorLoc = locationOfInterestList.get(locationOfInterestList.size() - 1);
		mPostcondition = unifier.getOrConstructPredicate(predicates.get(errorLoc).getFormula());
		assert mPostcondition != null;
		mInterpolants = generateInterpolants(locationOfInterestList, predicates, unifier);

		assert TraceCheckUtils.checkInterpolantsInductivityForward(Arrays.asList(mInterpolants),
				NestedWord.nestedWord(currentCex.getWord()), mPrecondition, mPostcondition, Collections.emptyMap(),
				getClass().getSimpleName(), icfg.getCfgSmtToolkit(), logger);
		mStats = sifaComponents.getStats();
		if (unifier.getFalsePredicate() == mPostcondition) {
			mIsCorrect = LBool.UNSAT;
			mTraceCheckReasonUnknown = null;
			mInterpolantComputationStatus = new InterpolantComputationStatus();
		} else {
			mIsCorrect = LBool.UNKNOWN;
			mTraceCheckReasonUnknown = new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null,
					ExceptionHandlingCategory.KNOWN_IGNORE);
			mInterpolantComputationStatus = new InterpolantComputationStatus(ItpErrorStatus.ALGORITHM_FAILED, null);
			logger.info("Sifa could not show that error location is unreachable, found '%s' at error location",
					mPostcondition);
		}
		mTracecheckFinishedNormally = true;
	}

	private static IPredicate[] generateInterpolants(final List<? extends IcfgLocation> locationSequence,
			final Map<IcfgLocation, IPredicate> predicates, final IPredicateUnifier unifier) {
		// the first location and the last location do not yield interpolants;
		final int length = locationSequence.size();
		final IPredicate[] rtr = new IPredicate[length - 2];
		int i = 0;
		int j = 0;
		for (final IcfgLocation location : locationSequence) {
			final IPredicate predicate = predicates.get(location);
			assert predicate != null;
			if (i != 0 && i != length - 1) {
				rtr[j] = unifier.getOrConstructPredicate(predicate.getFormula());
				j++;
			}
			i++;
		}
		return rtr;
	}

	@Override
	public LBool isCorrect() {
		return mIsCorrect;
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return false;
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStats;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mTraceCheckReasonUnknown;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTracecheckFinishedNormally;
	}

	@Override
	public List<L> getTrace() {
		return mTrace;
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// because Sifa analyzes the path program, we always find inductive invariants if we prove correctness.
		return isCorrect() == LBool.UNSAT;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

}
