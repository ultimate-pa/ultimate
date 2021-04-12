/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark.AcceleratedInterpolationStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.AcceleratorFastUPR;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.AcceleratorJordan;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.AcceleratorWernerOverapprox;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.IAccelerator;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.ILoopdetector;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.Loopdetector;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor.ILoopPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor.LoopPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class AcceleratedInterpolation<LETTER extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<LETTER> {

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IRun<LETTER, IPredicate> mCounterexampleTrace;
	private final List<LETTER> mCounterexample;
	private final IPredicateUnifier mPredUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final PredicateHelper<LETTER> mPredHelper;
	private final ITraceCheckPreferences mPrefs;
	private final IIcfg<?> mIcfg;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private IProgramExecution<LETTER, Term> mFeasibleProgramExecution;
	private TraceCheckReasonUnknown mReasonUnknown;
	private boolean mTraceCheckFinishedNormally;
	private final AcceleratedInterpolationBenchmark mAccelInterpolBench;
	private final Class<LETTER> mTransitionClazz;

	/**
	 * Interpolation using loopacceleration
	 *
	 * @param logger
	 * @param prefs
	 * @param script
	 * @param predicateUnifier
	 * @param counterexample
	 * @param transitionClazz
	 */
	public AcceleratedInterpolation(final ILogger logger, final ITraceCheckPreferences prefs,
			final ManagedScript script, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate> counterexample, final Class<LETTER> transitionClazz,
			final String accelerationMethod) {
		mLogger = logger;
		mScript = script;
		mTransitionClazz = transitionClazz;
		mServices = prefs.getUltimateServices();
		mCounterexampleTrace = counterexample;
		mCounterexample = mCounterexampleTrace.getWord().asList();
		mPrefs = prefs;
		mAccelInterpolBench = new AcceleratedInterpolationBenchmark();
		mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_OVERALL);

		mIcfg = mPrefs.getIcfgContainer();
		mPredUnifier = predicateUnifier;
		mLogger.debug("Accelerated Interpolation engaged!");
		mPredTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));
		mPredHelper = new PredicateHelper<>(mPredUnifier, mPredTransformer, mLogger, mScript, mServices);
		mInterpolants = new IPredicate[mCounterexample.size()];

		final ILoopdetector<IcfgLocation, LETTER> loopdetector;
		final ILoopPreprocessor<IcfgLocation, LETTER, UnmodifiableTransFormula> loopPreprocessor;
		final IAccelerator loopAccelerator;

		final AcceleratedInterpolationCore<LETTER> accelInterpolCore;

		if ("FAST_UPR".equals(accelerationMethod)) {
			loopdetector = new Loopdetector<>(mCounterexample, mLogger, 1);
			final List<String> fastUPRPreprocessOptions = new ArrayList<>(Arrays.asList("ite", "mod", "!=", "not"));
			loopPreprocessor = new LoopPreprocessor<>(mLogger, mScript, mServices, mPredUnifier, mPredHelper,
					mIcfg.getCfgSmtToolkit(), fastUPRPreprocessOptions);
			loopAccelerator =
					new AcceleratorFastUPR(mLogger, mScript, mServices, mIcfg.getCfgSmtToolkit().getSymbolTable());

		} else if ("WERNER_OVERAPPROX".equals(accelerationMethod)) {
			loopdetector = new Loopdetector<>(mCounterexample, mLogger, 1);
			loopPreprocessor = new LoopPreprocessor<>(mLogger, mScript, mServices, mPredUnifier, mPredHelper,
					mIcfg.getCfgSmtToolkit(), new ArrayList<>(Arrays.asList("")));
			loopAccelerator = new AcceleratorWernerOverapprox(mLogger, mScript, mServices,
					mIcfg.getCfgSmtToolkit().getSymbolTable());

		} else if ("JORDAN".equals(accelerationMethod)) {
			loopdetector = new Loopdetector<>(mCounterexample, mLogger, 1);
			loopPreprocessor = new LoopPreprocessor<>(mLogger, mScript, mServices, mPredUnifier, mPredHelper,
					mIcfg.getCfgSmtToolkit(), new ArrayList<>(Arrays.asList("")));
			loopAccelerator = new AcceleratorJordan(mLogger, mScript, mServices);
		} else {
			throw new UnsupportedOperationException();
		}

		accelInterpolCore = new AcceleratedInterpolationCore<>(mLogger, mScript, mPredUnifier, mPrefs,
				mCounterexampleTrace, mIcfg, loopdetector, loopPreprocessor, loopAccelerator);

		try {
			mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_CORE);
			mIsTraceCorrect = accelInterpolCore.acceleratedInterpolationCoreIsCorrect();
			if (mIsTraceCorrect == LBool.UNSAT) {
				mInterpolants = accelInterpolCore.getInterpolants();
			}

			/*
			 * Quick fix for unsound false: Sometimes the interpolator returns unknown.
			 */
			if (mIsTraceCorrect == LBool.UNKNOWN) {
				mReasonUnknown = new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null,
						ExceptionHandlingCategory.KNOWN_DEPENDING);
				mTraceCheckFinishedNormally = true;
			} else {
				mTraceCheckFinishedNormally = true;
				mReasonUnknown = null;
			}
		} catch (final ToolchainCanceledException tce) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mReasonUnknown = new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, tce,
					ExceptionHandlingCategory.KNOWN_DEPENDING);
		} catch (final SMTLIBException e) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mReasonUnknown = TraceCheckReasonUnknown.constructReasonUnknown(e);
		} finally {
			mAccelInterpolBench.stopAllStopwatches();
			mLogger.debug("Finished");
		}
	}

	private IProgramExecution<LETTER, Term> computeProgramExecution() {
		// TODO: construct a real IProgramExecution using
		// IcfgProgramExecutionBuilder (DD needs to refactor s.t. the
		// class becomes available here).
		if (mIsTraceCorrect == LBool.SAT) {
			return IProgramExecution.emptyExecution(Term.class, mTransitionClazz);
		}
		return null;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		if (isCorrect() == LBool.UNSAT) {
			return new InterpolantComputationStatus();
		} else if (isCorrect() == LBool.SAT) {
			return new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredUnifier.getFalsePredicate();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredUnifier.getTruePredicate();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredUnifier;
	}

	@Override
	public IProgramExecution<LETTER, Term> getRcfgProgramExecution() {
		if (mFeasibleProgramExecution == null) {
			mFeasibleProgramExecution = computeProgramExecution();
		}
		return mFeasibleProgramExecution;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<LETTER> getTrace() {
		return mCounterexample;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mReasonUnknown;
	}

	@Override
	public LBool isCorrect() {
		return mIsTraceCorrect;
	}

	@Override
	public boolean isPerfectSequence() {
		return isCorrect() == LBool.UNSAT;
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIsTraceCorrect != LBool.SAT;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinishedNormally;
	}

}
