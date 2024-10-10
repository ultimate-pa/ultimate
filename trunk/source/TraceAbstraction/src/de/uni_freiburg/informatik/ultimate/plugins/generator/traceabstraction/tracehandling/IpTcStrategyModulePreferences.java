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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.pdr.Pdr;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InterpolatingTraceCheckPathInvariantsWithFallback;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;

/**
 * Creates a {@link IInterpolatingTraceCheck} based on the current preferences.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class IpTcStrategyModulePreferences<L extends IIcfgTransition<?>>
		extends IpTcStrategyModuleTraceCheck<IInterpolatingTraceCheck<L>, L> {

	private final InterpolationTechnique mInterpolationTechnique;
	private final Class<L> mTransitionClazz;

	public IpTcStrategyModulePreferences(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<L> prefs, final Word<L> counterExample,
			final List<?> controlConfigurationSequence, final IPredicate precondition, final IPredicate postcondition,
			final AssertionOrderModulation<L> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
			final PredicateFactory predicateFactory, final Class<L> transitionClazz) {
		super(taskIdentifier, services, prefs, counterExample, controlConfigurationSequence, precondition,
				postcondition, assertionOrderModulation, predicateUnifier, predicateFactory);
		mInterpolationTechnique = mPrefs.getInterpolationTechnique();
		if (mInterpolationTechnique == null) {
			throw new UnsupportedOperationException("Cannot interpolate without a technique");
		}
		mTransitionClazz = transitionClazz;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IInterpolatingTraceCheck<L> construct() {
		final AssertCodeBlockOrder assertionOrder =
				mAssertionOrderModulation.get(mCounterexample, mInterpolationTechnique);
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
		final TreeMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final NestedWord<L> nestedWord = NestedWord.nestedWord(mCounterexample);

		final ManagedScript managedScript = constructManagedScript();

		switch (mInterpolationTechnique) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			final boolean instantiateArrayExt = true;
			final boolean innerRecursiveNestedInterpolationCall = false;
			return new InterpolatingTraceCheckCraig<>(mPrecondition, mPostcondition, pendingContexts, nestedWord,
					mControlConfigurationSequence, mServices, mPrefs.getCfgSmtToolkit(), managedScript,
					mPredicateFactory, mPredicateUnifier, assertionOrder, mPrefs.computeCounterexample(),
					mPrefs.collectInterpolantStatistics(), mInterpolationTechnique, instantiateArrayExt,
					simplificationTechnique, innerRecursiveNestedInterpolationCall);
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
			return new TraceCheckSpWp<>(mPrecondition, mPostcondition, pendingContexts, nestedWord,
					mPrefs.getCfgSmtToolkit(), assertionOrder, mPrefs.getUnsatCores(), mPrefs.getUseLiveVariables(),
					mServices, mPrefs.computeCounterexample(), mPredicateFactory, mPredicateUnifier,
					mInterpolationTechnique, managedScript, simplificationTechnique, mControlConfigurationSequence,
					mPrefs.collectInterpolantStatistics());
		case PathInvariants:
			final IIcfg<?> icfgContainer = mPrefs.getIcfgContainer();
			final boolean useNonlinearConstraints = mPrefs.getUseNonlinearConstraints();
			final boolean useUnsatCores = mPrefs.getUseVarsFromUnsatCore();
			final boolean useAbstractInterpretationPredicates = mPrefs.getUseAbstractInterpretation();
			final boolean useWpPredicates = mPrefs.getUseWeakestPreconditionForPathInvariants();

			final SolverSettings solverSettings = mPrefs.constructSolverSettings(mTaskIdentifier)
					.setUseFakeIncrementalScript(false).setUseExternalSolver(ExternalSolver.Z3, 12000);

			final InvariantSynthesisSettings invariantSynthesisSettings = new InvariantSynthesisSettings(solverSettings,
					useNonlinearConstraints, useUnsatCores, useAbstractInterpretationPredicates, useWpPredicates, true);

			return new InterpolatingTraceCheckPathInvariantsWithFallback<>(mPrecondition, mPostcondition,
					pendingContexts, (NestedRun<L, IPredicate>) mCounterexample, mPrefs.getCfgSmtToolkit(),
					assertionOrder, mServices, mPrefs.computeCounterexample(), mPredicateFactory, mPredicateUnifier,
					invariantSynthesisSettings, simplificationTechnique, icfgContainer,
					mPrefs.collectInterpolantStatistics());
		case PDR:
			return new Pdr<>(mServices, mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), mPrefs,
					mPredicateUnifier, mPrecondition, mPostcondition, mCounterexample.asList(), mTransitionClazz);
		default:
			throw new UnsupportedOperationException("Unsupported interpolation technique: " + mInterpolationTechnique);
		}

	}

	private ManagedScript constructManagedScript() throws AssertionError {
		if (mInterpolationTechnique == InterpolationTechnique.PathInvariants) {
			// Path invariants construct their own solver
			return null;
		}
		if (mPrefs.getUseSeparateSolverForTracechecks()) {
			final SolverSettings solverSettings = mPrefs.constructSolverSettings(mTaskIdentifier);
			return mPrefs.getCfgSmtToolkit().createFreshManagedScript(mServices, solverSettings);
		}
		return mPrefs.getCfgSmtToolkit().getManagedScript();
	}

	@Override
	public Collection<QualifiedTracePredicates> getPerfectInterpolantSequences() {
		final IInterpolatingTraceCheck<L> tc = getOrConstruct();
		if (tc instanceof TraceCheckSpWp<?>) {
			final TraceCheckSpWp<?> spwpTc = (TraceCheckSpWp<?>) tc;
			final Collection<QualifiedTracePredicates> rtr = new ArrayList<>();

			if (spwpTc.wasForwardPredicateComputationRequested() && spwpTc.isForwardSequencePerfect()) {
				rtr.add(new QualifiedTracePredicates(spwpTc.getForwardIpp(), spwpTc.getClass(), true));
			}
			if (spwpTc.wasBackwardSequenceConstructed() && spwpTc.isBackwardSequencePerfect()) {
				rtr.add(new QualifiedTracePredicates(spwpTc.getBackwardIpp(), spwpTc.getClass(), true));
			}
			return rtr;
		}
		return super.getPerfectInterpolantSequences();
	}

	@Override
	public Collection<QualifiedTracePredicates> getImperfectInterpolantSequences() {
		final IInterpolatingTraceCheck<L> tc = getOrConstruct();
		if (tc instanceof TraceCheckSpWp<?>) {
			final TraceCheckSpWp<?> spwpTc = (TraceCheckSpWp<?>) tc;
			final Collection<QualifiedTracePredicates> rtr = new ArrayList<>();

			if (spwpTc.wasForwardPredicateComputationRequested() && !spwpTc.isForwardSequencePerfect()) {
				rtr.add(new QualifiedTracePredicates(spwpTc.getForwardIpp(), spwpTc.getClass(), false));
			}
			if (spwpTc.wasBackwardSequenceConstructed() && !spwpTc.isBackwardSequencePerfect()) {
				rtr.add(new QualifiedTracePredicates(spwpTc.getBackwardIpp(), spwpTc.getClass(), false));
			}
			return rtr;
		}
		return super.getImperfectInterpolantSequences();
	}
}
