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
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;

/**
 * Creates a {@link TraceCheckSpWp} based on instructions of subclass.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class IpTcStrategyModuleSpWp<LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleTraceCheck<TraceCheckSpWp<LETTER>, LETTER> {
	private final InterpolationTechnique mInterpolationTechnique;

	public IpTcStrategyModuleSpWp(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final IRun<LETTER, ?> counterExample,
			final IPredicate precondition, final IPredicate postcondition,
			final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
			final PredicateFactory predicateFactory, final InterpolationTechnique interpolationTechnique) {
		super(taskIdentifier, services, prefs, counterExample, precondition, postcondition, assertionOrderModulation,
				predicateUnifier, predicateFactory);
		mInterpolationTechnique = interpolationTechnique;
	}

	@Override
	public Collection<QualifiedTracePredicates> getPerfectInterpolantSequences() {
		final Collection<QualifiedTracePredicates> rtr = new ArrayList<>();
		final TraceCheckSpWp<LETTER> tc = getOrConstruct();
		if (tc.wasForwardPredicateComputationRequested() && tc.isForwardSequencePerfect()) {
			rtr.add(new QualifiedTracePredicates(tc.getForwardIpp(), tc.getClass(), true));
		}
		if (tc.wasBackwardSequenceConstructed() && tc.isBackwardSequencePerfect()) {
			rtr.add(new QualifiedTracePredicates(tc.getBackwardIpp(), tc.getClass(), true));
		}
		return rtr;
	}

	@Override
	public Collection<QualifiedTracePredicates> getImperfectInterpolantSequences() {
		final Collection<QualifiedTracePredicates> rtr = new ArrayList<>();
		final TraceCheckSpWp<LETTER> tc = getOrConstruct();
		if (tc.wasForwardPredicateComputationRequested() && !tc.isForwardSequencePerfect()) {
			rtr.add(new QualifiedTracePredicates(tc.getForwardIpp(), tc.getClass(), false));
		}
		if (tc.wasBackwardSequenceConstructed() && !tc.isBackwardSequencePerfect()) {
			rtr.add(new QualifiedTracePredicates(tc.getBackwardIpp(), tc.getClass(), false));
		}
		return rtr;
	}

	@Override
	protected TraceCheckSpWp<LETTER> construct() {
		assert mInterpolationTechnique == InterpolationTechnique.ForwardPredicates
				|| mInterpolationTechnique == InterpolationTechnique.BackwardPredicates
				|| mInterpolationTechnique == InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect
				|| mInterpolationTechnique == InterpolationTechnique.FPandBP;

		final AssertCodeBlockOrder assertionOrder =
				mAssertionOrderModulation.get(mCounterexample, mInterpolationTechnique);
		final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
		final ManagedScript managedScript = createExternalManagedScript(getSolverSettings());

		return new TraceCheckSpWp<>(mPrecondition, mPostcondition, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(mCounterexample.getWord()), mPrefs.getCfgSmtToolkit(), assertionOrder,
				mPrefs.getUnsatCores(), mPrefs.getUseLiveVariables(), mServices, mPrefs.computeCounterexample(),
				mPredicateFactory, mPredicateUnifier, mInterpolationTechnique, managedScript, simplificationTechnique,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(mCounterexample.getWord())),
				mPrefs.collectInterpolantStatistics());
	}

	protected abstract SolverSettings getSolverSettings();
}
