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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.logic.Logics;

/**
 * Creates external instance of CVC 4 using {@link TraceCheckSpWp}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleCvc4<LETTER extends IIcfgTransition<?>> extends IpTcStrategyModuleSpWp<LETTER> {

	private static final InterpolationTechnique[] SUPPORTED_TECHNIQUES =
			new InterpolationTechnique[] { InterpolationTechnique.ForwardPredicates,
					InterpolationTechnique.ForwardPredicates, InterpolationTechnique.BackwardPredicates,
					InterpolationTechnique.FPandBP, InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect };

	private final InterpolationTechnique mInterpolationTechnique;
	private final boolean mUseTimeout;
	private final Logics mLogic;

	public IpTcStrategyModuleCvc4(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final IRun<LETTER, ?> counterExample,
			final IPredicate precondition, final IPredicate postcondition,
			final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
			final PredicateFactory predicateFactory, final boolean useTimeout,
			final InterpolationTechnique interpolationTechnique, final Logics cvc4Logic) {
		super(taskIdentifier, services, prefs, counterExample, precondition, postcondition, assertionOrderModulation,
				predicateUnifier, predicateFactory);
		mUseTimeout = useTimeout;
		mInterpolationTechnique = interpolationTechnique;
		mLogic = cvc4Logic;
		assert Arrays.stream(SUPPORTED_TECHNIQUES).anyMatch(
				a -> a == mInterpolationTechnique) : "Unsupported interpolation technique " + mInterpolationTechnique;
	}

	@Override
	protected ManagedScript constructManagedScript() {
		final String command = mUseTimeout ? SolverBuilder.COMMAND_CVC4_TIMEOUT : SolverBuilder.COMMAND_CVC4_NO_TIMEOUT;
		final SolverSettings solverSettings = mPrefs.constructSolverSettings(mTaskIdentifier)
				.setUseExternalSolver(true, command, mLogic).setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
		return createExternalManagedScript(solverSettings);
	}

	@Override
	protected final InterpolationTechnique getInterpolationTechnique() {
		return mInterpolationTechnique;
	}
}
