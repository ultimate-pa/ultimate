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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;

/**
 * Creates internal instance of SMTInterpol.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IpTcStrategyModuleSmtInterpolCraig<LETTER extends IIcfgTransition<?>>
		extends IpTcStrategyModuleCraig<LETTER> {

	private static final InterpolationTechnique[] SUPPORTED_TECHNIQUES = new InterpolationTechnique[] {
			InterpolationTechnique.Craig_NestedInterpolation, InterpolationTechnique.Craig_TreeInterpolation, };

	private final long mTimeoutInMillis;
	private final InterpolationTechnique mInterpolationTechnique;

	public IpTcStrategyModuleSmtInterpolCraig(final TaskIdentifier taskIdentifier,
			final IUltimateServiceProvider services, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final Word<LETTER> counterExample, final List<?> controlConfigurationSequence,
			final IPredicate precondition, final IPredicate postcondition,
			final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
			final PredicateFactory predicateFactory, final long timeoutInMillis,
			final InterpolationTechnique interpolationTechnique) {
		super(taskIdentifier, services, prefs, counterExample, controlConfigurationSequence, precondition,
				postcondition, assertionOrderModulation, predicateUnifier, predicateFactory);
		mTimeoutInMillis = timeoutInMillis;
		mInterpolationTechnique = interpolationTechnique;
		assert Arrays.stream(SUPPORTED_TECHNIQUES).anyMatch(
				a -> a == mInterpolationTechnique) : "Unsupported interpolation technique " + mInterpolationTechnique;
	}

	@Override
	protected ManagedScript constructManagedScript() {
		final long timeout = computeTimeout(mTimeoutInMillis);
		final SolverMode solverMode = SolverMode.Internal_SMTInterpol;

		final SolverSettings solverSettings = mPrefs.constructSolverSettings(mTaskIdentifier).setSolverMode(solverMode)
				.setSmtInterpolTimeout(timeout);
		return createExternalManagedScript(solverSettings);
	}

	@Override
	protected final InterpolationTechnique getInterpolationTechnique() {
		return mInterpolationTechnique;
	}
}
