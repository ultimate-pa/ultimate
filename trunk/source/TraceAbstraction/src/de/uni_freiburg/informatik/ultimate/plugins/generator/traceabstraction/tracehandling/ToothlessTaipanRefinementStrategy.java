/*
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Collections;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * Taipan refinement strategy that only uses Abstract Interpretation and no SMT solver. There is also no possibility to
 * generate interpolants other than the generated AI predicates.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of ICFG transitions.
 */
public class ToothlessTaipanRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends BaseTaipanRefinementStrategy<LETTER> {

	public ToothlessTaipanRefinementStrategy(final ILogger logger, final IUltimateServiceProvider services,
			final TaCheckAndRefinementPreferences<LETTER> prefs, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final CegarAbsIntRunner<LETTER> absIntRunner,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition, final IAutomaton<LETTER, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		super(logger, services, prefs, cfgSmtToolkit, predicateFactory, predicateUnifier, absIntRunner,
				assertionOrderModulation, counterexample, precondition, abstraction, taskIdentifier, emptyStackFactory);
	}

	@Override
	protected Mode getInitialMode() {
		return Mode.ABSTRACT_INTERPRETATION;
	}

	@Override
	public boolean hasNextTraceCheck() {
		return false;
	}

	@Override
	protected Mode getNextTraceCheckMode() {
		throw new NoSuchElementException("No next interpolant generator available.");
	}

	@Override
	protected boolean hasNextInterpolantGeneratorAvailable() {
		return false;
	}

	@Override
	protected Mode getNextInterpolantGenerator() {
		throw new NoSuchElementException("No next interpolant generator available.");
	}

	@Override
	protected Mode getWindowsCvcReplacementMode(final Mode cvcMode) {
		if (cvcMode == Mode.CVC4_IG) {
			return Mode.Z3_IG;
		} else if (cvcMode == Mode.CVC4_NO_IG) {
			return Mode.Z3_NO_IG;
		}
		return cvcMode;
	}

	@Override
	protected InterpolationTechnique getInterpolationTechnique(final Mode mode) {
		return null;
	}

	@Override
	public LBool executeStrategy() {
		mAbsIntRunner.generateFixpoints(mCounterexample,
				(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) mAbstraction, mPredicateUnifierSmt);

		if (mAbsIntRunner.hasShownInfeasibility()) {
			final TracePredicates tp = new TracePredicates(getInterpolantGenerator());
			return constructAutomatonFromIpps(Collections.singletonList(tp), Collections.emptyList());
		}

		return LBool.UNKNOWN;
	}

	@Override
	public IInterpolantGenerator<LETTER> getInterpolantGenerator() {
		return mAbsIntRunner.getInterpolantGenerator();
	}
}
