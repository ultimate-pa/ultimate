/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * {@link IRefinementStrategy} that is used by Taipan. It first tries an {@link InterpolatingTraceCheck} using
 * {@link SMTInterpol} with {@link InterpolationTechnique#Craig_TreeInterpolation}.<br>
 * If successful and the interpolant sequence is perfect, those interpolants are used.<br>
 * If not successful, it tries {@link TraceCheck} {@code Z3} and, if again not successful, {@code CVC4}.<br>
 * If none of those is successful, the strategy gives up.<br>
 * Otherwise, if the trace is infeasible, the strategy uses an {@link CegarAbsIntRunner} to construct interpolants.<br>
 * If not successful, the strategy again tries {@code Z3} and {@code CVC4}, but this time using interpolation
 * {@link InterpolationTechnique#FPandBP}.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class LazyTaipanRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends BaseTaipanRefinementStrategy<LETTER> {

	protected boolean mZ3TraceCheckUnsuccessful;

	public LazyTaipanRefinementStrategy(final ILogger logger, final IUltimateServiceProvider services,
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
		return Mode.SMTINTERPOL;
	}

	@Override
	protected Mode getNextTraceCheckMode() {
		switch (getCurrentMode()) {
		case ABSTRACT_INTERPRETATION:
			return Mode.SMTINTERPOL;
		case SMTINTERPOL:
			return Mode.Z3_NO_IG;
		case Z3_NO_IG:
			mZ3TraceCheckUnsuccessful = true;
			return Mode.CVC4_NO_IG;
		case CVC4_NO_IG:
		case Z3_IG:
		case CVC4_IG:
			assert !hasNextTraceCheck();
			throw new NoSuchElementException("No next trace checker available.");
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + getCurrentMode());
		}
	}

	@Override
	protected Mode getNextInterpolantGenerator() {
		Mode nextMode;
		switch (getCurrentMode()) {
		case SMTINTERPOL:
			nextMode = Mode.Z3_IG;
			break;
		case Z3_IG:
			nextMode = Mode.CVC4_IG;
			break;
		case CVC4_IG:
			nextMode = Mode.ABSTRACT_INTERPRETATION;
			break;
		case ABSTRACT_INTERPRETATION:
		case Z3_NO_IG:
		case CVC4_NO_IG:
			assert !hasNextInterpolantGeneratorAvailable();
			throw new NoSuchElementException("No next interpolant generator available.");
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + getCurrentMode());
		}
		resetTraceCheck();
		return nextMode;
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
		final InterpolationTechnique interpolationTechnique;
		switch (mode) {
		case SMTINTERPOL:
			interpolationTechnique = InterpolationTechnique.Craig_TreeInterpolation;
			break;
		case Z3_IG:
		case CVC4_IG:
			interpolationTechnique = InterpolationTechnique.FPandBP;
			break;
		case Z3_NO_IG:
		case CVC4_NO_IG:
		case ABSTRACT_INTERPRETATION:
			interpolationTechnique = null;
			break;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + mode);
		}
		return interpolationTechnique;
	}

	@Override
	public boolean hasNextTraceCheck() {
		switch (getCurrentMode()) {
		case SMTINTERPOL:
		case Z3_NO_IG:
			return true;
		case CVC4_NO_IG:
		case ABSTRACT_INTERPRETATION:
		case Z3_IG:
		case CVC4_IG:
			return false;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + getCurrentMode());
		}
	}

	@Override
	protected boolean hasNextInterpolantGeneratorAvailable() {
		switch (getCurrentMode()) {
		case SMTINTERPOL:
		case CVC4_IG:
		case Z3_IG:
			return true;
		case ABSTRACT_INTERPRETATION:
		case Z3_NO_IG:
		case CVC4_NO_IG:
			return false;
		default:
			throw new IllegalArgumentException(UNKNOWN_MODE + getCurrentMode());
		}
	}
}
