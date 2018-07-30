/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntNonSmtInterpolantAutomatonBuilder<LETTER>
		implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final IRun<LETTER, IPredicate, ?> mCurrentCounterExample;
	private final PredicateFactory mPredicateFactory;
	private final ManagedScript mBoogie2Smt;

	public AbsIntNonSmtInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction, final IPredicateUnifier predUnifier,
			final ManagedScript csToolkit, final IIcfgSymbolTable symbolTable,
			final IRun<LETTER, IPredicate, ?> currentCounterexample,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCurrentCounterExample = currentCounterexample;
		mBoogie2Smt = csToolkit;
		mPredicateFactory = new PredicateFactory(services, mBoogie2Smt, symbolTable, simplificationTechnique,
				xnfConversionTechnique);

		mResult = getPathProgramAutomaton(oldAbstraction, predUnifier, emptyStackFactory);
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<LETTER, IPredicate> getPathProgramAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction,
			final IPredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		return getPathProgramAutomatonNew(oldAbstraction, predicateUnifier, emptyStackFactory);
	}

	private NestedWordAutomaton<LETTER, IPredicate> getPathProgramAutomatonNew(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction,
			final IPredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mLogger.info("Creating interpolant automaton from AI using abstract post for generalization");

		final NestedRun<LETTER, IPredicate> cex = (NestedRun<LETTER, IPredicate>) mCurrentCounterExample;
		final ArrayList<IPredicate> stateSequence = cex.getStateSequence();

		if (stateSequence.size() <= 1) {
			throw new AssertionError("Unexpected: state sequence size <= 1");
		}

		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getVpAlphabet(), emptyStackFactory);

		final Map<IPredicate, IPredicate> newStates = new HashMap<>();
		final Map<LETTER, IPredicate> callHierPreds = new HashMap<>();
		final Word<LETTER> word = cex.getWord();
		int i = 0;
		for (final LETTER symbol : word) {
			final IPredicate prevState = stateSequence.get(i);
			final IPredicate succState = stateSequence.get(i + 1);
			++i;

			IPredicate newPrevState = newStates.get(prevState);
			if (newPrevState == null) {
				newPrevState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
				newStates.put(prevState, newPrevState);
				if (i == 1) {
					// the initial state is initial
					result.addState(true, false, newPrevState);
				} else {
					result.addState(false, false, newPrevState);
				}
			}

			IPredicate newSuccState = newStates.get(succState);
			if (newSuccState == null) {
				if (i == stateSequence.size() - 1) {
					// the last state is always an error state
					newSuccState = predicateUnifier.getFalsePredicate();
					result.addState(false, true, newSuccState);
				} else {
					newSuccState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
					result.addState(false, false, newSuccState);
				}
				newStates.put(succState, newSuccState);
			}

			// Add transition
			if (symbol instanceof IIcfgCallTransition<?>) {
				callHierPreds.put(symbol, newPrevState);
				result.addCallTransition(newPrevState, symbol, newSuccState);
			} else if (symbol instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> returnSymbol = (IIcfgReturnTransition<?, ?>) symbol;
				final IPredicate hierState = callHierPreds.get(returnSymbol.getCorrespondingCall());
				assert hierState != null : "Call has to be seen before return";
				result.addReturnTransition(newPrevState, hierState, symbol, newSuccState);
			} else {
				result.addInternalTransition(newPrevState, symbol, newSuccState);
			}
		}

		// Add self-loops to final state
		if (!result.getFinalStates().isEmpty()) {
			for (final IPredicate finalState : result.getFinalStates()) {
				oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
			}
		}

		return result;
	}

}
