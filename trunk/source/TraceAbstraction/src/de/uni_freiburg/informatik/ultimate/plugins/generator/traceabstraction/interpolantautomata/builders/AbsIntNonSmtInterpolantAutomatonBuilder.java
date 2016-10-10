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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntNonSmtInterpolantAutomatonBuilder implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final IRun<CodeBlock, IPredicate> mCurrentCounterExample;
	private final PredicateFactory mPredicateFactory;
	private final ManagedScript mBoogie2Smt;

	public AbsIntNonSmtInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction, final PredicateUnifier predUnifier,
			final ManagedScript smtManager, final Boogie2SmtSymbolTable symbolTable,
			final IRun<CodeBlock, IPredicate> currentCounterexample,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCurrentCounterExample = currentCounterexample;
		mBoogie2Smt = smtManager;
		mPredicateFactory = new PredicateFactory(services, mBoogie2Smt, symbolTable, simplificationTechnique,
				xnfConversionTechnique);

		mResult = getPathProgramAutomaton(oldAbstraction, predUnifier);
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomaton(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction,
			final PredicateUnifier predicateUnifier) {
		return getPathProgramAutomatonNew(oldAbstraction, predicateUnifier);
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomatonNew(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction,
			final PredicateUnifier predicateUnifier) {
		mLogger.info("Creating interpolant automaton from AI using abstract post for generalization");

		final NestedRun<CodeBlock, IPredicate> cex = (NestedRun<CodeBlock, IPredicate>) mCurrentCounterExample;
		final ArrayList<IPredicate> stateSequence = cex.getStateSequence();

		if (stateSequence.size() <= 1) {
			throw new AssertionError("Unexpected: state sequence size <= 1");
		}

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());

		final Map<IPredicate, IPredicate> newStates = new HashMap<>();
		final Map<Call, IPredicate> callHierPreds = new HashMap<>();
		final Word<CodeBlock> word = cex.getWord();
		int i = 0;
		for (final CodeBlock symbol : word) {
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
			if (symbol instanceof Call) {
				callHierPreds.put((Call) symbol, newPrevState);
				result.addCallTransition(newPrevState, symbol, newSuccState);
			} else if (symbol instanceof Return) {
				final Return returnSymbol = (Return) symbol;
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
