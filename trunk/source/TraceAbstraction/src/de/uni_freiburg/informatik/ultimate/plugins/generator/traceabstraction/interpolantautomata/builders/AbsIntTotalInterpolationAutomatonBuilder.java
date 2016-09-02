/*
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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.ESymbolType;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Builder for an interpolant automaton from abstract interpretation counterexamples using total interpolation (all
 * possible edges between abstract states are being inserted).
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class AbsIntTotalInterpolationAutomatonBuilder implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {

	private static final long PRINT_PREDS_LIMIT = 30;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final SmtManager mSmtManager;
	private final IRun<CodeBlock, IPredicate> mCurrentCounterExample;
	private final RcfgStatementExtractor mStatementExtractor;
	private final VariableCollector mVariableCollector;

	public AbsIntTotalInterpolationAutomatonBuilder(final IUltimateServiceProvider services,
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
			final PredicateUnifier predicateUnifier, final SmtManager smtManager,
			final IRun<CodeBlock, IPredicate> currentCounterExample,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSmtManager = smtManager;
		mCurrentCounterExample = currentCounterExample;
		mVariableCollector = new VariableCollector();
		mStatementExtractor = new RcfgStatementExtractor();

		mResult = constructAutomaton(oldAbstraction, aiResult, predicateUnifier);
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> constructAutomaton(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
			final PredicateUnifier predicateUnifier) {

		mLogger.info("Creating total interpolated automaton from AI predicates.");

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());

		final NestedRun<CodeBlock, IPredicate> counterExample =
				(NestedRun<CodeBlock, IPredicate>) mCurrentCounterExample;
		final Word<CodeBlock> word = counterExample.getWord();

		final int wordLength = word.length();
		assert wordLength > 1 : "Unexpected: length of word smaller or equal to 1.";

		final Map<Call, IPredicate> callHierarchyPredicates = new HashMap<>();

		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final Set<IPredicate> alreadyThereAsState = new HashSet<>();
		IPredicate previous = predicateUnifier.getTruePredicate();
		alreadyThereAsState.add(previous);
		result.addState(true, false, previous);

		final Map<IAbstractState<?, CodeBlock, IBoogieVar>, IPredicate> stateToPredicate = new HashMap<>();

		for (int i = 0; i < wordLength; i++) {
			final CodeBlock symbol = word.getSymbol(i);

			final Set<IAbstractState<?, CodeBlock, IBoogieVar>> nextStates =
					(Set<IAbstractState<?, CodeBlock, IBoogieVar>>) aiResult.getLoc2States().get(symbol.getTarget());

			final IPredicate target;
			if (nextStates == null) {
				target = falsePredicate;
				if (mLogger.isDebugEnabled()) {
					if (i == 0) {
						mLogger.debug("------------------------------------------------");
					}
					mLogger.debug("Transition: " + symbol);
					mLogger.debug("Original Target States: NONE");
					mLogger.debug("Target Term: " + target);
					mLogger.debug("------------------------------------------------");
				}
			} else {
				target = predicateUnifier.getOrConstructPredicateForDisjunction(
						nextStates.stream().map(s -> s.getTerm(mSmtManager.getScript(), mSmtManager.getBoogie2Smt()))
								.map(predicateUnifier::getOrConstructPredicate).collect(Collectors.toSet()));

				nextStates.forEach(state -> stateToPredicate.put(state, target));

				if (mLogger.isDebugEnabled()) {
					if (i == 0) {
						mLogger.debug("------------------------------------------------");
					}
					mLogger.debug("Transition: " + symbol);
					mLogger.debug("Original Target States: " + nextStates);
					mLogger.debug("Target Term: " + target);
					mLogger.debug("------------------------------------------------");
				}
			}

			if (alreadyThereAsState.add(target)) {
				result.addState(false, falsePredicate.equals(target), target);
			}

			// Add transition
			if (symbol instanceof Call) {
				result.addCallTransition(previous, symbol, target);
				callHierarchyPredicates.put((Call) symbol, previous);
			} else if (symbol instanceof Return) {
				final Return returnSymbol = (Return) symbol;
				final IPredicate hierarchyState = callHierarchyPredicates.get(returnSymbol.getCorrespondingCall());
				assert hierarchyState != null : "Return does not have a corresponding call.";
				result.addReturnTransition(previous, hierarchyState, symbol, target);
			} else {
				result.addInternalTransition(previous, symbol, target);
			}

			previous = target;
		}

		// Add self-loops to final states
		if (!result.getFinalStates().isEmpty()) {
			for (final IPredicate finalState : result.getFinalStates()) {
				oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
			}
		}

		if (PRINT_PREDS_LIMIT < alreadyThereAsState.size()) {
			mLogger.info("Using "
					+ alreadyThereAsState.size() + " predicates from AI: " + String.join(",", alreadyThereAsState
							.stream().limit(PRINT_PREDS_LIMIT).map(a -> a.toString()).collect(Collectors.toList()))
					+ "...");
		} else {
			mLogger.info("Using " + alreadyThereAsState.size() + " predicates from AI: " + String.join(",",
					alreadyThereAsState.stream().map(a -> a.toString()).collect(Collectors.toList())));
		}

		int numberOfTransitionsBeforeEnhancement = 0;

		if (mLogger.isDebugEnabled()) {
			final Analyze<CodeBlock, IPredicate> analyze =
					new Analyze<>(new AutomataLibraryServices(mServices), result);
			numberOfTransitionsBeforeEnhancement = analyze.getNumberOfTransitions(ESymbolType.TOTAL);
		}

		final IAbstractPostOperator<?, CodeBlock, IBoogieVar> postOperator = aiResult.getUsedDomain().getPostOperator();
		final Iterator<CodeBlock> letterIterator = oldAbstraction.getAlphabet().iterator();

		final Set<IAbstractState<?, CodeBlock, IBoogieVar>> allStates = stateToPredicate.keySet();

		while (letterIterator.hasNext()) {
			final CodeBlock currentLetter = letterIterator.next();

			// Skip call and return symbols.
			if (currentLetter instanceof Call || currentLetter instanceof Return) {
				continue;
			}

			final Set<String> variableNames =
					mVariableCollector.collectVariableNames(currentLetter, mStatementExtractor);

			final Iterator<IAbstractState<?, CodeBlock, IBoogieVar>> stateIterator = allStates.iterator();
			while (stateIterator.hasNext()) {
				final IAbstractState<?, CodeBlock, IBoogieVar> current = stateIterator.next();
				if (!areCompatible(current, variableNames)) {
					continue;
				}
				final List<IAbstractState> post = applyPostInternally(current, postOperator, currentLetter);

				for (final IAbstractState postState : post) {
					if (postState.isBottom()) {
						continue;
					}
					allStates.stream().forEach(s -> {
						// if post state \subseteq one of the states already found before.
						if (isSubsetInternally(postState, s)) {
							final IPredicate prestate = stateToPredicate.get(current);
							final IPredicate poststate = stateToPredicate.get(s);
							result.addInternalTransition(prestate, currentLetter, poststate);
						}
					});
				}
			}
		}

		if (mLogger.isDebugEnabled()) {
			final Analyze<CodeBlock, IPredicate> analyze =
					new Analyze<>(new AutomataLibraryServices(mServices), result);
			final int numberOfTransitionsAfter = analyze.getNumberOfTransitions(ESymbolType.TOTAL);

			mLogger.debug("Enhancement added " + (numberOfTransitionsAfter - numberOfTransitionsBeforeEnhancement)
					+ " transitions.");
			mLogger.debug("# Transitions before: " + numberOfTransitionsBeforeEnhancement);
			mLogger.debug("# Transitions after : " + numberOfTransitionsAfter);
		}

		return result;
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private static List<IAbstractState> applyPostInternally(final IAbstractState<?, CodeBlock, IBoogieVar> currentState,
			final IAbstractPostOperator postOperator, final CodeBlock transition) {
		return postOperator.apply(currentState, transition);
	}

	private static boolean isSubsetInternally(final IAbstractState firstState, final IAbstractState secondState) {
		if (firstState.getVariables().size() != secondState.getVariables().size()) {
			return false;
		}

		final SubsetResult subs = firstState.isSubsetOf(secondState);
		return subs == SubsetResult.EQUAL || subs == SubsetResult.NON_STRICT || subs == SubsetResult.STRICT;
	}

	private boolean areCompatible(final IAbstractState state, final Set<String> variableNames) {
		final Set<String> varsInState = (Set<String>) state.getVariables().stream()
				.map(var -> ((IBoogieVar) var).getIdentifier()).collect(Collectors.toSet());

		if (variableNames.size() == 0 && varsInState.size() == 0) {
			return true;
		}

		for (final String var : variableNames) {
			if (!varsInState.contains(var)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Collects all variable identifiers for a given statement.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	private final class VariableCollector extends BoogieVisitor {

		private Set<String> mVariableNames;

		private Set<String> collectVariableNames(final CodeBlock codeBlock,
				final RcfgStatementExtractor statementExtractor) {
			mVariableNames = new HashSet<>();
			for (final Statement statement : statementExtractor.process(codeBlock)) {
				processStatement(statement);
			}
			return mVariableNames;
		}

		@Override
		protected void visit(final IdentifierExpression expr) {
			mVariableNames.add(expr.getIdentifier());
		}

		@Override
		protected void visit(final VariableLHS lhs) {
			mVariableNames.add(lhs.getIdentifier());
		}

	}
}
