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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
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

	/**
	 * Constructs a new AbsIntTotalInterpolationAutomatonBuilder which preforms total interpolation on a given counter
	 * example and constructs an interpolant automaton.
	 *
	 * @param services
	 * @param oldAbstraction
	 * @param aiResult
	 * @param predicateUnifier
	 * @param smtManager
	 * @param currentCounterExample
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 */
	public AbsIntTotalInterpolationAutomatonBuilder(final IUltimateServiceProvider services,
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
			final PredicateUnifier predicateUnifier, final SmtManager smtManager,
			final IRun<CodeBlock, IPredicate> currentCounterExample) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSmtManager = smtManager;
		mCurrentCounterExample = currentCounterExample;
		mVariableCollector = new VariableCollector();
		mStatementExtractor = new RcfgStatementExtractor();
		mResult = constructAutomaton(oldAbstraction, aiResult, predicateUnifier);
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> constructAutomaton(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
			final PredicateUnifier predicateUnifier) {

		mLogger.info("Creating interpolant automaton from AI predicates (total)");

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

		final Map<IPredicate, Set<IAbstractState<?, CodeBlock, IBoogieVar>>> predicateToStates = new HashMap<>();

		for (int i = 0; i < wordLength; i++) {
			final CodeBlock symbol = word.getSymbol(i);

			final Set<IAbstractState<?, CodeBlock, IBoogieVar>> nextStates =
					(Set<IAbstractState<?, CodeBlock, IBoogieVar>>) aiResult.getLoc2States().get(symbol.getTarget());

			final IPredicate target;
			if (nextStates == null) {
				target = falsePredicate;

				if (mLogger.isDebugEnabled()) {
					writeTransitionAddLog(i, symbol, nextStates, previous, target);
				}
			} else {
				target = predicateUnifier.getOrConstructPredicateForDisjunction(
						nextStates.stream().map(s -> s.getTerm(mSmtManager.getScript(), mSmtManager.getBoogie2Smt()))
								.map(predicateUnifier::getOrConstructPredicate).collect(Collectors.toSet()));

				// Add mapping from predicate -> Set<STATE> to be able to determine all STATES the predicate is
				// originating from.
				if (!predicateToStates.containsKey(target)) {
					predicateToStates.put(target, nextStates.stream().collect(Collectors.toSet()));
				} else {
					predicateToStates.get(target).addAll(nextStates.stream().collect(Collectors.toSet()));
				}

				if (mLogger.isDebugEnabled()) {
					writeTransitionAddLog(i, symbol, nextStates, previous, target);
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

		// TODO maybe move this?
		if (PRINT_PREDS_LIMIT < alreadyThereAsState.size()) {
			mLogger.info("Using "
					+ alreadyThereAsState.size() + " predicates from AI: " + String.join(",", alreadyThereAsState
							.stream().limit(PRINT_PREDS_LIMIT).map(a -> a.toString()).collect(Collectors.toList()))
					+ "...");
		} else {
			mLogger.info("Using " + alreadyThereAsState.size() + " predicates from AI: " + String.join(",",
					alreadyThereAsState.stream().map(a -> a.toString()).collect(Collectors.toList())));
		}

		enhanceResult(oldAbstraction, aiResult, result, predicateToStates);

		return result;
	}

	/**
	 * Adds additional possible internal edges to the result automaton by iterating over all predicates and states and
	 * checking whether the abstract post is compatible with another predicate.
	 *
	 * @param oldAbstraction
	 * @param aiResult
	 * @param result
	 * @param predicateToStates
	 */
	private void enhanceResult(final INestedWordAutomatonSimple<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
			final NestedWordAutomaton<CodeBlock, IPredicate> result,
			final Map<IPredicate, Set<IAbstractState<?, CodeBlock, IBoogieVar>>> predicateToStates) {

		mLogger.info("Enhancing interpolant automaton by introducing valid transitions between predicates.");

		// Used for debugging reasons to determine impact of enhancement.
		int numberOfTransitionsBeforeEnhancement = -1;

		if (mLogger.isDebugEnabled()) {
			final Analyze<CodeBlock, IPredicate> analyze =
					new Analyze<>(new AutomataLibraryServices(mServices), result);
			numberOfTransitionsBeforeEnhancement = analyze.getNumberOfTransitions(SymbolType.TOTAL);
		}

		final Set<IPredicate> allPredicates = predicateToStates.keySet();
		final IAbstractPostOperator<?, CodeBlock, IBoogieVar> postOperator = aiResult.getUsedDomain().getPostOperator();

		// Iterate over all letters in the alphabet to find matching inductive transitions.
		for (final CodeBlock currentLetter : oldAbstraction.getAlphabet()) {

			// Skip call and return symbols.
			if (currentLetter instanceof Call || currentLetter instanceof Return) {
				continue;
			}

			// Collect all occurring variables in the current letter.
			final Set<IBoogieVar> variableNames = mVariableCollector.collectVariableNames(currentLetter,
					mStatementExtractor, mSmtManager.getBoogie2Smt().getBoogie2SmtSymbolTable());

			// Iterate over all predicates to find matching candidates for a transition.
			for (final IPredicate currentPredeicate : allPredicates) {
				final Set<IAbstractState<?, CodeBlock, IBoogieVar>> currentGenerators =
						predicateToStates.get(currentPredeicate);

				for (final IPredicate otherPredicate : allPredicates) {
					final Set<IAbstractState<?, CodeBlock, IBoogieVar>> otherGenerators =
							predicateToStates.get(otherPredicate);

					boolean allIncompatible = true;
					boolean noMatchingPostStateFound = false;

					for (final IAbstractState<?, CodeBlock, IBoogieVar> currentState : currentGenerators) {
						if (!areCompatible(currentState, variableNames)) {
							continue;
						}

						allIncompatible = false;

						final List<IAbstractState> currentPost =
								applyPostInternally(currentState, postOperator, currentLetter);

						boolean subsetFound = false;

						otherFor: for (final IAbstractState<?, CodeBlock, IBoogieVar> otherState : otherGenerators) {
							for (final IAbstractState postState : currentPost) {
								if (isSubsetInternally(postState, otherState)) {
									subsetFound = true;
									break otherFor;
								}
							}
						}

						if (!subsetFound) {
							noMatchingPostStateFound = true;
							break;
						}
					}

					if (allIncompatible || noMatchingPostStateFound) {
						continue;
					}

					// Add transition
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("Adding new transition: PRE={" + currentPredeicate + "} -> " + currentLetter
								+ " POST={" + otherPredicate + "}");
					}
					result.addInternalTransition(currentPredeicate, currentLetter, otherPredicate);
				}
			}
		}

		if (mLogger.isDebugEnabled()) {
			final Analyze<CodeBlock, IPredicate> analyze =
					new Analyze<>(new AutomataLibraryServices(mServices), result);
			final int numberOfTransitionsAfter = analyze.getNumberOfTransitions(SymbolType.TOTAL);

			mLogger.debug("Enhancement added " + (numberOfTransitionsAfter - numberOfTransitionsBeforeEnhancement)
					+ " transitions.");
			mLogger.debug("# Transitions before: " + numberOfTransitionsBeforeEnhancement);
			mLogger.debug("# Transitions after : " + numberOfTransitionsAfter);
		}
	}

	private void writeTransitionAddLog(final int i, final CodeBlock symbol,
			final Set<IAbstractState<?, CodeBlock, IBoogieVar>> nextStates, final IPredicate source,
			final IPredicate target) {
		final String divider = "------------------------------------------------";
		if (i == 0) {
			mLogger.debug(divider);
		}
		mLogger.debug("Transition: " + symbol);
		mLogger.debug("Original Target States: " + (nextStates == null ? "NONE" : nextStates));
		mLogger.debug("Source Term: " + source);
		mLogger.debug("Target Term: " + target);
		mLogger.debug(divider);
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

		if (!firstState.getVariables().stream().allMatch(secondState.getVariables()::contains)) {
			return false;
		}

		final SubsetResult subs = firstState.isSubsetOf(secondState);
		return subs != SubsetResult.NONE;
	}

	private static boolean areCompatible(final IAbstractState state, final Set<IBoogieVar> variableNames) {
		assert state != null;
		assert variableNames != null;

		if (variableNames.isEmpty()) {
			return true;
		}
		if (state.getVariables().isEmpty()) {
			return false;
		}

		final Set<IBoogieVar> varsInState = state.getVariables();

		for (final IBoogieVar var : variableNames) {
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
	 */
	private static final class VariableCollector extends BoogieVisitor {

		private Set<IBoogieVar> mVariables;
		private Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;

		private Set<IBoogieVar> collectVariableNames(final CodeBlock codeBlock,
				final RcfgStatementExtractor statementExtractor, final Boogie2SmtSymbolTable boogie2SmtSymbolTable) {
			mVariables = new HashSet<>();
			mBoogie2SmtSymbolTable = boogie2SmtSymbolTable;
			for (final Statement statement : statementExtractor.process(codeBlock)) {
				processStatement(statement);
			}
			return mVariables;
		}

		@Override
		protected void visit(final IdentifierExpression expr) {
			mVariables.add(
					mBoogie2SmtSymbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false));
		}

		@Override
		protected void visit(final VariableLHS lhs) {
			mVariables.add(
					mBoogie2SmtSymbolTable.getBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), false));
		}

	}
}
