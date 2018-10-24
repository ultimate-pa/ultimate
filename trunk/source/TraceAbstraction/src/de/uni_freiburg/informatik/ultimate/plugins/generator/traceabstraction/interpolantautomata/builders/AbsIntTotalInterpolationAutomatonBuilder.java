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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SdHoareTripleChecker;

/**
 * Builder for an interpolant automaton from abstract interpretation counterexamples using total interpolation (all
 * possible edges between abstract states are being inserted).
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class AbsIntTotalInterpolationAutomatonBuilder<LETTER extends IIcfgTransition<?>>
		implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {

	private static final long PRINT_PREDS_LIMIT = 30;
	private static final boolean SIMPLE_HOARE_CHECK = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final CfgSmtToolkit mCsToolkit;
	private final IRun<LETTER, IPredicate, ?> mCurrentCounterExample;
	private final RcfgStatementExtractor mStatementExtractor;
	private final VariableCollector mVariableCollector;
	private final IIcfgSymbolTable mSymbolTable;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;

	/**
	 * Constructs a new AbsIntTotalInterpolationAutomatonBuilder which preforms total interpolation on a given counter
	 * example and constructs an interpolant automaton.
	 *
	 * @param services
	 * @param oldAbstraction
	 * @param aiResult
	 * @param predicateUnifier
	 * @param csToolkit
	 * @param currentCounterExample
	 * @param symbolTable
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 */
	public AbsIntTotalInterpolationAutomatonBuilder(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, LETTER, ?> aiResult, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit, final IRun<LETTER, IPredicate, ?> currentCounterExample,
			final IIcfgSymbolTable symbolTable, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolkit = csToolkit;
		mSymbolTable = symbolTable;
		mCurrentCounterExample = currentCounterExample;
		mVariableCollector = new VariableCollector();
		mStatementExtractor = new RcfgStatementExtractor();
		mResult = constructAutomaton(oldAbstraction, aiResult, predicateUnifier, emptyStackFactory);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, LETTER, ?> aiResult, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {

		mLogger.info("Creating interpolant automaton from AI predicates (total)");

		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getVpAlphabet(), emptyStackFactory);

		final NestedRun<LETTER, IPredicate> counterExample = (NestedRun<LETTER, IPredicate>) mCurrentCounterExample;
		final Word<LETTER> word = counterExample.getWord();

		final int wordLength = word.length();
		assert wordLength > 1 : "Unexpected: length of word smaller or equal to 1.";

		final Map<LETTER, IPredicate> callHierarchyPredicates = new HashMap<>();

		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final Set<IPredicate> alreadyThereAsState = new HashSet<>();
		IPredicate previous = predicateUnifier.getTruePredicate();
		alreadyThereAsState.add(previous);
		result.addState(true, false, previous);

		final Map<IPredicate, Set<IAbstractState<?>>> predicateToStates = new HashMap<>();

		for (int i = 0; i < wordLength; i++) {
			final LETTER symbol = word.getSymbol(i);

			final Set<IAbstractState<?>> nextStates =
					(Set<IAbstractState<?>>) aiResult.getLoc2States().get(symbol.getTarget());

			final IPredicate target;
			if (nextStates == null) {
				target = falsePredicate;

				if (mLogger.isDebugEnabled()) {
					writeTransitionAddLog(i, symbol, nextStates, previous, target);
				}
			} else {
				// target = predicateUnifier
				// .getOrConstructPredicateForDisjunction(
				// nextStates.stream()
				// .map(state -> predicateFactory.newAbstractStatePredicate(state,
				// aiResult.getUsedDomain().getPostOperator()))
				// .collect(Collectors.toSet()));
				target = predicateUnifier.getOrConstructPredicateForDisjunction(
						nextStates.stream().map(s -> s.getTerm(mCsToolkit.getManagedScript().getScript()))
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
			if (symbol instanceof IIcfgCallTransition<?>) {
				result.addCallTransition(previous, symbol, target);
				callHierarchyPredicates.put(symbol, previous);
			} else if (symbol instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> returnSymbol = (IIcfgReturnTransition<?, ?>) symbol;
				final IPredicate hierarchyState = callHierarchyPredicates.get(returnSymbol.getCorrespondingCall());
				assert hierarchyState != null : "Return does not have a corresponding call.";
				result.addReturnTransition(previous, hierarchyState, symbol, target);
			} else {
				result.addInternalTransition(previous, symbol, target);
			}

			previous = target;
		}

		// Add self-loops to final states
		for (final IPredicate finalState : result.getFinalStates()) {
			oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
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

		enhanceResult(oldAbstraction, aiResult, result, predicateToStates, predicateUnifier);

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
	 * @param predicateUnifier
	 */
	private void enhanceResult(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, LETTER, ?> aiResult,
			final NestedWordAutomaton<LETTER, IPredicate> result,
			final Map<IPredicate, Set<IAbstractState<?>>> predicateToStates, final IPredicateUnifier predicateUnifier) {

		mLogger.info("Enhancing interpolant automaton by introducing valid transitions between predicates.");

		// Used for debugging reasons to determine impact of enhancement.
		int numberOfTransitionsBeforeEnhancement = -1;

		if (mLogger.isDebugEnabled()) {
			final Analyze<LETTER, IPredicate> analyze = new Analyze<>(new AutomataLibraryServices(mServices), result);
			numberOfTransitionsBeforeEnhancement = analyze.getNumberOfTransitions(SymbolType.TOTAL);
		}

		final Set<IPredicate> allPredicates = predicateToStates.keySet();
		final IAbstractPostOperator<?, LETTER> postOperator = aiResult.getUsedDomain().getPostOperator();
		final SdHoareTripleChecker sdChecker =
				new SdHoareTripleChecker(mCsToolkit, predicateUnifier, new HoareTripleCheckerStatisticsGenerator());

		// Iterate over all letters in the alphabet to find matching inductive transitions.
		for (final LETTER currentLetter : oldAbstraction.getAlphabet()) {

			final IInternalAction internalAction = (IInternalAction) currentLetter;

			// Skip call and return symbols.
			if (currentLetter instanceof IIcfgCallTransition<?>
					|| currentLetter instanceof IIcfgReturnTransition<?, ?>) {
				continue;
			}

			// Collect all occurring variables in the current letter.
			// TODO: Die here if letter is not codeblock
			final Set<IProgramVarOrConst> variableNames = mVariableCollector
					.collectVariableNames((CodeBlock) currentLetter, mStatementExtractor, mSymbolTable);

			// Iterate over all predicates to find matching candidates for a transition.
			for (final IPredicate currentPredicate : allPredicates) {
				final Set<IAbstractState<?>> currentGenerators = predicateToStates.get(currentPredicate);

				for (final IPredicate otherPredicate : allPredicates) {
					if (SIMPLE_HOARE_CHECK) {
						if (internalAction != null) {
							final Validity simpleHoareCheckResult =
									sdChecker.checkInternal(currentPredicate, internalAction, otherPredicate);
							if (simpleHoareCheckResult != Validity.UNKNOWN) {
								if (simpleHoareCheckResult == Validity.VALID) {
									result.addInternalTransition(currentPredicate, currentLetter, otherPredicate);
								}
								if (simpleHoareCheckResult == Validity.NOT_CHECKED) {
									throw new UnsupportedOperationException(
											"Validity result is NOT_CHECKED which should not happen.");
								}
								continue;
							}
						}
					}

					final Set<IAbstractState<?>> otherGenerators = predicateToStates.get(otherPredicate);

					boolean allIncompatible = true;
					boolean noMatchingPostStateFound = false;

					for (final IAbstractState<?> currentState : currentGenerators) {
						if (!areCompatible(currentState, variableNames)) {
							continue;
						}

						allIncompatible = false;

						final Collection<IAbstractState> currentPost =
								applyPostInternally(currentState, postOperator, currentLetter);

						boolean subsetFound = false;

						otherFor: for (final IAbstractState<?> otherState : otherGenerators) {
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
						mLogger.debug("Adding new transition: [" + currentPredicate.hashCode() + "] -> " + currentLetter
								+ " [" + otherPredicate.hashCode() + "]");
					}
					result.addInternalTransition(currentPredicate, currentLetter, otherPredicate);
				}
			}
		}

		if (mLogger.isDebugEnabled()) {
			final Analyze<LETTER, IPredicate> analyze = new Analyze<>(new AutomataLibraryServices(mServices), result);
			final int numberOfTransitionsAfter = analyze.getNumberOfTransitions(SymbolType.TOTAL);

			mLogger.debug("Enhancement added " + (numberOfTransitionsAfter - numberOfTransitionsBeforeEnhancement)
					+ " transitions.");
			mLogger.debug("# Transitions before: " + numberOfTransitionsBeforeEnhancement);
			mLogger.debug("# Transitions after : " + numberOfTransitionsAfter);
		}
	}

	private void writeTransitionAddLog(final int i, final LETTER symbol, final Set<IAbstractState<?>> nextStates,
			final IPredicate source, final IPredicate target) {
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
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}

	private Collection<IAbstractState> applyPostInternally(final IAbstractState<?> currentState,
			final IAbstractPostOperator postOperator, final LETTER transition) {
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

	private static boolean areCompatible(final IAbstractState state, final Set<IProgramVarOrConst> variableNames) {
		assert state != null;
		assert variableNames != null;

		if (variableNames.isEmpty()) {
			return true;
		}
		if (state.getVariables().isEmpty()) {
			return false;
		}

		final Set<IProgramVarOrConst> varsInState = state.getVariables();

		for (final IProgramVarOrConst var : variableNames) {
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

		private Set<IProgramVarOrConst> mVariables;
		private Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;

		private Set<IProgramVarOrConst> collectVariableNames(final CodeBlock codeBlock,
				final RcfgStatementExtractor statementExtractor, final IIcfgSymbolTable boogie2SmtSymbolTable) {
			mVariables = new HashSet<>();
			mBoogie2SmtSymbolTable = (Boogie2SmtSymbolTable) boogie2SmtSymbolTable;
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
