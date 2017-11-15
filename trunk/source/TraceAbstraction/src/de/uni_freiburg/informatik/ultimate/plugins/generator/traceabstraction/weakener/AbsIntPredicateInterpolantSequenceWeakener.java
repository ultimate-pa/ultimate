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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.weakener;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;

/**
 * Weakens a sequence of predicates by reducing the number of variables occurring in each Hoare-triple of {pred1} letter
 * {pred2}.
 * <p>
 * Each predicate occurring in the resulting sequence of predicates should contain only the necessary variables to prove
 * inductivity of the sequence of predicates.
 * </p>
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of the abstract states used.
 * @param <IProgramVarOrConst>
 *            The type of the variable declarations used in each abstract state.
 * @param <LETTER>
 *            The type of the letters occurring in the trace of predicate-letter-predicate-triplets.
 */
public class AbsIntPredicateInterpolantSequenceWeakener<STATE extends IAbstractState<STATE>, LETTER extends IIcfgTransition<?>>
		extends InterpolantSequenceWeakener<IHoareTripleChecker, AbsIntPredicate<STATE>, LETTER> {

	private Set<IProgramVar> mVarsToKeep = null;

	/**
	 * The default constructor.
	 *
	 * @param logger
	 *            A logger object.
	 * @param htc
	 *            The Hoare-triple checker that is able to check validity for the given predicate types.
	 * @param predicates
	 *            The sequence of predicates.
	 * @param trace
	 *            The sequence of letters who, in combination with the predicates, form an inductive sequence of
	 *            Hoare-triples.
	 * @param precondition
	 *            The precondition of the trace, i.e. the very first predicate to be considered.
	 * @param postcondition
	 *            The postcondition of the trace, i.e. the very last predicate to be considered.
	 * @param script
	 *            The SMT script to create terms with.
	 * @param predicateFactory
	 *            The factory to create new predicates.
	 */
	public AbsIntPredicateInterpolantSequenceWeakener(final ILogger logger, final IHoareTripleChecker htc,
			final List<AbsIntPredicate<STATE>> predicates, final List<LETTER> trace,
			final AbsIntPredicate<STATE> precondition, final AbsIntPredicate<STATE> postcondition, final Script script,
			final BasicPredicateFactory predicateFactory, final CegarLoopStatisticsGenerator cegarLoopBenchmark) {
		super(logger, htc, predicates, trace, precondition, postcondition, script, predicateFactory,
				cegarLoopBenchmark);
	}

	@Override
	protected AbsIntPredicate<STATE> refinePreState(final AbsIntPredicate<STATE> preState, final LETTER transition,
			final AbsIntPredicate<STATE> postState, final int tracePosition) {

		final AbsIntPredicate<STATE> newPreState = removeUnneededVariables(preState, transition);
		final boolean valid = determineInductivity(newPreState, transition, postState, tracePosition);

		if (valid) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Result of weakening: Number of variables in state before: " + preState.getVars().size()
						+ ", Now: " + newPreState.getVars().size());
			}
			return newPreState;
		}

		mLogger.debug("Unable to weaken prestate. Returning old prestate.");
		// throw new UnsupportedOperationException("This case should not happen");
		return preState;
	}

	/**
	 * Determines whether two states and one transition are inductive, i.e. whether {s1} tr {s2} is a valid
	 * Hoare-triple. This is done by using the Hoare-triple checker provided by the base class.
	 *
	 * @param newPreState
	 *            The new predicate, resulting from weakening <code>oldPreState</code>.
	 * @param transition
	 *            The transition to be considered.
	 * @param postState
	 *            The predicate that should hold after the transition.
	 * @param tracePosition
	 *            The position of the LETTER in the current trace.
	 * @return <code>true</code> iff the Hoare-triple {newPreState} transition {postState} is valid, <code>false</code>
	 *         otherwise.
	 */
	private boolean determineInductivity(final AbsIntPredicate<STATE> newPreState, final LETTER transition,
			final AbsIntPredicate<STATE> postState, final int tracePosition) {
		final Validity result;

		if (transition instanceof IInternalAction) {
			result = mHtc.checkInternal(newPreState, (IInternalAction) transition, postState);
		} else if (transition instanceof ICallAction) {
			result = mHtc.checkCall(newPreState, (ICallAction) transition, postState);
		} else if (transition instanceof IReturnAction) {
			final AbsIntPredicate<STATE> hierarchicalPre = mHierarchicalPreStates.get(tracePosition);
			assert hierarchicalPre != null;
			result = mHtc.checkReturn(newPreState, hierarchicalPre, (IReturnAction) transition, postState);
		} else {
			throw new IllegalStateException(
					"Transition type " + transition.getClass().getSimpleName() + " not supported.");
		}
		return result == Validity.VALID;
	}

	/**
	 * Removes Not needed variables from the current prestate.
	 * <p>
	 * A needed variable is one that occurs in the invars of the transformula of the transition.
	 * </p>
	 *
	 * @param preState
	 *            The original state.
	 * @param transition
	 *            The transition in concern.
	 * @return A new state stripped from all unnecessary variables wrt. the transition.
	 */
	private AbsIntPredicate<STATE> removeUnneededVariables(final AbsIntPredicate<STATE> preState,
			final LETTER transition) {

		// Collect all variables occurring in the invars
		if (mVarsToKeep == null) {
			mVarsToKeep = new HashSet<>();
		}

		final Set<IProgramVar> inVars = transition.getTransformula().getInVars().keySet();
		final Set<IProgramVar> outVars = transition.getTransformula().getOutVars().keySet();

		mVarsToKeep.addAll(inVars);

		// OutVars that do not occur in the InVars may be removed from the prestate as they are overwritten anyways.
		final Set<IProgramVar> removableOutVars =
				outVars.stream().filter(var -> !inVars.contains(var)).collect(Collectors.toSet());

		mVarsToKeep.removeAll(removableOutVars);

		mLogger.debug("Keeping variables " + mVarsToKeep + " for transition " + transition);

		final Set<STATE> newMultiState = new HashSet<>();

		assert preState.getAbstractStates().size() > 0;

		final int numStateVars = preState.getAbstractStates().stream().findFirst()
				.orElseThrow(() -> new UnsupportedOperationException("No states in preState.")).getVariables().size();
		final int numRemovedVars = removableOutVars.size();
		reportWeakeningVarsNumRemoved(numRemovedVars);
		final int leftVars = numStateVars - numRemovedVars;
		if (numStateVars == 0 || leftVars == numStateVars) {
			reportWeakeningRatio(1);
		} else {
			reportWeakeningRatio((double) leftVars / (double) numStateVars);
		}

		for (final STATE s : preState.getAbstractStates()) {
			if (s.isBottom()) {
				// Simply add the state to the new multi state if the state is bottom.
				newMultiState.add(s);
				continue;
			}

			final Set<IProgramVarOrConst> varsToRemove =
					s.getVariables().stream().filter(var -> !mVarsToKeep.contains(var)).collect(Collectors.toSet());

			final STATE removedVariablesState = s.removeVariables(varsToRemove);
			mLogger.debug("State before removing: " + s);
			mLogger.debug("State after removing : " + removedVariablesState);
			newMultiState.add(removedVariablesState);
		}

		final Set<Term> terms = newMultiState.stream().map(s -> s.getTerm(mScript)).collect(Collectors.toSet());
		final IPredicate disjunction = mPredicateFactory.newPredicate(SmtUtils.or(mScript, terms));

		final Set<Term> preStateTerms =
				preState.getAbstractStates().stream().map(s -> s.getTerm(mScript)).collect(Collectors.toSet());

		if (mLogger.isDebugEnabled()) {
			final Term firstTerm = preStateTerms.toArray(new Term[preStateTerms.size()])[0];
			final Term[] firstConjs = SmtUtils.getConjuncts(firstTerm);
			final Stream<Term> conj = Arrays.stream(firstConjs);
			final String conjString = conj.map(elem -> elem.toString()).collect(Collectors.joining("\n   "));
			mLogger.debug("PRE CONJUNCTS (" + firstConjs.length + "):");
			mLogger.debug("   " + conjString);

			final Term secondTerm = terms.toArray(new Term[terms.size()])[0];
			final Term[] secondConjs = SmtUtils.getConjuncts(secondTerm);
			final Stream<Term> conjSec = Arrays.stream(secondConjs);
			final String conjStringSec = conjSec.map(elem -> elem.toString()).collect(Collectors.joining("\n   "));
			mLogger.debug("POST CONJUNCTS (" + secondConjs.length + "):");
			mLogger.debug("   " + conjStringSec);
		}

		final int numberOfConjunctsBeforeWeakening =
				preStateTerms.stream().mapToInt(term -> SmtUtils.getConjuncts(term).length).sum();

		final int numberOfConjunctsAfterWeakening =
				terms.stream().mapToInt(term -> SmtUtils.getConjuncts(term).length).sum();

		final int conjunctReduction = numberOfConjunctsBeforeWeakening - numberOfConjunctsAfterWeakening;

		reportConjunctReduction(conjunctReduction);

		final AbsIntPredicate<STATE> newPreState = new AbsIntPredicate<>(disjunction, newMultiState);
		return newPreState;
	}
}
