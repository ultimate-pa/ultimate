/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Rebuilds the states of an automaton a worker returned as predicates of the main script.
 * <p>
 * {@link TransferBetweenMainAndWorker#transferAutomaton} transfers only the letters; the states of a worker's
 * subtrahend remain predicates of the worker's script. That is fine as long as the main thread only builds don't-care
 * states, but a Hoare annotation conjoins the states of the subtrahend with those of the abstraction, and its
 * computation runs after the worker scripts have been destroyed.
 * <p>
 * Only the formulas are transferred, by a plain {@link TermTransferrer}: the variables of a worker are copies of the
 * main thread's with the same names and sorts, so the transferred term speaks about the main thread's own
 * {@code TermVariable}s and the main {@link PredicateFactory} finds their {@code IProgramVar}s in the main symbol
 * table. No {@code IProgramVar} is created.
 * <p>
 * Not thread-safe: the main thread is the only one that may use it, since it creates terms of the main script.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class WorkerStateTransferrer<L> {

	private final AutomataLibraryServices mServices;
	private final ManagedScript mMainScript;
	private final PredicateFactory mMainPredicateFactory;
	// One per worker script; their caches stay valid for the whole run, since terms are immutable.
	private final Map<ManagedScript, TermTransferrer> mTransferrers = new HashMap<>();

	public WorkerStateTransferrer(final AutomataLibraryServices services, final ManagedScript mainScript,
			final PredicateFactory mainPredicateFactory) {
		mServices = services;
		mMainScript = mainScript;
		mMainPredicateFactory = mainPredicateFactory;
	}

	/**
	 * @param automaton
	 *            an automaton whose letters are already the main thread's, as {@link TransferBetweenMainAndWorker}
	 *            returns it for {@link TransferBetweenMainAndWorker.TransferMode#WORKER2MAIN}
	 * @param workerScript
	 *            the script the states of {@code automaton} belong to
	 * @param emptyStackFactory
	 *            provides the empty stack state of the main thread
	 * @return a copy of {@code automaton} with the same letters and transitions whose states are predicates of the main
	 *         script
	 */
	public NestedWordAutomaton<L, IPredicate> transferStates(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton, final ManagedScript workerScript,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		if (!(automaton instanceof INestedWordAutomaton)) {
			throw new UnsupportedOperationException(
					"Expected a fully constructed automaton, got a " + automaton.getClass().getSimpleName());
		}
		final INestedWordAutomaton<L, IPredicate> nwa = (INestedWordAutomaton<L, IPredicate>) automaton;
		final TermTransferrer transferrer = getTransferrer(workerScript);
		final NestedWordAutomaton<L, IPredicate> result =
				new NestedWordAutomaton<>(mServices, nwa.getVpAlphabet(), emptyStackFactory);

		final Map<IPredicate, IPredicate> worker2main = new HashMap<>();
		worker2main.put(nwa.getEmptyStackState(), result.getEmptyStackState());
		for (final IPredicate state : nwa.getStates()) {
			final IPredicate mainState = transfer(state, transferrer);
			worker2main.put(state, mainState);
			result.addState(nwa.isInitial(state), nwa.isFinal(state), mainState);
		}
		for (final IPredicate state : nwa.getStates()) {
			final IPredicate pred = worker2main.get(state);
			for (final OutgoingInternalTransition<L, IPredicate> trans : nwa.internalSuccessors(state)) {
				result.addInternalTransition(pred, trans.getLetter(), worker2main.get(trans.getSucc()));
			}
			for (final OutgoingCallTransition<L, IPredicate> trans : nwa.callSuccessors(state)) {
				result.addCallTransition(pred, trans.getLetter(), worker2main.get(trans.getSucc()));
			}
			for (final OutgoingReturnTransition<L, IPredicate> trans : nwa.returnSuccessors(state)) {
				result.addReturnTransition(pred, worker2main.get(trans.getHierPred()), trans.getLetter(),
						worker2main.get(trans.getSucc()));
			}
		}
		assert result.size() == nwa.size();
		return result;
	}

	private IPredicate transfer(final IPredicate pred, final TermTransferrer transferrer) {
		if (mMainPredicateFactory.isDontCare(pred)) {
			if (pred instanceof ISLPredicate) {
				return mMainPredicateFactory.newDontCarePredicate(((ISLPredicate) pred).getProgramPoint());
			}
			if (pred instanceof IMLPredicate) {
				return mMainPredicateFactory.newMLDontCarePredicate(((IMLPredicate) pred).getProgramPoints());
			}
			return mMainPredicateFactory.newDontCarePredicate(null);
		}
		final Term formula = transferTerm(pred.getFormula(), transferrer);
		if (pred instanceof ISLPredicate) {
			return mMainPredicateFactory.newSPredicate(((ISLPredicate) pred).getProgramPoint(), formula);
		}
		if (pred instanceof IMLPredicate) {
			return mMainPredicateFactory.newMLPredicate(((IMLPredicate) pred).getProgramPoints(), formula);
		}
		return mMainPredicateFactory.newPredicate(formula);
	}

	/**
	 * @return {@code term}, a term of {@code workerScript} over the program variables, as a term of the main script
	 */
	public Term transferTerm(final Term term, final ManagedScript workerScript) {
		return transferTerm(term, getTransferrer(workerScript));
	}

	private Term transferTerm(final Term term, final TermTransferrer transferrer) {
		final Term result = transferrer.transform(term);
		// The commuhash normal form sorts by hash code, which may differ between the two scripts.
		if (!CommuhashUtils.isInCommuhashNormalForm(result)) {
			return CommuhashNormalFormTransformer.apply(mMainScript.getScript(), result);
		}
		return result;
	}

	private TermTransferrer getTransferrer(final ManagedScript workerScript) {
		return mTransferrers.computeIfAbsent(workerScript,
				s -> new TermTransferrer(s.getScript(), mMainScript.getScript()));
	}
}
