/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.DownStateConsistencyCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;

/**
 * undocumented!
 * <p>
 * NOTE: The interface INestedWordAutomatonOldApi can be removed when also
 * removing the respective overridden methods.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomatonFilteredStates<LETTER, STATE>
		implements INestedWordAutomatonOldApi<LETTER, STATE>,
		INestedWordAutomaton<LETTER, STATE>,
		IDoubleDeckerAutomaton<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final INestedWordAutomatonOldApi<LETTER, STATE> mNwa;
	private final Set<STATE> mRemainingStates;
	private final Set<STATE> mNewInitials;
	private final Set<STATE> mNewFinals;
	private final NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation mAncestorComputation;
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> mTransitionFilter;
	
	/**
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            automaton
	 * @param remainingStates
	 *            remaining states
	 * @param newInitials
	 *            new initial states
	 * @param newFinals
	 *            new final states
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public NestedWordAutomatonFilteredStates(final AutomataLibraryServices services,
			final INestedWordAutomatonOldApi<LETTER, STATE> automaton,
			final Set<STATE> remainingStates, final Set<STATE> newInitials, final Set<STATE> newFinals)
					throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNwa = automaton;
		mRemainingStates = remainingStates;
		mNewInitials = newInitials;
		mNewFinals = newFinals;
		mAncestorComputation = null;
		mTransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(mRemainingStates);
		assert (new DownStateConsistencyCheck<LETTER, STATE>(mServices, this)).getResult() : "down states inconsistent";
	}
	
	/**
	 * @param services
	 *            Ultimate services
	 * @param automaton
	 *            automaton
	 * @param ancestorComputation
	 *            ancester computation object
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public NestedWordAutomatonFilteredStates(
			final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> automaton,
			final NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation ancestorComputation)
					throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNwa = automaton;
		mRemainingStates = ancestorComputation.getStates();
		mNewInitials = ancestorComputation.getInitials();
		mNewFinals = ancestorComputation.getFinals();
		mAncestorComputation = ancestorComputation;
		mTransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(mRemainingStates);
		assert (new DownStateConsistencyCheck<LETTER, STATE>(mServices, this)).getResult() : "down states inconsistent";
	}
	
	@Override
	public Set<STATE> getDownStates(final STATE up) {
		if (mAncestorComputation != null) {
			return mAncestorComputation.getDownStates(up);
		}
		throw new UnsupportedOperationException();
	}
	
	@Override
	public int size() {
		return getStates().size();
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return mNwa.getAlphabet();
	}
	
	@Override
	public String sizeInformation() {
		return mRemainingStates.size() + " states.";
	}
	
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mNwa.getInternalAlphabet();
	}
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		return mNwa.getCallAlphabet();
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mNwa.getReturnAlphabet();
	}
	
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mNwa.getStateFactory();
	}
	
	@Override
	public Set<STATE> getStates() {
		return mRemainingStates;
	}
	
	@Override
	public Set<STATE> getInitialStates() {
		return mNewInitials;
	}
	
	@Override
	public Collection<STATE> getFinalStates() {
		return mNewFinals;
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		return mNewInitials.contains(state);
	}
	
	@Override
	public boolean isFinal(final STATE state) {
		return mNewFinals.contains(state);
	}
	
	@Override
	public STATE getEmptyStackState() {
		return mNwa.getEmptyStackState();
	}
	
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final IncomingInternalTransition<LETTER, STATE> outTrans : internalPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final IncomingCallTransition<LETTER, STATE> outTrans : callPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final IncomingReturnTransition<LETTER, STATE> outTrans : returnPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		final Set<LETTER> letters = new HashSet<LETTER>();
		for (final SummaryReturnTransition<LETTER, STATE> outTrans : summarySuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}
	
	@Override
	public Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return new FilteredIterable<STATE>(mNwa.succInternal(state, letter),
				new IPredicate.SetBasedPredicate<>(mRemainingStates));
	}
	
	@Override
	public Iterable<STATE> succCall(final STATE state, final LETTER letter) {
		final Set<STATE> result = new HashSet<STATE>();
		for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state, letter)) {
			result.add(outTrans.getSucc());
		}
		return result;
	}
	
	@Override
	public Iterable<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		final Set<STATE> result = new HashSet<STATE>();
		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state, letter)) {
			if (mRemainingStates.contains(outTrans.getHierPred()) && mRemainingStates.contains(outTrans.getSucc())) {
				result.add(outTrans.getHierPred());
			}
		}
		return result;
	}
	
	@Override
	public Iterable<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		final Set<STATE> result = new HashSet<STATE>();
		for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state, hier, letter)) {
			if (mRemainingStates.contains(outTrans.getHierPred()) && mRemainingStates.contains(outTrans.getSucc())) {
				result.add(outTrans.getSucc());
			}
		}
		return result;
	}
	
	@Override
	public Iterable<STATE> predInternal(final STATE state, final LETTER letter) {
		return new FilteredIterable<STATE>(mNwa.predInternal(state, letter),
				new IPredicate.SetBasedPredicate<>(mRemainingStates));
	}
	
	@Override
	public Iterable<STATE> predCall(final STATE state, final LETTER letter) {
		final Set<STATE> result = new HashSet<STATE>();
		for (final IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state, letter)) {
			result.add(inTrans.getPred());
		}
		return result;
	}
	
	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public boolean isDeterministic() {
		return false;
	}
	
	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ, final LETTER letter) {
		final IPredicate<IncomingInternalTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getInternalPredecessorsPredicate();
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(
				mNwa.internalPredecessors(succ, letter), predicate);
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ) {
		final IPredicate<IncomingInternalTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getInternalPredecessorsPredicate();
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(
				mNwa.internalPredecessors(succ), predicate);
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ, final LETTER letter) {
		final IPredicate<IncomingCallTransition<LETTER, STATE>> predicate =
				new IPredicate<IncomingCallTransition<LETTER, STATE>>() {
					@Override
					public boolean evaluate(final IncomingCallTransition<LETTER, STATE> trans) {
						// filter out also transitions that are not contained any more
						// because (succ, trans.getPred()) is not a DoubleDecker of the
						// resulting automaton
						return mRemainingStates.contains(trans.getPred())
								&& isDoubleDecker(succ, trans.getPred());
					}
				};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(
				mNwa.callPredecessors(succ, letter), predicate);
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ) {
		final IPredicate<IncomingCallTransition<LETTER, STATE>> predicate =
				new IPredicate<IncomingCallTransition<LETTER, STATE>>() {
					@Override
					public boolean evaluate(final IncomingCallTransition<LETTER, STATE> trans) {
						// filter out also transitions that are not contained any more
						// because (succ, trans.getPred()) is not a DoubleDecker of the
						// resulting automaton
						return mRemainingStates.contains(trans.getPred())
								&& isDoubleDecker(succ, trans.getPred());
					}
				};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(
				mNwa.callPredecessors(succ), predicate);
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		final IPredicate<OutgoingInternalTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getInternalSuccessorPredicate();
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
				mNwa.internalSuccessors(state, letter), predicate);
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		final IPredicate<OutgoingInternalTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getInternalSuccessorPredicate();
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
				mNwa.internalSuccessors(state), predicate);
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		final IPredicate<OutgoingCallTransition<LETTER, STATE>> predicate =
				new IPredicate<OutgoingCallTransition<LETTER, STATE>>() {
					@Override
					public boolean evaluate(final OutgoingCallTransition<LETTER, STATE> trans) {
						// filter out also transitions that are not contained any more
						// because (trans.getSucc(), state) is not a DoubleDecker of the
						// resulting automaton
						return mRemainingStates.contains(trans.getSucc()) && isDoubleDecker(trans.getSucc(), state);
					}
				};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(mNwa.callSuccessors(state, letter),
				predicate);
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		final IPredicate<OutgoingCallTransition<LETTER, STATE>> predicate =
				new IPredicate<OutgoingCallTransition<LETTER, STATE>>() {
					@Override
					public boolean evaluate(final OutgoingCallTransition<LETTER, STATE> trans) {
						// filter out also transitions that are not contained any more
						// because (trans.getSucc(), state) is not a DoubleDecker of the
						// resulting automaton
						return mRemainingStates.contains(trans.getSucc())
								&& isDoubleDecker(trans.getSucc(), state);
					}
				};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(mNwa.callSuccessors(state), predicate);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final STATE hier, final LETTER letter) {
		final IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(
				mNwa.returnPredecessors(succ, hier, letter), predicate);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final LETTER letter) {
		final IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(
				mNwa.returnPredecessors(succ, letter), predicate);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ) {
		final IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(
				mNwa.returnPredecessors(succ), predicate);
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		final IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(
				mNwa.returnSuccessors(state, hier, letter), predicate);
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter) {
		final IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(
				mNwa.returnSuccessors(state, letter), predicate);
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state) {
		final IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(
				mNwa.returnSuccessors(state), predicate);
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		final IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(
				mNwa.returnSuccessorsGivenHier(state, hier), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(
			final STATE hier, final LETTER letter) {
		final IPredicate<SummaryReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSummaryPredicate();
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
				mNwa.summarySuccessors(hier, letter), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		final IPredicate<SummaryReturnTransition<LETTER, STATE>> predicate =
				mTransitionFilter.getReturnSummaryPredicate();
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(mNwa.summarySuccessors(hier),
				predicate);
	}
	
	@Override
	public String toString() {
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this))
				.getDefinitionAsString();
	}
	
	@Override
	public boolean isDoubleDecker(final STATE up, final STATE down) {
		return mAncestorComputation.isDownState(up, down);
	}
	
}
