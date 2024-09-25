/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.StateSplitter;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;

/**
 * Visitor for DFS using the conditional commutativity checker.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 * @param <V>
 *            Type of the underlying Visitor
 */
public class ConditionalCommutativityCheckerVisitor<L extends IIcfgTransition<?>, V extends IDfsVisitor<L, IPredicate>>
		extends WrapperVisitor<L, IPredicate, V> {

	private boolean mAbort = false;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;
	private final ConditionalCommutativityChecker<L> mChecker;
	private L mPendingLetter;
	private IPredicate mPendingState;
	private NestedRun<L, IPredicate> mRun;
	private TracePredicates mTracePredicates;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private StateSplitter<IPredicate> mSplitter;

	/**
	 * Constructs a new instance of ConditionalCommutativityChecker.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param underlying
	 *            Underlying Visitor
	 * @param abstraction
	 *            Abstraction
	 * @param services
	 *            Ultimate services
	 * @param emptyStackStateFactory
	 *            Factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param splitter
	 *            state splitter to retrieve predicates
	 * @param checker
	 *            Instance of ConditionalCommutativityChecker
	 */
	public ConditionalCommutativityCheckerVisitor(final V underlying,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final IUltimateServiceProvider services, final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			final IPredicateUnifier predicateUnifier, final StateSplitter<IPredicate> splitter,
			final ConditionalCommutativityChecker<L> checker) {
		super(underlying);
		mAbstraction = abstraction;
		mSplitter = splitter;
		mChecker = checker;
		mServices = services;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mPredicateUnifier = predicateUnifier;
	}

	@Override
	public boolean addStartState(final IPredicate state) {
		assert mRun == null : "start state must be first";
		mRun = new NestedRun<>(new NestedWord<>(), List.of(state));
		return mUnderlying.addStartState(state);
	}

	@Override
	public boolean discoverTransition(final IPredicate source, final L letter, final IPredicate target) {
		assert mRun.getStateSequence().get(mRun.getLength() - 1) == source : "Unexpected transition from state "
				+ source;
		mPendingLetter = letter;
		mPendingState = target;
		return mUnderlying.discoverTransition(source, letter, target);
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean discoverState(final IPredicate state) {

		if (mPendingLetter == null) {
			// Must be initial state
			assert mRun.getLength() == 1
					&& mRun.getStateSequence().get(mRun.getLength() - 1) == state : "Unexpected discovery of state "
							+ state;
		} else {
			// Pending transition must lead to given state
			assert mPendingState == state : "Unexpected discovery of state " + state;

			mRun = mRun.concatenate(new NestedRun<>(new NestedWord<>(mPendingLetter, -2),
					List.of(mRun.getStateSequence().get(mRun.getLength() - 1), mPendingState)));
			mPendingLetter = null;
			mPendingState = null;
		}

		IPredicate pred = mSplitter.getOriginal(state);
		// TODO this unpacking of the state will fail for many configurations
		/*
		 * IPredicate pred = ((SleepPredicate<L>) state).getUnderlying(); if (pred instanceof PredicateWithLastThread) {
		 * pred = ((PredicateWithLastThread) pred).getUnderlying(); }
		 */

		// TODO We need to have access on the annotation
		IPredicate annotation = null;
		if (!(pred instanceof MLPredicate)) {
			annotation = ((AnnotatedMLPredicate<IPredicate>) pred).getAnnotation();
		}

		final Iterator<OutgoingInternalTransition<L, IPredicate>> iterator =
				mAbstraction.internalSuccessors(pred).iterator();
		final List<OutgoingInternalTransition<L, IPredicate>> transitions = new ArrayList<>();

		while (iterator.hasNext()) {
			transitions.add(iterator.next());
		}

		// TODO check if this works correctly for semi-commutativity
		for (int j = 0; j < transitions.size(); j++) {
			final OutgoingInternalTransition<L, IPredicate> transition1 = transitions.get(j);
			for (int k = j + 1; k < transitions.size(); k++) {
				final OutgoingInternalTransition<L, IPredicate> transition2 = transitions.get(k);
				final L letter1 = transition1.getLetter();
				final L letter2 = transition2.getLetter();
				TracePredicates tracePredicates;

				if (annotation != null && !SmtUtils.isTrueLiteral(annotation.getFormula())) {
					tracePredicates =
							mChecker.checkConditionalCommutativity(mRun, List.of(annotation), state, letter1, letter2);
				} else {
					tracePredicates = mChecker.checkConditionalCommutativity(mRun, List.of(), state, letter1, letter2);
				}
				if (tracePredicates != null) {
					mAbort = true;
					mTracePredicates = tracePredicates;
					return mUnderlying.discoverState(state);
				}
			}
		}
		return mUnderlying.discoverState(state);
	}

	@Override
	public void backtrackState(final IPredicate state, final boolean isComplete) {

		mPendingLetter = null;
		mPendingState = null;

		if (mRun.getStateSequence().size() > 1) {
			mRun = mRun.getSubRun(0, mRun.getLength() - 2);
		} else {
			mRun = null;
		}

		mUnderlying.backtrackState(state, isComplete);
	}

	@Override
	public boolean isFinished() {
		final boolean result = mUnderlying.isFinished();
		return result || mAbort;
	}

	public boolean aborted() {
		return mAbort;
	}

	/**
	 * Constructs and returns an interpolant automaton if conditional commutativity has been detected.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @return interpolant automaton
	 */
	public NestedWordAutomaton<L, IPredicate> getInterpolantAutomaton() {
		if (mTracePredicates == null) {
			return null;
		}
		final List<IPredicate> conPredicates = new ArrayList<>();
		conPredicates.add(mTracePredicates.getPrecondition());
		conPredicates.addAll(mTracePredicates.getPredicates());
		conPredicates.add(mTracePredicates.getPostcondition());

		ConditionalCommutativityInterpolantAutomatonProvider<L> conComInterpolantProvider =
				new ConditionalCommutativityInterpolantAutomatonProvider<>(mServices, mAbstraction,
						mEmptyStackStateFactory, mPredicateUnifier);
		conComInterpolantProvider.setInterPolantAutomaton(null);
		conComInterpolantProvider.addToInterpolantAutomaton(conPredicates, mRun.getWord());
		return conComInterpolantProvider.getInterpolantAutomaton();
	}
}
