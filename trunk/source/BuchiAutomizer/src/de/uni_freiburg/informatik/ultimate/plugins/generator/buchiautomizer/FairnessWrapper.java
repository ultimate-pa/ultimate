/*
 * Copyright (C) 2026 Veronika Klasen
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/*
 * Wrapper for a nondeterministic interpolant automaton (certified module from termination analysis) to filter out
 * transitions that are illegal in the context of fairness. Used for the generalization of an unfair trace when doing termination under fairness
 * We assume that no states were pruned in the input automaton.
 */
public class FairnessWrapper<L extends IIcfgTransition<?>>
		implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate> {
	NondeterministicInterpolantAutomaton<L> mWrappedAutomaton;
	Set<String> mLoopThreads;
	UnmodifiableTransFormula mNotG;
	Set<IPredicate> mStemStates;
	Set<IPredicate> mLoopStates;

	// maps base loop predicates to upper/lower loop predicates
	Map<IPredicate, Pair<IPredicate, IPredicate>> mLoopPredicateMap;
	IPredicate mHonda;
	BuchiHoareTripleChecker mHTC;
	NestedMap3<IPredicate, L, IPredicate, IsContained> mOriginalEdges;

	// cache the already constructed transitions
	HashSet<OutgoingInternalTransition<L, IPredicate>> mAlreadyConstructedTS = new HashSet<>();
	HashMap<OutgoingInternalTransition<L, IPredicate>, IPredicate> mOrigins = new HashMap<>();

	/**
	 * Unfairness Wrapper.
	 *
	 * @param automaton
	 *            the automaton to wrap
	 *
	 * @param originalTS
	 *            set of edges of the original lasso; take from interpolant automaton
	 *
	 * @param loopthreads
	 *            the set of threads whose statements are part of the counterexample's loop
	 *
	 * @param stemInterpolants
	 *
	 *            the interpolants of the stem of the lasso
	 *
	 * @param loopInterpolants
	 *            the interpolants of the loop of the lasso
	 *
	 *
	 * @param honda
	 *            predicate of the lasso's honda
	 *
	 * @param notG
	 *            - negated disjunction of guards of non-loop thread statements at the honda
	 * @param htc
	 *            - atm we need a replacing hoare triple checker here to circumvent the duplicate predicate problem
	 *
	 *
	 */
	public FairnessWrapper(final NondeterministicInterpolantAutomaton<L> automaton, final Set<String> loopthreads,
			final NestedMap3<IPredicate, L, IPredicate, IsContained> originalTS, final Set<IPredicate> stemInterpolants,
			final Set<IPredicate> loopInterpolants, final Map<IPredicate, Pair<IPredicate, IPredicate>> loopMap,
			final IPredicate honda, final UnmodifiableTransFormula notG, final ReplacingBuchiHoareTripleChecker htc) {

		mWrappedAutomaton = automaton;
		mLoopThreads = loopthreads;
		mStemStates = stemInterpolants;
		mLoopStates = loopInterpolants;
		mHonda = honda;
		mNotG = notG;
		mHTC = htc;
		mOriginalEdges = originalTS;
		mLoopPredicateMap = loopMap;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mWrappedAutomaton.getVpAlphabet();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return mWrappedAutomaton.getEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		return mWrappedAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final IPredicate state) {
		return mWrappedAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final IPredicate state) {
		return mWrappedAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		// the number of states remains unchanged
		return mWrappedAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		// TODO implement
		return "size information not implemented yet";
	}

	/**
	 * Returns all internal successor transitions that are legal for unfairness generalization
	 */
	@Override
	public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(final IPredicate state,
			final L letter) {
		final List<OutgoingInternalTransition<L, IPredicate>> filteredTS = new ArrayList<>();
		for (final OutgoingInternalTransition<L, IPredicate> ts : mWrappedAutomaton.internalSuccessors(state, letter)) {
			for (final IPredicate target : mWrappedAutomaton.successorPredicates(state, letter)) {
				// TODO: for debugging, remove later
				// TODO: Warum haben dieselben Kanten unterschiedliche ids?
				final boolean c = mAlreadyConstructedTS.contains(ts);
				final IPredicate p = mOrigins.get(ts);
				final boolean o = mOrigins.get(ts) == state;
				if (mAlreadyConstructedTS.contains(ts) && (mOrigins.get(ts) == state)) {
					filteredTS.add(ts);
				} else {
					if (isLegalTS(state, ts.getLetter(), target)) {
						filteredTS.add(ts);
						mAlreadyConstructedTS.add(ts);
						mOrigins.put(ts, state);
					}
				}
			}
		}
		return filteredTS;
	}

	/**
	 * Call functions are not supported for concurrency, so this method should not be used.
	 *
	 * @return an empty iterable
	 *
	 */
	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(final IPredicate state, final L letter) {
		// the wrapped automaton should not have any call transitions
		assert !mWrappedAutomaton.callSuccessors(state, letter).iterator().hasNext()
				: "Call transitions are not supported";
		return mWrappedAutomaton.callSuccessors(state, letter);
	}

	/**
	 * Return functions are not supported for concurrent programs, so this method should not be used.
	 *
	 * @return an empty iterable
	 */
	@Override
	// TODO: remove
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final L letter) {
		// the wrapped automaton should not have any return transitions
		assert !mWrappedAutomaton.returnSuccessors(state, hier, letter).iterator().hasNext()
				: "Call return transitions are not supported";
		return mWrappedAutomaton.returnSuccessors(state, hier, letter);
	}

	/**
	 * Checks whether adding an edge is allowed according to unfairness generalization rules. Contains questionable type
	 * casts.
	 *
	 * @param source
	 *            source node of the edge
	 *
	 * @param ts
	 *            transition to be checked, needs to be an internal transition
	 *
	 * @return true if the edge is legal
	 */
	boolean isLegalTS(final IPredicate source, final L ts, final IPredicate target) {
		// we keep the edges of the original lasso
		// TODO: we need to make sure they are only added ONCE and in the right place...
		if (isOriginalEdge(source, ts, target)) {
			return true;
		}
		// adding additional non-loop ts is forbidden (we need to guarantee that nonloop thread locations remain
		// unchanged)
		if (!isLoopEdge(ts)) {
			return false;
		}
		// for stem states we allow all loop ts that form valid hoare triples; and the predicates should be the same as
		// for termination
		if (mStemStates.contains(source) && mStemStates.contains(target)) {
			return true;
		}
		assert !mStemStates.contains(target) : "Illegal Edge from loop to stem!";
		// for loop edges we need to check if they form valid hoare triples with the unfairness predicates
		if (mLoopStates.contains(source) && !isHonda(target)) {
			final Pair<IPredicate, IPredicate> sourcePreds = mLoopPredicateMap.get(source);
			final Pair<IPredicate, IPredicate> targetPreds = mLoopPredicateMap.get(target);
			boolean u = false;
			boolean l = false;

			// check if the upper loop ts forms a valid hoare triple
			u = mHTC.checkInternal(sourcePreds.getFirst(), (IInternalAction) ts,
					targetPreds.getFirst()) == Validity.VALID;
			// check if the lower loop forms a valid hoare triple
			l = mHTC.checkInternal(sourcePreds.getSecond(), (IInternalAction) ts,
					targetPreds.getSecond()) == Validity.VALID;

			return u && l;
		}

		// the honda is slightly special since we have a virtual 'assume not G' edge "splitting" it
		// TODO: think about honda cases
		return false;
	}

	// TODO: find out how to compare states
	boolean isHonda(final IPredicate state) {
		return state == mHonda;
	}

	/*
	 * Check if an edge was part of the original lasso trace (the counterexample)
	 */
	// TODO: Does this work? If so remove the unnecessary res
	boolean isOriginalEdge(final IPredicate source, final L ts, final IPredicate target) {
		final boolean res = mOriginalEdges.get(source, ts, target) == IsContained.IsContained;
		return res;
	}

	/**
	 * Checks whether the input transition originates from a loop thread.
	 *
	 * @param an
	 *            edge of the wrapped automaton
	 *
	 * @return true if the edge originates from a loop thread
	 */
	boolean isLoopEdge(final L ts) {
		return mLoopThreads.contains(ts.getSource().getProcedure());
	}

	public void switchToReadonlyMode() {
		// since the input automaton can to it...
		mWrappedAutomaton.switchToReadonlyMode();
	}

}