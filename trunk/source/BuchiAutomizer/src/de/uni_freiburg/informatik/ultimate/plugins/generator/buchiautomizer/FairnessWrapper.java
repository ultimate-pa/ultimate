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

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;

/*
 * Wrapper for a nondeterministic interpolant automaton (certified module from termination analysis) to filter out
 * transitions that are illegal in the context of fairness. Used when doing termination under fairness in the generalization of an unfair trace.
 * We assume that no states were pruned in the input automaton.
 */
public class FairnessWrapper<L extends IIcfgTransition<?>>
		implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate> {
	NondeterministicInterpolantAutomaton<L> mWrappedAutomaton;
	NestedLassoRun<L, IPredicate> mLassoRun; // needed for checking which ts existed in the original word
	Set<String> mNonLoopThreads;
	UnmodifiableTransFormula mNotG;
	IPredicate[] mStemInterpolants;
	IPredicate[] mLoopInterpolants;
	IPredicate[] mPredicates; // annotations for the "upper" loop of A_fair (with annotation ork = inf && sup. inv)
	IPredicate[] mPrimedPredicates; // annotations for the "lower" loop of A_fair (the one containing assume !G)
	List<IPredicate> mLoopStates; // what is better, set or list
	List<IPredicate> mStemStates;
	IPredicate mHonda;
	BuchiHoareTripleChecker mHTC;
	Set<L> mOriginalEdges;
	Set<IPredicate> mStemStateSet;
	Set<IPredicate> mLoopStateSet;

	/*
	 * Unfairness Wrapper.
	 *
	 * @param automaton - the automaton to wrap
	 *
	 * @param lasso - the counterexample from which the generalized automaton was build
	 *
	 * @param nonloopthreads - the set of threads of which there is no statement on the counterexample's loop
	 *
	 * @param stem - the interpolants of the stem of the lasso
	 *
	 * @param loop - the interpolants of the loop of the lasso
	 *
	 * @param loopbasic - the predicates for the states of the upper loop of A_fair
	 *
	 * @param loopprime - the predicates for the states of the guarded loop of A_fair; however we start at the state
	 * after the "assume not G" statement and leave out the oldrank stuff since that should already be covered by the
	 * termination predicates
	 *
	 * @param honda - predicate of the lasso's honda
	 *
	 * @param notG - negated disjunction of guards of non-loop thread statements at the honda
	 *
	 * @param htc - hoare triple checker able to handle the special honda predicates in termination
	 */
	public FairnessWrapper(final NondeterministicInterpolantAutomaton<L> automaton,
			final NestedLassoRun<L, IPredicate> lasso, final Set<String> nonloopthreads, final IPredicate[] stem,
			final IPredicate[] loop, final IPredicate[] loopbasic, final IPredicate[] loopprime, final IPredicate honda,
			final UnmodifiableTransFormula notG, final BuchiHoareTripleChecker htc) {
		mWrappedAutomaton = automaton;
		mLassoRun = lasso;
		mNonLoopThreads = nonloopthreads;
		mStemInterpolants = stem;
		mLoopInterpolants = loop;
		mPredicates = loopbasic;
		mPrimedPredicates = loopprime;
		mHonda = honda;
		mNotG = notG;
		mHTC = htc;

		mStemStateSet = Set.of(mStemInterpolants);
		mLoopStateSet = Set.of(mLoopInterpolants);
		mOriginalEdges = (mLassoRun.getLoop().getWord().asSet());
		mOriginalEdges.addAll(mLassoRun.getStem().getWord().asSet());

		// TODO: remove/streamline
		mLoopStates = mLassoRun.getLoop().getStateSequence();
		mStemStates = mLassoRun.getStem().getStateSequence();
		final int num_states_lasso = mLoopStates.size() + mStemStates.size();
		assert num_states_lasso == mWrappedAutomaton.size() : "States went missing!";

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
		return "to be implemented";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(final IPredicate state,
			final L letter) {
		final Iterable<OutgoingInternalTransition<L, IPredicate>> unfilteredTS =
				mWrappedAutomaton.internalSuccessors(state, letter);

		// all edges of the original lasso are kept
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(final IPredicate state, final L letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(final IPredicate state,
			final IPredicate hier, final L letter) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * Checks whether adding this edge is allowed according to unfairness generalization rules
	 *
	 */
	boolean isLegalTS(final IPredicate source, final L ts) {
		// TODO: are those actually predicates?
		final IPredicate target = (IPredicate) ts.getTarget();
		// we keep the edges of the counterexample
		if (isOriginalEdge(ts)) {
			return true;
		}
		// adding additional non-loop ts is forbidden (we need to guarantee that nonloop thread locations remain
		// unchanged)
		if (isNonLoopEdge(ts)) {
			return false;
		}
		// for stem states we allow all loop ts that form valid hoare triples; and the predicates should be the same as
		// for termination
		if (mStemStateSet.contains(source) && mStemStateSet.contains(target)) {
			return true;
		}
		assert !mStemStateSet.contains(target) : "Illegal Edge from loop to stem!";
		// for loop edges we need to check if they form valid hoare triples with the unfairness predicates
		return false;
	}

	// TODO: find out how to compare states
	boolean isHonda(final IPredicate state) {
		return state == mHonda;
	}

	/*
	 * Check if an edge was part of the original lasso trace (the counterexample)
	 */
	// TODO: Does this work?
	boolean isOriginalEdge(final L ts) {
		return mOriginalEdges.contains(ts);
	}

	/*
	 * Checks whether the input transition originates from a non-loop thread.
	 */
	boolean isNonLoopEdge(final L ts) {
		return mNonLoopThreads.contains(ts.getSource().getProcedure());
	}

	public void switchToReadonlyMode() {
		// since the input automaton can to it...
		mWrappedAutomaton.switchToReadonlyMode();
	}

}