package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class IsEmpty<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {

	private List<LETTER> mWordEvidence;
	private List<STATE> mStateEvidence;

	private int maxdfs = 0;
	private final ArrayList<STATE> U = new ArrayList<>();
	private final StackHashSet<STATE> S = new StackHashSet<>();
	private final Map<STATE, Integer> mDFS = new HashMap<>();
	private final Map<STATE, Integer> mLowLink = new HashMap<>();
	private final ArrayList<HashSet<STATE>> SZK = new ArrayList<>();
	private final ArrayList<HashSet<STATE>> acceptingBalls = new ArrayList<>();
	private final HashSet<STATE> visitedStates = new HashSet<>();

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton)
			throws AutomataOperationCanceledException {
		super(services);

		automaton.getInitialStates().forEach(x -> U.add(x));
		U.sort((x, y) -> Boolean.compare(automaton.isFinite(x), automaton.isFinite(y))); // try to construct purely
																							// nonFinite solutions First
		while (!U.isEmpty()) { // While there is a initial state not considered
			tarjan(automaton, U.remove(U.size() - 1));
			U.removeAll(visitedStates);// Start that has been reached from another is already explored
		}
	}

	/*
	 * Implements: https://de.wikipedia.org/wiki/Algorithmus_von_Tarjan_zur_Bestimmung_starker_Zusammenhangskomponenten
	 */
	private void tarjan(final IRabinAutomaton<LETTER, STATE> automaton, final STATE v)
			throws AutomataOperationCanceledException {
		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(getClass());
		}
		visitedStates.add(v);
		mDFS.put(v, maxdfs); // set discovery time
		mLowLink.put(v, maxdfs); // v.lowlink <= v.dfs
		maxdfs++; // time-index ++
		S.push(v);
		STATE vSucc = null;
		final ArrayList<STATE> sortedTransitions = new ArrayList<>();
		automaton.getSuccessors(v).forEach(x -> sortedTransitions.add(x.getSucc()));
		sortedTransitions.sort((x, y) -> Boolean.compare(automaton.isFinite(x), automaton.isFinite(y)));
		// again prefer nonFinite States to find accepting components first

		for (final STATE successor : sortedTransitions) {
			vSucc = successor;
			if (!visitedStates.contains(vSucc)) {
				tarjan(automaton, vSucc); // rekursiver Aufruf
				if (!automaton.isFinite(vSucc)) {// suppress blocks for NonFinite States
					final int temp = Math.min(mLowLink.get(v), mLowLink.get(vSucc));
					mLowLink.put(v, temp);
				}
			} else if (S.contains(vSucc)) {
				if (!automaton.isFinite(vSucc) && !automaton.isFinite(v)) { // suppress blocks for NonFinite States
					final int temp = Math.min(mLowLink.get(v), mDFS.get(vSucc));
					mLowLink.put(v, temp);
				}
			}
		}

		if (mLowLink.get(v).equals(mDFS.get(v))) // Root of a SZK
		{
			final HashSet<STATE> pendingSZK = new HashSet<>();
			boolean isAccepting = false;
			boolean isNonFinite = true;
			boolean isBall = false;

			do {
				vSucc = S.pop();
				pendingSZK.add(vSucc);
				if (isNonFinite) {
					isAccepting = isAccepting || automaton.isAccepting(vSucc);
					isNonFinite = !automaton.isFinite(vSucc);
				}
			} while (!vSucc.equals(v));

			isBall = pendingSZK.size() > 1;
			if (!isBall) {
				for (final OutgoingInternalTransition<LETTER, STATE> vSuccTransition : automaton.getSuccessors(vSucc)) {
					if (vSuccTransition.getSucc().equals(vSucc)) {
						isBall = true;
						break;
					}
				}

			}
			isAccepting = isNonFinite && isAccepting;

			if (isAccepting && isBall) {
				acceptingBalls.add(pendingSZK);
			}
			SZK.add(pendingSZK);

		}
	}

	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return acceptingBalls.isEmpty();
	}

	/**
	 * Stack and Set in one object. Elements that are already contained must not be added.
	 *
	 * @author Matthias Heizmann
	 *
	 */
	static class StackHashSet<STATE> {
		private final Deque<STATE> mStack = new ArrayDeque<>();
		private final Set<STATE> mSet = new HashSet<>();

		public STATE pop() {
			final STATE node = mStack.pop();
			mSet.remove(node);
			return node;
		}

		public void push(final STATE node) {
			mStack.push(node);
			final boolean modified = mSet.add(node);
			if (!modified) {
				throw new IllegalArgumentException("Illegal to add element twice " + node);
			}
		}

		public boolean contains(final STATE node) {
			return mSet.contains(node);
		}
	}
}