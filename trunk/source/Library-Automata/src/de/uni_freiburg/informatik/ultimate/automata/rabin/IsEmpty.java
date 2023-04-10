package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Stack;

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
	private final Stack<STATE> S = new Stack<>();
	private final Map<STATE, Integer> mDFS = new HashMap<>();
	private final Map<STATE, Integer> mLowLink = new HashMap<>();
	private final ArrayList<HashSet<STATE>> SZK = new ArrayList<>();
	private final ArrayList<HashSet<STATE>> acceptingBalls = new ArrayList<>();
	private final HashSet<STATE> visitedStates = new HashSet<>();

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton)
			throws AutomataOperationCanceledException {
		super(services);

		automaton.getInitialStates().forEach(x -> U.add(x));
		U.sort((x, y) -> Boolean.compare(automaton.isAccepting(x), automaton.isAccepting(y)));
		while (!U.isEmpty()) { // Solange es bis jetzt nicht erreichte Knoten gibt
			tarjan(automaton, U.remove(U.size() - 1));
			// Aufruf arbeitet alle von v0 erreichbaren Knoten ab
		}
		// mResult = (mWordEvidence == null && mStateEvidence == null);
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
		mDFS.put(v, maxdfs); // Tiefensuchindex setzen
		mLowLink.put(v, maxdfs); // v.lowlink <= v.dfs
		maxdfs++; // Zähler erhöhen
		S.push(v);
		STATE vSucc = null;
		for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton.getSuccessors(v)) {
			vSucc = transition.getSucc();
			if (!visitedStates.contains(vSucc)) {
				tarjan(automaton, vSucc); // rekursiver Aufruf
				if (!automaton.isFinite(vSucc)) {
					final int temp = Math.min(mLowLink.get(v), mLowLink.get(vSucc));
					mLowLink.put(v, temp);
				}
			}
			// Abfragen, ob v' im Stack ist.
			// Bei geschickter Realisierung in O(1).
			// (z. B. Setzen eines Bits beim Knoten beim "push" und "pop")
			// Idee: LinkedHashSet statt StackHashSet als Optimierung für S
			else if (S.contains(vSucc)) {
				if (!automaton.isFinite(vSucc) && !automaton.isFinite(v)) {
					final int temp = Math.min(mLowLink.get(v), mDFS.get(vSucc));
					mLowLink.put(v, temp);
				}
			}
		}

		if (mLowLink.get(v).equals(mDFS.get(v))) // Wurzel einer SZK
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
}
