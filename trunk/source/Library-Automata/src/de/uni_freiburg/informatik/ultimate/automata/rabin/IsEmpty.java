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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
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

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> word) throws AutomataOperationCanceledException {
		super(services);
		// TODO: Could we use another type of lasso-words here instead?
		if (!word.getStem().hasEmptyNestingRelation() || !word.getLoop().hasEmptyNestingRelation()) {
			throw new AssertionError("Rabin automata cannot handle calls/returns.");
		}

		automaton.getInitialStates().forEach(x -> U.add(x));
		while (!U.isEmpty()) { // Solange es bis jetzt nicht erreichte Knoten gibt
			tarjan(automaton, U.remove(U.size() - 1)); // Aufruf arbeitet alle von v0 erreichbaren Knoten ab
		}
		// mResult = (mWordEvidence == null && mStateEvidence == null);
	}

	/*
	 * Implements: https://de.wikipedia.org/wiki/Algorithmus_von_Tarjan_zur_Bestimmung_starker_Zusammenhangskomponenten
	 */
	private void tarjan(final IRabinAutomaton<LETTER, STATE> automaton, final STATE v) {
		mDFS.put(v, maxdfs); // Tiefensuchindex setzen
		mLowLink.put(v, maxdfs); // v.lowlink <= v.dfs
		maxdfs++; // Zähler erhöhen
		S.push(v);
		STATE vSucc = null;
		for (final OutgoingInternalTransition<LETTER, STATE> transition : automaton.getSuccessors(v)) {
			vSucc = transition.getSucc();
			if (U.contains(vSucc)) {
				tarjan(automaton, vSucc); // rekursiver Aufruf
				mLowLink.put(v, Math.min(mLowLink.get(v), mLowLink.get(vSucc)));
			}
			// Abfragen, ob v' im Stack ist.
			// Bei geschickter Realisierung in O(1).
			// (z. B. Setzen eines Bits beim Knoten beim "push" und "pop")
			else if (S.contains(vSucc)) {
				mLowLink.put(v, Math.min(mLowLink.get(v), mDFS.get(v)));
			}
		}

		if (mLowLink.get(v).equals(mDFS.get(v))) // Wurzel einer SZK
		{
			final HashSet<STATE> pendingSZK = new HashSet<>();

			while (!vSucc.equals(v)) {
				vSucc = S.pop();
				pendingSZK.add(vSucc);
			}
			SZK.add(pendingSZK);

		}
	}

	@Override
	public Object getResult() {
		// TODO Auto-generated method stub
		return null;
	}
}
