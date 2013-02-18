package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Automaton that is returned as the result of the {@code BuchiComplementSVW}
 * operation. States and transitions are built on the fly. <br>
 * 
 * The implementation follows the notation introduced in
 *     “Improved Ramsey-Based Büchi Complementation”
 * by Breuers, Löding and Olschewski (Springer, 2012).
 * 
 * @author Fabian Reiter
 * 
 */
public class BuchiComplementAutomatonSVW<LETTER, STATE>
								implements INestedWordAutomaton<LETTER, STATE> {
	private TransitionMonoidAutomaton m_TMA;
	private Collection<LETTER> m_Alphabet;
	private SizeInfoContainer m_sizeInfo = null;
	boolean m_BuildCompleted = false;  // not all transitions have been computed
	protected final StateFactory<STATE> m_StateFactory;
	protected final STATE m_emptyStackState;
	private final STATE m_InitialState;
	private Set<STATE> m_InitialStateSet = new HashSet<STATE>(1);  // only one
	private Set<STATE> m_FinalStateSet = null;
	private Map<STATE, Map<LETTER, Set<STATE>>> m_TransitionsOut =
								new HashMap<STATE, Map<LETTER, Set<STATE>>>();
	private Map<STATE, Map<LETTER, Set<STATE>>> m_TransitionsIn =
								new HashMap<STATE, Map<LETTER, Set<STATE>>>();
	private Map<STATE, MetaState> m_mapState2MS = new HashMap<STATE, MetaState>();
	private UltimateServices m_UltiServ = UltimateServices.getInstance();
	private static Logger s_Logger =
				UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private String UnsupportedOperationMessage =
						"Transform to NestedWordAutomaton to get full support.";

	public BuchiComplementAutomatonSVW(
			INestedWordAutomaton<LETTER, STATE> origAutomaton)
											throws OperationCanceledException {
		m_TMA = new TransitionMonoidAutomaton(origAutomaton);
		m_Alphabet = origAutomaton.getAlphabet();
		m_StateFactory = origAutomaton.getStateFactory();
		m_emptyStackState = m_StateFactory.createEmptyStackState();
		MetaState metaInitialState =
							getMetaState(m_TMA.initialState, m_TMA.initialTMA);
		m_InitialState = metaInitialState.outputState;
		m_InitialStateSet.add(m_InitialState);
	}

	/**
	 * @return an equivalent {@code NestedWordAutomaton} object <br>
	 * <b>Use with caution!</b> The automaton has to be computed entirely.
	 */
	public NestedWordAutomaton<LETTER, STATE> toNestedWordAutomaton()
											throws OperationCanceledException {
		NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<LETTER, STATE>(
										m_Alphabet, null, null, m_StateFactory);
		int size = getSizeInfo().totalSize;
		// Breadth-first traversal of the state space.
		Set<STATE> alreadySeen = new HashSet<STATE>(size);
		Queue<STATE> queue = new LinkedList<STATE>();
		alreadySeen.add(m_InitialState);
		queue.add(m_InitialState);
		result.addState(true, false, m_InitialState);
		while (!queue.isEmpty()) {
			STATE state = queue.remove();
			for (LETTER letter : m_Alphabet) {
				Collection<STATE> succSet = succInternal(state, letter);
				for (STATE succState : succSet) {
					if (!alreadySeen.contains(succState)) {
						alreadySeen.add(succState);
						queue.add(succState);
						if (isFinal(succState))
							result.addState(false, true, succState);
						else
							result.addState(false, false, succState);
					}
					result.addInternalTransition(state, letter, succState);
				}
			}
			if (!m_UltiServ.continueProcessing()) {
				throw new OperationCanceledException();
			}
		}
		m_BuildCompleted = true; // side effect of the BF traversal
		return result;
	}

	private class SizeInfoContainer {
		public int totalSize;
		public int tmaSize;
		public int numOfReachableTMAs;
	}

	private SizeInfoContainer getSizeInfo() {
		if (m_sizeInfo == null) {
			m_sizeInfo = new SizeInfoContainer();
			// Number of states per TMA:
			int m = m_sizeInfo.tmaSize = m_TMA.size();
			// Number of reachable TMAs (initial + looping part):
			int r = m_sizeInfo.numOfReachableTMAs = m_TMA
					.statesWithLeftRejectingPartners().size() + 1;
			// Total number of states:
			m_sizeInfo.totalSize = r * m;
		}
		return m_sizeInfo;
	}

	@Override
	public int size() {
		return getSizeInfo().totalSize;
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		return m_Alphabet;
	}

	@Override
	public String sizeInformation() {
		SizeInfoContainer sizeInfo = getSizeInfo();
		StringBuilder sb = new StringBuilder();
		sb.append("has ");
		sb.append(sizeInfo.totalSize);
		sb.append(" states.");
		sb.append(" Size of a transition monoid automaton (TMA): ");
		sb.append(sizeInfo.tmaSize);
		sb.append(".");
		sb.append(" Number of reachable TMAs: ");
		sb.append(sizeInfo.numOfReachableTMAs);
		sb.append(".");
		return sb.toString();
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_Alphabet;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}

	@Override
	public Collection<STATE> getStates() {
		if (!m_BuildCompleted) {
			int size = getSizeInfo().totalSize;
			// Breadth-first traversal of the state space.
			Set<STATE> alreadySeen = new HashSet<STATE>(size);
			Queue<STATE> queue = new LinkedList<STATE>();
			alreadySeen.add(m_InitialState);
			queue.add(m_InitialState);
			while (!queue.isEmpty()) {
				STATE state = queue.remove();
				for (LETTER letter : m_Alphabet) {
					Collection<STATE> succSet = succInternal(state, letter);
					for (STATE succState : succSet) {
						if (!alreadySeen.contains(succState)) {
							alreadySeen.add(succState);
							queue.add(succState);
						}
					}
				}
				// TODO: Uncomment the following, once getStates() in
				// INestedWordAutomaton has "throws OperationCanceledException"
				// ————————————————————————————————————————————————————————————
				// if (!m_UltiServ.continueProcessing()) {
				// throw new OperationCanceledException();
				// }
				// ————————————————————————————————————————————————————————————
			}
			m_BuildCompleted = true;
		}
		return m_TransitionsOut.keySet();
	}

	@Override
	public Collection<STATE> getInitialStates() {
		return m_InitialStateSet;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		if (m_FinalStateSet == null) {
			Set<Integer> reachableTMAs = m_TMA.statesWithLeftRejectingPartners();
			for (Integer tmaNb : reachableTMAs) {
				MetaState metaState = getMetaState(m_TMA.initialState, tmaNb);
				m_FinalStateSet.add(metaState.outputState);
			}
		}
		return m_FinalStateSet;
	}

	@Override
	public boolean isInitial(STATE state) {
		if (!knows(state))
			throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
		return state.equals(m_InitialState);
	}

	@Override
	public boolean isFinal(STATE state) {
		MetaState metaState = getMetaState(state);
		if (metaState == null)
			throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
		return metaState.stateNb.equals(m_TMA.initialState)
				&& !metaState.tmaNb.equals(m_TMA.initialTMA);
	}

	@Override
	public STATE getEmptyStackState() {
		return this.m_emptyStackState;
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		if (!knows(state))
			throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
		return m_Alphabet;
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		if (!knows(state))
			throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
		Set<LETTER> result = new HashSet<LETTER>();
		for (LETTER letter : m_Alphabet) {
			Collection<STATE> predStateSet = predInternal(state, letter);
			if (!predStateSet.isEmpty())
				result.add(letter);
		}
		return result;
	}

	@Override
	public Collection<STATE> succInternal(STATE state, LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_TransitionsOut.get(state);
		if (map == null) {
			map = new HashMap<LETTER, Set<STATE>>();
			m_TransitionsOut.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result == null) {
			if (!m_Alphabet.contains(letter))
				throw new IllegalArgumentException("Letter " + letter +
													" is not in the alphabet.");
			MetaState mState = getMetaState(state);
			if (mState == null)
				throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
			result = new HashSet<STATE>();
			map.put(letter, result);
			Set<MetaState> mResult = new HashSet<MetaState>();
			// Add the (unique) successor that is in the same TMA.
			Integer succStateNb = m_TMA.successor(mState.stateNb, letter);
			mResult.add(getMetaState(succStateNb, mState.tmaNb));
			// If we are in the initial TMA, we have to add transitions to the
			// initial states of some of the TMAs in the looping part of the
			// complement automaton.
			if (mState.tmaNb.equals(m_TMA.initialTMA)) {
				for (Integer otherTMA_Nb :
									m_TMA.rightRejectingPartners(succStateNb)) {
					mResult.add(getMetaState(m_TMA.initialState, otherTMA_Nb));
				}
			}
			// Otherwise we are in a TMA in the looping part. If we can reach
			// the final state (of this TMA), we have to add a transition that
			// loops back to the initial state.
			else {
				if (succStateNb.equals(mState.tmaNb))
					mResult.add(getMetaState(m_TMA.initialState, mState.tmaNb));
			}
			// Convert set of MetaStates to set of STATEs.
			for (MetaState mSuccState : mResult) {
				result.add(mSuccState.outputState);
			}
		}
		return result;
	}

	@Override
	public Collection<STATE> predInternal(STATE state, LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_TransitionsIn.get(state);
		if (map == null) {
			map = new HashMap<LETTER, Set<STATE>>();
			m_TransitionsIn.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result == null) {
			if (!m_Alphabet.contains(letter))
				throw new IllegalArgumentException("Letter " + letter +
													" is not in the alphabet.");
			MetaState mState = getMetaState(state);
			if (mState == null)
				throw new IllegalArgumentException("State " + state +
														" is not (yet) known.");
			result = new HashSet<STATE>();
			map.put(letter, result);
			Set<MetaState> mResult = new HashSet<MetaState>();
			// Add the predecessors inherited from the TMA.
			Set<Integer> predStateNbSet =
									m_TMA.predecessors(mState.stateNb, letter);
			for (Integer predStateNb : predStateNbSet) {
				mResult.add(getMetaState(predStateNb, mState.tmaNb));
			}
			// If state is the initial state of a TMA in the looping part of the
			// complement automaton, we have to add the transitions from the
			// initial part and those from within the same TMA that loop back to
			// the initial state.
			if (mState.stateNb.equals(m_TMA.initialState)
									&& !mState.tmaNb.equals(m_TMA.initialTMA)) {
				// Transitions from the initial part
				Set<Integer> leftRejectingPartnerSet =
									m_TMA.leftRejectingPartners(mState.tmaNb);
				for (Integer leftRejectingPartner : leftRejectingPartnerSet) {
					Set<Integer> predOfLRPSet =
							m_TMA.predecessors(leftRejectingPartner, letter);
					for (Integer predOfLRP : predOfLRPSet) {
						mResult.add(getMetaState(predOfLRP, m_TMA.initialTMA));
					}
				}
				// Back loops from within the same TMA
				Set<Integer> predOfTerminalSet =
										m_TMA.predecessors(mState.tmaNb, letter);
				for (Integer predOfTerminal : predOfTerminalSet) {
					mResult.add(getMetaState(predOfTerminal, mState.tmaNb));
				}
			}
			// Convert set of MetaStates to set of STATEs.
			for (MetaState mPredState : mResult) {
				result.add(mPredState.outputState);
			}
		}
		return result;
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
		// This method can be implemented very easily. There is exactly one
		// final state in each TMA in the looping part (and none in the TMA in
		// the initial part). Such a final state is the initial state of the TMA
		// in which it is contained. If we do not consider the additional
		// transitions from the complementation construction, the initial state
		// does not have any incoming transitions (since it is a copy of τ(ε)),
		// which means that it cannot be its own successor. Furthermore, the
		// initial state has at least one successor per symbol in the alphabet
		// (since the TMA is total). Thus it has non-final successors (they
		// cannot be final because the initial state is the only final state),
		// which means that from any final state a non-final state is reachable.
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return false;
		// —————————————————————————————————————————————————————————————————————
	}

	@Override
	public boolean isDeterministic() {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
		// This method can be implemented very easily. By construction the TMA
		// is always deterministic and total. Thus the complement automaton is
		// deterministic iff none of the TMAs in the looping part are reachable
		// (this also means that the language accepted by the complement
		// automaton is empty).
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return m_TMA.statesWithLeftRejectingPartners().isEmpty();
		// —————————————————————————————————————————————————————————————————————
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
		// This method can be implemented very easily. Since the TMA is always
		// total (by construction), the same holds for the complement automaton.
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return true;
		// —————————————————————————————————————————————————————————————————————
	}

	@Override
	public NestedRun<LETTER, STATE> included(
				INestedWordAutomaton<LETTER, STATE> nwa)
											throws OperationCanceledException {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public NestedLassoRun<LETTER, STATE> buchiIncluded(
				INestedWordAutomaton<LETTER, STATE> nwa)
											throws OperationCanceledException {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		s_Logger.warn("No nwa. Has no call alphabet.");
		return new HashSet<LETTER>(0);
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		s_Logger.warn("No nwa. Has no return alphabet.");
		return new HashSet<LETTER>(0);
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public void removeState(STATE state) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
//		s_Logger.warn("No nwa. Has no call alphabet.");
		return new HashSet<LETTER>(0);
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
//		s_Logger.warn("No nwa. Has no return alphabet.");
		return new HashSet<LETTER>(0);
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}
	
	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> succCall(STATE state, LETTER letter) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> hierPred(STATE state, LETTER letter) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> predCall(STATE state, LETTER letter) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> predReturnLin(STATE state, LETTER letter,
			STATE hier) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public Collection<STATE> predReturnHier(STATE state, LETTER letter) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE hier) {
		throw new UnsupportedOperationException(UnsupportedOperationMessage);
	}

	/**
	 * @return whether {@code state} is known, i.e. if it has already been seen
	 *         by the automaton
	 */
	private boolean knows(STATE state) {
		return m_mapState2MS.containsKey(state);
	}

	private MetaState getMetaState(Integer stateNb, Integer tmaNb) {
		MetaState metaState = new MetaState(stateNb, tmaNb);
		// If there is already a MetaState object equal to the computed
		// MetaState, use that object instead.
		if (m_mapState2MS.containsKey(metaState.outputState)) {
			metaState = m_mapState2MS.get(metaState.outputState);
		}
		// Otherwise add this new MetaState to the map.
		else {
			m_mapState2MS.put(metaState.outputState, metaState);
		}
		return metaState;
	}

	private MetaState getMetaState(STATE state) {
		return m_mapState2MS.get(state);
	}

	/**
	 * Copy of a TMA state indexed by the number of the TMA instance.
	 */
	private final class MetaState {
		final protected Integer stateNb;  // state number inside the TMA
		final protected Integer tmaNb;    // number of the TMA instance
		final protected STATE outputState;

		public MetaState(Integer stateNb, Integer tmaNb) {
			this.stateNb = stateNb;
			this.tmaNb = tmaNb;
			this.outputState =
						m_StateFactory.constructBuchiSVWState(stateNb, tmaNb);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result
					+ ((stateNb == null) ? 0 : stateNb.hashCode());
			result = prime * result + ((tmaNb == null) ? 0 : tmaNb.hashCode());
			return result;
		}

		@Override
		@SuppressWarnings("unchecked")
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if ((obj == null) || (this.getClass() != obj.getClass()))
				return false;
			MetaState other = (MetaState) obj;
			if ((stateNb == null) && (other.stateNb != null))
				return false;
			if ((tmaNb == null) && (other.tmaNb != null))
				return false;
			return stateNb.equals(other.stateNb) && tmaNb.equals(other.tmaNb);
		}
	}

	// ═════════════════════════════════════════════════════════════════════════
	//
	private class TransitionMonoidAutomaton {

		public Integer initialState = 0; // number assigned to copy of τ(ε)
		public Integer initialTMA = initialState;

		private INestedWordAutomaton<LETTER, STATE> m_OrigAutomaton;

		// Transitions
		private Map<Integer, Map<LETTER, Integer>> m_TransitionsOut =
								new HashMap<Integer, Map<LETTER, Integer>>();
		private Map<Integer, Map<LETTER, Set<Integer>>> m_TransitionsIn =
								new HashMap<Integer, Map<LETTER, Set<Integer>>>();

		// Rejecting s-t pairs
		private Map<Integer, Set<Integer>> m_RejectingPairsL2R;
		private Map<Integer, Set<Integer>> m_RejectingPairsR2L;

		private Set<Integer> m_StatesWithLeftRejectingPartners = null;

		/**
		 * Precomputes all the transitions and rejecting s-t-pairs and then
		 * forgets about the underlying transition profiles. After that, states
		 * are simply represented by Integer objects.
		 */
		public TransitionMonoidAutomaton(
				INestedWordAutomaton<LETTER, STATE> origAutomaton)
											throws OperationCanceledException {
			m_OrigAutomaton = origAutomaton;
			Collection<LETTER> alphabet = origAutomaton.getInternalAlphabet();

			// Map from numbers to corresponding transition profiles
			Map<Integer, TransitionProfile> mapNum2TP =
									new HashMap<Integer, TransitionProfile>();
			// Map for the reverse direction
			Map<TransitionProfile, Integer> mapTP2Num =
									new HashMap<TransitionProfile, Integer>();

			// Map from letters to their corresponding transition profiles
			// (to avoid recomputing them many times)
			Map<LETTER, TransitionProfile> mapLetter2TP =
									new HashMap<LETTER, TransitionProfile>();
			for (LETTER a : alphabet) {
				mapLetter2TP.put(a, new TransitionProfile(a));
			}
			// Build the automaton (i.e. compute the transitions)
			int i_init = initialState; // i.e. i_init = 0
			TransitionProfile t_init = new TransitionProfile(); // τ(ε)-copy
			mapNum2TP.put(i_init, t_init);
			mapTP2Num.put(t_init, i_init);
			m_TransitionsOut.put(i_init, new HashMap<LETTER, Integer>());
			m_TransitionsIn.put(i_init, new HashMap<LETTER, Set<Integer>>());
			int numOfStates = 1;
			for (int i_curr = i_init; i_curr < numOfStates; ++i_curr) {
				TransitionProfile t_curr = mapNum2TP.get(i_curr);
				for (LETTER a : alphabet) {
					// t_next = t_curr·τ(a)
					TransitionProfile t_next =
							new TransitionProfile(t_curr, mapLetter2TP.get(a));
					Integer i_next = mapTP2Num.get(t_next);
					// If i_next not yet known, add new entries for it.
					if (i_next == null) {
						i_next = numOfStates;
						++numOfStates;
						mapNum2TP.put(i_next, t_next);
						mapTP2Num.put(t_next, i_next);
						m_TransitionsOut.put(i_next,
										new HashMap<LETTER, Integer>());
						m_TransitionsIn.put(i_next,
										new HashMap<LETTER, Set<Integer>>());
					}
					// δ(i_curr, a) = i_next
					m_TransitionsOut.get(i_curr).put(a, i_next);
					// i_curr ∈ δ⁻¹(i_next, a)
					Set<Integer> preds = m_TransitionsIn.get(i_next).get(a);
					if (preds == null) {
						preds = new HashSet<Integer>();
						m_TransitionsIn.get(i_next).put(a, preds);
					}
					preds.add(i_curr);
				}
			}

			// Compute rejecting s-t pairs
			List<TransitionProfile> idempotents =
											new ArrayList<TransitionProfile>();
			for (TransitionProfile t : mapTP2Num.keySet()) {
				if (t.isIdempotent())
					idempotents.add(t);
			}
			m_RejectingPairsL2R = new HashMap<Integer, Set<Integer>>(numOfStates);
			m_RejectingPairsR2L = new HashMap<Integer, Set<Integer>>(numOfStates);
			for (int i_s = i_init; i_s < numOfStates; ++i_s) {
				m_RejectingPairsL2R.put(i_s, new HashSet<Integer>(0));
				m_RejectingPairsR2L.put(i_s, new HashSet<Integer>(0));
			}
			for (int i_s = i_init; i_s < numOfStates; ++i_s) {
				TransitionProfile s = mapNum2TP.get(i_s);
				Set<Integer> rightRejectingPartners_s = m_RejectingPairsL2R.get(i_s);
				for (TransitionProfile t : idempotents) {
					// If ⟨s,t⟩ ∈ s-t-Pairs ∧ L(⟨s,t⟩) ∩ L_ω(A) = ∅
					if (s.isInvariantUnder(t) && !s.hasAcceptingLasso(t)) {
						Integer i_t = mapTP2Num.get(t);
						Set<Integer> leftRejectingPartners_t =
												m_RejectingPairsR2L.get(i_t);
						rightRejectingPartners_s.add(i_t);
						leftRejectingPartners_t.add(i_s);
					}
				}
			}
		}

		/**
		 * @return the total number of states
		 */
		public int size() {
			return m_TransitionsOut.size();
		}

		/**
		 * @return the (unique) successor of {@code state} under letter
		 *         {@code a}, i.e. δ(state, a)
		 */
		public Integer successor(Integer state, LETTER a) {
			return m_TransitionsOut.get(state).get(a);
		}

		/**
		 * @return the set of predecessors of {@code state} under letter
		 *         {@code a}, i.e. δ⁻¹(state, a)
		 */
		public Set<Integer> predecessors(Integer state, LETTER a) {
			return m_TransitionsIn.get(state).get(a);
		}

		/**
		 * @return the largest set of states such that for any included state qₜ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to {@code state}</li>
		 *         <li>
		 *         t is the TP corresponding to qₜ</li>
		 *         </ul>
		 */
		public Set<Integer> rightRejectingPartners(Integer state) {
			return m_RejectingPairsL2R.get(state);
		}

		/**
		 * @return the largest set of states such that for any included state qₛ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to qₛ</li>
		 *         <li>
		 *         t is the TP corresponding to {@code state}</li>
		 *         </ul>
		 */
		public Set<Integer> leftRejectingPartners(Integer state) {
			return m_RejectingPairsR2L.get(state);
		}

		/**
		 * @return the set of states for which {@code leftRejectingPartners()}
		 *         would return a nonempty set
		 */
		public Set<Integer> statesWithLeftRejectingPartners() {
			if (m_StatesWithLeftRejectingPartners == null) {
				m_StatesWithLeftRejectingPartners = new HashSet<Integer>();
				for (Entry<Integer, Set<Integer>> e
											: m_RejectingPairsR2L.entrySet()) {
					if (!e.getValue().isEmpty())
						m_StatesWithLeftRejectingPartners.add(e.getKey());
				}
			}
			return m_StatesWithLeftRejectingPartners;
		}

		private class TransitionProfile {
			boolean m_IsInitial = false; // only true for the copy of τ(ε)
			Map<Transition, Boolean> m_Transitions =
											new HashMap<Transition, Boolean>();

			/**
			 * @return the copy of the transition profile τ(ε), i.e. the initial
			 *         state of the TMA
			 */
			public TransitionProfile() throws OperationCanceledException {
				m_IsInitial = true;
				for (STATE q : m_OrigAutomaton.getStates()) {
					if (m_OrigAutomaton.isFinal(q))
						m_Transitions.put(new Transition(q, q), true);
					else
						m_Transitions.put(new Transition(q, q), false);
				}
			}

			/**
			 * @param a
			 * @return the transition profile τ(a) for letter {@code a}
			 */
			public TransitionProfile(LETTER a)
											throws OperationCanceledException {
				for (STATE p : m_OrigAutomaton.getStates()) {
					boolean p_isFinal = m_OrigAutomaton.isFinal(p);
					for (STATE q : m_OrigAutomaton.succInternal(p, a)) {
						if (p_isFinal || m_OrigAutomaton.isFinal(q))
							m_Transitions.put(new Transition(p, q), true);
						else
							m_Transitions.put(new Transition(p, q), false);
					}
				}
			}

			/**
			 * @param s
			 * @param t
			 * @return the transition profile for the concatenation s·t
			 */
			public TransitionProfile(TransitionProfile s, TransitionProfile t) {
				for (Transition trans1 : s.m_Transitions.keySet()) {
					for (Transition trans2 : t.m_Transitions.keySet()) {
						if (trans1.q2.equals(trans2.q1)) {
							Transition trans1x2 =
										new Transition(trans1.q1, trans2.q2);
							if (s.m_Transitions.get(trans1)
												|| t.m_Transitions.get(trans2))
								m_Transitions.put(trans1x2, true);
							else if (!this.m_Transitions.containsKey(trans1x2))
								m_Transitions.put(trans1x2, false);
						}
					}
				}
			}

			/**
			 * @return whether s·t = s, where s = {@code this}
			 */
			public boolean isInvariantUnder(TransitionProfile t) {
				return (new TransitionProfile(this, t).equals(this));
			}

			/**
			 * @return whether t·t = t, where t = {@code this}
			 */
			public boolean isIdempotent() {
				return (new TransitionProfile(this, this).equals(this));
			}

			/**
			 * @return whether L(⟨s,t⟩) ⊆ L_ω(A), where s = {@code this} <br>
			 *         Assumes that ⟨s,t⟩ is an s-t-pair, i.e. that L(⟨s,t⟩) is
			 *         “proper”.
			 */
			public boolean hasAcceptingLasso(TransitionProfile t) {
				for (Transition trans1 : this.m_Transitions.keySet()) {
					if (m_OrigAutomaton.isInitial(trans1.q1)) {
						Transition trans2 = new Transition(trans1.q2, trans1.q2);
						if (t.m_Transitions.containsKey(trans2)
												&& t.m_Transitions.get(trans2))
							return true;
					}
				}
				return false;
			}

			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime
						* result
						+ ((m_Transitions == null) ? 0 : m_Transitions.hashCode());
				return result;
			}

			@Override
			@SuppressWarnings("unchecked")
			public boolean equals(Object obj) {
				if (this == obj)
					return true;
				if ((obj == null) || (this.getClass() != obj.getClass()))
					return false;
				TransitionProfile other = (TransitionProfile) obj;
				if ((m_Transitions == null) && (other.m_Transitions != null))
					return false;
				return m_Transitions.equals(other.m_Transitions)
						&& m_IsInitial == other.m_IsInitial;
			}
		}

		/**
		 * Transitions are the basic building blocks of transition profiles.
		 * They are implemented as tuples of states.
		 */
		private final class Transition {
			final protected STATE q1;
			final protected STATE q2;

			public Transition(STATE q1, STATE q2) {
				this.q1 = q1;
				this.q2 = q2;
			}

			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime * result + ((q1 == null) ? 0 : q1.hashCode());
				result = prime * result + ((q2 == null) ? 0 : q2.hashCode());
				return result;
			}

			@SuppressWarnings("unchecked")
			@Override
			public boolean equals(Object obj) {
				if (this == obj)
					return true;
				if ((obj == null) || (this.getClass() != obj.getClass()))
					return false;
				Transition other = (Transition) obj;
				if ((q1 == null) && (other.q1 != null))
					return false;
				if ((q2 == null) && (other.q2 != null))
					return false;
				return q1.equals(other.q1) && q2.equals(other.q2);
			}
		}
	}

}