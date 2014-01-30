package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class BuchiIntersectNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> m_SndOperand;
	private final StateFactory<STATE> m_StateFactory;
	private final STATE m_EmptyStackState;
	
	private final Map<STATE,Map<STATE,ProductState>> m_Track1_fst2snd2res =
			new HashMap<STATE,Map<STATE,ProductState>>();
	private final Map<STATE,Map<STATE,ProductState>> m_Track2_fst2snd2res =
			new HashMap<STATE,Map<STATE,ProductState>>();
	private final Map<STATE, ProductState> m_res2prod = new HashMap<STATE, ProductState>();
	
	private Set<STATE> m_InitialStates;
	
	
	private class ProductState {
		private final STATE m_fst;
		private final STATE m_snd;
		private final byte m_track;
		private final STATE m_res;
		private final boolean m_IsFinal;
		
		ProductState(STATE fst, STATE snd, byte track, STATE res, boolean isFinal) {
			m_fst = fst;
			m_snd = snd;
			m_track = track;
			m_res = res;
			m_IsFinal = isFinal;
		}

		public STATE getFst() {
			return m_fst;
		}

		public STATE getSnd() {
			return m_snd;
		}
		
		public byte getTrack() {
			return m_track;
		}
		
		public STATE getRes() {
			return m_res;
		}

		public boolean isFinal() {
			return m_IsFinal;
		}
		
		@Override
		public String toString() {
			return "<" + m_fst.toString() + "," + m_snd.toString() + " " + m_track+ ">";
		}
		
	}
	
	
	public BuchiIntersectNwa(INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER, STATE> sndOperand, 
			StateFactory<STATE> sf) throws AutomataLibraryException {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		if (!NestedWordAutomaton.sameAlphabet(m_FstOperand, m_SndOperand)) {
			throw new AutomataLibraryException("Unable to apply operation to automata with different alphabets.");
		}

		m_StateFactory = sf;
		m_EmptyStackState = m_StateFactory.createEmptyStackState();
	}


	private Set<STATE> constructInitialState() {
		Set<STATE> initialStates = new HashSet<STATE>();
		for (STATE fst : m_FstOperand.getInitialStates()) {
			for (STATE snd : m_SndOperand.getInitialStates()) {
				STATE init = getOrConstructStateOnTrack1(fst,snd);
				initialStates.add(init);
			}
		}
		return initialStates;
	}
	
	private STATE getOrConstructStateOnTrack1(STATE fst, STATE snd) {
		Map<STATE, ProductState> snd2res = m_Track1_fst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			m_Track1_fst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			STATE res = m_StateFactory.intersectBuchi(fst, snd, 1);
			boolean isFinal = m_FstOperand.isFinal(fst);
			prod = new ProductState(fst, snd, (byte) 1, res, isFinal);
			snd2res.put(snd, prod);
			m_res2prod.put(res, prod);
		}
		return prod.getRes();
	}
	
	private STATE getOrConstructStateOnTrack2(STATE fst, STATE snd) {
		Map<STATE, ProductState> snd2res = m_Track2_fst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			m_Track2_fst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			STATE res = m_StateFactory.intersectBuchi(fst, snd, 2);
			prod = new ProductState(fst, snd, (byte) 2, res, false);
			snd2res.put(snd, prod);
			m_res2prod.put(res, prod);
		}
		return prod.getRes();
	}
	
	private byte getSuccTrack(ProductState prodState) {
		byte succTrack;
			if (prodState.getTrack() == 1) {
				if (m_FstOperand.isFinal(prodState.getFst()) && !m_SndOperand.isFinal(prodState.getSnd())) {
					succTrack = 2;
				}
				else {
					succTrack = 1;
				}
			}
			else {
				assert(prodState.getTrack() == 2);
				if (m_SndOperand.isFinal(prodState.getSnd())) {
					succTrack = 1;
				}
				else {
					succTrack = 2;
				}
			}
		return succTrack;
	}
	
	
	
	@Override
	public Iterable<STATE> getInitialStates() {
		if (m_InitialStates == null) {
			m_InitialStates = constructInitialState();
		}
		return m_InitialStates;
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_FstOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_FstOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_FstOperand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_InitialStates.contains(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_res2prod.get(state).isFinal();
	}

	@Override
	public STATE getEmptyStackState() {
		return m_EmptyStackState;
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersInternal(fst);
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersCall(fst);
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersReturn(fst);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		ProductState prod = m_res2prod.get(state);
		return internalSuccessors(m_FstOperand.internalSuccessors(prod.getFst(),letter), prod);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		ProductState prod = m_res2prod.get(state);
		return internalSuccessors(m_FstOperand.internalSuccessors(prod.getFst()), prod);
	}


	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			Iterable<OutgoingInternalTransition<LETTER, STATE>> fstInternalSuccs,
			ProductState prod) {
		Collection<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (OutgoingInternalTransition<LETTER, STATE> fstTrans : fstInternalSuccs) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingInternalTransition<LETTER, STATE> sndTrans : m_SndOperand.internalSuccessors(prod.getSnd(), letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				byte succTrack = getSuccTrack(prod); 
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}
	


	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		ProductState prod = m_res2prod.get(state);
		return callSuccessors(m_FstOperand.callSuccessors(prod.getFst(),letter), prod);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		ProductState prod = m_res2prod.get(state);
		return callSuccessors(m_FstOperand.callSuccessors(prod.getFst()), prod);
	}


	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			Iterable<OutgoingCallTransition<LETTER, STATE>> fstCallSuccs,
			ProductState prod) {
		Collection<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		for (OutgoingCallTransition<LETTER, STATE> fstTrans : fstCallSuccs) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingCallTransition<LETTER, STATE> sndTrans : 
						m_SndOperand.callSuccessors(prod.getSnd(), letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				byte succTrack = getSuccTrack(prod); 
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingCallTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		ProductState prodState = m_res2prod.get(state);
		ProductState prodHier = m_res2prod.get(hier);
		STATE fstHier = prodHier.getFst();
		STATE sndHier = prodHier.getSnd();
		return returnSuccessors(m_FstOperand.returnSucccessors(
				prodState.getFst(), fstHier, letter), prodState, hier, sndHier);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		ProductState prodState = m_res2prod.get(state);
		ProductState prodHier = m_res2prod.get(hier);
		STATE fstHier = prodHier.getFst();
		STATE sndHier = prodHier.getSnd();
		return returnSuccessors(m_FstOperand.returnSuccessorsGivenHier(
							prodState.getFst(), fstHier), prodState, hier, sndHier);
	}


	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			Iterable<OutgoingReturnTransition<LETTER, STATE>> fstReturnSuccs,
			ProductState prod, STATE hier, STATE sndHier) {
		Collection<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (OutgoingReturnTransition<LETTER, STATE> fstTrans : fstReturnSuccs) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingReturnTransition<LETTER, STATE> sndTrans : 
						m_SndOperand.returnSucccessors(prod.getSnd(), sndHier,  letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				STATE resSucc;
				byte succTrack = getSuccTrack(prod); 
				if (succTrack == 1) {
					resSucc = getOrConstructStateOnTrack1(fstSucc, sndSucc);
				} else {
					assert (succTrack == 2);
					resSucc = getOrConstructStateOnTrack2(fstSucc, sndSucc);
				}
				result.add(new OutgoingReturnTransition<LETTER, STATE>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return getInternalAlphabet();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}


}
