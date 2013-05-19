package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class IntersectNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> m_SndOperand;
	private final StateFactory<STATE> m_StateFactory;
	private final STATE m_EmptyStackState;
	
	private final Map<STATE,Map<STATE,ProductState>> m_fst2snd2res =
			new HashMap<STATE,Map<STATE,ProductState>>();
	private final Map<STATE, ProductState> m_res2prod = new HashMap<STATE, ProductState>();
	
	private final boolean m_AssumeInSndNonFinalIsTrap;

	
	private Set<STATE> m_InitialStates;
	
	
	private class ProductState {
		private final STATE m_fast;
		private final STATE m_snd;
		private final STATE m_res;
		private boolean m_IsFinal;
		
		ProductState(STATE fst, STATE snd, STATE res, boolean isFinal) {
			m_fast = fst;
			m_snd = snd;
			m_res = res;
			m_IsFinal = isFinal;
		}

		public STATE getFst() {
			return m_fast;
		}

		public STATE getSnd() {
			return m_snd;
		}
		
		public STATE getRes() {
			return m_res;
		}

		public boolean isFinal() {
			return m_IsFinal;
		}
		
		@Override
		public String toString() {
			return "<" + m_fast.toString() + "," + m_snd.toString() + ">";
		}
		
	}
	
	
	public IntersectNwa(INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			INestedWordAutomatonSimple<LETTER, STATE> sndOperand, 
			StateFactory<STATE> sf, boolean assumeInSndNonFinalIsTrap) {
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = sf;
		m_AssumeInSndNonFinalIsTrap = assumeInSndNonFinalIsTrap;
		m_EmptyStackState = m_StateFactory.createEmptyStackState();
	}


	private Set<STATE> constructInitialState() {
		Set<STATE> initialStates = new HashSet<STATE>();
		for (STATE fst : m_FstOperand.getInitialStates()) {
			for (STATE snd : m_SndOperand.getInitialStates()) {
				STATE init = getOrConstructState(fst,snd);
				initialStates.add(init);
			}
		}
		return initialStates;
	}
	
	private STATE getOrConstructState(STATE fst, STATE snd) {
		Map<STATE, ProductState> snd2res = m_fst2snd2res.get(fst);
		if (snd2res == null) {
			snd2res = new HashMap<STATE, ProductState>();
			m_fst2snd2res.put(fst, snd2res);
		}
		ProductState prod = snd2res.get(snd);
		if (prod == null) {
			STATE res = m_StateFactory.intersection(fst, snd);
			boolean isFinal = m_FstOperand.isFinal(fst) && m_SndOperand.isFinal(snd);
			prod = new ProductState(fst, snd, res, isFinal);
			snd2res.put(snd, prod);
			m_res2prod.put(res, prod);
		}
		return prod.getRes();
	}
	
	
	
	@Override
	public Iterable<STATE> getInitialStates() {
		if (m_InitialStates == null) {
			m_InitialStates = constructInitialState();
		}
		return m_InitialStates;
	}


	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_FstOperand.getInternalAlphabet();
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		return m_FstOperand.getCallAlphabet();
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
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
	public Collection<LETTER> lettersInternal(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersInternal(fst);
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersCall(fst);
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		STATE fst = m_res2prod.get(state).getFst(); 
		return m_FstOperand.lettersReturn(fst);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Collection<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		ProductState prod = m_res2prod.get(state);
		STATE fst = prod.getFst();
		STATE snd = prod.getSnd();
		for (OutgoingInternalTransition<LETTER, STATE> fstTrans : m_FstOperand.internalSuccessors(fst, letter)) {
			for (OutgoingInternalTransition<LETTER, STATE> sndTrans : m_FstOperand.internalSuccessors(snd, letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		Collection<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		ProductState prod = m_res2prod.get(state);
		STATE fst = prod.getFst();
		STATE snd = prod.getSnd();
		for (OutgoingInternalTransition<LETTER, STATE> fstTrans : m_FstOperand.internalSuccessors(fst)) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingInternalTransition<LETTER, STATE> sndTrans : m_FstOperand.internalSuccessors(snd, letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		Collection<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		ProductState prod = m_res2prod.get(state);
		STATE fst = prod.getFst();
		STATE snd = prod.getSnd();
		for (OutgoingCallTransition<LETTER, STATE> fstTrans : m_FstOperand.callSuccessors(fst, letter)) {
			for (OutgoingCallTransition<LETTER, STATE> sndTrans : m_FstOperand.callSuccessors(snd, letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingCallTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		Collection<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		ProductState prod = m_res2prod.get(state);
		STATE fst = prod.getFst();
		STATE snd = prod.getSnd();
		for (OutgoingCallTransition<LETTER, STATE> fstTrans : m_FstOperand.callSuccessors(fst)) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingCallTransition<LETTER, STATE> sndTrans : m_FstOperand.callSuccessors(snd, letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingCallTransition<LETTER, STATE>(letter, resSucc));
			}

		}
		return result;
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		Collection<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		ProductState prodState = m_res2prod.get(state);
		STATE fstState = prodState.getFst();
		STATE sndState = prodState.getSnd();
		ProductState prodHier = m_res2prod.get(hier);
		STATE fstHier = prodHier.getFst();
		STATE sndHier = prodHier.getSnd();
		for (OutgoingReturnTransition<LETTER, STATE> fstTrans : m_FstOperand.returnSucccessors(fstState, fstHier, letter)) {
			for (OutgoingReturnTransition<LETTER, STATE> sndTrans : m_FstOperand.returnSucccessors(sndState, sndHier,  letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingReturnTransition<LETTER, STATE>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		Collection<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		ProductState prodState = m_res2prod.get(state);
		STATE fstState = prodState.getFst();
		STATE sndState = prodState.getSnd();
		ProductState prodHier = m_res2prod.get(hier);
		STATE fstHier = prodHier.getFst();
		STATE sndHier = prodHier.getSnd();
		for (OutgoingReturnTransition<LETTER, STATE> fstTrans : m_FstOperand.returnSuccessorsGivenHier(fstState, fstHier)) {
			LETTER letter = fstTrans.getLetter();
			for (OutgoingReturnTransition<LETTER, STATE> sndTrans : m_FstOperand.returnSucccessors(sndState, sndHier,  letter)) {
				STATE fstSucc = fstTrans.getSucc();
				STATE sndSucc = sndTrans.getSucc();
				if (m_AssumeInSndNonFinalIsTrap && !m_SndOperand.isFinal(sndSucc)) {
					continue;
				}
				STATE resSucc = getOrConstructState(fstSucc, sndSucc);
				result.add(new OutgoingReturnTransition<LETTER, STATE>(hier, letter, resSucc));
			}

		}
		return result;
	}

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}


}
