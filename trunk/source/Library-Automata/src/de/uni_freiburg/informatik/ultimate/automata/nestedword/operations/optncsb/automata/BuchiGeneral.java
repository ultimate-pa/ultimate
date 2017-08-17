package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

public class BuchiGeneral implements IBuchi {

	private final IntSet mInitStates;
	
	private final IntSet mFinalStates;
	
	private final List<IState> mStates;
	
	private final int mAlphabetSize;
		
	public BuchiGeneral(int alphabetSize) {
		this.mAlphabetSize = alphabetSize;
		this.mInitStates  = UtilIntSet.newIntSet();
		this.mFinalStates = UtilIntSet.newIntSet();
		this.mStates = new ArrayList<>();
	}
	
	@Override
	public int getAlphabetSize() {
		// TODO Auto-generated method stub
		return mAlphabetSize;
	}

	@Override
	public IState addState() {
		int id = mStates.size();
		mStates.add(makeState(id));
		return mStates.get(id);
	}
	
	/** should keep it safe */
	@Override
	public int addState(IState state) {
		// TODO Auto-generated method stub
		int id = mStates.size();
		mStates.add(state);
		return id;
	}

	@Override
	public IState getState(int id) {
		// TODO Auto-generated method stub
		if(id < mStates.size()) {
			return mStates.get(id);
		}
		return null;
	}

	@Override
	public IntSet getInitialStates() {
		// TODO Auto-generated method stub
		return mInitStates.clone();
	}

	@Override
	public boolean isInitial(int id) {
		// TODO Auto-generated method stub
		return mInitStates.get(id);
	}

	@Override
	public boolean isFinal(int id) {
		// TODO Auto-generated method stub
		return mFinalStates.get(id);
	}

	@Override
	public void setInitial(int id) {
		// TODO Auto-generated method stub
		mInitStates.set(id);
	}

	@Override
	public void setFinal(int id) {
		// TODO Auto-generated method stub
		mFinalStates.set(id);
	}

	@Override
	public Collection<IState> getStates() {
		// TODO Auto-generated method stub
		return Collections.unmodifiableList(mStates);
	}

	@Override
	public IntSet getFinalStates() {
		// TODO Auto-generated method stub
		return mFinalStates.clone();
	}

	@Override
	public int getStateSize() {
		// TODO Auto-generated method stub
		return mStates.size();
	}
	
	public String toString() {
		return toDot();
	}

	@Override
	public IntSet getSuccessors(int state, int letter) {
		// TODO Auto-generated method stub
		return mStates.get(state).getSuccessors(letter);
	}

	protected Acc acc;
	
	@Override
	public Acc getAcceptance() {
		if(acc == null) {
			acc = new AccBuchi();
		}
		return acc;
	}
	
	private class AccBuchi implements Acc {
		List<IntSet> accs = new ArrayList<>();
		
		public AccBuchi() {
			accs.add(mFinalStates);
		}
		@Override
		public boolean isAccepted(IntSet set) {
			return mFinalStates.overlap(set);
		}

		@Override
		public List<IntSet> getAccs() {
			return Collections.unmodifiableList(accs);
		}
	}

	@Override
	public void makeComplete() {
		// TODO Auto-generated method stub
		IState deadState = addState();;
		Iterator<IState> iter = mStates.iterator();
		while(iter.hasNext()) {
			IState state = iter.next();
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	IntSet succs = state.getSuccessors(letter);
            	if(succs.cardinality() == 0) {
            		state.addSuccessor(letter, deadState.getId());
            	}
            }
        }
	}

	@Override
	public IState makeState(int id) {
		// TODO Auto-generated method stub
		return new StateGeneral(id);
	}

}
