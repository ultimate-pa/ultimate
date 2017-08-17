package complement;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedList;
import java.util.List;

import automata.BuchiGeneral;
import automata.IBuchi;
import automata.IState;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;
import main.Options;
import util.IntIterator;
import util.IntSet;
import util.UtilIntSet;

/**
 * only valid for semi-deterministic Buchi automaton
 * */
public class BuchiComplementSDBA extends BuchiGeneral implements IBuchiComplement {

	private final IBuchi mOperand;
	
	private final List<IntSet> mOpTransUsed;
	
	public BuchiComplementSDBA(IBuchi buchi) {
		super(buchi.getAlphabetSize());
		// TODO Auto-generated constructor stub
		this.mOperand = buchi;
		this.mOpTransUsed = new ArrayList<>();
		for(int i = 0; i < mOperand.getAlphabetSize(); i ++) {
			this.mOpTransUsed.add(UtilIntSet.newIntSet());
		}
		computeInitialStates();
	}
	
	private final TObjectIntMap<StateNCSB> mState2Int = new TObjectIntHashMap<>();

	private void computeInitialStates() {
		// TODO Auto-generated method stub
		StateNCSB state = new StateNCSB(0, this);
		// TODO get also the initial states where initial state is also final state
		IntSet csets = mOperand.getInitialStates().clone();
		csets.and(mOperand.getFinalStates()); // goto C
		state.setSets(mOperand.getInitialStates(), csets, UtilIntSet.newIntSet(), csets);
		if(csets.isEmpty()) this.setFinal(0);
		this.setInitial(0);
		int id = this.addState(state);
		mState2Int.put(state, id);
	}
	

	protected StateNCSB addState(IntSet N, IntSet C, IntSet S, IntSet B) {
		
		StateNCSB state = new StateNCSB(0, this);
		state.setSets(N, C, S, B);
		
		if(mState2Int.containsKey(state)) {
			return (StateNCSB) getState(mState2Int.get(state));
		}else {
			int index = getStateSize();
			StateNCSB newState = new StateNCSB(index, this);
			newState.setSets(N, C, S, B);
			int id = this.addState(newState);
			mState2Int.put(newState, id);
			
			if(B.isEmpty()) setFinal(index);
			
			return newState;
		}
	}

	@Override
	public IBuchi getOperand() {
		// TODO Auto-generated method stub
		return mOperand;
	}
	
	
	private boolean mExplored = false;
	
	public void explore() {
		
		if(mExplored) return ;
		
		mExplored = true;
		
		LinkedList<IState> walkList = new LinkedList<>();
		IntSet initialStates = getInitialStates();
		
		IntIterator iter = initialStates.iterator();
		while(iter.hasNext()) {
			walkList.addFirst(getState(iter.next()));
		}

		
        BitSet visited = new BitSet();
        
        while(! walkList.isEmpty()) {
        	IState s = walkList.remove();
        	if(visited.get(s.getId())) continue;
        	visited.set(s.getId());
        	if(Options.verbose) System.out.println("s"+ s.getId() + ": " + s.toString());
        	for(int i = 0; i < mOperand.getAlphabetSize(); i ++) {
        		IntSet succs = s.getSuccessors(i);
        		iter = succs.iterator();
        		while(iter.hasNext()) {
        			int n = iter.next();
        			if(Options.verbose) System.out.println(" s"+ s.getId() + ": " + s.toString() + "- L" + i + " -> s" + n + ": " + getState(n));
        			if(! visited.get(n)) {
        				walkList.addFirst(getState(n));
        			}
        		}
        	}
        }
	}


	@Override
	public void useOpTransition(int letter, IntSet states) {
		// TODO Auto-generated method stub
		this.mOpTransUsed.get(letter).or(states);
	}


	@Override
	public int getNumUsedOpTransition() {
		// TODO Auto-generated method stub
		int num = 0;
		for(int i = 0; i < mOpTransUsed.size(); i ++) {
			IntSet sources = mOpTransUsed.get(i);
			IntIterator iter = sources.iterator();
			while(iter.hasNext()) {
				num += mOperand.getState(iter.next()).getSuccessors(i).cardinality();
			}
		}
		return num;
	}
	
	
}
