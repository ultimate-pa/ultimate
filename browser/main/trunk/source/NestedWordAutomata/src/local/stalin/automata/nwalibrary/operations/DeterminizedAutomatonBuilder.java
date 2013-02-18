package local.stalin.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.DoubleDecker;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;


public class DeterminizedAutomatonBuilder<S,C> extends
		DoubleDeckerGraphBuilder<S, C> {

	
	private INestedWordAutomaton<S, C> input;
	private IStateDeterminizer<S, C> stateDeterminizer;
	private IState<S, C> inputAuxilliaryEmptyStackState;
	private ContentFactory<C> contentFactory;
	
	
	/**
	 * Maps a DeterminizedState to its representative in the resulting automaton.
	 */
	private Map<DeterminizedState<S,C>,IState<S,C>> det2res =
		new HashMap<DeterminizedState<S,C>, IState<S,C>>();
	
	/**
	 * Maps a state in resulting automaton to the DeterminizedState for which it
	 * was created.
	 */
	private final Map<IState<S,C>,DeterminizedState<S,C>> res2det =
		new HashMap<IState<S,C>, DeterminizedState<S,C>>();

	
	public DeterminizedAutomatonBuilder(
			INestedWordAutomaton<S,C> input,
			IStateDeterminizer<S,C> stateDeterminizer) {
		this.contentFactory = input.getContentFactory();
		this.input = input;
		this.inputAuxilliaryEmptyStackState = 
			((NestedWordAutomaton<S,C>)input).getEmptyStackState();
		this.stateDeterminizer = stateDeterminizer;
		super.result = new NestedWordAutomaton<S,C>(
				input.getInternalAlphabet(),
				input.getCallAlphabet(),
				input.getReturnAlphabet(),
				input.getContentFactory());
		minimize = false;
		computeResult();
	}
	
	@Override
	protected Collection<IState<S,C>> computeInitialStates() {
		ArrayList<IState<S,C>> resInitials = 
			new ArrayList<IState<S,C>>(input.getInitialStates().size());
		DeterminizedState<S,C> detState = 
			new DeterminizedState<S,C>(contentFactory);
		for (IState<S,C> inputState : input.getInitialStates()) {
			detState.addPair(inputAuxilliaryEmptyStackState,inputState);
		}		
		IState<S,C> resState = result.addState(true,
									detState.isFinal(), detState.getContent());
		det2res.put(detState,resState);
		res2det.put(resState, detState);
		resInitials.add(resState);

		return resInitials;
	}





	@Override
	protected Collection<IState<S, C>> computeInternalSuccessors(
			DoubleDecker<S, C> doubleDecker) {
		List<IState<S,C>> resInternalSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		
		DeterminizedState<S,C> detState = res2det.get(resState);
		
		for (S symbol : input.getInternalAlphabet()) {
			DeterminizedState<S,C> detSucc = 
				stateDeterminizer.internalSuccessor(detState, symbol);
			IState<S,C> resSucc = getResState(detSucc);
			result.addInternalTransition(resState, symbol, resSucc);
			resInternalSuccessors.add(resSucc);
		}
		return resInternalSuccessors;
	}
	
	
	@Override
	protected Collection<IState<S, C>> computeCallSuccessors(
			DoubleDecker<S, C> doubleDecker) {
		List<IState<S,C>> resCallSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		
		DeterminizedState<S,C> detState = res2det.get(resState);
		
		for (S symbol : input.getCallAlphabet()) {
			DeterminizedState<S,C> detSucc = 
				stateDeterminizer.callSuccessor(detState, symbol);
			IState<S,C> resSucc = getResState(detSucc);
			result.addCallTransition(resState, symbol, resSucc);
			resCallSuccessors.add(resSucc);
		}
		return resCallSuccessors;
	}


	@Override
	protected Collection<IState<S, C>> computeReturnSuccessors(
			DoubleDecker<S, C> doubleDecker) {
		List<IState<S,C>> resReturnSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		IState<S,C> resLinPred = doubleDecker.getDown();
		DeterminizedState<S,C> detState = res2det.get(resState);
		DeterminizedState<S,C> detLinPred = res2det.get(resLinPred);
		if (resLinPred == result.getEmptyStackState()) {
			return resReturnSuccessors;
		}
		
		for (S symbol : input.getReturnAlphabet()) {
			DeterminizedState<S,C> detSucc = 
				stateDeterminizer.returnSuccessor(detState, detLinPred, symbol);
			IState<S,C> resSucc = getResState(detSucc);
			result.addReturnTransition(resState, resLinPred, symbol, resSucc);
			resReturnSuccessors.add(resSucc);
		}
		return resReturnSuccessors;
	}

	
	
	/**
	 * Get the state in the resulting automaton that represents a
	 * DeterminizedState. If this state in the resulting automaton does not exist
	 * yet, construct it.
	 */
	IState<S,C> getResState(DeterminizedState<S,C> detState) {
		if (det2res.containsKey(detState)) {
			return det2res.get(detState);
		}
		else {
			IState<S,C> resState = result.addState(false,
									detState.isFinal(), detState.getContent());
			det2res.put(detState,resState);
			res2det.put(resState,detState);
			return resState;
		}
	}
	
	
	
	
}

