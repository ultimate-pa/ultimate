package local.stalin.automata.nwalibrary.operations;

import java.util.Set;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;

/**
 * Construct deterministic states like in the classical powerset construction.
 * For determinization of NWAs there is also a powerset construction. This
 * class implements the computation of deterministic successor states according
 * to this powerset construction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class PowersetSuccessorStateDeterminization<S,C> 
			implements IStateDeterminizer<S,C> {
	
	ContentFactory<C> contentFactory;
	
	public PowersetSuccessorStateDeterminization(
			ContentFactory<C> contentFactory) {
		
		this.contentFactory = contentFactory;
	}

	
	@Override
	public DeterminizedState<S,C> internalSuccessor(
			DeterminizedState<S,C> detState,
			S symbol) {
		
		DeterminizedState<S,C> succDetState = 
				new DeterminizedState<S,C>(contentFactory);
		for (IState<S,C> downState : detState.getCallerStates()) {
			for (IState<S,C> upState : detState.getPresentStates(downState)) {
				for (IState<S,C> upSucc : upState.getInternalSucc(symbol)) {
					succDetState.addPair(downState,upSucc);
				}
			}
		}
		return succDetState;	
	}
	


	@Override
	public DeterminizedState<S,C> callSuccessor(
			DeterminizedState<S,C> detState, 
			S symbol) {
		
		DeterminizedState<S,C> succDetState = 
				new DeterminizedState<S,C>(contentFactory);
		for (IState<S,C> downState : detState.getCallerStates()) {
			for (IState<S,C> upState : detState.getPresentStates(downState)) {
				for (IState<S,C> upSucc : upState.getCallSucc(symbol)) {
					succDetState.addPair(upState,upSucc);
				}
			}
		}
		return succDetState;	
	}

	

	@Override
	public DeterminizedState<S,C> returnSuccessor(
			DeterminizedState<S,C> detState,
			DeterminizedState<S,C> detLinPred,
			S symbol) {
		
		DeterminizedState<S,C> succDetState = 
				new DeterminizedState<S,C>(contentFactory);
		
		for (IState<S,C> downLinPred : detLinPred.getCallerStates()) {
			for (IState<S,C> upLinPred : detLinPred.getPresentStates(downLinPred)) {
				Set<IState<S, C>> upStates = detState.getPresentStates(upLinPred);
				if (upStates == null) continue;
				for (IState<S,C> upState : upStates) {
					for (IState<S,C> upSucc : upState.getReturnSucc(upLinPred,symbol)) {
						succDetState.addPair(downLinPred, upSucc);
					}
				}
			}
		}
		return succDetState;	
	}


	
	
}
