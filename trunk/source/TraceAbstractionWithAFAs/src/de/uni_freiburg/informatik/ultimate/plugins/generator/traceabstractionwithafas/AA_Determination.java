package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.Collections;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.BitUtil;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class AA_Determination<LETTER> implements IOperation<LETTER, IPredicate>{

	public AA_Determination(IUltimateServiceProvider ultimateServiceProvider, AlternatingAutomaton<LETTER, IPredicate> alternatingAutomaton, SmtManager smtManager, PredicateUnifier predicateUnifier){
		this.alternatingAutomaton = alternatingAutomaton;
		this.smtManager = smtManager;
		this.predicateUnifier = predicateUnifier;
		resultAutomaton = new NestedWordAutomaton<LETTER, IPredicate>(
			ultimateServiceProvider,
			alternatingAutomaton.getAlphabet(),
			Collections.<LETTER>emptySet(),
			Collections.<LETTER>emptySet(),
			alternatingAutomaton.getStateFactory()
		);
		LinkedList<Long> newStates = new LinkedList<Long>();
		newStates.add(alternatingAutomaton.getFinalStatesBitVector());
		resultAutomaton.addState(true, alternatingAutomaton.getAcceptingFunction().getResult(alternatingAutomaton.getFinalStatesBitVector()), getPredicate(alternatingAutomaton.getFinalStatesBitVector()));
		while(!newStates.isEmpty()){
			Long state = newStates.removeFirst();
			IPredicate predicate = getPredicate(state);
			for(LETTER letter : alternatingAutomaton.getAlphabet()){
				long nextState = alternatingAutomaton.resolveLetter(letter, state);
				if(nextState != 0){
					IPredicate nextPredicate = getPredicate(nextState);
					if(!resultAutomaton.getStates().contains(nextPredicate)){
						resultAutomaton.addState(false, alternatingAutomaton.getAcceptingFunction().getResult(nextState), nextPredicate);
						newStates.add(nextState);
					}
					resultAutomaton.addInternalTransition(predicate, letter, nextPredicate);
				}
			}
		}
	}
	private AlternatingAutomaton<LETTER, IPredicate> alternatingAutomaton;
	private SmtManager smtManager;
	private PredicateUnifier predicateUnifier;
	private NestedWordAutomaton<LETTER, IPredicate> resultAutomaton;

	private IPredicate getPredicate(long state){
		IPredicate predicate = predicateUnifier.getTruePredicate();
		int setBitIndex = BitUtil.getNextSetBit(state, 0);
		while(setBitIndex != -1){
			predicate = predicateUnifier.getOrConstructPredicate(smtManager.and(predicate, alternatingAutomaton.getStates().get(setBitIndex)));
			setBitIndex = BitUtil.getNextSetBit(state, setBitIndex + 1);
		}
		return predicate;
	}
	
	@Override
	public String operationName(){
		return "AA_Determination";
	}

	@Override
	public String startMessage(){
		return "Start: " + operationName();
	}

	@Override
	public String exitMessage(){
		return "Exit: " + operationName();
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() throws OperationCanceledException{
		return resultAutomaton;
	}

	@Override
	public boolean checkResult(StateFactory<IPredicate> stateFactory) throws AutomataLibraryException{
		return true;
	}
}
