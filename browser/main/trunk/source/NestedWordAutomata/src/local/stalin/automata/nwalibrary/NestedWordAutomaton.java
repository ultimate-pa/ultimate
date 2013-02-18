package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentLinkedQueue;

import local.stalin.automata.Activator;
import local.stalin.automata.NestedWordAutomata;
import local.stalin.automata.TestFileWriter;
import local.stalin.automata.nwalibrary.buchiNwa.AcceptanceCheck;
import local.stalin.automata.nwalibrary.buchiNwa.EmptinessCheck;
import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoRun;
import local.stalin.automata.nwalibrary.buchiNwa.NestedLassoWord;
import local.stalin.automata.nwalibrary.operations.BfsEmptiness;
import local.stalin.automata.nwalibrary.operations.DeterminizedAutomatonBuilder;
import local.stalin.automata.nwalibrary.operations.DifferenceAutomatonBuilder;
import local.stalin.automata.nwalibrary.operations.IStateDeterminizer;
import local.stalin.automata.nwalibrary.operations.Intersection;
import local.stalin.automata.nwalibrary.operations.PowersetSuccessorStateDeterminization;
import local.stalin.automata.nwalibrary.operations.SingleEntryNwaBuilder;
import local.stalin.automata.nwalibrary.operations.StandaloneDeterminize;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;



public class NestedWordAutomaton<S,C> implements INestedWordAutomaton<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	protected Collection<S> internalAlphabet;
	protected Collection<S> callAlphabet;
	protected Collection<S> returnAlphabet;
	
	protected Collection<IState<S,C>> states;
	protected Collection<IState<S,C>> initialStates;
	protected Collection<IState<S,C>> finalStates;
	protected final IState<S,C> emptyStackState;
	
	protected ContentFactory<C> m_contentFactory;
	
	
	public NestedWordAutomaton(Collection<S> internalAlphabet,
			   Collection<S> callAlphabet,
			   Collection<S> returnAlphabet,
			   ContentFactory<C> contentFactory) {
		
		this.internalAlphabet = internalAlphabet;
		this.callAlphabet = callAlphabet;
		this.returnAlphabet = returnAlphabet;
		this.states = new ArrayList<IState<S,C>>();
		this.initialStates = new ArrayList<IState<S,C>>();
		this.finalStates = new ArrayList<IState<S,C>>();
		if (contentFactory == null) {
			this.m_contentFactory = new ContentFactory<C>();
		}
		else {
			this.m_contentFactory = contentFactory;
		}
		this.emptyStackState = new State<S,C>(false,
				m_contentFactory.createEmptyStackContent());
	}
	
	/**
	 * @author Marcus Zeiger
	 * @author Jan Leike
	 * Copy constructor 
	 */
	public NestedWordAutomaton(NestedWordAutomaton<S,C> nwa) {
		super();
		
		if (nwa == null)
			throw new NullPointerException();
		//FIXME: Case where Symbol is compareable
		this.internalAlphabet = new HashSet<S>();
		this.internalAlphabet.addAll(nwa.getInternalAlphabet());
		this.callAlphabet = new HashSet<S>();
		this.callAlphabet.addAll(nwa.getCallAlphabet());
		this.returnAlphabet = new HashSet<S>();
		this.returnAlphabet.addAll(nwa.getReturnAlphabet());
		this.m_contentFactory = nwa.m_contentFactory;
		
		this.states = new TreeSet<IState<S,C>>(CompareByHash.instance);
		this.initialStates = new TreeSet<IState<S,C>>(CompareByHash.instance);
		this.finalStates = new TreeSet<IState<S,C>>(CompareByHash.instance);
		this.emptyStackState = new State<S,C>(false,
				m_contentFactory.createEmptyStackContent());
		
		// Copy all states
		Map<IState<S,C>, State<S,C>> stateCopies
			= new TreeMap<IState<S,C>, State<S,C>>(CompareByHash.instance);
		for (IState<S,C> state : nwa.states) {
			State<S,C> newState = new StateDl<S,C>(state);
			this.states.add(newState);
			if (nwa.getInitialStates().contains(state))
				this.initialStates.add(newState);
			if (nwa.getInitialStates().contains(state))
				this.finalStates.add(newState);
			
			stateCopies.put(state, newState);
		}
		
		// Copy transition functions for each state
		for (IState<S,C> state : nwa.states) {
			State<S,C> newState = stateCopies.get(state);
			
			// Copy internal transitions
			for (S symbol : state.getSymbolsInternal())
				for(IState<S,C> succState : state.getInternalSucc(symbol)) {
					IState<S,C> newSuccState = stateCopies.get(succState);
					newState.addInternalTransition(symbol, newSuccState);
				}
			
			// Copy call transitions
			for (S symbol : state.getSymbolsCall())
				for(IState<S,C> succState : state.getCallSucc(symbol)) {
					IState<S,C> newSuccState = stateCopies.get(succState);
					newState.addCallTransition(symbol, newSuccState);
				}
			
			// Copy return transitions
			for (S symbol : state.getSymbolsReturn())
				for (IState<S,C> linPred : state.getReturnLinearPred(symbol)) {
					IState<S,C> newLinPred = stateCopies.get(linPred);
					for (IState<S,C> succState : state.getReturnSucc(linPred, symbol)) {
						IState<S,C> newSuccState = stateCopies.get(succState);
						newState.addReturnTransition(symbol, newLinPred, newSuccState);
					}
				}
		}
	}
	
	@Override
	public Collection<S> getInternalAlphabet() {
		return internalAlphabet == null ? new ArrayList<S>(0) : internalAlphabet;
	}	
	
	@Override
	public Collection<S> getCallAlphabet() {
		return callAlphabet == null ? new ArrayList<S>(0) : callAlphabet;
	}
	
	@Override
	public Collection<S> getReturnAlphabet() {
		return returnAlphabet == null ? new ArrayList<S>(0) : returnAlphabet;
	}
	
	@Override
	public Collection<IState<S,C>> getAllStates() {
		return this.states;
	}
	
	@Override
	public Collection<IState<S,C>> getInitialStates() {
		return this.initialStates;
	}
	
	@Deprecated
	@Override
	public Collection<IState<S,C>> getFinalStates() {
		return this.finalStates;
	}
	
	@Override
	public IState<S, C> getEmptyStackState() {
		return this.emptyStackState;
	}

	public ContentFactory<C> getContentFactory() {
		return this.m_contentFactory;
	}
	
	public boolean isInitial(IState<S,C> state) {
		return initialStates.contains(state);
	}
	
	public boolean isFinal(IState<S,C> state) {
		return finalStates.contains(state);
	}
	
	@Override
	public IState<S,C> addState(boolean isInitial, boolean isFinal, C content) {
		IState<S,C> state = new StateDl<S,C>(isFinal, content);
		states.add(state);
		if (isInitial)
			initialStates.add(state);
		if (isFinal)
			finalStates.add(state);
		return state;
	}
	
//	public boolean delState(IState<S,C> state) {
//		State<S,C> s = (State<S,C>) state;
//		List<S> symbolsInternal = new ArrayList<S>(s.getSymbolsInternal());
//		for (S symbol: symbolsInternal) {
//			List<IState<S,C>> internalSuccs = new ArrayList<IState<S,C>>(s.getInternalSucc(symbol));
//			for (IState<S,C> succ : internalSuccs) {
//				boolean existed =
//				s.delInternalTransition(symbol, succ);
//				assert(existed);
//			}
//		}
//		List<S> symbolsCall = new ArrayList<S>(s.getSymbolsCall());
//		for (S symbol: symbolsCall) {
//			List<IState<S,C>> callSuccs = new ArrayList<IState<S,C>>(s.getCallSucc(symbol));
//			for (IState<S,C> succ : callSuccs) {
//				boolean existed =
//					s.delCallTransition(symbol, succ);
//				assert(existed);
//			}
//		}
//		List<S> symbolsReturn = new ArrayList<S>(s.getSymbolsReturn());
//		for (S symbol: symbolsReturn) {
//			List<IState<S,C>> returnLinPreds = new ArrayList<IState<S,C>>(s.getReturnLinearPred(symbol));
//			for (IState<S,C> caller : returnLinPreds) {
//				List<IState<S,C>> returnSuccs = new ArrayList<IState<S,C>>(s.getReturnSucc(caller,symbol));
//				for (IState<S,C> succ : returnSuccs) {
//					boolean existed =
//						s.delReturnTransition(symbol,caller,succ);
//					assert(existed) : "This could also be a wrong assertion";
//				}
//			}
//		}
//		this.initialStates.remove(state);
//		this.finalStates.remove(state);
//		return this.states.remove(state);
//	}
	
	@Override
	public void addInternalTransition(IState<S,C> iState, S symbol, IState<S,C> succState) {
		assert states.contains(iState) : "State not in set of states";
		assert states.contains(succState) : "succState not in set of states";
		assert internalAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		state.addInternalTransition(symbol, succState);
	}
	
	@Override
	public void addInternalTransition(IState<S,C> iState, S symbol, Collection<IState<S,C>> succStates) {
		assert states.contains(iState) : "State not in set of states";
		assert states.containsAll(succStates);
		assert internalAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		for (IState<S,C> succState : succStates)
			state.addInternalTransition(symbol, succState);
	}
	
	@Override
	public void addCallTransition(IState<S,C> iState, S symbol, IState<S,C> succState) {
		assert states.contains(iState) : "State not in set of states";
		assert states.contains(succState)  : "succState not in set of states";
		assert callAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		state.addCallTransition(symbol, succState);
	}
	
	@Override
	public void addCallTransition(IState<S,C> iState, S symbol, Collection<IState<S,C>> succStates) {
		assert states.contains(iState) : "State not in set of states";
		assert states.containsAll(succStates);
		assert callAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		
		for (IState<S,C> succState : succStates)
			state.addCallTransition(symbol, succState);
	}
	
	@Override
	public void addReturnTransition(IState<S,C> iState, IState<S,C> linearPred, S symbol, IState<S,C> succState) {
		assert states.contains(iState) : "State not in set of states";
		assert states.contains(linearPred) : "linPred " + linearPred +" not in set of states";
		assert states.contains(succState)  : "succState not in set of states";
		assert returnAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		state.addReturnTransition(symbol, linearPred, succState);
	}
	
	@Override
	public void addReturnTransition(IState<S,C> iState, IState<S,C> linearPred, S symbol, Collection<IState<S,C>> succStates) {
		assert states.contains(iState) : "State not in set of states";
		assert states.contains(linearPred) : "linPred not in set of states";
		assert states.containsAll(succStates);
		assert returnAlphabet.contains(symbol) : "symbol not in alphabet";
		State<S,C> state = (State<S,C>)iState;
		for (IState<S,C> succState : succStates)
			state.addReturnTransition(symbol, linearPred, succState);
	}

	
	@Override
	/**
	 * @author Jan Leike 
	 */
	public void totalize() {
		/*
		 * Totalize the automaton by adding a transition for each symbol (and each predecessor) at
		 * every state
		 *
		 * NOTE: The automaton will be totalized according to the alphabet segmentation
		 *
		 * Runtime: O(a*s^2); s being the number of states and a the alphabet size
		 */
		
		assert this.isDeterministic(); // Otherwise totalization would not make sense
		
		// Add new sink state
		C sinkContent = m_contentFactory.createSinkStateContent();

		IState<S,C> sinkState = this.addState(false, false, sinkContent);
		
		// Never leave the sink state
		for (S symbol : internalAlphabet)
			this.addInternalTransition(sinkState, symbol, sinkState);
		for (S symbol : callAlphabet)
			this.addCallTransition(sinkState, symbol, sinkState);
		for (S symbol : returnAlphabet)
			for (IState<S,C> state : states)
				this.addReturnTransition(sinkState, state, symbol, sinkState);
		
		// Add all sink transitions
		boolean addedTransition = false;
		for (IState<S,C> state : states) {
			// Make internal transitions total 
			for (S symbol : internalAlphabet)
				if (state.getInternalSucc(symbol).size() == 0) {
					this.addInternalTransition(state, symbol, sinkState);
					addedTransition = true;
				}
			
			// Make call transitions total 
			for (S symbol : callAlphabet)
				if (state.getCallSucc(symbol).size() == 0) {
					this.addCallTransition(state, symbol, sinkState);
					addedTransition = true;
				}
			
			// Make return transitions total  
			for (S symbol : returnAlphabet)
				for (IState<S,C> linPred : states)
					if (state.getReturnSucc(linPred, symbol).size() == 0) {
						this.addReturnTransition(state, linPred, symbol, sinkState);
						addedTransition = true;
					}
		}
		
		// Check if sink state was needed
		if (!addedTransition)
			this.states.remove(sinkState);
	}
	

	
	
	@Override
	public INestedWordAutomaton<S,C> complement() {
		/*
		 * Complement the automaton by first creating the deterministic version, totalizing it
		 * and complementing the final states.
		 * 
		 * This algorithm creates the complement according to the alphabet partitioning.
		 * 
		 * Runtime: O(2^(s^2) + a*s^2); s being the number of states and a the alphabet size
		 */
		INestedWordAutomaton<S,C> result = new NestedWordAutomaton<S, C>(this);
		if (this.isDeterministic()) {
		}
		else {
			result = result.determinize();
		}
		result.totalize();
		
		for (IState<S,C> state : ((NestedWordAutomaton<S,C>)result).states)
			state.setFinal(!state.isFinal());
		
		return result;
	}
	
	
	



	
	@Override
	/**
	 * @author Jan Leike
	 * Check if all transitions are deterministic 
	 */
	public boolean isDeterministic() {
		
		if(this.initialStates.size() > 1)
			return false;
		
		// Check each state separately
		for (IState<S,C> state : this.states) {
			
			// Check call transitions
			for (S symbol : state.getSymbolsCall())
				if (state.getCallSucc(symbol).size() > 1)
					return false;
			
			// Check internal transitions
			for (S symbol : state.getSymbolsInternal())
				if (state.getInternalSucc(symbol).size() > 1)
					return false;
			
			// Check return transitions
			for (S symbol : state.getSymbolsReturn())
				for (IState<S,C> linPred : state.getReturnLinearPred(symbol))
					if (state.getReturnSucc(linPred, symbol).size() > 1)
						return false;
		}
		
		return true;
	}
	
	
	
	@Override
	public boolean accepts(NestedWord<S> nw) {
		NwaBasicOperations<S, C> nbo = new NwaBasicOperations<S,C>(this);
		return nbo.accepts(nw);
	}
	
	public INestedWordAutomaton<S,C> determinize() {
		DeterminizedAutomatonBuilder<S,C> determinizer = 
			new DeterminizedAutomatonBuilder<S, C>(this, 
					new PowersetSuccessorStateDeterminization<S, C>(
															m_contentFactory));
		INestedWordAutomaton<S,C> result = determinizer.getResult();

		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of determinization");
			NwaBasicOperations<S,C> nbo = 
											new NwaBasicOperations<S,C>(this);
			INestedWordAutomaton<S,C> resultJM = nbo.determinizeJM();
			assert (included(result, resultJM) == null);
			assert (included(resultJM, result) == null);
			
			StandaloneDeterminize<S,C> determinizerMH = 
				new StandaloneDeterminize<S, C>(this);
			INestedWordAutomaton<S,C> resultMH = determinizerMH.determinize();
			assert (included(result, resultMH) == null);
			assert (included(resultMH, result) == null);
		}
		return result;
	}
	
	public INestedWordAutomaton<S,C> determinizeJM() {
		NwaBasicOperations<S,C> determinizer = new NwaBasicOperations<S,C>(this);
		return determinizer.determinizeJM();
	}
	
	public INestedWordAutomaton<S,C> determinizeMH() {
		StandaloneDeterminize<S, C> determinizer = new StandaloneDeterminize<S, C>(this);
		return determinizer.determinize();
	}
	
	public INestedWordAutomaton<S,C> determinizeDoubleDecker() {
		DeterminizedAutomatonBuilder<S,C> determinizer = 
			new DeterminizedAutomatonBuilder<S, C>(this, new PowersetSuccessorStateDeterminization<S, C>(m_contentFactory));
		return determinizer.getResult();
	}
	
	

	
	
	
	
	
	@Override
	public INestedWordAutomaton<S,C> intersect(INestedWordAutomaton<S,C> nwa) {
		Intersection<S,C> inter = new Intersection<S,C>(this);
		INestedWordAutomaton<S,C> result = inter.buildProduct(nwa);
		
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of intersection");
			NwaBasicOperations<S,C> nbo = new NwaBasicOperations<S,C>(this);
			INestedWordAutomaton<S,C> resultFP = nbo.intersectFullProduct(nwa);
			assert (included(result, resultFP) == null);
			assert (included(resultFP, result) == null);
		}
		return result;		
	}		
	
	@Override
	public NestedRun<S,C> getAcceptingNestedRun() {
		NestedRun<S,C> result = (new BfsEmptiness<S,C>(this).getAcceptingRun());
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of emptiness check");
			assert(result == null || this.accepts(result.getNestedWord()));
		}
		return result;
	}
	
	

	public INestedWordAutomaton<S,C> difference(INestedWordAutomaton<S,C> nwa2){
		IStateDeterminizer<S,C> powersetDeterminizer = 
			new PowersetSuccessorStateDeterminization<S, C>(m_contentFactory);
		DifferenceAutomatonBuilder<S,C> dab = 
			new DifferenceAutomatonBuilder<S,C>(this,
												nwa2,
												powersetDeterminizer,
												false);
		INestedWordAutomaton<S,C> result = dab.getResult();

		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of difference");
			DeterminizedAutomatonBuilder<S,C> determinizer = 
				new DeterminizedAutomatonBuilder<S, C>(nwa2,powersetDeterminizer);
			INestedWordAutomaton<S,C> nwa2detDD = determinizer.getResult();
			INestedWordAutomaton<S,C> resultDD = 
				(new Intersection<S,C>(this)).buildProduct(nwa2detDD.complement());
			assert (included(result, resultDD) == null);
			assert (included(resultDD, result) == null);
			
			StandaloneDeterminize<S,C> determinizerMH = 
				new StandaloneDeterminize<S,C>(nwa2);
			INestedWordAutomaton<S,C> nwa2detMH = determinizerMH.determinize();
			INestedWordAutomaton<S,C> resultMH = 
				(new Intersection<S,C>(this)).buildProduct(nwa2detMH.complement());
			assert (included(result, resultMH) == null);
			assert (included(resultMH, result) == null);
		}
		return result;		
	}
	
	

	@Override
	public boolean accepts(NestedLassoWord<S> nlw) {
		AcceptanceCheck<S,C> acceptanceCheck = new AcceptanceCheck<S, C>();
		return acceptanceCheck.accepts(nlw, this);
	}
	
	public void downsize() {
		NwaDownsizer<S,C> downsizer = new NwaDownsizer<S,C>();
		
		INestedWordAutomaton<S,C> copy = null;
		if (NestedWordAutomata.TEST) {
			copy = new NestedWordAutomaton<S,C>(this);
		}
		downsizer.downsize(this);
		if (NestedWordAutomata.TEST) {
			assert (included(copy, this) == null);
			assert (included(this, copy) == null);
		}
	}
	
	
	public INestedWordAutomaton<S,C> getConcurrentProduct(
											INestedWordAutomaton<S,C> nwa) {
		return (new ConcurrentProduct<S,C>(this, nwa, false)).getResult();
	}

	
	public INestedWordAutomaton<S,C> getConcurrentPrefixProduct(
			INestedWordAutomaton<S,C> nwa) {
		return (new ConcurrentProduct<S,C>(this, nwa, true)).getResult();
	}
	
	
	public INestedWordAutomaton<S,C> constructSingleEntryNwa(
												INestedWordAutomaton<S,C> nwa) {
		SingleEntryNwaBuilder<S,C> singleEntryNwaBuilder = 
			new SingleEntryNwaBuilder<S,C>(nwa);
		INestedWordAutomaton<S,C> result = singleEntryNwaBuilder.getResult();
		
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Testing correctness of singleEntryNwa");
			SingleEntryNwaBuilder<S, C> test = 
				new SingleEntryNwaBuilder<S,C>(result,true);
			NestedRun<S, C> counterexample = included(nwa, result);
			assert (counterexample == null);
			assert (included(result, nwa) == null);
		}
		return result;
	}
	
	
	
	/**
	 * Is the language recognized by nwa1 a subset of the language recognized by
	 * nwa2? If yes, the result is null. Otherwise an accepting run of nwa1 for
	 * a word that is not accepted by nwa2 is returned.
	 */
//	public NestedRun<S,C> included(INestedWordAutomaton<S,C> nwa1,
//			INestedWordAutomaton<S,C> nwa2) {
//		return nwa1.intersect(nwa2.complement()).getAcceptingNestedRun();
//	}
	
	public NestedRun<S,C> included(INestedWordAutomaton<S,C> nwa1,
			INestedWordAutomaton<S,C> nwa2) {
	return new BfsEmptiness<S, C>(
			(new DifferenceAutomatonBuilder<S,C>(nwa1, nwa2)).getResult()
			).getAcceptingRun();
	}
	
	

	public boolean equivalent(INestedWordAutomaton<S,C> nwa1,
			INestedWordAutomaton<S,C> nwa2) {
		if (nwa1.intersect(nwa2.complement()).getAcceptingNestedRun() == null
				&& nwa2.intersect(nwa1.complement()).getAcceptingNestedRun() == null) {
			return true;
		}
		return false;		
	}
	
	
	
	


	@Override
	public NestedLassoRun<S,C> getAcceptingNestedLassoRun() {
		EmptinessCheck<S,C> emptinessCheck = new EmptinessCheck<S,C>();
		NestedLassoRun<S,C> result = 
								emptinessCheck.getAcceptingNestedLassoRun(this);
		if (NestedWordAutomata.TEST) {
			s_Logger.debug("Check if acceptance agrees on emptiness test");
			if (result != null) {
				NestedWord<S> stem = result.getStem().getNestedWord();
				NestedWord<S> loop = result.getLoop().getNestedWord();
				assert (this.accepts(new NestedLassoWord<S>(stem, loop)));
			}
		}
		return result;
	}
	
	
	


	
	public int[] transitions() {
		int[] quantity = new int[3];
		for (IState<S,C> state : states) {
			quantity[0] += state.internalTransitions();
			quantity[1] += state.callTransitions();
			quantity[2] += state.returnTransitions();
		}
		return quantity;
	}
	
	
	public String sizeInformation() {
		int[] transitions = transitions();
		return "has " + states.size() + "states, " + transitions[0] + 
			" internal transitions " +  transitions[1] + " call transitions " +
			transitions[2] + "return transitions";
	}
	

	




	
	/**
	 * Returns true iff all states that appear in the graph structure of the
	 * automaton occur in the automatons list of states. 
	 */
	public boolean allStatesRegistered() {
		for (IState<S,C> state : states) {
			for (S symbol : state.getSymbolsInternal()) {
				for (IState<S,C> succ : state.getInternalSucc(symbol)) {
					if (!states.contains(succ)) {
						assert(false);
						return false;
					}
				}
			}
			
			for (S symbol : state.getSymbolsCall()) {
				for (IState<S,C> succ : state.getCallSucc(symbol)) {
					if (!states.contains(succ)) {
						assert(false);
						return false;
					}
				}
			}
			
			for (S symbol : state.getSymbolsReturn()) {
				for (IState<S,C> linearPred : state.getReturnLinearPred(symbol)) {
					if (!states.contains(linearPred)) {
						assert(false);
						return false;
					}
					for (IState<S,C> succ : state.getReturnSucc(linearPred,symbol)) {
						if (!states.contains(succ)) {
							assert(false);
							return false;
						}
					}
				}
			}
		}
		return true;
	}
	
	public InternalTransitions getInternalTransitions(IState<S,C> state, S symbol) {
		return new InternalTransitions(state, symbol);
	}
	
	public InternalTransitions getInternalTransitions(IState<S,C> state) {
		return new InternalTransitions(state);
	}
	
	public InternalTransitions getInternalTransitions() {
		return new InternalTransitions();
	}


	public class InternalTransition {
		private final IState<S,C> predecessor;
		private final S symbol;
		private final IState<S,C> successor;

		public InternalTransition(IState<S,C> predecessor, 
								  S symbol,
								  IState<S,C> successor) {
			this.predecessor = predecessor;
			this.symbol = symbol;
			this.successor = successor;
		}
		
		public IState<S,C> getPredecessor() {
			return predecessor;
		}
		
		public S getSymbol() {
			return symbol;
		}
		
		public IState<S,C> getSuccessor() {
			return successor;
		}
		
		public String toString() {
			return "( " + predecessor + " , " + symbol + " , " + 
															successor + " )";
		}
	}
	
	public class InternalTransitions implements Iterable<InternalTransition> {
		private final boolean fixedPredecessor;
		private IState<S,C> predecessor;
		private final boolean fixedSymbol;
		private S symbol;
		
		public InternalTransitions(IState<S,C> state, S symbol) {
			fixedPredecessor = true;
			this.predecessor = state;
			fixedSymbol = true;
			this.symbol = symbol;
		}
		
		public InternalTransitions(IState<S,C> state) {
			fixedPredecessor = true;
			this.predecessor = state;
			fixedSymbol = false;
		}
		
		public InternalTransitions() {
			fixedPredecessor = false;
			fixedSymbol = false;
		}
		

		@Override
		public Iterator<InternalTransition> iterator() {
			return new InternalTransitionIterator();
		}
		
		public class InternalTransitionIterator implements Iterator<InternalTransition> {
			
			public Iterator<IState<S, C>> predIterator;
			private Iterator<S> symbolIterator;
			private Iterator<IState<S,C>> succIterator;
			
			private boolean finished = false;
			


			public InternalTransitionIterator() {
				if (fixedSymbol) {
					assert (fixedPredecessor);
					predIterator = null;
					symbolIterator = null;
					succIterator = predecessor.getInternalSucc(symbol).iterator();
					assert (succIterator != null);
				}
				else {
					if (fixedPredecessor) {
						predIterator = null;
						symbolIterator = predecessor.getSymbolsInternal().iterator();
						assert (symbolIterator != null);
						updateSuccIterator();
						while (!finished && !succIterator.hasNext()) {
							updateSymbolIterator();
						}
					}
					else {
						predIterator = getAllStates().iterator();
						updateSymbolIterator();
						updateSuccIterator();
						while (!finished && !succIterator.hasNext()) {
							updateSymbolIterator();
						}
					}
				}
			}
			
			
			
			private void updateSuccIterator(){
				if (fixedSymbol) {
					this.finished = true;
					return;
				}
				else {
					while (!finished && !symbolIterator.hasNext() ) {
						updateSymbolIterator();
					}	
					if (this.finished) {
						return;
					}
					else {
						assert (symbolIterator.hasNext());
						symbol = symbolIterator.next();
						succIterator = predecessor.getInternalSucc(symbol).iterator();
					}
				}
			}
				
			private void updateSymbolIterator() {
				if (fixedPredecessor) {
					this.finished = true;
					return;
				}
				else {
					if (predIterator.hasNext()) {
						predecessor = predIterator.next();
						symbolIterator = predecessor.getSymbolsInternal().iterator();
					}
					else {
						this.finished = true;
					}
				}
			}

			@Override
			public boolean hasNext() {
				if (finished) {
					return false;
				}
				else {
					return succIterator.hasNext();
				}
				
			}

			@Override
			public InternalTransition next() {
				IState<S,C> succ = succIterator.next();
				InternalTransition result = 
					new InternalTransition(predecessor, symbol, succ);
				while (!finished && !succIterator.hasNext()) {
					updateSuccIterator();
				}
				return result; 
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
			
		}
		
	}
	
}
