package local.stalin.plugins.generator.traceabstraction;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import local.stalin.SMTInterface.SMTInterface;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.CallAnnot;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.ReturnAnnot;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.traceabstraction.TAPreferences.AdditionalEdges;



import org.apache.log4j.Logger;

public class InterpolantAutomataBuilder {

	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final NestedRun<TransAnnot,IProgramState> m_NestedRun;
	HashMap<ProgramPoint, Set<IState<TransAnnot, IProgramState>>> m_loc2states =
		new HashMap<ProgramPoint,Set<IState<TransAnnot,IProgramState>>>();
	NestedWordAutomaton<TransAnnot, IProgramState> m_IA;
	final AdditionalEdges m_AdditionalEdges;
	final SmtManager m_SmtManager;
	IState<TransAnnot, IProgramState>[] states;
	final int m_Iteration;
	int m_satProbNumber = 0;
	final boolean m_Dump2File;
	final String m_DumpPath;
	final PrintWriter m_IterationPW;
	final boolean m_SelfloopTrue;
	final boolean m_SelfloopFalse = true;
	Set<IState<TransAnnot,IProgramState>> m_CallPredecessors = new HashSet<IState<TransAnnot,IProgramState>>();
	
	
	
	public InterpolantAutomataBuilder(
			NestedRun<TransAnnot,IProgramState> nestedRun,
			AdditionalEdges additionalEdges,
			SmtManager smtManager,
			int iterationNumber,
			boolean dump2File,
			String dumpPath,
			PrintWriter iterationPW,
			boolean selfloopTrue) {
		m_NestedRun = nestedRun;
		m_AdditionalEdges = additionalEdges;
		m_SmtManager = smtManager;
		m_Iteration = iterationNumber;
		m_Dump2File = dump2File;
		m_DumpPath = dumpPath;
		m_IterationPW = iterationPW;
		m_SelfloopTrue = selfloopTrue;
	}
	
	
	public NestedWordAutomaton<TransAnnot, IProgramState> 
	buildInterpolantAutomaton(StateFormula[] stateFormulas,
			Collection<TransAnnot> internalAlphabet,
			Collection<TransAnnot> callAlphabet,
			Collection<TransAnnot> returnAlphabet,
			ContentFactory<IProgramState> tAContentFactory) {
		assert(m_NestedRun.getStateSequence().size()==stateFormulas.length);
		String interpolantAutomatonType;
		switch (m_AdditionalEdges) {
		case NONE:
			interpolantAutomatonType = 
				"Constructing interpolant automaton without backedges";
			break;
		case CANONICAL:
			interpolantAutomatonType = 
				"Constructing canonical interpolant automaton";
			break;
		case EAGER:
			interpolantAutomatonType = 
				"Constructing eager interpolant automaton"; 
			break;
		default:
			throw new IllegalArgumentException();
			
		}
		if (m_SelfloopTrue) {
			interpolantAutomatonType += ", with selfloop in true state";
		}
		if (m_SelfloopFalse) {
			interpolantAutomatonType += ", with selfloop in false state";
		}
		s_Logger.info(interpolantAutomatonType);

		m_IA = new NestedWordAutomaton<TransAnnot, IProgramState>(
				internalAlphabet,
				callAlphabet,
				returnAlphabet,
				tAContentFactory);

		//maps a formula the automaton state that represents this formula
		HashMap<StateFormula,IState<TransAnnot,IProgramState>> representative = 
		        	new HashMap<StateFormula,IState<TransAnnot,IProgramState>>(); 
		
		// Statistics for the interpolant automaton with backedges.
		// yield[0] is the number of backedges whose inductiveness could be
		// proven
		// yield[1] is the number of backedges whose inductiveness could be
		// refuted
		// yield[2] is the number of backedges whose inductiveness could be
		// neither proven nor refuted
		// yield[3] is the number of backedges whose inductiveness could be
		// trivially decided
		int[] yield = new int[4]; 

		states = new IState[stateFormulas.length];
		{
			states[0] = m_IA.addState(true, false, stateFormulas[0]);
			representative.put(stateFormulas[0], states[0]);
			if (m_AdditionalEdges == AdditionalEdges.CANONICAL) {
				updateLoc2states(getLocationName(0), states[0]);
			}
		}
		for (int i=1; i<stateFormulas.length; i++) {
			
			if (representative.containsKey(stateFormulas[i])) {
				 states[i] = representative.get(stateFormulas[i]);
			}
			else {
				boolean isAccepting = false;
				if (stateFormulas[i]!=null && 
					stateFormulas[i].getFormula() == Atom.FALSE) {
					isAccepting = true;
				}
				states[i] = m_IA.addState(false, isAccepting, stateFormulas[i]);
				if (stateFormulas[i]!=null) {
					representative.put(stateFormulas[i], states[i]);
				}
			}
			if (m_NestedRun.getNestedWord().isCallPosition(i-1)) {
				m_IA.addCallTransition(
						states[i-1], getSymbol(i-1), states[i]);
				m_CallPredecessors.add(states[i-1]);
			}
			else if (m_NestedRun.getNestedWord().isReturnPosition(i-1)) {
				int callPos = m_NestedRun.getNestedWord().getCallPosition(i-1);
				m_IA.addReturnTransition(
					   states[i-1], states[callPos], getSymbol(i-1), states[i]);
			}
			else {
				m_IA.addInternalTransition(
						states[i-1], getSymbol(i-1), states[i]);
			}
			
			if (m_AdditionalEdges == AdditionalEdges.CANONICAL
					&& !stateFormulas[i].isUnknown()) {
				int[] thisStateYield =
				addBackedges(i);
				yield[0]+= thisStateYield[0];
				yield[1]+= thisStateYield[1];
				yield[2]+= thisStateYield[2];
				yield[3]+= thisStateYield[3];
			}
			if (m_AdditionalEdges == AdditionalEdges.CANONICAL) {
				updateLoc2states(getLocationName(i), states[i]);
			}
			
		}
		
		if (m_SelfloopTrue) {
			for (TransAnnot symbol : internalAlphabet) {
				m_IA.addInternalTransition(states[0], symbol, states[0]);
			}
			for (TransAnnot symbol : callAlphabet) {
				m_IA.addCallTransition(states[0], symbol, states[0]);
			}
			for (TransAnnot symbol : returnAlphabet) {
					m_IA.addReturnTransition(states[0], states[0] , symbol, states[0]);
			}
			
		}
		
		
		
		if (m_SelfloopFalse) {
			for (TransAnnot symbol : internalAlphabet) {
				m_IA.addInternalTransition(states[stateFormulas.length-1], symbol, states[stateFormulas.length-1]);
			}
			for (TransAnnot symbol : callAlphabet) {
				m_IA.addCallTransition(states[stateFormulas.length-1], symbol, states[stateFormulas.length-1]);
			}
			for (TransAnnot symbol : returnAlphabet) {
				for (IState<TransAnnot, IProgramState> linPred : m_CallPredecessors) {
					m_IA.addReturnTransition(states[stateFormulas.length-1], linPred , symbol, states[stateFormulas.length-1]);
				}
			}
		}
		
		
		s_Logger.info("Check inductivity of " +
				(yield[0]+yield[1]+yield[2]+yield[3]) +	" backedges. " + 
				yield[0] + " proven. " + 
				yield[1] + " refuted. " + 
				yield[2] + " times theorem prover too weak." +
				yield[3] + " trivial.");
		
		
		if (m_AdditionalEdges == AdditionalEdges.EAGER) {
			throw new UnsupportedOperationException();
//			addEdgesBetweenAllPairs();
		}
		return m_IA;
	}
	
	
	private ProgramPoint getLocationName(int i) {
		return m_NestedRun.getStateAtPosition(i).getContent().getProgramPoint();
	}
	
	private TransAnnot getSymbol(int i){
		return m_NestedRun.getNestedWord().getSymbolAt(i);
	}
	
	private void updateLoc2states(ProgramPoint location, 
					IState<TransAnnot, IProgramState> state) {
		Set<IState<TransAnnot, IProgramState>> set;
		if (m_loc2states.containsKey(location)) {
			set = m_loc2states.get(location);
		}
		else {
			set = new HashSet<IState<TransAnnot, IProgramState>>();
			m_loc2states.put(location,set);
		}
		set.add(state);
	}
	
	
	
	private int[] addBackedges(int repLocPos) {
		IState<TransAnnot, IProgramState>
		repLocState = m_NestedRun.getStateAtPosition(repLocPos);
		Set<IState<TransAnnot, IProgramState>> repLocPredStates = 
			m_loc2states.get(repLocState.getContent().getProgramPoint());
		
		int[] yield = new int[4];
		if (repLocPredStates != null) {
			for (IState<TransAnnot,IProgramState> predState : repLocPredStates){
				int success = addBackedge(repLocPos,predState);
				switch (success) {
				case SMTInterface.SMT_UNSAT:
					yield[0]++;
					break;
				case SMTInterface.SMT_SAT:
					yield[1]++;
					break;
				case SMTInterface.SMT_UNKNOWN:
					yield[2]++;
					break;
				case 1729:
					yield[3]++;
					break;
				case -5:
					// do nothing
					// special case that means that formula of potential back
					// edge target was not computed
					break;
				default:
					throw new IllegalArgumentException();
				}
			}
		}
		return yield;
	}
	
	
	

	
	private int addBackedge(int repLocPos,
			IState<TransAnnot, IProgramState> occured) {
		IProgramState ps1 = states[repLocPos].getContent();
		IProgramState ps2 = occured.getContent();
		if (ps2 == null) {
			return -5;
		}
		
		
		int result = m_SmtManager.isCovered(ps1, ps2);
		
		IState<TransAnnot,IProgramState> backedgePredState = 
			states[repLocPos-1];
		if (result == SMTInterface.SMT_UNSAT || result == 1729) {
			TransAnnot symbol = m_NestedRun.getSymbol(repLocPos-1);
			if (m_NestedRun.isCallPosition(repLocPos-1)) {
				m_IA.addCallTransition(backedgePredState,
									   symbol,
									   occured);
			}
			else if(m_NestedRun.isInternalPosition(repLocPos-1)) {
				m_IA.addInternalTransition(backedgePredState,
						   symbol,
						   occured);
			}
			else if(m_NestedRun.isReturnPosition(repLocPos-1)) {
				
				Collection<IState<TransAnnot, IProgramState>> retLinPreds = 
					backedgePredState.getReturnLinearPred(symbol);
				for (IState<TransAnnot,IProgramState> retLinPred : retLinPreds){
					if (backedgePredState.getReturnSucc(retLinPred, symbol) != 
						states[repLocPos]) continue; 
					m_IA.addReturnTransition(backedgePredState, retLinPred, symbol, occured);
					assert (m_SmtManager.isInductiveReturn(
							backedgePredState.getContent(),
							retLinPred.getContent(),
							(ReturnAnnot) symbol,
							occured.getContent()) != SMTInterface.SMT_SAT);
				}
			}
			else {
				throw new IllegalArgumentException();
			}
			if (m_Dump2File) {
				ProgramPoint repLocName = m_NestedRun.getStateAtPosition(repLocPos).getContent().getProgramPoint(); 
				CegarLoop.dumpBackedges(repLocName,repLocPos,backedgePredState,backedgePredState.getReturnLinearPred(symbol),symbol,occured,					
						ps1, ps2, result, m_Iteration, m_satProbNumber, m_IterationPW);
			}
		}
		return result;
	}
	
	
	
	
}
