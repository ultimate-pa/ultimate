package local.stalin.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.DoubleDecker;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.operations.DoubleDeckerGraphBuilder;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.CallAnnot;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.RCfgState;
import local.stalin.plugins.generator.rcfgbuilder.RootAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;

public class RcfgHoareAnnotation extends DoubleDeckerGraphBuilder<TransAnnot,IProgramState> {
	
	
	INestedWordAutomaton<TransAnnot,IProgramState> m_Abstraction;
	
	private Map<IState,CallAnnot> m_State2Call = 
		new HashMap<IState,CallAnnot>();
	private Map<IState,IProgramState> m_State2Context = 
		new HashMap<IState,IProgramState>();
	private Set<IState> m_StatesWithoutContext = new HashSet<IState>();
	
	private Map<ProgramPoint,Set<IState>> m_ProgramPoint2States = 
		new HashMap<ProgramPoint,Set<IState>>();
	
	Map<String, Map<String, LocNode>> m_locNodeMapping;
	Theory m_Theory;
	
	public RcfgHoareAnnotation(INestedWordAutomaton<TransAnnot,IProgramState> abstraction, RootAnnot rootAnnot, SmtManager smtManager) {
		result = (NestedWordAutomaton<TransAnnot, IProgramState>) abstraction;
		m_Abstraction = result.constructSingleEntryNwa(abstraction);
		computeResult();
		m_locNodeMapping = rootAnnot.getLocNodes();
		m_Theory = smtManager.getTheory();
		
		
		for (IState<TransAnnot,IProgramState> state : m_StatesWithoutContext) {
			addFormulasToLocNodes(Atom.TRUE, state.getContent());
		}
		for (IState<TransAnnot,IProgramState> state : m_State2Context.keySet()) {
			Formula context = m_State2Context.get(state).getFormula();
			addFormulasToLocNodes(context, state.getContent());
		}
		
		
	}
	
	
	private void addFormulasToLocNodes(Formula context, IProgramState ps) {
		String procName = ps.getProgramPoint().getProcedure();
		String locName = ps.getProgramPoint().getLocation();
		LocNode locNode = m_locNodeMapping.get(procName).get(locName);
		RCfgState rcfgstate = locNode.getStateAnnot();
		Map<Formula, Formula> formulaMapping = rcfgstate.getFormulaMapping();
		Formula current = formulaMapping.get(context);
		if (current == null) {
			formulaMapping.put(context, ps.getFormula());
		}
		else {
			current = m_Theory.or(current, ps.getFormula());
			formulaMapping.put(context, current);
		}
	}
	
	
	private void addInformation(IState<TransAnnot,IProgramState> state, IProgramState ps) {
		ProgramPoint programPoint = state.getContent().getProgramPoint();
		Set<IState> states = m_ProgramPoint2States.get(programPoint);
		if (states == null) {
			states = new HashSet<IState>();
			m_ProgramPoint2States.put(programPoint, states);
		}
		states.add(state);
		CallAnnot call = m_State2Call.get(state);		
		if (call == null) {
			assert (ps == result.getEmptyStackState().getContent());
			m_StatesWithoutContext.add(state);
		}
		else {
			assert (ps != null);
			m_State2Context.put(state, ps);
		}
		
	}
	
	@Override
	protected Collection<IState<TransAnnot,IProgramState>> computeInitialStates() {
		Collection<IState<TransAnnot, IProgramState>> initialStates = 
			m_Abstraction.getInitialStates();
		for (IState state : initialStates) {
			m_StatesWithoutContext.add(state);
		}
		return initialStates; 
	}

	
	
	
	@Override
	protected Collection<IState<TransAnnot,IProgramState>> computeCallSuccessors(
			DoubleDecker<TransAnnot,IProgramState> doubleDecker) {
		IProgramState context = doubleDecker.getDown().getContent();
		addInformation(doubleDecker.getUp(), context);
		ArrayList succs = new ArrayList();
		for (TransAnnot symbol : doubleDecker.getUp().getSymbolsCall()) {
			CallAnnot call = (CallAnnot) symbol;
			for (IState succ : doubleDecker.getUp().getCallSucc(symbol)) {
				assert (m_State2Call.get(succ) == null ||
						m_State2Call.get(succ) == call);
				m_State2Call.put(succ, call);
				succs.add(succ);
			}
		}
		return succs;
	}


	@Override
	protected Collection<IState<TransAnnot,IProgramState>> computeInternalSuccessors(
			DoubleDecker<TransAnnot,IProgramState> doubleDecker) {
		IProgramState context = doubleDecker.getDown().getContent();
		addInformation(doubleDecker.getUp(), context);
		
		CallAnnot call = m_State2Call.get(doubleDecker.getUp());
		if (call == null) {
			assert (m_StatesWithoutContext.contains(doubleDecker.getUp()));
		}
		ArrayList succs = new ArrayList();
		for (TransAnnot symbol : doubleDecker.getUp().getSymbolsInternal()) {
			for (IState succ : doubleDecker.getUp().getInternalSucc(symbol)) {
				CallAnnot succCall = m_State2Call.get(succ);
				if (call == null) {
					assert (succCall == null);
					m_StatesWithoutContext.add(succ);
				}
				else {
					assert (succCall == null ||
							succCall == call);
					m_State2Call.put(succ, call);	
				}
				succs.add(succ);
			}
		}
		return succs;
	}
	

	@Override
	protected Collection<IState<TransAnnot,IProgramState>> computeReturnSuccessors(
			DoubleDecker<TransAnnot,IProgramState> doubleDecker) {
		IProgramState context = doubleDecker.getDown().getContent();
		addInformation(doubleDecker.getUp(), context);
		ArrayList succs = new ArrayList();
		for (TransAnnot symbol : doubleDecker.getUp().getSymbolsReturn()) {
			for (IState linPred : doubleDecker.getUp().getReturnLinearPred(symbol)) {
				CallAnnot call = m_State2Call.get(linPred);
				for (IState succ : doubleDecker.getUp().getReturnSucc(linPred,symbol)) {

					if (linPred == doubleDecker.getDown()) {
						succs.add(succ);
						if (call == null) {
							assert (m_State2Call.get(succ) == null);
							m_StatesWithoutContext.add(succ);
						}
						else {
							assert (m_State2Call.get(succ) == null ||
									m_State2Call.get(succ) == call);
							m_State2Call.put(succ, call);	
						}
					}
				}
			}
			
		}
		return succs;

	}

}
