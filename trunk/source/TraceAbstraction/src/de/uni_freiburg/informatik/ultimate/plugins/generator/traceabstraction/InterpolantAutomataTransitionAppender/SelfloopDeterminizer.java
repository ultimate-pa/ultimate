package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;


/**
 * Tradeoff between PowersetDeterminizer and BestApproximationDeterminizer.
 * Idea: Make a selfloop if inductive. If not inductive use PowersetDeterminizer
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * TODO: For Call and Return this does not make much sense. Use there
 * generally the PowersetDeterminizer or the BestApproximationDeterminizer.
 */
public class SelfloopDeterminizer 
					implements IStateDeterminizer<CodeBlock, IPredicate> {

	SmtManager m_SmtManager;
	PowersetDeterminizer<CodeBlock, IPredicate> m_PowersetDeterminizer;
	
	INestedWordAutomaton<CodeBlock, IPredicate> m_InterpolantAutomaton;
	private final StateFactory<IPredicate> m_StateFactory;
	IPredicate m_InterpolantAutomatonFinalState;
	
	DeterminizedState<CodeBlock, IPredicate> m_ResultFinalState;
	
	public int m_InternalSelfloop = 0;
	public int m_InternalNonSelfloop = 0;

	public int m_CallSelfloop = 0;
	public int m_CallNonSelfloop = 0;

	public int m_ReturnSelfloop = 0;
	public int m_ReturnNonSelfloop = 0;
	
	public SelfloopDeterminizer(SmtManager mSmtManager,
			TAPreferences taPreferences,
			INestedWordAutomaton<CodeBlock, IPredicate> interpolantAutom,
			StateFactory<IPredicate> stateFactory) {
		super();
		m_SmtManager = mSmtManager;
		m_InterpolantAutomaton = interpolantAutom;
		m_StateFactory = stateFactory;
		m_PowersetDeterminizer = 
			new PowersetDeterminizer<CodeBlock, IPredicate>(m_InterpolantAutomaton, true, m_StateFactory);
		for (IPredicate state : m_InterpolantAutomaton.getStates()) {
			if (m_InterpolantAutomatonFinalState == null) {
				if (m_InterpolantAutomaton.isFinal(state)) {
					m_InterpolantAutomatonFinalState = state;
				}
			}
			else {
				throw new IllegalArgumentException("Interpolant Automaton" +
						" must have one final state");
			}
		}
		m_ResultFinalState = 
			new DeterminizedState<CodeBlock, IPredicate>(m_InterpolantAutomaton);
		m_ResultFinalState.addPair(m_InterpolantAutomaton.getEmptyStackState(),
											m_InterpolantAutomatonFinalState, m_InterpolantAutomaton);
	}
	
	@Override
	public DeterminizedState<CodeBlock, IPredicate> initialState() {
		return m_PowersetDeterminizer.initialState();
	}
	

	@Override
	public DeterminizedState<CodeBlock, IPredicate> internalSuccessor(
						DeterminizedState<CodeBlock, IPredicate> detState,
						CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_InternalSelfloop++;
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
					m_PowersetDeterminizer.internalSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			m_InternalNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			LBool isInductive = m_SmtManager.isInductive(detStateContent,
													   symbol, detStateContent);
			if (isInductive == Script.LBool.UNSAT) {
				m_InternalSelfloop++;
				return detState;
			}
		}
		m_InternalNonSelfloop++;
		return powersetSucc;
	}
	

	@Override
	public DeterminizedState<CodeBlock, IPredicate> callSuccessor(
						DeterminizedState<CodeBlock, IPredicate> detState,
						CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_CallSelfloop++;
			return m_ResultFinalState;
		}
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
					m_PowersetDeterminizer.callSuccessor(detState, symbol);
		if (containsFinal(powersetSucc)) {
			m_CallNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			LBool isInductive = m_SmtManager.isInductiveCall(detStateContent,
										   (Call) symbol, detStateContent);
			if (isInductive == Script.LBool.UNSAT) {
				m_CallSelfloop++;
				return detState;
			}
		}
		m_CallNonSelfloop++;
		return powersetSucc;
	}


	@Override
	public DeterminizedState<CodeBlock, IPredicate> returnSuccessor(
			DeterminizedState<CodeBlock, IPredicate> detState,
			DeterminizedState<CodeBlock, IPredicate> derHier,
			CodeBlock symbol) {
		if (detState == m_ResultFinalState) {
			m_ReturnSelfloop++;
			return m_ResultFinalState;
		}
		if (derHier == m_ResultFinalState) {
			throw new AssertionError("I guess this never happens");
		}		
		DeterminizedState<CodeBlock, IPredicate> powersetSucc = 
			m_PowersetDeterminizer.returnSuccessor(detState, derHier, symbol);
		if (containsFinal(powersetSucc)) {
			m_ReturnNonSelfloop++;
			return m_ResultFinalState;
		}
		if (powersetSucc.isSubsetOf(detState)) {
			IPredicate detStateContent = getState(detState);
			IPredicate detHierContent = getState(derHier);
			LBool isInductive = m_SmtManager.isInductiveReturn(detStateContent, 
						detHierContent, (Return) symbol, detStateContent);
			if (isInductive == Script.LBool.UNSAT) {
				m_ReturnSelfloop++;
				return detState;
			}
		}
		m_ReturnNonSelfloop++;
		return powersetSucc;
	}
	

	
	
	private boolean containsFinal(
						DeterminizedState<CodeBlock, IPredicate> detState) {
		for (IPredicate down : detState.getDownStates()) {
			for (IPredicate up : detState.getUpStates(down)) {
				if (up == m_InterpolantAutomatonFinalState) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public int getMaxDegreeOfNondeterminism() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean useDoubleDeckers() {
		return true;
	}
	
	@Override
	public IPredicate getState(
			DeterminizedState<CodeBlock, IPredicate> determinizedState) {
		return determinizedState.getContent(m_StateFactory);
	}

}
