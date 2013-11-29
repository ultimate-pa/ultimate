package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class that computes a handle of an automaton.
 * We call an initial run of an automaton a <i>handle</i> if 
 * <ul>
 * <li> there is exactly one initial state
 * <li> each state but the last of the run has exactly one successor
 * <li> each state but the first of the run has exactly one predecessor
 * <li> no state occurs more than once in the handle (automaton does not have
 * a cycle shape)
 * </ul>
 * @author Matthias Heizmann
 */
public class GetHandle<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	INestedWordAutomaton<LETTER, STATE> m_Operand;
	NestedRun<LETTER,STATE> m_Handle;

	public GetHandle(INestedWordAutomaton<LETTER, STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		if (m_Operand.getInitialStates().size() != 1) {
			s_Logger.debug("not exactly one initial state, automaton has no handle");
			// do nothing
		} else {
			STATE singleInitial = m_Operand.getInitialStates().iterator().next();
			m_Handle = getSingleSuccessor(singleInitial);
			if (m_Handle == null) {
				// do nothing
			} else {
				while (true) {
					STATE knownPredecessor = m_Handle.getStateAtPosition(m_Handle.getLength()-2);
					STATE current = m_Handle.getStateAtPosition(m_Handle.getLength()-1);
					boolean singlePred = hasSinglePredecessor(current, knownPredecessor);
					if (!singlePred) {
						break;
					}
					NestedRun<LETTER, STATE> newSuffix = getSingleSuccessor(current);
					if (newSuffix == null) {
						break;
					} else {
						m_Handle = m_Handle.concatenate(newSuffix);
					}
					if (m_Handle.getLength() > m_Operand.size()) {
						s_Logger.info("automaton has cycle shape");
						m_Handle = null;
						break;
					}
				}
			}
		}
		s_Logger.info(exitMessage());
	}
	
	
	public NestedRun<LETTER,STATE> getSingleSuccessor(STATE state) {
		NestedRun<LETTER,STATE> result = null;
		for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Operand.internalSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state, 
						outTrans.getLetter(), NestedWord.INTERNAL_POSITION,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (OutgoingCallTransition<LETTER, STATE> outTrans : m_Operand.callSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state, 
						outTrans.getLetter(), NestedWord.PLUS_INFINITY,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		for (OutgoingReturnTransition<LETTER, STATE> outTrans : m_Operand.returnSuccessors(state)) {
			if (result == null) {
				result = new NestedRun<LETTER, STATE>(state, 
						outTrans.getLetter(), NestedWord.MINUS_INFINITY,
						outTrans.getSucc());
			} else {
				// two or more successors
				return null;
			}
		}
		return result;
	}
	
	public boolean hasSinglePredecessor(STATE state, STATE knownPredecessor) {
		STATE predecessor = null;
		for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Operand.internalPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		for (IncomingCallTransition<LETTER, STATE> inTrans : m_Operand.callPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		for (IncomingReturnTransition<LETTER, STATE> inTrans : m_Operand.returnPredecessors(state)) {
			if (predecessor == null) {
				predecessor = inTrans.getLinPred();
			} else {
				// two or more predecessors
				return false;
			}
		}
		if (predecessor == null) {
			return false;
		} else {
			assert predecessor == knownPredecessor : "wrong state";
			return true;
		}
	}

	@Override
	public NestedRun<LETTER,STATE> getResult() throws OperationCanceledException {
		return m_Handle;
	}

	@Override
	public String operationName() {
		return "getHandle";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		String result = "Finished " + operationName();
		if (m_Handle == null) {
			result += ". Automaton has no handle. ";
		} else {
			result += ". Found word of length " + m_Handle.getLength();
		}
		return result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
