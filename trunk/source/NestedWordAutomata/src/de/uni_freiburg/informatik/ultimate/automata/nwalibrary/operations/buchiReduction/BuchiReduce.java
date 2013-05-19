/**
 * Reduce the state space of a given Buchi automaton, as described in the paper
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 10.12.2011
 */
public class BuchiReduce<LETTER,STATE> implements IOperation {
    private static Logger s_Logger = UltimateServices.getInstance().getLogger(
            Activator.PLUGIN_ID);
    /**
     * The resulting Buchi automaton.
     */
    private INestedWordAutomatonOldApi<LETTER,STATE> m_Result;
    /**
     * The input automaton.
     */
    private INestedWordAutomatonOldApi<LETTER,STATE> m_Operand;

    /**
     * Constructor.
     * 
     * @param operand
     *            the automaton to reduce
     * @throws OperationCanceledException 
     */
    public BuchiReduce(INestedWordAutomatonOldApi<LETTER,STATE> operand)
            throws OperationCanceledException {
    	m_Operand = operand;
        BuchiReduce.s_Logger.info(startMessage());
        
        // Remove dead ends. 
        // Removal of dead ends is no optimization but a requirement for
        // correctness of the algorithm
        m_Operand = new ReachableStatesCopy<LETTER,STATE>(operand,false,false,true,false).getResult();
    	if(s_Logger.isDebugEnabled()) {
	    	StringBuilder msg = new StringBuilder();
	        msg.append(" W/O dead ends ").append(m_Operand.sizeInformation());
	        s_Logger.debug(msg.toString());
    	}
        m_Result = new DelayedSimulation<LETTER,STATE>(m_Operand, true).result;
        
        boolean compareWithNonSccResult = false;
        if (compareWithNonSccResult) {
        	NestedWordAutomaton<LETTER,STATE> nonSCCresult = 
        			new DelayedSimulation<LETTER,STATE>(m_Operand, false).result;
        	if (m_Result.size() != nonSCCresult.size()) {
        		throw new AssertionError();
        	}
        }
    	
    	//assert (ResultChecker.reduceBuchi(m_Operand, m_Result));
        s_Logger.info(exitMessage());
    }
    
    @Override
    public String operationName() {
        return "reduceBuchi";
    }

    @Override
    public String startMessage() {
		return "Start " + operationName() + ". Operand has " + 
		m_Operand.sizeInformation();	
    }

    @Override
    public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
		m_Result.sizeInformation();
    }

    @Override
    public INestedWordAutomatonOldApi<LETTER,STATE> getResult() {
        return m_Result;
    }
}