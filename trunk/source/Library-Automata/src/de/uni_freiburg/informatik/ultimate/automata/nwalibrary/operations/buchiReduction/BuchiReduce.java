/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Reduce the state space of a given Buchi automaton, as described in the paper
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 10.12.2011
 */
public class BuchiReduce<LETTER,STATE> implements IOperation<LETTER,STATE> {
    private static Logger s_Logger = NestedWordAutomata.getLogger();
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

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return ResultChecker.reduceBuchi(m_Operand, m_Result);
	}
}