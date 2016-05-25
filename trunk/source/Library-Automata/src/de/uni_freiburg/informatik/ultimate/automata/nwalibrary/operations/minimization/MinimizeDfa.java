/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Provides the DFA minimization operation "minimizeDFA" to the
 * NestedWordAutomaton Tool. It can also be used to reduce the state space of
 * NFAs. However: Unreachable states cannot be handled!
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.HasUnreachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 13.11.2011
 */
public class MinimizeDfa<LETTER,STATE> implements IOperation<LETTER,STATE> {
	private final AutomataLibraryServices mServices;
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
    
    /**
     * The jLogger instance.
     */
	private final ILogger mLogger;
    /**
     * The resulting automaton.
     */
    private NestedWordAutomaton<LETTER,STATE> mResult;
    /**
     * The input automaton.
     */
    private final INestedWordAutomatonOldApi<LETTER,STATE> mOperand;

    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            the input automaton
	 * @throws AutomataOperationCanceledException 
	 */
    public MinimizeDfa(AutomataLibraryServices services, INestedWordAutomatonOldApi<LETTER,STATE> operand)
            throws AutomataLibraryException {
    	mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
        if (new HasUnreachableStates<LETTER,STATE>(mServices, operand)
				.result()) {
			throw new IllegalArgumentException("No unreachalbe states allowed");
		}
		mOperand = operand;
		mLogger.info(startMessage());

		final ArrayList<STATE> states = new ArrayList<STATE>();
		states.addAll(mOperand.getStates());
		final boolean[][] table = initializeTable(states);
		calculateTable(states, table);

		if (mLogger.isDebugEnabled()) {
			printTable(states, table);
		}
		generateResultAutomaton(states, table);

		mLogger.info(exitMessage());
	}

	/*_______________________________________________________________________*\
    \* METHODS                                                               */
	
    /**
	 * Calculate, where in the table to set markers.
	 * 
	 * @param states
	 *            the states
	 * @param alphabet
	 *            the alphabet
	 * @param table
	 *            the table
     * @throws AutomataOperationCanceledException 
	 */
	private void calculateTable(ArrayList<STATE> states, boolean[][] table) throws AutomataLibraryException {
		// we iterate on the table to get all the equivalent states
		boolean makeNextIteration = true;
		while (makeNextIteration) {
			makeNextIteration = false;
			for (int i = 0; i < states.size(); i++) {
				for (int j = 0; j < i; j++) { // for each (i, j)
					if (!table[i][j]) { // if (i, j) not marked
						for (final LETTER s : mOperand.getInternalAlphabet()) {
							final ArrayList<STATE> first = getSuccessors(states, s, i);
							final ArrayList<STATE> second = getSuccessors(states, s, j);
							// if either i or j has no successors, for k mark
							// (i, j) as not equivalent
							if (first.isEmpty() ^ second.isEmpty()) {
								mark(table, i, j);
								makeNextIteration = true;
								break;
							}
							if (markTable(first, second, table, i, j, states)
									| markTable(second, first, table, i, j,
											states)) {
								mark(table, i, j);
								makeNextIteration = true;
								break;
							}
						}
					}
				}
				if (mServices.getProgressMonitorService() != null
						&& !mServices.getProgressMonitorService().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}
	}

	/**
	 * Mark the table at (i, j) and (j, i).
	 * @param table the table to mark
	 * @param i position i
	 * @param j position j
	 */
	private void mark(boolean[][] table, int i, int j) {
		table[i][j] = true;
		table[j][i] = true;
	}

	/**
	 * Get successor for state i and symbol s.
	 * @param states
	 *            the states.
	 * @param alphabet
	 *            the alphabet
	 * @param i
	 *            the states counter i
	 * @param k
	 *            the alphabet counter k
	 * @return
	 */
	private ArrayList<STATE> getSuccessors(ArrayList<STATE> states, LETTER s, int i) {
		// check successor pairs (i', j') for each k
		// all successors of i for symbol k
		final ArrayList<STATE> first = new ArrayList<STATE>();
		for(final STATE state : mOperand.succInternal(states.get(i), s)) {
			first.add(state);
		}
		return first;
	}

	/**
	 * Initialize the table.
	 * 
	 * @param states
	 *            the states
	 * @return the initialized table
	 */
	private boolean[][] initializeTable(ArrayList<STATE> states) {
		// table that will save the equivalent states
		final boolean[][] table = new boolean[states.size()][states.size()];
		// Initialization:
		// we mark all the states (p,q) such that p in F and q not in F
		for (int r = 0; r < states.size(); r++) {
			for (int c = 0; c < r; c++) {
				if (!table[r][c]
						&& (mOperand.getFinalStates().contains(states.get(r)) !=
						mOperand.getFinalStates().contains(states.get(c)))) {
					mark(table, r, c);
				}
			}
		}
		return table;
	}

	/**
	 * Generate the resulting automaton.
	 * 
	 * @param states
	 *            the states
	 * @param alphabet
	 *            the alphabet
	 * @param table
	 *            the table
	 */
	private void generateResultAutomaton(ArrayList<STATE> states, boolean[][] table) {
		// merge states
		final boolean[] marker = new boolean[states.size()];
		final Set<STATE> temp = new HashSet<STATE>();
		final HashMap<STATE,STATE> oldSNames2newSNames = new HashMap<STATE,STATE>();
		@SuppressWarnings("unchecked")
		final
		StateFactory<STATE> snf = mOperand.getStateFactory();
        mResult = new NestedWordAutomaton<LETTER,STATE>(
        		mServices, 
                mOperand.getInternalAlphabet(), null, null, snf);

		for (int i = 0; i < states.size(); i++) {
			if (marker[i]) {
				continue;
			}
			temp.clear();
			// here we have the name of first state
			boolean isFinal = false;
			boolean isInitial = false;
			for (int j = 0; j < states.size(); j++) {
				if (!table[i][j]) {
					temp.add(states.get(j));
					marker[j] = true;
                    if (!isFinal) {
                        isFinal = mOperand.isFinal(states.get(j));
                    }
                    if (!isInitial) {
                        isInitial = mOperand.isInitial(states.get(j));
                    }
				}
			}
			final STATE minimizedStateName = snf.minimize(temp);
			for (final STATE c : temp) {
				oldSNames2newSNames.put(c, minimizedStateName);
			}
			mResult.addState(isInitial, isFinal, minimizedStateName);
			marker[i] = true;
		}

		// add edges
		for (final STATE c : mOperand.getStates()) {
			for (final LETTER s : mOperand.getInternalAlphabet()) {
				for (final STATE succ : mOperand.succInternal(c, s)) {
					final STATE newPred = oldSNames2newSNames.get(c);
					final STATE newSucc = oldSNames2newSNames.get(succ);
					mResult.addInternalTransition(newPred, s, newSucc);
				}
			}
		}
	}

	/**
	 * Print the table.
	 * 
	 * @param t
	 *            table
	 * @param st
	 *            states
	 */
	private void printTable(ArrayList<STATE> st, boolean[][] t) {
		StringBuilder sb = new StringBuilder();
		sb.append(" \t");
		for (int i = 0; i < st.size(); i++) {
			sb.append(st.get(i) + "\t");
		}
		mLogger.debug(sb.toString());
		sb = new StringBuilder();
		for (int i = 0; i < st.size(); i++) {
			sb.append(st.get(i) + "\t");
			for (int j = 0; j < st.size(); j++) {
				sb.append(t[i][j] ? "X\t" : " \t");
			}
			mLogger.debug(sb.toString());
			sb = new StringBuilder();
		}
	}
	
	/**
	 * Print transitions of this nwa.
	 * @param nwa
	 */
	private void printTransitions(INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
		StringBuilder msg;
		for (final STATE c : nwa.getStates()) {
			for (final LETTER s : nwa.getInternalAlphabet()) {
				for (final STATE succ : nwa.succInternal(c, s)) {
		        	msg = new StringBuilder(c.toString());
		            msg.append(" ").append(s).append(" ").append(succ);
		            mLogger.debug(msg);
		        }
			}
		}
	}

	/**
	 * Set markers in the table.
	 * 
	 * @param f
	 *            first successor array
	 * @param s
	 *            second successor array
	 * @param t
	 *            table
	 * @param i
	 *            counter i
	 * @param j
	 *            counter j
	 * @param st
	 *            states list
	 * @return boolean whether to continue or not ...
	 */
	private boolean markTable(ArrayList<STATE> f, ArrayList<STATE> s, boolean[][] t,
			int i, int j, ArrayList<STATE> st) {
		// if for one symbol k and for one I' it holds, that
		// all pairs (I', j') are marked, mark (i, j)
		nextSucc1: for (int g = 0; g < f.size(); g++) {
			for (int h = 0; h < s.size(); h++) {
				if (!t[st.indexOf(f.get(g))][st.indexOf(s.get(h))]) {
					// one successor pair is not marked for k and I'!
					continue nextSucc1; // Take next I'!
				}
			}
			return true;
		}
		return false;
	}
	
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String operationName() {
        return "minimizeDFA";
    }

    @Override
    public String startMessage() {
    	mLogger.info("Starting DFA Minimizer");
        final StringBuilder msg = new StringBuilder("Start ");
		msg.append(operationName()).append(" Operand ")
				.append(mOperand.sizeInformation());
        mLogger.info(msg.toString());

        if (mLogger.isDebugEnabled()) {
            printTransitions(mOperand);
        }
        
        if (!mOperand.isDeterministic()) {
            mLogger.info("Given automaton is not deterministic!");
            mLogger.info("Automaton will not be minimized, but only reduced.");
        }
        
        return "Starting to minimize...";
    }
    
    @Override
    public String exitMessage() {
        if (mLogger.isDebugEnabled()) {
        	printTransitions(mResult);
        }
        final StringBuilder msg = new StringBuilder();
        msg.append("Finished ").append(operationName()).append(" Result ")
                .append(mResult.sizeInformation());
        mLogger.info(msg.toString());

        return "Exiting DFA minimization";
    }

    @Override
    public  INestedWordAutomatonOldApi<LETTER,STATE> getResult() {
        return mResult;
    }

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(mServices, mOperand, mResult, stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(mServices, mResult, mOperand, stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mOperand);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                   */
}
