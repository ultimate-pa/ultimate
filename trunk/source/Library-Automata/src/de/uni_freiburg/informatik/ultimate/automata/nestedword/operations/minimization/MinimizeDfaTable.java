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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.HasUnreachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 13.11.2011
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class MinimizeDfaTable<LETTER,STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	/*_______________________________________________________________________*\
	\* FIELDS / ATTRIBUTES                                                   */
	
	private final boolean mIsDeterministic;
	
	/*_______________________________________________________________________*\
	\* CONSTRUCTORS                                                          */
	
	/**
	 * Constructor.
	 * 
	 * @param services Ultimate services
	 * @param operand
	 *            the input automaton
	 * @throws AutomataLibraryException if construction fails
	 */
	public MinimizeDfaTable(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER,STATE> operand)
					throws AutomataLibraryException {
		super(services, operand.getStateFactory(), "minimizeDFA", operand);
		
	    assert !new HasUnreachableStates<LETTER,STATE>(mServices, operand).result() :
			"No unreachable states allowed";
		
		mIsDeterministic = isDeterministic();
		startMessageDebug();
	
		final ArrayList<STATE> states = new ArrayList<STATE>();
		states.addAll(mOperand.getStates());
		final boolean[][] table = initializeTable(states);
		calculateTable(states, table);
	
		if (mLogger.isDebugEnabled()) {
			printTable(states, table);
		}
		generateResultAutomaton(states, table);
	
		exitMessageDebug();
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
	 * @throws AutomataOperationCanceledException if timeout exceeds
	 */
	private void calculateTable(final ArrayList<STATE> states,
			final boolean[][] table)
					throws AutomataLibraryException {
		// we iterate on the table to get all the equivalent states
		boolean makeNextIteration = true;
		while (makeNextIteration) {
			makeNextIteration = false;
			for (int i = 0; i < states.size(); i++) {
				// for each (i, j)
				for (int j = 0; j < i; j++) {
					// if (i, j) not marked
					if (!table[i][j]) {
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
				if (isCancellationRequested()) {
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
	private void mark(final boolean[][] table, final int i, final int j) {
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
	 */
	private ArrayList<STATE> getSuccessors(final ArrayList<STATE> states,
			final LETTER s, final int i) {
		// check successor pairs (i', j') for each k
		// all successors of i for symbol k
		final ArrayList<STATE> first = new ArrayList<STATE>();
		for (final OutgoingInternalTransition<LETTER, STATE> trans :
				mOperand.internalSuccessors(states.get(i), s)) {
			first.add(trans.getSucc());
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
	private boolean[][] initializeTable(final ArrayList<STATE> states) {
		// table that will save the equivalent states
		final boolean[][] table = new boolean[states.size()][states.size()];
		// Initialization:
		// we mark all the states (p,q) such that p in F and q not in F
		for (int r = 0; r < states.size(); r++) {
			for (int c = 0; c < r; c++) {
				if (!table[r][c]
						&& (mOperand.isFinal(states.get(r))
								!= mOperand.isFinal(states.get(c)))) {
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
	private void generateResultAutomaton(final ArrayList<STATE> states, final boolean[][] table) {
		// merge states
		final boolean[] marker = new boolean[states.size()];
		final Set<STATE> temp = new HashSet<STATE>();
		final HashMap<STATE,STATE> oldSNames2newSNames = new HashMap<STATE,STATE>();
		startResultConstruction();
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
			final STATE minimizedStateName = mStateFactory.minimize(temp);
			for (final STATE c : temp) {
				oldSNames2newSNames.put(c, minimizedStateName);
			}
			addState(isInitial, isFinal, minimizedStateName);
			marker[i] = true;
		}
	
		// add edges
		for (final STATE c : mOperand.getStates()) {
			for (final LETTER s : mOperand.getInternalAlphabet()) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans :
						mOperand.internalSuccessors(c, s)) {
					final STATE newPred = oldSNames2newSNames.get(c);
					final STATE newSucc = oldSNames2newSNames.get(trans.getSucc());
					addInternalTransition(newPred, s, newSucc);
				}
			}
		}
		finishResultConstruction(null, false);
	}
	
	/**
	 * Print the table.
	 * 
	 * @param t
	 *            table
	 * @param st
	 *            states
	 */
	private void printTable(final ArrayList<STATE> st, final boolean[][] t) {
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
	 * @param nwa nested word automaton
	 */
	private void printTransitions(final INestedWordAutomaton<LETTER,STATE> nwa) {
		StringBuilder msg;
		for (final STATE c : nwa.getStates()) {
			for (final LETTER s : nwa.getInternalAlphabet()) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans :
						nwa.internalSuccessors(c, s)) {
		        	msg = new StringBuilder(c.toString());
		            msg.append(" ").append(s).append(" ").append(trans.getSucc());
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
	private boolean markTable(final ArrayList<STATE> f, final ArrayList<STATE> s, final boolean[][] t,
			final int i, final int j, final ArrayList<STATE> st) {
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
	
	
	private void startMessageDebug() {
	    final StringBuilder msg = new StringBuilder("Start ");
		msg.append(operationName()).append(" Operand ")
				.append(mOperand.sizeInformation());
	    mLogger.info(msg.toString());
	
	    if (mLogger.isDebugEnabled()) {
	        printTransitions(mOperand);
	    }
	    
	    if (! mIsDeterministic) {
	        mLogger.info("Given automaton is not deterministic!");
	        mLogger.info("Automaton will not be minimized, but only reduced.");
	    }
	    
	    mLogger.info("Starting to minimize...");
	}
	
	private void exitMessageDebug() {
	    if (mLogger.isDebugEnabled()) {
	    	printTransitions(getResult());
	    }
	    final StringBuilder msg = new StringBuilder();
	    msg.append("Finished ").append(operationName()).append(" Result ")
				.append(getResult().sizeInformation());
		mLogger.info(msg.toString());
	}
	
	/*_______________________________________________________________________*\
	\* GETTERS AND SETTERS                                                   */
}
