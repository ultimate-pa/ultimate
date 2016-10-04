/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;

/**
 * Partial MAX-SAT solver bridge to an external solver.
 * <p>
 * Communication happens via a DIMACS file of the following format (description inspired by the
 * <a href=http://www.maxsat.udl.cat/16/index.html>Max-SAT 2016 web page</a>):
 * <p>
 * <ol>
 * <li>The file can start with comments( lines beginning with the character 'c').</li>
 * <li>The parameters line is "p wcnf <i>V C W</i>" where <i>V</i> is the number of variables, <i>C</i> is the number of
 * clauses, and <i>W</i> is the maximum weight.</li>
 * <li>A clause with <i>n</i> variables is a one-line sequence "<i>w v1 ... vn</i> 0" where <i>w</i> is the weight
 * (which is 1 for soft clauses and <i>&gt;=W</i> for hard clauses) and the <i>vi</i> are distinct non-zero integers
 * between -<i>V</i> and <i>V</i>. A positive number denotes the corresponding variable, and a negative number denotes
 * the negation of the corresponding variable.</li>
 * </ol>
 * The weight of a clause (the first integer in the clause) must be positive and the sum of all soft clauses must be
 * smaller than 2^63. Hard clauses have weight greater or equal to <i>W</i> and soft clauses have weight 1. <i>W</i> is
 * always greater than the sum of the weights of violated soft clauses in the solution.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <V>
 *            variably type
 */
public class DimacsMaxSatSolver<V> extends AbstractMaxSatSolver<V> {
	private int mVariablesNumber;
	
	public DimacsMaxSatSolver(final AutomataLibraryServices services) {
		super(services);
		mVariablesNumber = 0;
	}
	
	@Override
	public void addVariable(final V var) {
		++mVariablesNumber;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public void addHornClause(final V[] negativeAtoms, final V positiveAtom) {
		addClause(negativeAtoms, (V[]) new Object[] { positiveAtom });
	}
	
	@Override
	public void addClause(final V[] negativeAtoms, final V[] positiveAtoms) {
		// TODO Auto-generated method stub
	}
	
	@Override
	public boolean solve() throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return false;
	}
	
	@Override
	protected Boolean getPersistentAssignment(final V var) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Map<V, Boolean> getValues() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	protected void log() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected VariableStatus getTemporaryAssignment(final V var) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected void backtrack(final V var) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected void makeAssignmentPersistent() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected void setVariable(final V var, final boolean newStatus) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected void decideOne() {
		throw new UnsupportedOperationException();
	}
}
