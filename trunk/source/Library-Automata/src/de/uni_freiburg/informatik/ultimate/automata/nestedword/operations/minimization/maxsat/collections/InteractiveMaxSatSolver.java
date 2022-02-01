/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Partial Max-SAT solver for propositional logic clauses.
 * <p>
 * The extension toward {@link GeneralMaxSatSolver} is that there is a collection of
 * {@link IAssignmentCheckerAndGenerator}, i.e., interactive assignment checkers that produce additional
 * assignments.<br>
 * For example, one such instance allows that transitivity clauses need not be inserted but the equivalent information
 * can be generated on demand.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            type of {@link V} pair wrapper
 */
public class InteractiveMaxSatSolver<T> extends GeneralMaxSatSolver<T> {
	private final Iterable<IAssignmentCheckerAndGenerator<T>> mAssignmentCheckerAndGenerators;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param assignmentCheckerAndConstraintGenerators
	 *            collection of objects that check and produce new assignments
	 */
	public InteractiveMaxSatSolver(final AutomataLibraryServices services,
			final Iterable<IAssignmentCheckerAndGenerator<T>> assignmentCheckerAndConstraintGenerators) {
		super(services);
		mAssignmentCheckerAndGenerators = assignmentCheckerAndConstraintGenerators;
	}

	@Override
	public void addVariable(final T pair) {
		for (final IAssignmentCheckerAndGenerator<T> ccag : mAssignmentCheckerAndGenerators) {
			ccag.addVariable(pair);
		}
		super.addVariable(pair);
	}

	@Override
	protected void setVariable(final T pair, final boolean newStatus) {
		super.setVariable(pair, newStatus);

		// let all checkers know about new assignment, fetch implied assignments, and check for contradictions
		for (final IAssignmentCheckerAndGenerator<T> ccag : mAssignmentCheckerAndGenerators) {
			final Iterable<Pair<T, Boolean>> newVarStatusPairs = ccag.checkAssignment(pair, newStatus);
			if (applyAssignmentsAndReturnTrueIfContradicting(newVarStatusPairs)) {
				mConjunctionEquivalentToFalse = true;
				return;
			}
		}
		// do not call propagateAll() here, this will lead to (heavy) recursion!
	}

	private boolean applyAssignmentsAndReturnTrueIfContradicting(final Iterable<Pair<T, Boolean>> newVarStatusPairs) {
		for (final Pair<T, Boolean> varStatusPair : newVarStatusPairs) {
			final T var = varStatusPair.getFirst();
			final VariableStatus oldStatusOfVar = getCurrentVariableStatus(var);
			final Boolean newStatusOfVar = varStatusPair.getSecond();
			switch (oldStatusOfVar) {
				case TRUE:
				case FALSE:
					if (isContradicting(oldStatusOfVar, newStatusOfVar)) {
						// contradiction, stop and let parent solver backtrack
						return true;
					}
					// no contradiction, continue
					break;

				case UNSET:
					// do not check transitivity for this variable, we have already done that
					super.setVariable(var, true);
					break;
				default:
					throw new IllegalArgumentException("Unknown variable status.");
			}
		}
		return false;
	}

	private static boolean isContradicting(final VariableStatus oldStatusOfVar, final Boolean newStatusOfVar) {
		assert oldStatusOfVar == VariableStatus.TRUE
				|| oldStatusOfVar == VariableStatus.FALSE : "Only TRUE or FALSE is allowed.";
		return oldStatusOfVar == VariableStatus.TRUE ^ newStatusOfVar;
	}

	@Override
	protected void makeAssignmentPersistent() {
		for (final IAssignmentCheckerAndGenerator<T> ccag : mAssignmentCheckerAndGenerators) {
			ccag.makeAssignmentsPersistent();
		}
		super.makeAssignmentPersistent();
	}

	@Override
	protected void backtrack(final T pair) {
		for (final IAssignmentCheckerAndGenerator<T> ccag : mAssignmentCheckerAndGenerators) {
			ccag.revertOneScope();
		}
		super.backtrack(pair);
	}

	@Override
	protected void decideOne() {
		for (final IAssignmentCheckerAndGenerator<T> ccag : mAssignmentCheckerAndGenerators) {
			ccag.addScope();
		}
		super.decideOne();
	}
}
