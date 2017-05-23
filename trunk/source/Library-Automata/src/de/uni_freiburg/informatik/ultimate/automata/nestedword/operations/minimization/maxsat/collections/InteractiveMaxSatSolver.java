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
