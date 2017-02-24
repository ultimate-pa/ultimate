package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;

/**
 * Partial Max-SAT solver for propositional logic clauses.
 * <p>
 * The extension toward {@link GeneralMaxSatSolver} is that transitivity clauses need not be inserted but the equivalent
 * information can be generated on demand.<br>
 * As a price, the type of variables is more specific, namely a parametric pair (type {@link T}) of some other type
 * {@link V}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            type of {@link V} pair wrapper
 * @param <V>
 *            type of contents
 */
public class TransitivityGeneralMaxSatSolver<T, V> extends GeneralMaxSatSolver<T> {
	private final ScopedTransitivityGenerator<T, V> mTransitivityGenerator;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param transitivityGenerator
	 *            transitivity generator
	 */
	public TransitivityGeneralMaxSatSolver(final AutomataLibraryServices services,
			final ScopedTransitivityGenerator<T, V> transitivityGenerator) {
		super(services);
		mTransitivityGenerator = transitivityGenerator;
	}

	@Override
	public void addVariable(final T pair) {
		// check that transitivity generator knows the variables
		assert mTransitivityGenerator.hasContent(pair);

		super.addVariable(pair);
	}

	@Override
	protected void setVariable(final T pair, final boolean newStatus) {
		super.setVariable(pair, newStatus);

		if (!newStatus) {
			// ignore inequality
			return;
		}

		// process the transitivity information here
		final Iterable<T> transitiveVariables = mTransitivityGenerator.assertEquality(pair);
		for (final T equalityPair : transitiveVariables) {
			final VariableStatus status = getCurrentVariableStatus(equalityPair);
			switch (status) {
				case TRUE:
					// ignore already true variables (can legally happen!)
					break;

				case FALSE:
					mConjunctionEquivalentToFalse = true;
					return;

				case UNSET:
					// do not check transitivity for this variable, we have already done that
					super.setVariable(equalityPair, true);
					break;

				default:
					throw new IllegalArgumentException("Unknown variable status.");
			}
		}
		// do not call propagateAll() here, this will lead to (heavy) recursion!
	}

	@Override
	protected void makeAssignmentPersistent() {
		// report to transitivity generator
		mTransitivityGenerator.makeAllScopesPersistent();

		super.makeAssignmentPersistent();
	}

	@Override
	protected void backtrack(final T doubleton) {
		// report to transitivity generator
		mTransitivityGenerator.revertOneScope();

		super.backtrack(doubleton);
	}

	@Override
	protected void decideOne() {
		// report to transitivity generator
		mTransitivityGenerator.addScope();

		super.decideOne();
	}
}
