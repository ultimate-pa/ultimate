package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;

/**
 * The sum of infeasibility pivoter. This implements the pivoting strategy of [KBD2013]. The core idea is to optimize
 * all out of bounds variables at the same time by minimizing the sum of the error for each bound. The error of a bound
 * is the amount that an out of bound variable is currently larger resp. smaller than its bound. The algorithm ensures
 * that each pivoting step will not increase the sum of errors. We only consider bounds that were set as external
 * literals, not derived composites bounds, for two reasons: (1) the derived bounds will be upheld automatically, and
 * (2) pivoting may create new derived composites bound which messes up the global optimization goal.
 *
 * <p>
 * We have to be very precise with the epsilons and even consider a variable out of bounds if it has a strict bound and
 * the epsilon value is not large enough. Otherwise we again mess up the global optimization goal. When we reach a
 * plateau we follow a Bland like strategy as outlined in the paper.
 *
 * <p>
 * The core of this pivoter is fixOobs(), which runs until an error is found, or a rational solution is achieved.
 *
 * <dl>
 * <dt>[KBD2013]</dt>
 * <dd>T. King, C. Barret, B. Dutertre: Simplex with sum of infeasibilities for SMT. FMCAD 2013</dd>
 * </dl>
 *
 * @author hoenicke
 *
 */
public class SOIPivoter {

	LinArSolve mSolver;
	/**
	 * The variables that are currently out of bounds, and participate in the SOI
	 */
	ArrayList<LiteralReason> mOOBs;
	/**
	 * The current coefficients for the sum of out of bounds variables expressed
	 * using the current column variables.
	 */
	SortedMap<LinVar, Rational> mSOIVar;
	/**
	 * The current value for the sum of infeasibility
	 */
	ExactInfinitesimalNumber mSOIValue;
	/**
	 * The limiter describing the next pivot step.
	 */
	FreedomLimiter mBestLimiter;

	public SOIPivoter(final LinArSolve solver) {
		mSolver = solver;
	}

	/**
	 * Compute the virtual Sum Of Infeasibility variable and its value.
	 *
	 * @return true if there is a variable that is out of bound.
	 */
	public boolean computeSOI() {
		boolean isOOB = false;
		mSOIValue = ExactInfinitesimalNumber.ZERO;
		mSOIVar = new TreeMap<>();
		mOOBs = new ArrayList<>();
		for (final LinVar var : mSolver.mLinvars) {
			boolean isUpper;
			ExactInfinitesimalNumber diff = var.getValue().isub(var.getLowerBound());
			if (diff.signum() > 0) {
				isUpper = false;
			} else {
				diff = var.getValue().isub(var.getUpperBound()).negate();
				if (diff.signum() > 0) {
					isUpper = true;
				} else {
					continue;
				}
			}

			assert var.mBasic;
			isOOB = true;
			mOOBs.add(isUpper ? var.mUpperLiteral : var.mLowerLiteral);
			mSOIValue = mSOIValue.add(diff);
			// now we have found an out of bound variable.
			// isUpper is true if we violate the upper bound.
			// mSoiValue is already updated.
			// Next step: Update soiVar by adding the row of coefficients.

			BigInteger divisor = mSolver.mTableaux.get(var.mMatrixpos).getRawCoeff(0);
			if (isUpper) {
				divisor = divisor.negate();
			}
			boolean isConflicting = true;
			for (final MatrixEntry entry : var.getTableauxRow(mSolver)) {
				final LinVar colVar = entry.getColumn();
				Rational coeff = Rational.valueOf(entry.getCoeff(), divisor);
				final LiteralReason reason = coeff.signum() < 0 ? colVar.mUpperLiteral : colVar.mLowerLiteral;
				if (reason == null || !colVar.getValue().equals(reason.getBound())) {
					isConflicting = false;
				}
				final Rational oldValue = mSOIVar.get(colVar);
				if (oldValue != null) {
					coeff = coeff.add(oldValue);
				}
				mSOIVar.put(colVar, coeff);
			}
			// if we already found a conflict in a single variable, make it the only variable in the SOI.  The
			// remaining code will immediately find the conflict again and conflict and report it.
			if (isConflicting) {
				mOOBs.clear();
				mOOBs.add(isUpper ? var.mUpperLiteral : var.mLowerLiteral);
				mSOIValue = diff;
				mSOIVar.clear();
				for (final MatrixEntry entry : var.getTableauxRow(mSolver)) {
					final LinVar colVar = entry.getColumn();
					final Rational coeff = Rational.valueOf(entry.getCoeff(), divisor);
					mSOIVar.put(colVar, coeff);
				}
				return true;
			}
		}
		return isOOB;
	}

	/**
	 * Check if SOI cannot be strictly decreased by any pivot step.
	 * As a side effect it also updates mBestLimiter to be the one used for Bland pivoting strategy.
	 * @return true if SOI cannot be decreased.
	 */
	public boolean checkZeroFreedom() {
		boolean firstColumn = true;
		mBestLimiter = null;
		nextColumn:
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			// for negative coeff: check if we cannot increase var to lower the soi.
			// otherwise check if we cannot decrease var to lower the SOI.  In both cases the variable can be skipped.
			if (colVar.getValue().equals(coeff.signum() < 0 ? colVar.getUpperBound() : colVar.getLowerBound())) {
				continue;
			}

			for (final MatrixEntry me : colVar.getTableauxColumn(mSolver)) {
				final LinVar rowVar = me.getRow();
				final Rational weight = Rational.valueOf(me.getCoeff(), me.getHeadCoeff().negate());
				final LAReason bound = weight.signum() == coeff.signum() ? rowVar.mLowerLiteral : rowVar.mUpperLiteral;
				if (bound != null && rowVar.getValue().equals(new ExactInfinitesimalNumber(bound.getBound()))) {
					// check if this entry would be used by Bland strategy (first column, smallest row variable)
					if (firstColumn &&
							(mBestLimiter == null || mBestLimiter.getRowVar().compareTo(rowVar) > 0)) {
						mBestLimiter = new FreedomLimiter(ExactInfinitesimalNumber.ZERO, weight, bound.getBound(),
								rowVar, colVar);
					}

					// make weight the opposite sign of coeff and add it, to decrease absolute value of coeff.
					if (weight.signum() == coeff.signum()) {
						weight.negate();
					}
					coeff = coeff.add(weight);
					/* if adding the weight changed the sign, this column has zero freedom. Break the loop. */
					if (coeff.signum() != -weight.signum()) {
						firstColumn = false;
						continue nextColumn;
					}
				}
			}
			/* we got round and weight did not toggle: we can pivot */
			mBestLimiter = null;
			return false;
		}
		assert firstColumn || mBestLimiter != null;
		// we got through all columns -> freedom cannot be decreased.
		return true;
	}

	/**
	 * Find the pivot candidate using the Sum Of Infeasibility heuristic.
	 *
	 * @return The matrix entry describing the pivot point (row + column).
	 */
	public boolean findPivot() {
		ExactInfinitesimalNumber bestDiff = new ExactInfinitesimalNumber(Rational.MONE);
		mBestLimiter = null;
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			final Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			// for negative coeff: check if we cannot increase var to lower the soi.
			// otherwise check if we cannot decrease var to lower the SOI.  In both cases the variable can be skipped.
			final InfinitesimalNumber colBound = coeff.signum() < 0 ? colVar.getUpperBound() : colVar.getLowerBound();
			if (colVar.getValue().equals(colBound)) {
				continue;
			}

			// mSolver.mEngine.getLogger().debug("Column %2$s * %1$s", colVar, coeff);

			// Check how much we can lower the soi by changing this column variable.
			// For this collect all bounds on all variables and sort them by the time until they are hit.
			// bounds maps from the absolute difference of the new value for the column variable to the FreedomLimiter
			// describing which row variable+bound would be used as new limiter and the weight that tells how much the
			// SOI gradient for this column variable would change due to the newly met bounds.
			final SortedMap<ExactInfinitesimalNumber, FreedomLimiter> bounds = new TreeMap<>();

			// We also need to consider the other bound of the column variable as change point.
			{
				if (!colBound.isInfinity()) {
					final ExactInfinitesimalNumber colFreedom = colVar.getValue().isub(colBound).abs();
					bounds.put(colFreedom,
							new FreedomLimiter(colFreedom, Rational.ONE, colBound, colVar, colVar));
				}
			}
			for (final MatrixEntry me : colVar.getTableauxColumn(mSolver)) {
				// for each variable in this column, check by how much the column variable would change if the current
				// row variable would be used as bound. There may even be two interesting points for a row variable
				// that is currently out of bounds: when it is satisfied and when it is no longer satisfied.
				// weight is basically the matrix entry, i.e., the factor by which the column variable changes if the
				// row variable changes.
				// freedom is the amount the column variable changes if the row variable would be used as bounds.
				final LinVar rowVar = me.getRow();
				Rational weight = Rational.valueOf(me.getCoeff(), me.getHeadCoeff());
				if (coeff.signum() < 0) {
					weight = weight.negate();
				}
				if (rowVar.mLowerLiteral != null) {
					final InfinitesimalNumber bound = rowVar.mLowerLiteral.getBound();
					final ExactInfinitesimalNumber diff = rowVar.getValue().isub(bound);
					// a difference of zero counts as negative, because it means the rowVar is in bound.
					if (weight.signum() * (2 * diff.signum() - 1) > 0) {
						final ExactInfinitesimalNumber freedom = diff.div(weight);
						assert freedom.signum() >= 0;
						final FreedomLimiter prev = bounds.get(freedom);
						if (prev != null) {
							prev.merge(weight, bound, rowVar);
						} else {
							bounds.put(freedom, new FreedomLimiter(freedom, weight, bound, rowVar, colVar));
						}
					}
				}
				if (rowVar.mUpperLiteral != null) {
					final InfinitesimalNumber bound = rowVar.mUpperLiteral.getBound();
					final ExactInfinitesimalNumber diff = rowVar.getValue().isub(bound);
					// a difference of zero counts as positive, because it means the rowVar is in bound.
					if (weight.signum() * (2 * diff.signum() + 1) > 0) {
						final ExactInfinitesimalNumber freedom = diff.div(weight);
						assert freedom.signum() >= 0;
						final FreedomLimiter prev = bounds.get(freedom);
						if (prev != null) {
							prev.merge(weight, bound, rowVar);
						} else {
							bounds.put(freedom, new FreedomLimiter(freedom, weight, bound, rowVar, colVar));
						}
					}
				}
			}
			// mSolver.mEngine.getLogger().debug(bounds);
			Rational weight = coeff.abs();
			ExactInfinitesimalNumber lastFreedom = new ExactInfinitesimalNumber(Rational.ZERO);
			ExactInfinitesimalNumber soidiff = new ExactInfinitesimalNumber(Rational.ZERO);
			// mSolver.mEngine.getLogger().debug("Candidates: %s + %s", colVar, bounds);
			for (final FreedomLimiter limiter : bounds.values()) {
				soidiff = soidiff.add(limiter.mFreedom.sub(lastFreedom).mul(weight));
				lastFreedom = limiter.mFreedom;
				weight = weight.sub(limiter.getWeight());
				if (weight.signum() <= 0) {
					// with this variable we reach pivoting point; changing the column variable further would increase
					// the SOI again.
					// mSolver.mEngine.getLogger().debug("Candidate: %s", limiter);
					// mSolver.mEngine.getLogger().debug("soi diff: %s", soidiff);
					if (bestDiff.compareTo(soidiff) < 0) {
						bestDiff = soidiff;
						mBestLimiter = limiter;
						if (bestDiff.equals(mSOIValue)) {
							mSolver.getLogger().debug("Solved it!", bestDiff);
							return true;
						}
					}
					break;
				}
			}
			assert weight.signum() <= 0;
		}
		mSolver.getLogger().debug("Best Candidate: (%s)", bestDiff);
		return mBestLimiter != null;
	}

	/**
	 * Check if the current conflict is still a conflict if the bound is removed
	 * from the SOI. This must only be called if bound is already part of the SOI
	 * and the SOIVar is already in conflict.
	 *
	 * @return true, if the bound can be removed from the current conflict.
	 */
	private boolean isRedundant(LiteralReason bound) {
		// check if removing the bound from the SOI would still lead to a conflict.
		final LinVar var = bound.getVar();
		BigInteger divisor = mSolver.mTableaux.get(var.mMatrixpos).getRawCoeff(0);
		if (!bound.isUpper()) {
			divisor = divisor.negate();
		}
		for (final MatrixEntry entry : var.getTableauxRow(mSolver)) {
			final LinVar colVar = entry.getColumn();
			Rational coeff = Rational.valueOf(entry.getCoeff(), divisor);
			final Rational oldValue = mSOIVar.get(colVar);
			if (oldValue != null) {
				coeff = coeff.add(oldValue);
			}
			final InfinitesimalNumber colBound = coeff.signum() < 0 ? colVar.getUpperBound() : colVar.getLowerBound();
			if (!colVar.getValue().equals(colBound)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Compute the conflict clause from the Sum-Of-Infeasibility variable. All
	 * column variables should be at their bounds and the bound can be used to
	 * explain the conflict with the sum of all currently violated bounds.
	 *
	 * @return A conflict clause.
	 */
	public Clause computeConflict() {
		assert mSOIValue.signum() > 0;
		// Check for each OOB, if it can be removed without changing the conflict.
		for (final Iterator<LiteralReason> it = mOOBs.iterator(); it.hasNext();) {
			final LiteralReason bound = it.next();
			if (mOOBs.size() > 1 && isRedundant(bound)) {
				// remove it from the SOI.
				final LinVar var = bound.getVar();
				mSOIValue = mSOIValue.sub(bound.getBound().sub(var.getValue()).abs());
				assert mSOIValue.signum() > 0;
				BigInteger divisor = mSolver.mTableaux.get(var.mMatrixpos).getRawCoeff(0);
				if (!bound.isUpper()) {
					divisor = divisor.negate();
				}
				for (final MatrixEntry entry : var.getTableauxRow(mSolver)) {
					final LinVar colVar = entry.getColumn();
					Rational coeff = Rational.valueOf(entry.getCoeff(), divisor);
					final Rational oldValue = mSOIVar.get(colVar);
					if (oldValue != null) {
						coeff = coeff.add(oldValue);
					}
					mSOIVar.put(colVar, coeff);
				}
				it.remove();
			}
		}
		final Explainer explainer = new Explainer(mSolver, mSolver.getEngine().isProofGenerationEnabled(), null);
		InfinitesimalNumber slack = mSOIValue.roundToInfinitesimal();
		// Now sum up the remaining bounds
		for (final LiteralReason bound : mOOBs) {
			final Rational factor = bound.isUpper() ? Rational.ONE : Rational.MONE;
			assert slack.signum() > 0;
			slack = bound.explain(explainer, slack, factor);
			assert slack.signum() > 0;
		}
		// Now go through all columns and sum up the bounds of all involved column
		// variables.
		for (final Entry<LinVar, Rational> entry : mSOIVar.entrySet()) {
			final LinVar colVar = entry.getKey();
			final Rational coeff = entry.getValue();
			if (coeff.signum() == 0) {
				continue;
			}
			final LiteralReason reason = coeff.signum() < 0 ? colVar.mUpperLiteral : colVar.mLowerLiteral;
			assert colVar.getValue().equals(reason.getBound());
			slack = slack.div(coeff.abs());
			assert slack.signum() > 0;
			slack = reason.explain(explainer, slack, coeff.negate());
			assert slack.signum() > 0;
			slack = slack.mul(coeff.abs());
		}
		assert (explainer.checkSlack(slack));
		return explainer.createClause(mSolver.getEngine());
	}

	/**
	 * The main procedure. Fixes all out of bound variables.
	 *
	 * @return a conflict clause if some conflict was found, or null, if a solution satisfying all bounds was found.
	 */
	public Clause fixOobs() {
		mSolver.getLogger().debug("=== fixoobs ===");
		while (true) {
			if (!computeSOI()) {
				return null;
			}
			if (mSolver.getLogger().isDebugEnabled()) {
				mSolver.getLogger().debug("SOI: %s.%04d", mSOIValue.getRealValue().floor(),
						mSOIValue.getRealValue().frac().mul(BigInteger.valueOf(10000)).floor().numerator().intValue());
			}
			if (!findPivot()) {
				return computeConflict();
			}
			// inner loop if we didn't make progress
			int blandPivotStep = 0;
			while (mBestLimiter.mFreedom.signum() == 0) {
				mSolver.pivot(mBestLimiter.getRowVar().mMatrixpos, mBestLimiter.getColumnVar().mMatrixpos);
				mSolver.mNumPivotsBland++;
				blandPivotStep++;
				computeSOI();
				if (checkZeroFreedom()) {
					if (mBestLimiter == null) {
						mSolver.getLogger().debug("Conflict after %d Bland pivot steps", blandPivotStep);
						return computeConflict();
					}
				} else {
					mSolver.getLogger().debug("Finished %d Bland pivot steps", blandPivotStep);
					findPivot();
					assert mBestLimiter.mFreedom.signum() > 0;
				}
			}

			if (mBestLimiter.getRowVar() != mBestLimiter.getColumnVar()) {
				mSolver.pivot(mBestLimiter.getRowVar().mMatrixpos, mBestLimiter.getColumnVar().mMatrixpos);
			}
			mSolver.updateVariableValue(mBestLimiter.getRowVar(), new ExactInfinitesimalNumber(mBestLimiter.mBound));
		}
	}

	private static class FreedomLimiter {
		ExactInfinitesimalNumber mFreedom;
		Rational mWeight;
		InfinitesimalNumber mBound;
		LinVar mRow, mColumn;

		public FreedomLimiter(final ExactInfinitesimalNumber freedom, final Rational weight, final InfinitesimalNumber bound,
				final LinVar row, final LinVar column) {
			assert freedom.signum() >= 0;
			mFreedom = freedom;
			mWeight = weight.abs();
			mBound = bound;
			mRow = row;
			mColumn = column;
		}

		/**
		 * Merge two freedom limiter entries for the same freedom. Add the weights together and choose one of the
		 * variables as the new column candidate. We choose the smaller one (Bland's strategy).
		 *
		 * @param weight
		 *            The weight of the additional entry
		 * @param bound
		 *            The bound for the candidate variable described by entry.
		 * @param entry
		 *            The candidate variable.
		 */
		public void merge(final Rational weight, final InfinitesimalNumber bound, final LinVar newRow) {
			mWeight = mWeight.add(weight.abs());
			if (mRow.compareTo(newRow) > 0) {
				mRow = newRow;
				mBound = bound;
			}
		}

		public Rational getWeight() {
			return mWeight;
		}

		public LinVar getRowVar() {
			return mRow;
		}

		public LinVar getColumnVar() {
			return mColumn;
		}

		@Override
		public String toString() {
			return "Freedom[" + mFreedom + ",(" + getRowVar() + ")," + mWeight + "]";
		}
	}
}
