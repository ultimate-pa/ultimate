package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctValue;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OctagonState {
	public static final OctagonState TOP = new OctagonState(Map.of(), OctMatrix.NEW, true);

	/**
	 * Map of numerical variable (ints and reals) names to the index of the corresponding block row/column in the
	 * octagon matrix {@link #mNumericAbstraction}. Block row/column i contains the rows/columns 2i and 2i+1.
	 */
	private final Map<Term, Integer> mMapNumericVarToIndex;

	/** Abstract state for numeric variables (ints and reals). This is the actual octagon. */
	private final OctMatrix mNumericAbstraction;

	private final boolean mAllVarsAreInt;

	private OctagonState(final Map<Term, Integer> mapNumericVarToIndex, final OctMatrix numericAbstraction,
			final boolean allVarsAreInt) {
		mMapNumericVarToIndex = mapNumericVarToIndex;
		mNumericAbstraction = numericAbstraction;
		mAllVarsAreInt = allVarsAreInt;
	}

	public static OctagonState from(final Term term, final Script script) {
		final List<PolynomialRelation> numericRelations = new ArrayList<>();
		final Map<Term, Integer> varToIndex = new HashMap<>();
		boolean allVarsAreInt = true;
		for (final Term conjunct : SmtUtils.getConjuncts(term)) {
			final PolynomialRelation polynomial = PolynomialRelation.of(script, conjunct);
			if (polynomial == null) {
				continue;
			}
			numericRelations.add(polynomial);
			for (final Term var : polynomial.getPolynomialTerm().getAbstractVariableAsTerm2Coefficient(script)
					.keySet()) {
				if (allVarsAreInt && SmtSortUtils.isRealSort(var.getSort())) {
					allVarsAreInt = false;
				}
				varToIndex.putIfAbsent(var, varToIndex.size());
			}
		}
		OctMatrix resultMatrix = getFreshMatrix(varToIndex.size());
		for (final PolynomialRelation rel : numericRelations) {
			// TODO: Insert the information of rel into newMatrix
			final OctMatrix newMatrix = getFreshMatrix(varToIndex.size());
			resultMatrix = OctMatrix.min(bestAvailableClosure(resultMatrix, allVarsAreInt),
					bestAvailableClosure(newMatrix, allVarsAreInt));
		}
		return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
	}

	private static OctMatrix getFreshMatrix(final int size) {
		final OctMatrix result = new OctMatrix(size);
		result.fill(OctValue.INFINITY);
		return result;
	}

	private static OctMatrix bestAvailableClosure(final OctMatrix numericAbstraction, final boolean allVarsAreInt) {
		if (allVarsAreInt && numericAbstraction.hasCachedTightClosure()) {
			return numericAbstraction.cachedTightClosure();
		} else if (numericAbstraction.hasCachedStrongClosure()) {
			return numericAbstraction.cachedStrongClosure();
		}
		return numericAbstraction;
	}

	public Term toTerm(final Script script) {
		final Term[] mapIndexToTerm = new Term[mMapNumericVarToIndex.size()];
		for (final Entry<Term, Integer> entry : mMapNumericVarToIndex.entrySet()) {
			mapIndexToTerm[entry.getValue()] = entry.getKey();
		}
		return SmtUtils.and(script, cachedSelectiveClosure().getTerm(script, mapIndexToTerm));
	}

	private OctMatrix cachedSelectiveClosure() {
		return mAllVarsAreInt ? mNumericAbstraction.cachedTightClosure() : mNumericAbstraction.cachedStrongClosure();
	}
}
