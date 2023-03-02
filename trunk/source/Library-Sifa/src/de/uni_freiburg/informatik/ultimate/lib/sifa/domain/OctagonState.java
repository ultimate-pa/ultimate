package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon.OctValue;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.OctagonRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
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
		final List<OctagonRelation> octRelations = new ArrayList<>();
		final Map<Term, Integer> varToIndex = new HashMap<>();
		for (final Term conjunct : SmtUtils.getConjuncts(term)) {
			final PolynomialRelation polynomial = PolynomialRelation.of(script, conjunct);
			if (polynomial == null) {
				continue;
			}
			final OctagonRelation octRel = OctagonRelation.from(polynomial);
			if (octRel == null) {
				continue;
			}
			octRelations.add(octRel);
			varToIndex.putIfAbsent(octRel.getVar1(), varToIndex.size());
			varToIndex.putIfAbsent(octRel.getVar2(), varToIndex.size());
		}
		boolean allVarsAreInt = true;
		final OctMatrix resultMatrix = new OctMatrix(varToIndex.size());
		resultMatrix.fill(OctValue.INFINITY);
		for (final OctagonRelation octRel : octRelations) {
			final boolean isRealSort = SmtSortUtils.isRealSort(octRel.getVar1().getSort());
			allVarsAreInt &= !isRealSort;
			processRelation(varToIndex, octRel, resultMatrix, isRealSort);
		}
		return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
	}

	private static void processRelation(final Map<Term, Integer> varToIndex, final OctagonRelation octRel,
			final OctMatrix matrix, final boolean isRealSort) {
		final Rational constant;
		final boolean var1Negated;
		final boolean var2Negated;
		final Rational oldConstant = octRel.getConstant();
		switch (octRel.getRelationSymbol()) {
		case LEQ:
			constant = octRel.getConstant();
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GEQ:
			constant = octRel.getConstant().negate();
			var1Negated = !octRel.isNegateVar1();
			var2Negated = !octRel.isNegateVar2();
			break;
		case LESS:
			// For int sort: Replace a+b < c by a+b <= c-1
			// For real sort: Replace a+b < c by a+b <= c (overapproximation)
			constant = isRealSort ? oldConstant : oldConstant.sub(Rational.ONE);
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GREATER:
			// For int sort: Replace a+b > c by -a-b <= -c-1
			// For real sort: Replace a+b > c by -a-b <= -c (overapproximation)
			constant = isRealSort ? oldConstant.negate() : oldConstant.negate().sub(Rational.ONE);
			var1Negated = !octRel.isNegateVar1();
			var2Negated = !octRel.isNegateVar2();
			break;
		default:
			return;
		}
		final BigDecimal constantAsDecimal =
				new BigDecimal(constant.numerator()).divide(new BigDecimal(constant.denominator()));
		matrix.assumeVarRelationLeConstant(varToIndex.get(octRel.getVar1()), var1Negated,
				varToIndex.get(octRel.getVar2()), var2Negated, new OctValue(constantAsDecimal));
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

	public OctagonState widen(final OctagonState other) {
		// TODO: Do we need to rearrange other, if this is not satisfied?
		assert mMapNumericVarToIndex.equals(other.mMapNumericVarToIndex);
		return new OctagonState(mMapNumericVarToIndex, mNumericAbstraction.widenSimple(other.bestAvailableClosure()),
				mAllVarsAreInt);
	}

	private OctMatrix bestAvailableClosure() {
		if (mAllVarsAreInt && mNumericAbstraction.hasCachedTightClosure()) {
			return mNumericAbstraction.cachedTightClosure();
		} else if (mNumericAbstraction.hasCachedStrongClosure()) {
			return mNumericAbstraction.cachedStrongClosure();
		}
		return mNumericAbstraction;
	}
}
