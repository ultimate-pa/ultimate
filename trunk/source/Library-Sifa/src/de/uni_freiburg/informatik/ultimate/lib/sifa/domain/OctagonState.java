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
		boolean allVarsAreInt = true;
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
			final Term var1 = octRel.getVar1();
			final Term var2 = octRel.getVar2();
			varToIndex.putIfAbsent(var1, varToIndex.size());
			varToIndex.putIfAbsent(var2, varToIndex.size());
			if (allVarsAreInt && (SmtSortUtils.isRealSort(var1.getSort()) || SmtSortUtils.isRealSort(var2.getSort()))) {
				allVarsAreInt = false;
			}
		}
		final OctMatrix resultMatrix = new OctMatrix(varToIndex.size());
		resultMatrix.fill(OctValue.INFINITY);
		for (final OctagonRelation octRel : octRelations) {
			processRelation(varToIndex, octRel, resultMatrix);
		}
		return new OctagonState(varToIndex, resultMatrix, allVarsAreInt);
	}

	private static void processRelation(final Map<Term, Integer> varToIndex, final OctagonRelation octRel,
			final OctMatrix matrix) {
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
			if (oldConstant.isIntegral()) {
				constant = oldConstant.sub(Rational.ONE);
			} else {
				constant = oldConstant.floor();
			}
			var1Negated = octRel.isNegateVar1();
			var2Negated = octRel.isNegateVar2();
			break;
		case GREATER:
			if (oldConstant.isIntegral()) {
				constant = oldConstant.negate().sub(Rational.ONE);
			} else {
				constant = oldConstant.negate().floor();
			}
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
}
