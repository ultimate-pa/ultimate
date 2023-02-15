/*
 * Copyright (C) 2021-2022 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class TranslationManager {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final FunctionSymbol mIntand;
	private LinkedHashMap<Term, Term> mVariableMap; // Maps BV Var to Integer Var
	private LinkedHashMap<Term, Term> mReversedVarMap;
	private final TranslationConstrainer mTc;

	private HashSet<Term> mConstraintSet; // Set of all constraints
	private final boolean mCongruenceBasedTransformation;
	private final ConstraintsForBitwiseOperations mCfo;

	/*
	 * Wrapper class for bit-vector to integer translation and back-translation Manages: variables and constraints
	 */
	public TranslationManager(final ManagedScript mgdscript, final ConstraintsForBitwiseOperations cfbo,
			final boolean useCongruenceBasedTransformation) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();

		mVariableMap = new LinkedHashMap<>();
		mReversedVarMap = new LinkedHashMap<>();

		mConstraintSet = new HashSet<>();
		mTc = new TranslationConstrainer(mMgdScript, cfbo);
		mIntand = mTc.getIntAndFunctionSymbol();

		mCongruenceBasedTransformation = useCongruenceBasedTransformation;
		mCfo = cfbo;
	}

	public void setReplacementVarMaps(final LinkedHashMap<Term, Term> replacementVarMap) {
		mVariableMap = replacementVarMap;
	}

	/*
	 * Method to translate bit-vector to integer. This method fills mVariableMap, mReversedVarMap and mConstraintSet in
	 * the process. returns a triple, first element is the translation result, second element is a map containing all
	 * variables used to overapproximate bit-wise function in constraint mode NONE, third is a flag that is true if
	 * constraint mode is NONE
	 */
	public Triple<Term, Set<TermVariable>, Boolean> translateBvtoInt(final Term bitvecFormula) {
		final BvToIntTranslation bvToInt = new BvToIntTranslation(mMgdScript, mVariableMap, mTc,
				bitvecFormula.getFreeVars(), mCongruenceBasedTransformation);
		final Term integerFormulaNoConstraint = bvToInt.transform(bitvecFormula);
		mVariableMap = bvToInt.getVarMap();
		mReversedVarMap = bvToInt.getReversedVarMap();
		final Set<TermVariable> overapproxVariables = bvToInt.getOverapproxVariables();
		final boolean isOverapproximation = bvToInt.wasOverapproximation();
		if (!mCongruenceBasedTransformation) {
			mConstraintSet.addAll(mTc.getConstraints());
			mConstraintSet.addAll(bvToInt.mArraySelectConstraintMap.values());
		}
		// TODO: Also add the constraints with mCongruenceBasedTransformation=true, maybe we need to be more careful
		// there
		final Term integerFormula =
				SmtUtils.and(mScript, integerFormulaNoConstraint, SmtUtils.and(mScript, mConstraintSet));
		return new Triple<>(integerFormula, overapproxVariables, isOverapproximation);

	}

	public Triple<Term, Set<Term>, Boolean> translateBvtoIntTransferrer(final Term bitvecFormula, final Script scriptBV,
			final Script scriptINT) {
		mConstraintSet = new HashSet<>();
		final TranslationConstrainer tc = new TranslationConstrainer(mMgdScript, mCfo);
		final BvToIntTransferrer bvToInt = new BvToIntTransferrer(scriptBV, scriptINT, mMgdScript, mVariableMap, tc,
				bitvecFormula.getFreeVars(), mCongruenceBasedTransformation);
		final Term integerFormulaNoConstraint;
		try {
			integerFormulaNoConstraint = bvToInt.transform(bitvecFormula);
		} catch (final SMTLIBException e) {
			throw new AssertionError("Translation error " + e);
		}
		mVariableMap = bvToInt.getVarMap();
		mReversedVarMap = bvToInt.getReversedVarMap();
		final Set<Term> overapproxVariables = bvToInt.getOverapproxVariables();
		final boolean isOverapproximation = bvToInt.wasOverapproximation();
		if (!mCongruenceBasedTransformation) {
			mConstraintSet.addAll(tc.getConstraints());
			mConstraintSet.addAll(bvToInt.mArraySelectConstraintMap.values());
		} else {
			mConstraintSet.addAll(tc.getBvandConstraints());
		}
		if (!mConstraintSet.isEmpty() && !SmtSortUtils.isBoolSort(integerFormulaNoConstraint.getSort())) {
			throw new AssertionError("Cannot add constraints to non-Boolean formula.");
		}
		// TODO: Also add the constraints with mCongruenceBasedTransformation=true, maybe we need to be more careful
		// there
		final Term integerFormula =
				SmtUtils.and(mScript, integerFormulaNoConstraint, SmtUtils.and(mScript, mConstraintSet));
		return new Triple<>(integerFormula, overapproxVariables, isOverapproximation);

	}

	/*
	 * Method to translate from integer back to bit-vector requires mReversedVarMap to be filled returns the translation
	 * result
	 */
	// TODO: Is there anything we need to change here with the congruence based transformation?
	public Term translateIntBacktoBv(final Term integerFormula) {
		// The preprocessing steps need also to be applied on the constraint, to ensure the map matches them.
		final UnfTransformer unfT = new UnfTransformer(mScript);
		final Term simplifiedInput = unfT.transform(integerFormula);

		final HashSet<Term> constraints = mConstraintSet;
		constraints.addAll(mTc.getTvConstraints());

		final IntToBvBackTranslation intToBv =
				new IntToBvBackTranslation(mMgdScript, mReversedVarMap, constraints, mIntand);

		return intToBv.transform(simplifiedInput);
	}

	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}

}
