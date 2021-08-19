package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.util.HashSet;
import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class TranslationManager {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private FunctionSymbol mIntand;
	private LinkedHashMap<Term, Term> mVariableMap; // Maps BV Var to Integer Var
	private LinkedHashMap<Term, Term> mReversedVarMap;
	private final TranslationConstrainer mTc;

	private final HashSet<Term> mConstraintSet; // Set of all constraints

	// private final HashMap<Term, Term> mTranslatedTerms; // Maps Bv term to Int
	// private final HashMap<Term, Term> mReversedTranslationMap;



	public TranslationManager(final ManagedScript mgdscript) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();

		mVariableMap = new LinkedHashMap<Term, Term>();
		mReversedVarMap = new LinkedHashMap<>();

		mConstraintSet = new HashSet<Term>();
		mTc = new TranslationConstrainer(mMgdScript);
	}

	public Term translateBvtoInt(final Term bitvecFromula) {

		final BvToIntTranslation bvToInt = new BvToIntTranslation(mMgdScript, mTc);
		bvToInt.setNutzTransformation(false);
		final Term integerFormulaNoConstraint = bvToInt.transform(bitvecFromula);
		mVariableMap = bvToInt.getVarMap();
		mReversedVarMap = bvToInt.getReversedVarMap();


		mConstraintSet.addAll(mTc.getConstraints());

		final Term integerFormula =
				SmtUtils.and(mScript, integerFormulaNoConstraint, SmtUtils.and(mScript, mConstraintSet));

		return integerFormula;

	}

	public Term translateIntBacktoBv(final Term integerFromula) {
		final HashSet<Term> constraints = mConstraintSet;
		constraints.addAll(mTc.getTvConstraints());
		final IntToBvBackTranslation intToBv = new IntToBvBackTranslation(mMgdScript, mReversedVarMap, constraints);

		return intToBv.transform(integerFromula);
	}


	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}

}
