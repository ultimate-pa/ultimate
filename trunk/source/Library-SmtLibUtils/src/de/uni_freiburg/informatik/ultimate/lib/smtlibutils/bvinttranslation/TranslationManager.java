package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
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

	private final HashSet<Term> mConstraintSet; // Set of all constraints

	// private final HashMap<Term, Term> mTranslatedTerms; // Maps Bv term to Int
	// private final HashMap<Term, Term> mReversedTranslationMap;



	public TranslationManager(final ManagedScript mgdscript, final ConstraintsForBitwiseOperations cfbo) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();

		mVariableMap = new LinkedHashMap<Term, Term>();
		mReversedVarMap = new LinkedHashMap<>();

		mConstraintSet = new HashSet<Term>();
		mTc = new TranslationConstrainer(mMgdScript, cfbo);
		mIntand = mTc.getIntAndFunctionSymbol();
	}

	public void setReplacementVarMaps(final LinkedHashMap replacementVarMap) {
		mVariableMap = replacementVarMap;
	}

	public Triple<Term, Set<TermVariable>, Boolean> translateBvtoInt(final Term bitvecFromula) {
		final BvToIntTranslation bvToInt =
				new BvToIntTranslation(mMgdScript, mVariableMap, mTc, bitvecFromula.getFreeVars());
		bvToInt.setNutzTransformation(false);
		final Term integerFormulaNoConstraint = bvToInt.transform(bitvecFromula);
		mVariableMap = bvToInt.getVarMap();
		mReversedVarMap = bvToInt.getReversedVarMap();
		final Set<TermVariable> overapproxVariables = bvToInt.getOverapproxVariables();
		final boolean isOverapproximation = bvToInt.wasOverapproximation();
		if (!bvToInt.getNutzFlag()) {
			mConstraintSet.addAll(mTc.getConstraints());
			mConstraintSet.addAll(bvToInt.mArraySelectConstraintMap.values());
		}
		final Term integerFormula =
				SmtUtils.and(mScript, integerFormulaNoConstraint, SmtUtils.and(mScript, mConstraintSet));
		return new Triple<Term, Set<TermVariable>, Boolean>(integerFormula, overapproxVariables, isOverapproximation);

	}


	public Term translateIntBacktoBv(final Term integerFormula) {
		// The preprocessing steps need also to be applied on the constraint, to ensure the map matches them.
		final UnfTransformer unfT = new UnfTransformer(mScript);
		final Term simplifiedInput = unfT.transform(integerFormula); // very helpfull

		final HashSet<Term> constraints = mConstraintSet;
		constraints.addAll(mTc.getTvConstraints());

		final IntToBvBackTranslation intToBv =
				new IntToBvBackTranslation(mMgdScript, mReversedVarMap, constraints, mIntand);
		// TODO postpreocessing select propagation

		return intToBv.transform(simplifiedInput);
	}



	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}


}
