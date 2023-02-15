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

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class BvToIntTranslation extends TermTransformer {
	private final Script mScript;
	private static final String BITVEC_CONST_PATTERN = "bv\\d+";
	private final boolean mCongruenceBasedTransformation;
	private final ManagedScript mMgdScript;
	private final TermVariable[] mFreeVars;
	private final TranslationConstrainer mTc;

	private final LinkedHashMap<Term, Term> mVariableMap; // Maps BV Var to Integer Var
	private final LinkedHashMap<Term, Term> mReversedVarMap;
	public final LinkedHashMap<Term, Term> mArraySelectConstraintMap;
	private final Set<TermVariable> mOverapproxVariables;
	private boolean mIsOverapproximation;

	/*
	 * Translates a formula over bit-vector to a formula over integers. Can translate arrays and quantifiers.
	 *
	 */
	public BvToIntTranslation(final ManagedScript mgdscript, final LinkedHashMap<Term, Term> variableMap,
			final TranslationConstrainer tc, final TermVariable[] freeVars,
			final boolean useCongruenceBasedTransformation) {

		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();

		mCongruenceBasedTransformation = useCongruenceBasedTransformation;

		mFreeVars = freeVars;
		if (variableMap != null) {
			mVariableMap = variableMap;
		} else {
			mVariableMap = new LinkedHashMap<>();
		}

		mReversedVarMap = new LinkedHashMap<>();
		mArraySelectConstraintMap = new LinkedHashMap<>();
		mOverapproxVariables = new HashSet<>();
		mIsOverapproximation = false;
		mTc = tc;
	}

	@Override
	public void convert(final Term term) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (term instanceof TermVariable) {
			for (final TermVariable variable : mFreeVars) {
				if (term == variable && SmtSortUtils.isBitvecSort(term.getSort())) {
					final Term intVar = translateVars(term, true);
					assert (SmtSortUtils.isIntSort(intVar.getSort()));
					mTc.varConstraint(term, intVar); // Create and Collect Constraints
					setResult(intVar);
					return;
				}
			}
			setResult(translateVars(term, true));
			return;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;

			final FunctionSymbol fsym = appTerm.getFunction();
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					final Term intVar = translateVars(term, true);
					if (SmtSortUtils.isBitvecSort(term.getSort())) {
						mTc.varConstraint(term, intVar); // Create and Collect Constraints
					}
					setResult(intVar);
					return;
				}
			}
			// NONE Overapproximation
			if (mTc.mMode.equals(ConstraintsForBitwiseOperations.NONE) && overaproxWithVars(appTerm)) {
				final Sort newSort = translateSort(mScript, appTerm.getSort());
				final TermVariable overaproxVar = mMgdScript.constructFreshTermVariable("overaproxVar", newSort);
				mOverapproxVariables.add(overaproxVar);
				mIsOverapproximation = true;
				setResult(overaproxVar);
				return;
			}

			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvor": {
					// bvor = bvsub(bvadd, bvand)
					final Term bvor = BitvectorUtils.unfTerm(mScript, "bvsub", null,
							BitvectorUtils.unfTerm(mScript, "bvadd", null, appTerm.getParameters()),
							BitvectorUtils.unfTerm(mScript, "bvand", null,
									appTerm.getParameters()));
					pushTerm(bvor);
					return;
				}
				case "bvxor": {
					final Term bvxor = BitvectorUtils.unfTerm(mScript, "bvsub", null,
							BitvectorUtils.unfTerm(mScript, "bvsub", null,
									BitvectorUtils.unfTerm(mScript, "bvadd", null,
											appTerm.getParameters()),
									BitvectorUtils.unfTerm(mScript, "bvand", null,
											appTerm.getParameters())),
							BitvectorUtils.unfTerm(mScript, "bvand", null,
									appTerm.getParameters()));

					pushTerm(bvxor);
					return;
				}
				case "bvashr": {
					pushTerm(bvashrAbbriviation(appTerm));
					return;
				}
				case "sign_extend": {
					pushTerm(signextendAbbriviation(appTerm));
					return;
				}
				case "bvsrem": {
					pushTerm(bvsremAbbriviation(appTerm));
					return;
				}

				case "bvsdiv": {
					pushTerm(bvsdivAbbriviation(appTerm));
					return;
				}
				}
			}
		} else if (term instanceof ConstantTerm) {
			if (SmtSortUtils.isBitvecSort(term.getSort())) {
				final ConstantTerm constTerm = (ConstantTerm) term;
				assert isBitVecSort(constTerm.getSort());
				BigInteger constValue;
				if (constTerm.getValue() instanceof String) {
					String bitString = (String) constTerm.getValue();
					if (bitString.startsWith("#b")) {
						bitString = (String) constTerm.getValue();
						constValue = new BigInteger(bitString.substring(2), 2);
					} else if (bitString.startsWith("#x")) {
						constValue = new BigInteger(bitString.substring(2), 16);
					} else {
						throw new UnsupportedOperationException("Unexpected constant type");
					}
				} else {
					constValue = (BigInteger) constTerm.getValue();
				}
				final Term intConst =
						SmtUtils.rational2Term(mScript, Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else {
				throw new UnsupportedOperationException("unexpected constant sort");
			}
		}
		super.convert(term);

	}

	private Term bvashrAbbriviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term zeroVec = SmtUtils.rational2Term(mScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mScript, 1));
		final Term extract =
				BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[0]);

		final Term ifTerm = SmtUtils.binaryEquality(mScript, extract, zeroVec);

		final Term thenTerm =
				BitvectorUtils.unfTerm(mScript, "bvlshr", null, appTerm.getParameters());

		final Term elseTerm = BitvectorUtils.unfTerm(mScript, "bvnot", null,
				BitvectorUtils.unfTerm(mScript, "bvlshr", null,
						BitvectorUtils.unfTerm(mScript, "bvnot", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));

		final Term ite = SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
		return ite;
	}

	private Term signextendAbbriviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);

		Term repeat = appTerm.getParameters()[0];
		final int difference = Integer.valueOf(appTerm.getSort().getIndices()[0])
				- Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]);
		for (int i = 0; i < difference; i++) {
			repeat = BitvectorUtils.unfTerm(mScript, "concat", null,
					BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[0]),
					repeat);
		}
		return repeat;
	}

	/*
	 * This method gets as input an application term with function symbol bvsrem and returns the definition of bvsrem.
	 */
	private Term bvsremAbbriviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs =
				BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[0]);
		final Term msbRhs =
				BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[1]);

		final Term zeroVec = SmtUtils.rational2Term(mScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mScript, 1));
		final Term oneVec = SmtUtils.rational2Term(mScript, Rational.ONE, SmtSortUtils.getBitvectorSort(mScript, 1));
		final Term ifterm1 = SmtUtils.and(mScript, SmtUtils.equality(mScript, zeroVec, msbLhs),
				SmtUtils.equality(mScript, zeroVec, msbRhs));
		final Term ifterm2 = SmtUtils.and(mScript, SmtUtils.equality(mScript, oneVec, msbLhs),
				SmtUtils.equality(mScript, zeroVec, msbRhs));
		final Term ifterm3 = SmtUtils.and(mScript, SmtUtils.equality(mScript, zeroVec, msbLhs),
				SmtUtils.equality(mScript, oneVec, msbRhs));

		final Term bvurem =
				BitvectorUtils.unfTerm(mScript, "bvurem", null, appTerm.getParameters());
		final Term thenTerm2 = BitvectorUtils.unfTerm(mScript, "bvneg", null,
				BitvectorUtils.unfTerm(mScript, "bvurem", null,
						BitvectorUtils.unfTerm(mScript, "bvneg", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));
		final Term thenTerm3 = BitvectorUtils.unfTerm(mScript, "bvneg", null,
				BitvectorUtils.unfTerm(mScript, "bvurem", null, appTerm.getParameters()[0],
						BitvectorUtils.unfTerm(mScript, "bvneg", null,
								appTerm.getParameters()[1])));

		final Term elseTerm = BitvectorUtils.unfTerm(mScript, "bvneg", null,
				BitvectorUtils.unfTerm(mScript, "bvurem", null,
						BitvectorUtils.unfTerm(mScript, "bvneg", null, appTerm.getParameters()[0]),
						BitvectorUtils.unfTerm(mScript, "bvneg", null,
								appTerm.getParameters()[1])));

		final Term iteChain2 = SmtUtils.ite(mScript, ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = SmtUtils.ite(mScript, ifterm2, thenTerm2, iteChain2);
		final Term bvsrem = SmtUtils.ite(mScript, ifterm1, bvurem, iteChain1);
		return bvsrem;

	}

	/*
	 * This method gets as input an application term with function symbol bvsdiv and returns the definition of bvsdiv.
	 */
	private Term bvsdivAbbriviation(final ApplicationTerm appTerm) {
		final BigInteger[] indices = new BigInteger[2];
		indices[0] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		indices[1] = BigInteger.valueOf(Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]) - 1);
		final Term msbLhs =
				BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[0]);
		final Term msbRhs =
				BitvectorUtils.unfTerm(mScript, "extract", indices, appTerm.getParameters()[1]);

		final Term zeroVec = SmtUtils.rational2Term(mScript, Rational.ZERO, SmtSortUtils.getBitvectorSort(mScript, 1));
		final Term oneVec = SmtUtils.rational2Term(mScript, Rational.ONE, SmtSortUtils.getBitvectorSort(mScript, 1));
		final Term ifterm1 = SmtUtils.and(mScript, SmtUtils.equality(mScript, zeroVec, msbLhs),
				SmtUtils.equality(mScript, zeroVec, msbRhs));
		final Term ifterm2 = SmtUtils.and(mScript, SmtUtils.equality(mScript, oneVec, msbLhs),
				SmtUtils.equality(mScript, zeroVec, msbRhs));
		final Term ifterm3 = SmtUtils.and(mScript, SmtUtils.equality(mScript, zeroVec, msbLhs),
				SmtUtils.equality(mScript, oneVec, msbRhs));

		final Term bvudiv =
				BitvectorUtils.unfTerm(mScript, "bvudiv", null, appTerm.getParameters());
		final Term thenTerm2 = BitvectorUtils.unfTerm(mScript, "bvneg", null,
				BitvectorUtils.unfTerm(mScript, "bvudiv", null,
						BitvectorUtils.unfTerm(mScript, "bvneg", null, appTerm.getParameters()[0]),
						appTerm.getParameters()[1]));
		final Term thenTerm3 = BitvectorUtils.unfTerm(mScript, "bvneg", null,
				BitvectorUtils.unfTerm(mScript, "bvudiv", null, appTerm.getParameters()[0],
						BitvectorUtils.unfTerm(mScript, "bvneg", null,
								appTerm.getParameters()[1])));

		final Term elseTerm = BitvectorUtils.unfTerm(mScript, "bvudiv", null,
				BitvectorUtils.unfTerm(mScript, "bvneg", null, appTerm.getParameters()[0]),
				BitvectorUtils.unfTerm(mScript, "bvneg", null, appTerm.getParameters()[1]));

		final Term iteChain2 = SmtUtils.ite(mScript, ifterm3, thenTerm3, elseTerm);
		final Term iteChain1 = SmtUtils.ite(mScript, ifterm2, thenTerm2, iteChain2);
		final Term bvsdiv = SmtUtils.ite(mScript, ifterm1, bvudiv, iteChain1);

		return bvsdiv;
	}

	/*
	 * translate variables and uninterpreted constants of bit-vector sort or array sort adds bv and int variable to
	 * mVariableMap and mReversedVarMap returns the new variable (translation results)
	 */
	private Term translateVars(final Term term, final boolean addToVarMap) {
		if (mVariableMap.containsKey(term)) {
			mReversedVarMap.put(mVariableMap.get(term), term);
			return mVariableMap.get(term);
		} else {
			final Sort sort = term.getSort();
			if (SmtSortUtils.isArraySort(sort)) {
				Term arrayVar;
				arrayVar = mMgdScript.constructFreshTermVariable("arrayVar", IntBlastingWrapper.translateSort(mMgdScript.getScript(), sort));
				if (!(term instanceof TermVariable)) {
					arrayVar = SmtUtils.termVariable2constant(mScript, (TermVariable) arrayVar, true);
				}
				if (addToVarMap) {
					mVariableMap.put(term, arrayVar);
					mReversedVarMap.put(arrayVar, term);
				}
				return arrayVar;
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				Term intVar;
				intVar = mMgdScript.constructFreshTermVariable("intVar", SmtSortUtils.getIntSort(mScript));
				if (!(term instanceof TermVariable)) {
					intVar = SmtUtils.termVariable2constant(mScript, (TermVariable) intVar, true);
				}
				if (addToVarMap) {
					mVariableMap.put(term, intVar);
					mReversedVarMap.put(intVar, term);
				}
				return intVar;
			} else {
				return term;
			}

		}

	}

	/*
	 * translates quantified formulas, adds constraints for translated quantified variables in their scope
	 */
	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final HashSet<TermVariable> newTermVars = new HashSet();
		final HashSet<Term> tvConstraints = new HashSet();
		if (newBody != old.getSubformula()) {
			for (int i = 0; i < old.getVariables().length; i++) {
				if (SmtSortUtils.isBitvecSort(old.getVariables()[i].getSort())) {
					newTermVars.add((TermVariable) mVariableMap.get(old.getVariables()[i]));

						tvConstraints.add(
								mTc.getTvConstraint(old.getVariables()[i], mVariableMap.get(old.getVariables()[i])));

				} else if (SmtSortUtils.isArraySort(old.getVariables()[i].getSort())) {
					final Term newQuantifiedVar = mVariableMap.get(old.getVariables()[i]);
					newTermVars.add((TermVariable) newQuantifiedVar);

					final Term arrayConstraint = mArraySelectConstraintMap.get(newQuantifiedVar);
					if (arrayConstraint != null) {
						tvConstraints.add(arrayConstraint);
					}

					mArraySelectConstraintMap.remove(newQuantifiedVar);
				} else {
					newTermVars.add(old.getVariables()[i]);
				}
			}

			setResult(SmtUtils.quantifier(mScript, old.getQuantifier(), newTermVars,
					QuantifierUtils.applyDualFiniteConnective(mScript, old.getQuantifier(), newBody, QuantifierUtils
							.negateIfUniversal(mScript, old.getQuantifier(), SmtUtils.and(mScript, tvConstraints)))));
			return;
		} else {
			super.postConvertQuantifier(old, newBody);
		}
	}

	private boolean overaproxWithVars(final ApplicationTerm appTerm) {
		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "bvand":
			case "bvor":
			case "bvxor":
			case "bvashr":
			case "bvshl":
			case "bvlshr": {
				return true;
			}
			default: {
				// not a bit-wise function symbol
				return false;
			}
			}
		}
		return false;
	}

	/*
	 * TODO more modular
	 */
	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "and":
			case "or":
			case "not":
			case "=>":
			case "store":
				setResult(mScript.term(fsym.getName(), args));
				return;
			case "select": {
				// select terms can act as variables
				if (SmtSortUtils.isBitvecSort(appTerm.getSort())) {
					mArraySelectConstraintMap.put(args[0],
							mTc.getSelectConstraint(appTerm, mScript.term(fsym.getName(), args)));
				}
				setResult(mScript.term(fsym.getName(), args));
				return;
			}
			}
		}

		if (appTerm.getParameters().length == 0) {
			if (fsym.getName().matches(BITVEC_CONST_PATTERN)) {
				final BigInteger constValue = new BigInteger(fsym.getName().substring(2));
				final Term intConst =
						SmtUtils.rational2Term(mScript, Rational.valueOf(constValue, BigInteger.ONE), intSort);

				setResult(intConst);
				return;
			} else if (SmtUtils.isFalseLiteral(appTerm)) {
				setResult(appTerm);
				return;
			} else if (SmtUtils.isTrueLiteral(appTerm)) {
				setResult(appTerm);
				return;
			} else {
				setResult(mVariableMap.get(appTerm));
				return;
			}
		} else if (appTerm.getParameters().length == 1
				&& SmtSortUtils.isBitvecSort(appTerm.getParameters()[0].getSort())) {
			// width of the first argument
			final int width = Integer.valueOf(appTerm.getParameters()[0].getSort().getIndices()[0]);
			// maximal representable number by a bit-vector of width "width" plus one
			final Term maxNumberPlusOne =
					SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);

			final Term translatedLHS = args[0];
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "bvnot": {
					final Term not = SmtUtils.unfTerm(mScript, "-", null,
							SmtSortUtils.getIntSort(mMgdScript), maxNumberPlusOne,
							SmtUtils.unfTerm(mScript, "+", null,
									SmtSortUtils.getIntSort(mMgdScript), translatedLHS,
									SmtUtils.rational2Term(mScript, Rational.ONE, intSort)));

					setResult(not);
					return;
				}
				case "bvneg": {
					final Term negation = SmtUtils.unfTerm(mScript, "-", null,
							SmtSortUtils.getIntSort(mMgdScript), maxNumberPlusOne, translatedLHS);
					if (mCongruenceBasedTransformation) {
						setResult(negation);
						return;
					}
					setResult(SmtUtils.mod(mScript, negation, maxNumberPlusOne));
					return;
				}
				case "extract": {
					if (mCongruenceBasedTransformation) {
						// TODO not sure if we need to do sth here
					}

					setResult(translateExtract(appTerm, translatedLHS));
					return;
				}
				case "zero_extend":
					setResult(args[0]);
					return;
				case "const":
					setResult(mScript.term("const", null, IntBlastingWrapper.translateSort(mMgdScript.getScript(), appTerm.getSort()), args));
					return;
				case "repeat":
				case "rotate_left":
				case "rotate_right":
				default:
					throw new UnsupportedOperationException("unexpected function: " + fsym.getName());
				}
			}
		} else {
			int width = 0;
			if (SmtSortUtils.isBitvecSort(appTerm.getParameters()[0].getSort())) {
				width = Integer.valueOf(appTerm.getParameters()[1].getSort().getIndices()[0]);
			}
			final Term maxNumber =
					SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(width), BigInteger.ONE), intSort);
			final Term[] translatedArgs = args;
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "distinct":
				case "bvult":
				case "bvule":
				case "bvugt":
				case "bvuge":
				case "bvslt":
				case "bvsle":
				case "bvsgt":
				case "bvsge": {
					setResult(translateRelations(fsym, args, maxNumber, width));
					return;
				}
				case "bvadd": {
					final Term addition = SmtUtils.unfTerm(mScript, "+", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					if (mCongruenceBasedTransformation) {
						setResult(addition);
						return;
					}
					setResult(SmtUtils.mod(mScript, addition, maxNumber));
					return;
				}
				case "bvsub": {
					final Term substraction = SmtUtils.unfTerm(mScript, "-", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					if (mCongruenceBasedTransformation) {
						setResult(substraction);
						return;
					}
					setResult(SmtUtils.mod(mScript, substraction, maxNumber));
					return;
				}
				case "bvmul": {
					final Term multiplication = SmtUtils.unfTerm(mScript, "*", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedArgs);
					if (mCongruenceBasedTransformation) {
						setResult(multiplication);
						return;
					}
					setResult(SmtUtils.mod(mScript, multiplication, maxNumber));
					return;
				}
				case "ite": {
					setResult(SmtUtils.ite(mScript, args[0], args[1], args[2]));
					return;
				}
				}

				if (appTerm.getParameters().length == 2) {
					final Term translatedLHS = translatedArgs[0];
					final Term translatedRHS = translatedArgs[1];
					switch (fsym.getName()) {
					case "bvshl": {
						setResult(translateBvshl(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}
					case "bvlshr": {
						setResult(translateBvlshr(translatedLHS, translatedRHS, width, maxNumber));
						return;
					}

					case "bvashr": {
						throw new UnsupportedOperationException(fsym.getName());
					}
					case "concat": {
						final Term multiplication = SmtUtils.unfTerm(mScript, "*", null,
								SmtSortUtils.getIntSort(mMgdScript), translatedLHS, maxNumber);
						if (mCongruenceBasedTransformation) {
							// TODO not sure if we need to do sth here
						}
						setResult(SmtUtils.unfTerm(mScript, "+", null,
								SmtSortUtils.getIntSort(mMgdScript), multiplication, translatedRHS));
						return;
					}

					case "bvudiv": {
						setResult(translateBvudiv(translatedLHS, translatedRHS, maxNumber));
						return;
					}

					case "bvurem": {
						setResult(translateBvurem(translatedLHS, translatedRHS, maxNumber));
						return;
					}
					case "bvand": {
						final Term intAnd =
								mScript.term(mTc.getIntAndFunctionSymbol().getName(), translatedLHS, translatedRHS);
						final boolean constraintsOverapproximate = mTc.bvandConstraint(intAnd, width);
						if (constraintsOverapproximate) {
							mIsOverapproximation = true;
						}
						setResult(intAnd);
						return;
					}

					}
				}
			}

		}
		super.convertApplicationTerm(appTerm, args);
	}

	private Term translateExtract(final ApplicationTerm appTerm, final Term translatedLHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final int lowerIndex = Integer.parseInt(appTerm.getFunction().getIndices()[1]);
		final int upperIndex = Integer.parseInt(appTerm.getFunction().getIndices()[0]);

		final Term divby =
				SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(lowerIndex), BigInteger.ONE), intSort);
		final Term modby = SmtUtils.rational2Term(mScript,
				Rational.valueOf(two.pow(upperIndex - lowerIndex + 1), BigInteger.ONE), intSort);
		return SmtUtils.mod(mScript,
				SmtUtils.unfTerm(mScript, "div", null, SmtSortUtils.getIntSort(mMgdScript),
						translatedLHS, divby),
				modby);
	}

	private Term translateBvudiv(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		Term rhs;
		Term lhs;
		if (mCongruenceBasedTransformation) {
			rhs = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			lhs = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}
		final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null,
				SmtSortUtils.getIntSort(mMgdScript), rhs, SmtUtils.rational2Term(mScript, Rational.ZERO, intSort));
		final Term thenTerm = SmtUtils.unfTerm(mScript, "-", null,
				SmtSortUtils.getIntSort(mMgdScript), maxNumber, SmtUtils.rational2Term(mScript, Rational.ONE, intSort));
		final Term elseTerm = SmtUtils.unfTerm(mScript, "div", null,
				SmtSortUtils.getIntSort(mMgdScript), lhs, rhs);
		return SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvurem(final Term translatedLHS, final Term translatedRHS, final Term maxNumber) {
		Term rhs;
		Term lhs;
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (mCongruenceBasedTransformation) {
			rhs = SmtUtils.mod(mScript, translatedRHS, maxNumber);
			lhs = SmtUtils.mod(mScript, translatedLHS, maxNumber);
		} else {
			rhs = translatedRHS;
			lhs = translatedLHS;
		}
		final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript), rhs,
				SmtUtils.rational2Term(mScript, Rational.ZERO, intSort));
		final Term thenTerm = translatedLHS; //Congruence Based doesnt need mod here.
		final Term elseTerm = SmtUtils.mod(mScript, lhs, rhs);
		return SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
	}

	private Term translateBvshl(final Term translatedLHS, final Term translatedRHS, final int width,
			final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = SmtUtils.unfTerm(mScript, "*", null,
					SmtSortUtils.getIntSort(mMgdScript), translatedLHS, pow2(translatedRHS));
			return SmtUtils.mod(mScript, shift, maxNumber);
		} else {
			Term iteChain = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = SmtUtils.rational2Term(mScript, Rational.valueOf(0, 1), intSort);
					iteChain = SmtUtils.ite(mScript, SmtUtils.binaryEquality(mScript, constInt, translatedRHS),
							translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedRHS,
							SmtUtils.rational2Term(mScript, powResult, intSort));
					final int pow = (int) Math.pow(2, i);
					final Term thenTerm = SmtUtils.mod(mScript, SmtUtils.unfTerm(mScript, "*", null,
									SmtSortUtils.getIntSort(mMgdScript),
									SmtUtils.rational2Term(mScript, Rational.valueOf(pow, 1), intSort), translatedLHS),
							maxNumber);
					iteChain = SmtUtils.ite(mScript, ifTerm, thenTerm, iteChain);
				}
			}
			return iteChain;
		}
	}

	private Term translateBvlshr(final Term translatedLHS, final Term translatedRHS, final int width,
			final Term maxNumber) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (translatedRHS instanceof ConstantTerm) {
			final Term shift = SmtUtils.unfTerm(mScript, "div", null,
					SmtSortUtils.getIntSort(mMgdScript), translatedLHS, pow2(translatedRHS));
			return shift;
		} else {
			Term iteChain = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			for (int i = width - 1; i >= 0; i--) {
				if (i == 0) {
					final Term constInt = SmtUtils.rational2Term(mScript, Rational.valueOf(0, 1), intSort);
					iteChain = SmtUtils.ite(mScript,
							SmtUtils.unfTerm(mScript, "=", null,
									SmtSortUtils.getIntSort(mMgdScript), constInt, translatedRHS),
							translatedLHS, iteChain);
				} else {
					final Rational powResult = Rational.valueOf(i, 1);
					final Term ifTerm = SmtUtils.unfTerm(mScript, "=", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedRHS,
							SmtUtils.rational2Term(mScript, powResult, intSort));
					final int pow = (int) Math.pow(2, i);
					final Term thenTerm = SmtUtils.unfTerm(mScript, "div", null,
							SmtSortUtils.getIntSort(mMgdScript), translatedLHS,
							SmtUtils.rational2Term(mScript, Rational.valueOf(pow, 1), intSort));
					iteChain = SmtUtils.ite(mScript, ifTerm, thenTerm, iteChain);
				}
			}
			return iteChain;
		}
	}

	private Term translateRelations(final FunctionSymbol fsym, final Term[] args, final Term maxNumberPlusOne,
			final int width) {
		Term[] translatedArgs = new Term[args.length];
		final Term[] utsArgs = args;
		translatedArgs = args;

		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=": {
				if (mCongruenceBasedTransformation && SmtSortUtils.isNumericSort(args[0].getSort())) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.unfTerm(mScript, "=", null, SmtSortUtils.getIntSort(mMgdScript),
						translatedArgs);
			}
			case "distinct": {
				if (mCongruenceBasedTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);

					}
				}
				return SmtUtils.unfTerm(mScript, "distinct", null,
						SmtSortUtils.getIntSort(mMgdScript), translatedArgs);

			}
			case "bvult": {
				if (mCongruenceBasedTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);

					}
				}
				return SmtUtils.less(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvule": {
				if (mCongruenceBasedTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.leq(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvugt": {
				if (mCongruenceBasedTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.greater(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvuge": {
				if (mCongruenceBasedTransformation) {
					for (int i = 0; i < args.length; i++) {
						translatedArgs[i] = SmtUtils.mod(mScript, args[i], maxNumberPlusOne);
					}
				}
				return SmtUtils.geq(mScript, translatedArgs[0], translatedArgs[1]);

			}
			case "bvslt": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i]);
				}

				return SmtUtils.less(mScript, utsArgs[0], utsArgs[1]);
			}
			case "bvsle": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i]);
				}
				return SmtUtils.leq(mScript, utsArgs[0], utsArgs[1]);

			}
			case "bvsgt": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i]);
				}
				return SmtUtils.greater(mScript, utsArgs[0], utsArgs[1]);
			}
			case "bvsge": {
				for (int i = 0; i < args.length; i++) {
					utsArgs[i] = uts(width, args[i]);
				}
				return SmtUtils.geq(mScript, utsArgs[0], utsArgs[1]);

			}
			}
		}
		throw new UnsupportedOperationException("unexpected relation");
	}

	// unsigned to signed for relations
	private final Term uts(final int width, final Term term) {
		// 2 * (x mod 2^(k - 1) ) - x
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final Term two =
				SmtUtils.rational2Term(mScript, Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowWidth = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(width - 1), BigInteger.ONE), intSort);

		if (mCongruenceBasedTransformation) {
			final Term congruencePow = SmtUtils.rational2Term(mScript,
					Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE), intSort);
			final Term modulo = SmtUtils.mod(mScript, SmtUtils.mod(mScript, term, congruencePow), twoPowWidth);

			return SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
					SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), two, modulo),
					SmtUtils.mod(mScript, term, congruencePow));
		} else {
			final Term modulo = SmtUtils.mod(mScript, term, twoPowWidth);
			return SmtUtils.unfTerm(mScript, "-", null, SmtSortUtils.getIntSort(mMgdScript),
					SmtUtils.unfTerm(mScript, "*", null, SmtSortUtils.getIntSort(mMgdScript), two, modulo), term);
		}

	}

	// calculates power of two if exponent is a constant, otherwise this is not implemented in the SMT integer theory
	private Term pow2(final Term term) {
		assert term.getSort().isNumericSort();
		if (term instanceof ConstantTerm) {
			final Sort intSort = SmtSortUtils.getIntSort(mScript);
			final ConstantTerm constTerm = (ConstantTerm) term;
			final Term twoPow;
			if (constTerm.getValue() instanceof Rational) {
				final Rational ratint = (Rational) constTerm.getValue();
				twoPow = SmtUtils.rational2Term(mScript,
						Rational.valueOf(BigInteger.valueOf(2).pow(ratint.numerator().intValue()), BigInteger.ONE),
						intSort);
			} else {
				final BigInteger bigint = (BigInteger) constTerm.getValue();
				twoPow = SmtUtils.rational2Term(mScript,
						Rational.valueOf(BigInteger.valueOf(2).pow(bigint.intValue()), BigInteger.ONE), intSort);
			}
			return twoPow;
		}
		throw new UnsupportedOperationException("function pow2 not implemented");
		// return term;
	}

	private boolean isBitVecSort(final Sort sort) {
		if (sort.getName().equals("BitVec")) {
			return true;
		}
		return false;
	}

	private Sort translateSort(final Script script, final Sort sort) {
		final Sort result;
		if (isBitVecSort(sort)) {
			result = SmtSortUtils.getIntSort(script);
		} else if (SmtSortUtils.isArraySort(sort)) {
			result = IntBlastingWrapper.translateSort(mMgdScript.getScript(), sort);
		} else {
			throw new UnsupportedOperationException("Unsupported sort: " + sort);
		}
		return result;
	}

	public LinkedHashMap<Term, Term> getVarMap() {
		return mVariableMap;
	}

	public LinkedHashMap<Term, Term> getReversedVarMap() {
		return mReversedVarMap;
	}

	public Set<TermVariable> getOverapproxVariables() {
		return mOverapproxVariables;
	}

	public boolean wasOverapproximation() {
		return mIsOverapproximation;
	}
}
