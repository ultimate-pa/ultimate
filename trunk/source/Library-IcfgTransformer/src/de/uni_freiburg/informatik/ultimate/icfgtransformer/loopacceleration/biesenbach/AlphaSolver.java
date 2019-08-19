/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class AlphaSolver<INLOC extends IcfgLocation> {

	private final UnmodifiableTransFormula mOriginalTransFormula;
	private final ILogger mLogger;
	private final Map<Integer, Map<Term, Term>> mMatrix;
	private final Map<Integer, Map<Term, Term>> mLGS;
	private final IProgramVar[] mProgramVar;
	private final Script mScript;
	private final ManagedScript mMgScript;
	private List<Term> mVectorTerms;
	private Map<IProgramVar, TermVariable[]> mAlphaMap;
	private final TermVariable[] mAlphaN = new TermVariable[2];
	private final Map<Term, Term> mAlphaDefaultConstant = new HashMap<>();
	private TermVariable mNVar;
	private Term mFinalTerm;
	private Map<IProgramVar, Term> mValues = new HashMap<>();

	public AlphaSolver(final ILogger logger, final UnmodifiableTransFormula loopTransFormula, final ManagedScript script,
			final Map<Integer, Map<Term, Term>> matrix, final Map<Integer, Map<Term, Term>> lgs,
			final IUltimateServiceProvider service, int loopCounter) {
		mMgScript = script;
		mScript = mMgScript.getScript();

		mOriginalTransFormula = loopTransFormula;
		mLogger = logger;
		final Set<IProgramVar> programVar = mOriginalTransFormula.getAssignedVars();
		mProgramVar = programVar.toArray(new IProgramVar[programVar.size()]);
		mMatrix = matrix;
		mLGS = lgs;

		mMgScript.lock(this);

		initAlphas(loopCounter);

		final List<Term> finalTerms = new ArrayList<>();
		for (final IProgramVar pVar : mProgramVar) {
			mVectorTerms = new ArrayList<>();
			lgsTermN0(pVar);
			lgsTermN1(pVar);
			lgsTermN2(pVar);
			final Term lgsTerm = mScript.term("and", mVectorTerms.toArray(new Term[mVectorTerms.size()]));
			final Term pVarTerm = solveTerm(lgsTerm, pVar);
			finalTerms.add(pVarTerm);
		}
		if (finalTerms.isEmpty()) {
			mFinalTerm = null;
		} else if (finalTerms.size() == 1) {
			mFinalTerm = finalTerms.get(0);
		} else {
			mFinalTerm = mScript.term("and", finalTerms.toArray(new Term[finalTerms.size()]));
		}
		mMgScript.unlock(this);
	}

	private Term solveTerm(final Term term, final IProgramVar pVar) {
		final Substitution sub = new Substitution(mMgScript, mAlphaDefaultConstant);
		final Term transformedTerm = sub.transform(term);
		mScript.push(1);
		final LBool result = checkSat(mScript, transformedTerm);
		Term finalTerm = null;
		
		try {
			if (result == LBool.SAT) {
				final Collection<Term> terms = mAlphaDefaultConstant.values();
				final Map<Term, Term> termvar2value = SmtUtils.getValues(mScript, terms);
				final Term zero = mScript.decimal("0.0");
				
				// v and v*n
				final List<Term> multiplication = new ArrayList<>();
				for (final IProgramVar pV : mProgramVar) {
					if (!termvar2value.get(mAlphaDefaultConstant.get(mAlphaMap.get(pV)[0])).equals(zero)) {
						multiplication.add(
								mScript.term("*", mScript.term("to_int", termvar2value.get(mAlphaDefaultConstant.get(mAlphaMap.get(pV)[0]))),
										mOriginalTransFormula.getInVars().get(pV)));
					}
					if (!termvar2value.get(mAlphaDefaultConstant.get(mAlphaMap.get(pV)[1])).equals(zero)) {
						multiplication.add(
								mScript.term("*", mScript.term("to_int", termvar2value.get(mAlphaDefaultConstant.get(mAlphaMap.get(pV)[1]))),
										mOriginalTransFormula.getInVars().get(pV), mNVar));
					}
				}
				final Term addition;
				//TODO multiplication.size() == 0
				if(multiplication.size() == 1){
					addition = multiplication.get(0);
				}else{
					addition = mScript.term("+", multiplication.toArray(new Term[multiplication.size()]));
				}
				// n and n*n
				final List<Term> multiplicationN = new ArrayList<>();
				if (!termvar2value.get(mAlphaDefaultConstant.get(mAlphaN[0])).equals(zero)) {
					multiplicationN
							.add(mScript.term("*", termvar2value.get(mAlphaDefaultConstant.get(mAlphaN[0])), mScript.term("to_real", mNVar)));
				}
				if (!termvar2value.get(mAlphaDefaultConstant.get(mAlphaN[1])).equals(zero)) {
					multiplicationN.add(
							mScript.term("*", termvar2value.get(mAlphaDefaultConstant.get(mAlphaN[1])), mScript.term("to_real", mNVar), mScript.term("to_real", mNVar)));
				}
				final Term additionN;
				//TODO multiplication.size() == 0
				if(multiplicationN.size() == 1){
					additionN = mScript.term("to_int", multiplicationN.get(0));
				}else{
					additionN = mScript.term("to_int", mScript.term("+", multiplicationN.toArray(new Term[multiplicationN.size()])));
				}
				finalTerm = mScript.term("=", mOriginalTransFormula.getOutVars().get(pVar), mScript.term("+", addition, additionN));
				mValues.put(pVar, mScript.term("+", addition, additionN));
			}
		} finally {
			mScript.pop(1);
		}
		return finalTerm;
	}
	
	public Map<IProgramVar, Term> getValues(){
		return mValues;
	}

	public Term getResult() {
		return mFinalTerm;
	}

	public TermVariable getN() {
		return mNVar;
	}

	private static LBool checkSat(final Script script, final Term term) {
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i = 0; i < vars.length; i++) {
			values[i] = termVariable2constant(script, vars[i]);
		}
		final Term newTerm = script.let(vars, values, term);
		LBool result = script.assertTerm(newTerm);
		if (result == LBool.UNKNOWN) {
			result = script.checkSat();
		}
		return result;
	}

	private static Term termVariable2constant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		script.declareFun(name, Script.EMPTY_SORT_ARRAY, tv.getSort());
		return script.term(name);
	}

	private void initAlphas(int loopCounter) {
		mAlphaMap = new HashMap<>();
		mNVar = mScript.variable("n", mScript.sort("Int"));
		for (final IProgramVar var : mProgramVar) {
			final TermVariable alphaVar = mScript.variable("alpha" + var.toString(), mScript.sort("Real"));
			final TermVariable alphaVarN =
					mScript.variable("alpha" + var.toString() + "n", mScript.sort("Real"));
			final TermVariable[] alphas = { alphaVar, alphaVarN };
			mAlphaMap.put(var, alphas);

			mAlphaDefaultConstant.put(alphaVar,
					ProgramVarUtils.constructDefaultConstant(mMgScript, this, alphaVar.getSort(), alphaVar.getName() + loopCounter));
			mAlphaDefaultConstant.put(alphaVarN, ProgramVarUtils.constructDefaultConstant(mMgScript, this,
					alphaVarN.getSort(), alphaVarN.getName() + loopCounter));
		}
		mAlphaN[0] = mScript.variable("alpha_n", mScript.sort("Real"));
		mAlphaN[1] = mScript.variable("alpha_nn", mScript.sort("Real"));
		mAlphaDefaultConstant.put(mAlphaN[0],
				ProgramVarUtils.constructDefaultConstant(mMgScript, this, mAlphaN[0].getSort(), mAlphaN[0].getName() + loopCounter));
		mAlphaDefaultConstant.put(mAlphaN[1],
				ProgramVarUtils.constructDefaultConstant(mMgScript, this, mAlphaN[1].getSort(), mAlphaN[1].getName() + loopCounter));
	}

	private void lgsTermN0(final IProgramVar var) {
		final Term one = mScript.decimal("1.0");
		final Term zero = mScript.decimal("0.0");
		for (final IProgramVar vari : mProgramVar) {
			if (vari == var) {
				mVectorTerms.add(mScript.term("=", mScript.term("*", one, mAlphaMap.get(vari)[0]), one));
			} else {
				mVectorTerms.add(mScript.term("=", mScript.term("*", one, mAlphaMap.get(vari)[0]), zero));
			}
		}
	}

	private void lgsTermN1(final IProgramVar var) {
		for (int i = 0; i < mMatrix.size() - 1; i++) {
			final Map<Term, Term> map = mMatrix.get(i);
			final List<Term> list = new ArrayList<>();
			for (final IProgramVar vari : mProgramVar) {
				list.add(mScript.term("*", mAlphaMap.get(vari)[0],
						mScript.term("to_real", map.get(mOriginalTransFormula.getInVars().get(vari)))));
				list.add(mScript.term("*", mAlphaMap.get(vari)[1],
						mScript.term("to_real", map.get(mOriginalTransFormula.getInVars().get(vari)))));
			}
			list.add(mAlphaN[0]);
			list.add(mAlphaN[1]);
			mVectorTerms.add(mScript.term("=", mScript.term("+", list.toArray(new Term[mProgramVar.length])),
					mScript.term("to_real", mLGS.get(i).get(mOriginalTransFormula.getOutVars().get(var)))));
		}
	}

	private void lgsTermN2(final IProgramVar var) {
		final int i = mMatrix.size() - 1;
		final Map<Term, Term> map = mMatrix.get(i);
		final List<Term> list = new ArrayList<>();
		for (final IProgramVar vari : mProgramVar) {
			list.add(mScript.term("*", mAlphaMap.get(vari)[0],
					mScript.term("to_real", map.get(mOriginalTransFormula.getInVars().get(vari)))));
			list.add(mScript.term("*", mAlphaMap.get(vari)[1],
					mScript.term("to_real", map.get(mOriginalTransFormula.getInVars().get(vari))),
					mScript.decimal("2.0")));
		}
		list.add(mScript.term("*", mAlphaN[0], mScript.decimal("2.0")));
		list.add(mScript.term("*", mAlphaN[1], mScript.decimal("4.0")));
		mVectorTerms.add(mScript.term("=", mScript.term("+", list.toArray(new Term[mProgramVar.length])),
				mScript.term("to_real", mLGS.get(i).get(mOriginalTransFormula.getOutVars().get(var)))));
	}
}