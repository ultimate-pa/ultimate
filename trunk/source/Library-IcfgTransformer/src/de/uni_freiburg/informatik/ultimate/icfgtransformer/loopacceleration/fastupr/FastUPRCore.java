/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonDetector;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.ParametricOctMatrix;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("unused")
public class FastUPRCore<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final Term mRelation;
	private final UnmodifiableTransFormula mFormula;
	private UnmodifiableTransFormula mResult;
	private final ILogger mLogger;
	private final FastUPRUtils mUtils;
	private final ILocationFactory<INLOC, OUTLOC> mReplacementVarFactory;

	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final OctagonTransformer mOctagonTransformer;
	private final OctagonDetector mOctagonDetector;
	private final OctagonCalculator mOctagonCalculator;
	private OctagonConjunction mConjunc;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private ArrayList<TermVariable> mVariables;
	private final TermChecker mTermChecker;
	private final FastUPRFormulaBuilder mFormulaBuilder;

	public FastUPRCore(UnmodifiableTransFormula formula, ILocationFactory<INLOC, OUTLOC> factory,
			ManagedScript managedScript, ILogger logger, IUltimateServiceProvider services) throws Exception {
		mLogger = logger;
		mServices = services;
		mManagedScript = managedScript;
		mReplacementVarFactory = factory;
		mUtils = new FastUPRUtils(logger, false);
		mUtils.output("==================================================");
		mUtils.output("== FAST UPR CORE ==");
		mUtils.output("==================================================");
		mFormula = formula;
		mRelation = formula.getFormula();

		for (final IProgramVar p : mFormula.getInVars().keySet()) {
			mUtils.debug(p.toString());
			mUtils.debug(p.getTermVariable().toString());
		}

		mOctagonDetector = new OctagonDetector(mUtils, managedScript, services);
		mOctagonTransformer = new OctagonTransformer(mUtils, managedScript, mOctagonDetector);
		mOctagonCalculator = new OctagonCalculator(mUtils, managedScript);
		mFormulaBuilder = new FastUPRFormulaBuilder(mUtils, mManagedScript);
		mTermChecker = new TermChecker(mUtils, mManagedScript, mOctagonCalculator, mFormulaBuilder);

		mUtils.output("Formula:" + mFormula.toString());

		mInVars = new HashMap<>(mFormula.getInVars());
		mOutVars = new HashMap<>(mFormula.getOutVars());

		mVariables = new ArrayList<>();

		// mUtils.debug(mUtils.composition(mServices, mManagedScript, mFormula,
		// 3).getFormula().toString());

		// TODO: REMOVE
		final boolean skip = true;

		if (isOctagon(mRelation, managedScript.getScript())) {
			mConjunc = mOctagonTransformer.transform(mRelation);
			mUtils.output(">> IS OCTAGON: STARTING PREFIX LOOP");
			mUtils.output("Conjunction: " + mConjunc.toString());

			mConjunc = mOctagonCalculator.normalizeVarNames(mConjunc, mInVars, mOutVars);

			mConjunc = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, 10);

			mVariables = mOctagonCalculator.getSortedVariables(mInVars, mOutVars);

			mTermChecker.setConjunction(mConjunc, mInVars, mOutVars);

			prefixLoop();

		} else {
			// TODO :
		}

	}

	private void prefixLoop() {
		int b = 0;
		while (!periodLoop(b++)) {
			// TODO remove
			if (b > 100)
				return;
		}
	}

	private boolean periodLoop(int b) {
		for (int c = 1; c <= b; c++) {
			mUtils.output(">> Checking Consistency for b=" + b + ", c=" + c);
			mUtils.setDetailed(true);
			final int k = mTermChecker.checkConsistency(b, c);
			if (k >= 0) {
				mUtils.output(">> NOT CONSISTENT FOR 2 ITERATIONS: RETURNING COMPOSITION RESULT");
				mResult = mFormulaBuilder.buildConsistencyFormula(mConjunc, k * c + b - 1, mInVars, mOutVars);
				return true;
			} else {
				mUtils.output(">> CONSISTENT: CHECKING FOR PERIODICITY");
				mUtils.setDetailed(false);
				final ParametricOctMatrix difference = periodCheck(b, c);

				// TODO REMOVE && true

				if (difference != null) {
					if (checkForAll(difference, b, c)) {
						mResult = paramatericSolution();
					}
				}

				throw new IllegalArgumentException();

			}

		}
		return false;
	}

	private UnmodifiableTransFormula paramatericSolution() {
		// TODO Auto-generated method stub
		return null;
	}

	private ParametricOctMatrix periodCheck(int b, int c) {
		// Check if difference between R^(c+b) and R^(b) is equal to difference
		// between R^(2c+b) and R^(c+b)

		// Prepare conjunctions for c0 = R^(b), c1 = R^(c+b), c2 = R^(2c+b)

		mUtils.output(">>> PERIOD CHECK");

		final OctagonConjunction c0 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
		final OctagonConjunction c1 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b + c);
		final OctagonConjunction c2 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b + 2 * c);

		mUtils.debug(c0.toString());
		mUtils.debug(c1.toString());
		mUtils.debug(c2.toString());

		// Convert conjunctions to matrices.

		final ParametricOctMatrix c0Matrix = mOctagonTransformer.getMatrix(c0, mVariables);
		final ParametricOctMatrix c1Matrix = mOctagonTransformer.getMatrix(c1, mVariables);
		final ParametricOctMatrix c2Matrix = mOctagonTransformer.getMatrix(c2, mVariables);

		mUtils.debug(c0Matrix.getMatrix().toString());
		mUtils.debug(c1Matrix.getMatrix().toString());
		mUtils.debug(c2Matrix.getMatrix().toString());

		// Calculate difference = c1-c0, difference2 = c2-c1

		final ParametricOctMatrix difference = c1Matrix.subtract(c0Matrix);
		final ParametricOctMatrix difference2 = c2Matrix.subtract(c1Matrix);

		mUtils.debug(difference.getMatrix().toString());
		mUtils.debug(difference2.getMatrix().toString());
		mUtils.debug(difference.toOctagonConjunction().toString());
		mUtils.debug(difference2.toOctagonConjunction().toString());

		// Check Equality

		if (difference.equals(difference2)) {
			mUtils.output("> Success!");
			return difference;
		}

		return null;
	}

	private boolean checkForAll(ParametricOctMatrix difference, int b, int c) {
		// if for all n>=0 : rho( n * difference + sigma(R^b))∘R^c
		// <=> rho((n+1) * difference + sigma(R^b))∘R^c <=/=> false

		mUtils.output(">>> FOR ALL CHECK, b=" + b + ",c=" + c);

		// PREPARATIONS

		final Script script = mManagedScript.getScript();
		final OctagonConjunction rB = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
		final OctagonConjunction rC = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, c);
		final ParametricOctMatrix rBMatrix = mOctagonTransformer.getMatrix(rB, mVariables);

		// n * difference, (n+1) * difference

		mUtils.debug("Creating Parametric Matrix differenceN.");
		final ParametricOctMatrix differenceN = difference.multiplyVar("n", mManagedScript);
		mUtils.debug(differenceN.toOctagonConjunction().toString());

		// Additions

		final ParametricOctMatrix intervalBeginningMatrix = differenceN.add(rBMatrix);
		final ParametricOctMatrix intervalEndMatrix = differenceN.add(rBMatrix);

		// Back to OctagonConjunction and concatinate with R^c

		final OctagonConjunction intervalBeginning = mOctagonCalculator
				.binarySequentialize(intervalBeginningMatrix.toOctagonConjunction(), rC, mInVars, mOutVars);
		final OctagonConjunction intervalEnd = mOctagonCalculator
				.binarySequentialize(intervalBeginningMatrix.toOctagonConjunction(1), rC, mInVars, mOutVars);

		// Equality Term (<=>)

		final Term eqTerm = script.term("=", intervalBeginning.toTerm(script), intervalEnd.toTerm(script));
		mUtils.debug("eqTerm: " + eqTerm.toString());

		// QuantifiedTerm (for all n >= 0)

		final Term quantTerm = script.quantifier(1, new TermVariable[] { differenceN.getParametricVar() }, eqTerm,
				null);
		mUtils.debug("quantTerm: " + eqTerm.toString());

		mTermChecker.checkTerm(quantTerm);

		return false;
	}

	private boolean isOctagon(Term relation, Script script) throws NotAffineException {

		// Convert Term to CNF

		final Term cnfRelation = SmtUtils.toCnf(mServices, mManagedScript, relation,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mUtils.output("CNF");
		mUtils.output(cnfRelation.toString());

		// Get all SubTerms seperated by conjunction.

		final HashSet<Term> subTerms = mOctagonDetector.getConjunctSubTerms(cnfRelation);
		mUtils.debug("Term count:" + subTerms.size());

		mOctagonDetector.clearChecked();

		for (Term t : subTerms) {

			// Get Term in positive Normal Form

			final AffineRelation affine = new AffineRelation(script, t);
			t = affine.positiveNormalForm(script);
			mUtils.debug("Term as Positive Normal Form:");
			mUtils.debug(t.toString());

			// Check if Term is a possible OctagonTerm
			// (is equal to a Term of the form: +-x +-y <= c)

			if (!mOctagonDetector.isOctagonTerm(t))
				return false;

		}
		return true;
	}

}
