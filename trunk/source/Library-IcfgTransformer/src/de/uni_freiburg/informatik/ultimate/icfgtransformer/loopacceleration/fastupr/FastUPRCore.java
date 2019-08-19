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

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonDetector;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.ParametricOctMatrix;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * FastUPR Loop Acceleration - Main TransFormulaTranformation.
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRCore {

	private final Term mRelation;
	private final UnmodifiableTransFormula mFormula;
	private Term mResultTerm;
	private final FastUPRUtils mUtils;

	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final OctagonTransformer mOctagonTransformer;
	private final OctagonDetector mOctagonDetector;
	private final OctagonCalculator mOctagonCalculator;
	private OctConjunction mConjunc;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private List<TermVariable> mVariables;
	private final FastUPRTermChecker mTermChecker;
	private final FastUPRFormulaBuilder mFormulaBuilder;

	/**
	 * Constructor to transform a TransFormula via FastUPR Loop Acceleration.
	 *
	 * @param formula
	 *            The {@link UnmodifiableTransFormula} to be transformed.
	 * @param managedScript
	 *            The {@link ManagedScript} to use for {@link Term}
	 *            transformation.
	 * @param logger
	 *            The {@link ILogger} used for Debug Logging.
	 * @param services
	 *            An {IUlitmateServiceProvider}
	 * @throws NotAffineException
	 *             If the Formula is not an Octagon an Exception will be thrown.
	 */
	public FastUPRCore(final UnmodifiableTransFormula formula, final ManagedScript managedScript, final ILogger logger,
			final IUltimateServiceProvider services) throws NotAffineException {
		mServices = services;
		mManagedScript = managedScript;
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

		mOctagonDetector = new OctagonDetector(logger, managedScript, services);
		mOctagonTransformer = new OctagonTransformer(mUtils, managedScript.getScript(), mOctagonDetector);
		mOctagonCalculator = new OctagonCalculator(mUtils, managedScript);
		mFormulaBuilder = new FastUPRFormulaBuilder(mUtils, mManagedScript, mOctagonCalculator, mOctagonTransformer);
		mTermChecker = new FastUPRTermChecker(mUtils, mManagedScript, mOctagonCalculator, mFormulaBuilder, mServices);

		mUtils.output("Formula:" + mFormula.toString());

		mInVars = new HashMap<>(mFormula.getInVars());
		mOutVars = new HashMap<>(mFormula.getOutVars());

		mVariables = new ArrayList<>();

		if (mOctagonCalculator.isTrivial(mInVars, mOutVars)) {
			mUtils.output("Trivial TransFormula, loop does nothing.");
			mResultTerm = formula.getFormula();
		} else if (isOctagon(mRelation, managedScript.getScript())) {
			mConjunc = mOctagonTransformer.transform(mRelation);

			mConjunc = mOctagonCalculator.normalizeVarNames(mConjunc, mInVars, mOutVars);
			mUtils.debug(mConjunc.toString());
			mConjunc = mOctagonCalculator.removeInOutVars(mConjunc, mInVars, mOutVars);
			mUtils.debug(mConjunc.toString());

			mVariables = mOctagonCalculator.getSortedVariables(mInVars, mOutVars);

			mTermChecker.setConjunction(mConjunc, mInVars, mOutVars);

			mUtils.output(">> IS OCTAGON: STARTING PREFIX LOOP");
			mUtils.output("Conjunction: " + mConjunc.toString());

			prefixLoop();
		} else {
			mResultTerm = null;
		}

	}

	private void prefixLoop() {
		int b = 0;
		while (!periodLoop(b)) {
			b++;
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(new RunningTaskInfo(this.getClass(), "the current task"));
			}
		}
	}

	private boolean periodLoop(final int b) {
		for (int c = 1; c <= b; c++) {
			mUtils.output(">> Checking Consistency for b=" + b + ", c=" + c);
			mUtils.setDetailed(true);
			final int k = mTermChecker.checkConsistency(b, c);
			if (k >= 0) {
				mUtils.output(">> NOT CONSISTENT FOR 2 ITERATIONS: RETURNING COMPOSITION RESULT");
				mResultTerm = mFormulaBuilder.buildConsistencyResult(mConjunc, k * c + b - 1, mInVars, mOutVars);
				return true;
			}
			mUtils.output(">> CONSISTENT: CHECKING FOR PERIODICITY");
			mUtils.setDetailed(false);
			final ParametricOctMatrix difference = periodCheck(b, c);
			if (difference == null) {
				mUtils.output("PeriodCheck Not Successful.");
				continue;
			}
			final boolean forAll = checkForAll(difference, b, c);
			if (forAll) {
				mUtils.output("ForAll Successful.");
				mResultTerm = mFormulaBuilder.buildParametricResult(mConjunc, b, difference, mInVars, mOutVars,
						mVariables);
				return true;
			}
			mUtils.output("ForAll Unsuccessful. Periodicity until Inconsistency.");
			final boolean periodicity = checkPeriodicity(difference, b, c);
			if (periodicity && periodicityCalculation(difference, b, c)) {
				return true;
			}

		}
		return false;

	}

	private boolean periodicityCalculation(final ParametricOctMatrix difference, final int b, final int c) {
		boolean consistent = true;
		int n = 0;

		mUtils.setDetailed(false);

		// Find minimum n for which the period becomes inconsistent.
		while (consistent) {
			final ParametricOctMatrix differenceN = difference.multiplyConstant(new BigDecimal(n));
			final ParametricOctMatrix differenceN1 = difference.multiplyConstant(new BigDecimal(n + 1));
			final OctConjunction rB = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
			final ParametricOctMatrix rBMatrix = mOctagonTransformer.getMatrix(rB, mVariables);
			final ParametricOctMatrix intervalMatrix = differenceN.add(rBMatrix);
			final OctConjunction interval = intervalMatrix.toOctConjunction();
			final OctConjunction rC = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, c);
			final OctConjunction intervalRC = mOctagonCalculator.binarySequentialize(interval, rC, mInVars, mOutVars);
			consistent = mTermChecker.checkTerm(intervalRC.toTerm(mManagedScript.getScript()));
			final OctConjunction interval1 = (differenceN1.add(rBMatrix)).toOctConjunction();

			mUtils.output(intervalRC.toString());
			mUtils.output(intervalRC.toTerm(mManagedScript.getScript()).toStringDirect());

			if (!mTermChecker.checkTerm(mManagedScript.getScript().term("=",
					intervalRC.toTerm(mManagedScript.getScript()), interval1.toTerm(mManagedScript.getScript())))) {
				return false;
			}
			n++;

			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(new RunningTaskInfo(this.getClass(), "the current task"));
			}

		}

		mResultTerm = mFormulaBuilder.buildPeriodicityResult(mConjunc, difference, b, c, n, mInVars, mOutVars,
				mVariables);
		return true;
	}

	private boolean checkPeriodicity(final ParametricOctMatrix difference, final int b, final int c) {
		// Exists n >= 0 rho(n*difference + sigma(R^b) ○ R^c

		final Script script = mManagedScript.getScript();
		final OctConjunction rB = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
		final ParametricOctMatrix rBMatrix = mOctagonTransformer.getMatrix(rB, mVariables);
		final ParametricOctMatrix differenceN = difference.multiplyVar("n", mManagedScript);
		final ParametricOctMatrix intervalMatrix = differenceN.add(rBMatrix);

		final OctConjunction rC = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, c);
		final OctConjunction interval = mOctagonCalculator.binarySequentialize(intervalMatrix.toOctConjunction(), rC,
				mInVars, mOutVars);

		final Term quantified = script.quantifier(QuantifiedFormula.EXISTS,
				new TermVariable[] { differenceN.getParametricVar() },
				script.term("and", script.term(">=", differenceN.getParametricVar(), script.decimal(BigDecimal.ZERO)),
						interval.toTerm(script)));
		return mTermChecker.checkQuantifiedTerm(quantified);
	}

	private ParametricOctMatrix periodCheck(final int b, final int c) {
		// Check if difference between R^(c+b) and R^(b) is equal to difference
		// between R^(2c+b) and R^(c+b)

		// Prepare conjunctions for c0 = R^(b), c1 = R^(c+b), c2 = R^(2c+b)

		mUtils.output(">>> PERIOD CHECK");

		final OctConjunction c0 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
		final OctConjunction c1 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b + c);
		final OctConjunction c2 = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b + 2 * c);

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

		mUtils.setDetailed(true);

		mUtils.debug(difference.getMatrix().toString());
		mUtils.debug(difference2.getMatrix().toString());
		mUtils.debug(difference.toOctConjunction().toString());
		mUtils.debug(difference2.toOctConjunction().toString());

		mUtils.setDetailed(false);
		// Check Equality

		if (difference.isEqualTo(difference2)) {
			mUtils.output("> Success!");
			return difference;
		}

		return null;
	}

	private boolean checkForAll(final ParametricOctMatrix difference, final int b, final int c) {
		// if for all n>=0 : rho( n * difference + sigma(R^b))∘R^c
		// <=> rho((n+1) * difference + sigma(R^b)) <=/=> false

		mUtils.output(">>> FOR ALL CHECK, b=" + b + ",c=" + c);
		mUtils.setDetailed(true);

		// PREPARATIONS

		final Script script = mManagedScript.getScript();
		final OctConjunction rB = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, b);
		final OctConjunction rC = mOctagonCalculator.sequentialize(mConjunc, mInVars, mOutVars, c);
		final ParametricOctMatrix rBMatrix = mOctagonTransformer.getMatrix(rB, mVariables);

		// n * difference, (n+1) * difference

		mUtils.debug("Creating Parametric Matrix differenceN.");
		final ParametricOctMatrix differenceN = difference.multiplyVar("n", mManagedScript);
		mUtils.debug(differenceN.toOctConjunction().toString());

		// Additions

		mUtils.debug(differenceN.getMapping().toString());
		mUtils.debug(rBMatrix.getMapping().toString());
		mUtils.debug(differenceN.getMatrix().toString());
		mUtils.debug(rBMatrix.getMatrix().toString());
		mUtils.debug(differenceN.getSummands().toString());
		mUtils.debug(differenceN.getParametricVar().toString());

		differenceN.setLogger(mUtils.getLogger());
		final ParametricOctMatrix intervalMatrix = differenceN.add(rBMatrix);

		mUtils.debug("Creating Intervals.");

		// Back to OctagonConjunction and concatinate with R^c

		intervalMatrix.setLogger(mUtils.getLogger());

		final OctConjunction intervalMatrixConjunction = intervalMatrix.toOctConjunction();
		final OctConjunction intervalBeginning = mOctagonCalculator.binarySequentialize(intervalMatrixConjunction, rC,
				mInVars, mOutVars);
		final OctConjunction intervalEnd = intervalMatrix.toOctConjunction(1);

		mUtils.debug("Intervals:");
		mUtils.debug(intervalBeginning.toString());
		mUtils.debug(intervalEnd.toString());

		// Equality Term (<=>)

		final Term eqTerm = script.term("=", intervalBeginning.toTerm(script), intervalEnd.toTerm(script));
		mUtils.debug("eqTerm: " + eqTerm.toString());

		// QuantifiedTerm (for all n >= 0)

		final Term greaterEqZero = script.term("and",
				script.term(">=", differenceN.getParametricVar(), script.decimal(BigDecimal.ZERO)), eqTerm);
		final Term lesserZero = script.term("<", differenceN.getParametricVar(), script.decimal(BigDecimal.ZERO));
		final Term quantTerm = script.quantifier(QuantifiedFormula.FORALL,
				new TermVariable[] { differenceN.getParametricVar() }, script.term("or", greaterEqZero, lesserZero));
		mUtils.debug("quantTerm: " + quantTerm.toString());

		// INCONSISTENCY

		final HashSet<TermVariable> vars = intervalBeginning.getVariables();
		final Term satisfiableVars = script.quantifier(QuantifiedFormula.EXISTS, vars.toArray(new TermVariable[0]),
				intervalBeginning.toTerm(script));

		final Term satisfiable = script.quantifier(QuantifiedFormula.FORALL,
				new TermVariable[] { differenceN.getParametricVar() }, script.term("or", lesserZero, satisfiableVars));

		final boolean isSat = mTermChecker.checkQuantifiedTerm(quantTerm);
		if (!isSat) {
			return false;
		}
		final boolean isConsistent = mTermChecker.checkQuantifiedTerm(satisfiable);

		return isConsistent;
	}

	private boolean isOctagon(final Term relation, final Script script) throws NotAffineException {

		// Convert Term to CNF

		final Term cnfRelation = SmtUtils.toCnf(mServices, mManagedScript, relation,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mUtils.output("CNF");
		mUtils.output(cnfRelation.toString());

		// Get all SubTerms seperated by conjunction.

		final Set<Term> subTerms = mOctagonDetector.getConjunctSubTerms(cnfRelation);
		mUtils.debug("Term count:" + subTerms.size());

		mOctagonDetector.clearChecked();

		for (Term t : subTerms) {

			// Get Term in positive Normal Form

			final AffineRelation affine = AffineRelation.convert(script, t);
			t = affine.positiveNormalForm(script);
			mUtils.debug("Term as Positive Normal Form:");
			mUtils.debug(t.toString());

			// Check if Term is a possible OctagonTerm
			// (is equal to a Term of the form: +-x +-y <= c)

			if (!mOctagonDetector.isOctTerm(t)) {
				return false;
			}

		}
		return true;
	}

	public UnmodifiableTransFormula getResult() {
		if (mResultTerm == null) {
			throw new UnsupportedOperationException("No Result found.");
		}
		return mFormulaBuilder.buildTransFormula(mResultTerm, mInVars, mOutVars);
	}

	/**
	 * Get a result merged with an ExitEdge.
	 *
	 * @param exitEdgeFormula
	 *            The {@link UmodifiableTransFormula} of the exit edge.
	 * @return accelerated result including the exit edge.
	 */
	public UnmodifiableTransFormula getExitEdgeResult(final UnmodifiableTransFormula exitEdgeFormula) {
		mResultTerm = mFormulaBuilder.getExitEdgeResult(exitEdgeFormula, mResultTerm, mInVars, mOutVars);
		return getResult();
	}

}
