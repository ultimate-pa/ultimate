/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Interpolator<LETTER extends IIcfgTransition<?>> {

	public enum InterpolationMethod {
		POST, BINARY, CRAIG_NESTED, CRAIG_TREE
	}

	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final PredicateHelper mPredHelper;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final ITraceCheckPreferences mPrefs;
	private IPredicate[] mInterpolants;
	private LBool mIsTraceCorrect;

	/**
	 * Class to help with interplation.
	 *
	 * @param predicateUnifier
	 * @param predTransformer
	 * @param logger
	 * @param script
	 * @param services
	 * @param predHelper
	 */
	public Interpolator(final IPredicateUnifier predicateUnifier,
			final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer, final ILogger logger,
			final ManagedScript script, final IUltimateServiceProvider services, final PredicateHelper predHelper,
			final ITraceCheckPreferences prefs) {

		mPredicateUnifier = predicateUnifier;
		mPredTransformer = predTransformer;
		mPredHelper = predHelper;
		mScript = script;
		mLogger = logger;
		mServices = services;
		mPrefs = prefs;
		mIsTraceCorrect = null;
		mInterpolants = new IPredicate[0];

	}

	public void generateInterpolants(final InterpolationMethod interpolationMethod,
			final IRun<LETTER, IPredicate> counterexample,
			final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {
		switch (interpolationMethod) {
		case POST:
			generateInterpolantsPost(counterexample);
			return;
		case BINARY:
			generateInterpolantsBinary(counterexample, accelerations);
			return;
		case CRAIG_NESTED:
			generateInterpolantsCraigNested(counterexample, accelerations);
			return;
		default:
			throw new UnsupportedOperationException();
		}

	}

	/**
	 * Naive way of generating interpolants, by just applying the post operator
	 *
	 * @param counterexample
	 * @return
	 */
	private IPredicate[] generateInterpolantsPost(final IRun<LETTER, IPredicate> counterexampleRun) {
		final List<LETTER> counterexample = counterexampleRun.getWord().asList();
		final IPredicate[] interpolants = new IPredicate[counterexample.size() + 1];
		interpolants[0] = mPredicateUnifier.getTruePredicate();
		interpolants[counterexample.size()] = mPredicateUnifier.getFalsePredicate();
		for (int i = 1; i <= counterexample.size(); i++) {
			interpolants[i] = mPredicateUnifier.getOrConstructPredicate(mPredTransformer
					.strongestPostcondition(interpolants[i - 1], counterexample.get(i - 1).getTransformula()));
		}
		final IPredicate[] actualInterpolants = Arrays.copyOfRange(interpolants, 1, counterexample.size());
		return actualInterpolants;
	}

	/**
	 * Generate inteprolants using a given infeasible counterexample. WITH the knowledge that the counterexample
	 * contains loops using binary interpolation.
	 *
	 * @param counterexample
	 * @return
	 */
	private IPredicate[] generateInterpolantsBinary(final IRun<LETTER, IPredicate> counterexampleRun,
			final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {
		final List<LETTER> counterexample = counterexampleRun.getWord().asList();
		final IPredicate[] interpolants = new IPredicate[counterexample.size() + 1];

		interpolants[0] = mPredicateUnifier.getTruePredicate();
		interpolants[counterexample.size()] = mPredicateUnifier.getFalsePredicate();
		final Term[] counterexampleTerms = new Term[counterexample.size()];
		for (int i = 0; i < counterexample.size(); i++) {
			counterexampleTerms[i] = counterexample.get(i).getTransformula().getFormula();
		}
		for (int j = 0; j < counterexample.size(); j++) {
			final LETTER l = counterexample.get(j);
			final Term first = mPredTransformer.strongestPostcondition(interpolants[j], l.getTransformula());
			final IPredicate firstPred = mPredicateUnifier.getOrConstructPredicate(first);
			Term second = mPredicateUnifier.getTruePredicate().getFormula();

			final List<UnmodifiableTransFormula> secondTfList = new ArrayList<>();

			for (int k = j + 1; k < counterexample.size(); k++) {
				final LETTER m = counterexample.get(k);
				second = SmtUtils.and(mScript.getScript(), second,
						counterexample.get(k).getTransformula().getClosedFormula());
				secondTfList.add(counterexample.get(k).getTransformula());
				if (accelerations != null && accelerations.containsKey(m.getTarget())) {
					/*
					 * TODO Multiple accelerations. (underapprox)
					 */
					if (accelerations != null && accelerations.get(m.getTarget()).size() > 1) {
						mLogger.debug("Dealing with multiple accelerations is not DONE YET!");
						throw new UnsupportedOperationException();
					}
					for (final UnmodifiableTransFormula accelTf : accelerations.get(m.getTarget())) {
						secondTfList.add(accelTf);
					}
				}
			}
			/*
			 * note: auxvar elimination yields error. because aux vars have no defaultconstant -> but we need closed
			 * formula.
			 */
			final UnmodifiableTransFormula secondTf = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					mScript, false, false, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
					SimplificationTechnique.SIMPLIFY_DDA, secondTfList);
			IPredicate interpolPred = computeInterpolantBinary(firstPred, secondTf);
			if (interpolPred == mPredicateUnifier.getTruePredicate()) {
				final Term t = mPredTransformer.strongestPostcondition(interpolants[j],
						counterexample.get(j).getTransformula());
				interpolPred = mPredicateUnifier.getOrConstructPredicate(t);
			}
			interpolants[j + 1] = interpolPred;
		}
		final IPredicate[] actualInterpolants = Arrays.copyOfRange(interpolants, 1, counterexample.size());
		return actualInterpolants;
	}

	/**
	 * Compute BINARY interpolants for a given partition.
	 *
	 * @param firstPred
	 * @param secondTf
	 * @return
	 */
	private IPredicate computeInterpolantBinary(final IPredicate firstPred, final UnmodifiableTransFormula secondTf) {
		final Map<IProgramVar, TermVariable> inVars = secondTf.getOutVars();
		final Map<IProgramVar, TermVariable> outVars = secondTf.getOutVars();
		final List<Term> inConst = new ArrayList<>();
		final List<Term> outConst = new ArrayList<>();
		Term secondClosed = secondTf.getClosedFormula();

		final Map<Term, Term> subIn = new HashMap<>();
		final Map<Term, Term> subOut = new HashMap<>();
		// final Map<Term, Term> subFirst = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> inVar : inVars.entrySet()) {
			subIn.put(inVar.getKey().getDefaultConstant(), inVar.getKey().getTermVariable());
			inConst.add((inVar.getKey().getDefaultConstant()));
		}
		for (final Entry<IProgramVar, TermVariable> outVar : outVars.entrySet()) {
			subOut.put(outVar.getKey().getPrimedConstant(), outVar.getKey().getTermVariable());
			outConst.add((outVar.getKey().getPrimedConstant()));
		}

		secondClosed = SmtUtils.and(mScript.getScript(), secondClosed,
				SmtUtils.pairwiseEquality(mScript.getScript(), inConst, outConst));

		final Pair<LBool, Term> interpolPair =
				SmtUtils.interpolateBinary(mScript.getScript(), firstPred.getClosedFormula(), secondClosed);

		/*
		 * Interpolant consists of constants, we need to unconstant them
		 */
		final Substitution substitutionIn = new Substitution(mScript, subIn);
		Term interpolant = substitutionIn.transform(interpolPair.getSecond());

		final Substitution substitutionOut = new Substitution(mScript, subOut);
		interpolant = substitutionOut.transform(interpolant);
		return mPredicateUnifier.getOrConstructPredicate(interpolant);
	}

	/**
	 * Generation of interpolants by instantiating an {@link InterpolatingTraceCheckCraig} The code creates an
	 * InterpolatingTraceCheckCraig with settings for Craig_NestedInterpolation -- we could also try and wrap a strategy
	 * module to gain more flexibility.
	 *
	 * @param counterexample
	 */
	private void generateInterpolantsCraigNested(final IRun<LETTER, IPredicate> counterexampleRun,
			final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {

		final List<LETTER> counterexample = counterexampleRun.getWord().asList();
		final NestedWord<LETTER> nestedWord = TraceCheckUtils.toNestedWord(counterexample);
		final TreeMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		final boolean instanticateArrayExt = true;
		final boolean innerRecursiveNestedInterpolationCall = false;
		final IPredicate preCondition = mPredicateUnifier.getTruePredicate();
		final IPredicate postCondition = mPredicateUnifier.getFalsePredicate();

		final InterpolatingTraceCheckCraig<LETTER> itcc = new InterpolatingTraceCheckCraig<>(preCondition,
				postCondition, pendingContexts, nestedWord, counterexampleRun.getStateSequence(), mServices,
				mPrefs.getCfgSmtToolkit(), mScript, (PredicateFactory) mPredicateUnifier.getPredicateFactory(),
				mPredicateUnifier, mPrefs.getAssertCodeBlocksOrder(), mPrefs.computeCounterexample(),
				mPrefs.collectInterpolantStatistics(), InterpolationTechnique.Craig_NestedInterpolation,
				instanticateArrayExt, mPrefs.getXnfConversionTechnique(), mPrefs.getSimplificationTechnique(),
				innerRecursiveNestedInterpolationCall);
		mIsTraceCorrect = itcc.isCorrect();
		if (mIsTraceCorrect == LBool.UNSAT) {
			mInterpolants = itcc.getInterpolants();
		}
	}

	public LBool isTraceCorrect() {
		return mIsTraceCorrect;
	}

	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}
}
