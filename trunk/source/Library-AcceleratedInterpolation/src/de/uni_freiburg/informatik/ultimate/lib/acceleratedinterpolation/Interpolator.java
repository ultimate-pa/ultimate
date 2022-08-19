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

import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Interpolator used to generate interpolants from a given meta-trace
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The transition.
 *
 */
public class Interpolator<LETTER extends IIcfgTransition<?>> {
	/**
	 * Define which technique of interpolation is used.
	 *
	 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
	 *
	 */
	public enum InterpolationMethod {
		POST, BINARY, CRAIG_NESTED, CRAIG_TREE
	}

	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final ITraceCheckPreferences mPrefs;
	private IPredicate[] mInterpolants;
	private LBool mTraceCheckResult;

	/**
	 * The accelerated interpolation interpolator. Generates interpolants along a meta trace according to the specified
	 * interpolation method.
	 *
	 * @param predicateUnifier
	 *            A {@link PredicateUnifier}
	 * @param predTransformer
	 *            A {@link PredicateTransformer}
	 * @param logger
	 *            A {@link ILogger}
	 * @param script
	 *            A {@link ManagedScript}
	 * @param services
	 *            An {@link IUltimateServiceProvider}
	 * @param prefs
	 *            Ultimate's preferences as specified in the settings file.
	 */
	public Interpolator(final IPredicateUnifier predicateUnifier,
			final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer, final ILogger logger,
			final ManagedScript script, final IUltimateServiceProvider services, final ITraceCheckPreferences prefs) {
		mPredicateUnifier = predicateUnifier;
		mPredTransformer = predTransformer;
		mScript = script;
		mLogger = logger;
		mServices = services;
		mPrefs = prefs;
	}

	/**
	 * Given a counterexample, like a meta-trace, generate a sequence of interpolants
	 *
	 * @param interpolationMethod
	 *            which method of interpolation is used
	 * @param counterexample
	 *            A possible counterexample trace.
	 */
	public void generateInterpolants(final InterpolationMethod interpolationMethod,
			final IRun<LETTER, IPredicate> counterexample) {
		switch (interpolationMethod) {
		case POST:
			mInterpolants = generateInterpolantsPost(counterexample);
			return;
		case CRAIG_NESTED:
			mInterpolants = generateInterpolantsCraigNested(counterexample);
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
		mTraceCheckResult = LBool.UNSAT;
		final List<LETTER> counterexample = counterexampleRun.getWord().asList();
		final IPredicate[] interpolants = new IPredicate[counterexample.size() + 1];
		interpolants[0] = mPredicateUnifier.getTruePredicate();
		interpolants[counterexample.size()] = mPredicateUnifier.getFalsePredicate();
		for (int i = 1; i <= counterexample.size(); i++) {
			interpolants[i] = mPredicateUnifier.getOrConstructPredicate(mPredTransformer
					.strongestPostcondition(interpolants[i - 1], counterexample.get(i - 1).getTransformula()));
		}
		return Arrays.copyOfRange(interpolants, 1, counterexample.size());
	}

	/**
	 * Generation of interpolants by instantiating an {@link InterpolatingTraceCheckCraig} The code creates an
	 * InterpolatingTraceCheckCraig with settings for Craig_NestedInterpolation -- we could also try and wrap a strategy
	 * module to gain more flexibility.
	 *
	 * @param counterexample
	 * @return
	 */
	private IPredicate[] generateInterpolantsCraigNested(final IRun<LETTER, IPredicate> counterexampleRun) {
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
				mPredicateUnifier, mPrefs.getAssertCodeBlockOrder(), mPrefs.computeCounterexample(),
				mPrefs.collectInterpolantStatistics(), InterpolationTechnique.Craig_NestedInterpolation,
				instanticateArrayExt, mPrefs.getXnfConversionTechnique(), mPrefs.getSimplificationTechnique(),
				innerRecursiveNestedInterpolationCall);
		mTraceCheckResult = itcc.isCorrect();
		if (mTraceCheckResult == LBool.UNSAT) {
			return itcc.getInterpolants();
		}
		return new IPredicate[0];
	}

	public LBool getTraceCheckResult() {
		return mTraceCheckResult;
	}

	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}
}
