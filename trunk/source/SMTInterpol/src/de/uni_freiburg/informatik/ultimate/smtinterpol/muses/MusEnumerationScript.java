/*
 * Copyright (C) 2020 Leonard Fichtner
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.BooleanOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.DoubleOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.EnumOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.LongOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap.CopyMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;

/**
 * An implementation of a WrapperScript, which provides additional functionality in terms of MUS enumeration and
 * interpolation.
 *
 * @author LeonardFichtner
 *
 */
public class MusEnumerationScript extends WrapperScript {

	/**
	 * For the exact meaning of the respective Heuristic, see the respective descriptions in {@link Heuristics}. That
	 * class does not contain the "FIRST" heuristic. The "FIRST" Heuristic means to just enumerate one MUS and generate
	 * the Interpolant from it.
	 */
	public enum HeuristicsType {
		RANDOM, SMALLEST, BIGGEST, LOWLEXORDER, HIGHLEXORDER, SHALLOWEST, DEEPEST, NARROWEST, WIDEST, SMALLESTAMONGWIDE,
		WIDESTAMONGSMALL, FIRST;
	}

	TimeoutHandler mHandler;

	ScopedArrayList<Term> mRememberedAssertions;
	int mCustomNameId;
	boolean mAssertedTermsAreUnsat;

	EnumOption<HeuristicsType> mInterpolationHeuristic;
	DoubleOption mTolerance;
	LongOption mEnumerationTimeout;
	LongOption mHeuristicTimeout;
	BooleanOption mLogAdditionalInformation;
	BooleanOption mUnknownAllowed;
	LogProxy mLogger;

	Random mRandom;

	/**
	 * Default constructor.
	 */
	public MusEnumerationScript() {
		this(new SMTInterpol());
	}

	/**
	 * Takes the LogProxy of the given SMTInterpol for logging.
	 */
	public MusEnumerationScript(final SMTInterpol wrappedScript) {
		this(wrappedScript, null);
	}

	/**
	 * Will use the given LogProxy for logging.
	 */
	public MusEnumerationScript(final SMTInterpol wrappedScript, final LogProxy logger) {
		super(wrappedScript);
		assert wrappedScript instanceof SMTInterpol : "Currently, only SMTInterpol is supported.";
		final SMTInterpol wrappedSMTInterpol = (SMTInterpol) mScript;
		mCustomNameId = 0;
		mAssertedTermsAreUnsat = false;
		mHandler = new TimeoutHandler(wrappedSMTInterpol.getTerminationRequest());
		if (logger == null) {
			mLogger = wrappedScript.getLogger();
		} else {
			mLogger = logger;
		}
		mRandom = new Random(getRandomSeed());
		mRememberedAssertions = new ScopedArrayList<>();

		mInterpolationHeuristic = new EnumOption<>(HeuristicsType.RANDOM, true, HeuristicsType.class,
				"The Heuristic that is used to choose a minimal unsatisfiable subset/core for interpolant generation");
		mTolerance = new DoubleOption(0.1, true,
				"The tolerance value that is used by the SMALLESTAMONGWIDE and the WIDESTAMONGSMALL Heuristic.");
		mEnumerationTimeout = new LongOption(0, true, "The time that is invested into enumerating Muses");
		mHeuristicTimeout = new LongOption(0, true,
				"The time that is invested into finding the best Mus according to the set Heuristic");
		mLogAdditionalInformation = new BooleanOption(false, true,
				"Whether additional information (e.g. of the enumeration) should be logged.");
		mUnknownAllowed =
				new BooleanOption(false, true, "Whether LBool.UNKNOWN is allowed to occur in the enumeration process.");
	}

	private long getRandomSeed() {
		return ((BigInteger) getOption(SMTLIBConstants.RANDOM_SEED)).longValue();
	}

	private long getEnumerationTimeout() {
		return ((BigInteger) getOption(MusOptions.ENUMERATION_TIMEOUT)).longValue();
	}

	private long getHeuristicTimeout() {
		return ((BigInteger) getOption(MusOptions.HEURISTIC_TIMEOUT)).longValue();
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mScript.getFunctionSymbol(constructor);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) {
		final int[] startOfSubtrees = new int[partition.length];
		return getInterpolants(partition, startOfSubtrees);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree) {
		return mScript.getInterpolants(partition, startOfSubtree, proofTree);
	}

	/**
	 * This method first enumerates MUSes (with the ReMus algorithm) of the current asserted terms, then it applies a
	 * heuristic for choosing a MUS amongst them. Lastly, the proof of unsatisfiability of the chosen MUS is used to
	 * generate the Sequence of Interpolants that is returned. The enumeration of Muses, the heuristic and
	 * getInterpolants use different timeouts, respectively. The timeout for enumeration and heuristics can be set with
	 * the keys in {@link MusOptions}, the interpolant generation is set with the timeout key in
	 * {@link SMTInterpolConstants}. If the timeout for the enumeration is exceeded, it returns the muses found so far. If
	 * the timeout for the heuristic is exceeded, it returns the best mus found so far wrt. the heuristic. If the
	 * timeout for the enumeration is exceeded, before any MUSes could be produced, this method uses the
	 * Vanilla-SMTInterpol proof for interpolant generation. An exception occurs, if the timeout for interpolant
	 * generation is exceeded.
	 *
	 * DEFAULT: Per Default, the HeuristicsType is set to RANDOM, the tolerance to 0.9 and the Timeout is unlimited.
	 *
	 * OPTIONS: For a description of the Options special to the MUSEnumerationScript, see
	 * {@link #setOption(String, Object)}
	 *
	 * This method is only available if proof production is enabled. To enable proof production, call
	 * setOption(":produce-proofs",true). For the FIRST Heuristic, unsat core production must be enabled. To enable
	 * unsat core production, call setOption(":produce-unsat-cores", true). Also, if unsat core production is turned on,
	 * in case the script is not able to enumerate a MUS and logging is turned on, info about the vanilla unsat core is
	 * logged.
	 */
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted terms must be determined to be unsatisfiable before an interpolant can be generated. Call checkSat to determine satisfiability.");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_PROOFS))) {
			throw new SMTLIBException("Proof production must be enabled (you can do this via setOption).");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))
				&& mInterpolationHeuristic.getValue() == HeuristicsType.FIRST) {
			throw new SMTLIBException("For the FIRST Heuristic, unsat core production must be enabled.");
		}

		final Translator translator = new Translator();

		final long enumerationTimeout = getEnumerationTimeout();
		final long heuristicTimeout = getHeuristicTimeout();

		if (enumerationTimeout > 0) {
			mHandler.setTimeout(enumerationTimeout);
		}

		long elapsedTime = System.nanoTime();
		final ArrayList<MusContainer> muses;
		if (mInterpolationHeuristic.getValue() == HeuristicsType.FIRST) {
			muses = shrinkVanillaUnsatCore(translator);
		} else {
			muses = executeReMus(translator);
		}
		elapsedTime = (System.nanoTime() - elapsedTime) / 1000000;

		if (mLogAdditionalInformation.getValue()) {
			String value;
			if (enumerationTimeout <= 0) {
				value = "Unlimited (no timeout set)";
			} else {
				value = Long.toString(enumerationTimeout);
			}
			mLogger.fatal("Timeout: " + value);
			mLogger.fatal("Cardinality of Constraint set: " + translator.getNumberOfConstraints());
			mLogger.fatal("Number of enumerated Muses: " + muses.size());
			mLogger.fatal("Time needed for enumeration: " + elapsedTime);
		}
		mHandler.clearTimeout();

		if (muses.isEmpty()) {
			if (mLogAdditionalInformation.getValue()) {
				mLogger.fatal("Timeout for enumeration exceeded before any muses could be found.");
				mLogger.fatal("Heuristic: None (UC is from Vanilla-SMTInterpol)");
				if (((boolean) getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
					final MusContainer container =
							new MusContainer(translator.translateToBitSet(mScript.getUnsatCore()), null);
					mLogger.fatal("Vanilla-UC has size: " + Heuristics.size(container));
					mLogger.fatal("Vanilla-UC has depth: " + Heuristics.depth(container));
					mLogger.fatal("Vanilla-UC has width: " + Heuristics.width(container));
				}
			}
			final Term[] sequenceOfInterpolants = getInterpolants(partition, startOfSubtree, mScript.getProof());
			return sequenceOfInterpolants;
		}

		if (heuristicTimeout > 0) {
			mHandler.setTimeout(heuristicTimeout);
		}

		elapsedTime = System.nanoTime();
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);
		elapsedTime = (System.nanoTime() - elapsedTime) / 1000000;

		if (mLogAdditionalInformation.getValue()) {
			mLogger.fatal("Time needed for Heuristics: " + elapsedTime);
		}

		mHandler.clearTimeout();

		final Term[] sequenceOfInterpolants = getInterpolants(partition, startOfSubtree, chosenMus.getProof());
		return sequenceOfInterpolants;
	}

	/**
	 * First, uses the ReMUS algorithm to enumerate MUSes of the set of asserted Terms. Then, it searches for the best
	 * MUS according to the chosen heuristic. If the first timeout is exceeded, the enumeration stops and the heuristic
	 * is applied to the MUSes found so far. If the second timeout is exceeded, the best MUS that has been found so far
	 * is returned. If ReMUS could not find any MUS in the given time, an arbitrary unsat core (i.e., the unsat core of
	 * the wrapped script) is returned, which is not necessarily minimal wrt. satisfiability. Every step (enumeration,
	 * heuristic, getUnsatCore of the wrapped script) has its own timeout.
	 *
	 * DEFAULT: Per Default, the HeuristicsType is set to RANDOM, the tolerance to 0.9 and the Timeout is unlimited.
	 *
	 * OPTIONS: For a description of the Options special to the MUSEnumerationScript, see
	 * {@link #setOption(String, Object)}
	 *
	 * This method is only available if proof production and unsat core production is enabled. To enable proof
	 * production, call setOption(":produce-proofs",true). To enable unsat core production, call
	 * setOption(":produce-unsat-cores", true). Also, if unsat core production is turned on, in case the script is not
	 * able to enumerate a MUS and logging is turned on, info about the vanilla unsat core is logged.
	 */
	@Override
	public Term[] getUnsatCore() {
		if (!mAssertedTermsAreUnsat) {
			throw new SMTLIBException(
					"Asserted Terms must be determined Unsat to return an unsat core. Call checkSat to determine satisfiability.");
		} else if (!((boolean) getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
			throw new SMTLIBException("Unsat core production must be enabled (you can do this via setOption).");
		}

		final Translator translator = new Translator();

		final long timeoutForReMus = getEnumerationTimeout();
		final long timeoutForHeuristic = getHeuristicTimeout();

		if (timeoutForReMus > 0) {
			mHandler.setTimeout(timeoutForReMus);
		}

		long elapsedTime = System.nanoTime();
		final ArrayList<MusContainer> muses;
		if (mInterpolationHeuristic.getValue() == HeuristicsType.FIRST) {
			muses = shrinkVanillaUnsatCore(translator);
		} else {
			muses = executeReMus(translator);
		}
		elapsedTime = (System.nanoTime() - elapsedTime) / 1000000;

		if (mLogAdditionalInformation.getValue()) {
			String value;
			if (timeoutForReMus <= 0) {
				value = "Unlimited (no timeout set)";
			} else {
				value = Long.toString(timeoutForReMus);
			}
			mLogger.fatal("Timeout: " + value);
			mLogger.fatal("Cardinality of Constraint set: " + translator.getNumberOfConstraints());
			mLogger.fatal("Number of enumerated Muses: " + muses.size());
			mLogger.fatal("Time needed for enumeration: " + elapsedTime);
		}
		mHandler.clearTimeout();

		if (muses.isEmpty()) {

			final Term[] alternativeUnsatCore = mScript.getUnsatCore();

			if (mLogAdditionalInformation.getValue()) {
				mLogger.fatal("Enumeration timeout exceeded. Returning Unsat Core of wrapped Script.");
				final MusContainer container =
						new MusContainer(translator.translateToBitSet(alternativeUnsatCore), null);
				mLogger.fatal("Heuristic: None (UC is from Vanilla-SMTInterpol)");
				mLogger.fatal("Vanilla-UC has size: " + Heuristics.size(container));
				mLogger.fatal("Vanilla-UC has depth: " + Heuristics.depth(container));
				mLogger.fatal("Vanilla-UC has width: " + Heuristics.width(container));
			}

			return alternativeUnsatCore;
		}

		if (timeoutForHeuristic > 0) {
			mHandler.setTimeout(timeoutForHeuristic);
		}

		elapsedTime = System.nanoTime();
		final MusContainer chosenMus = chooseMusAccordingToHeuristic(muses, mHandler);
		elapsedTime = (System.nanoTime() - elapsedTime) / 1000000;

		if (mLogAdditionalInformation.getValue()) {
			mLogger.fatal("Time needed for Heuristics: " + elapsedTime);
		}

		mHandler.clearTimeout();

		final ArrayDeque<Term> unsatcore = new ArrayDeque<>();
		for (final Term t : translator.translateToTerms(chosenMus.getMus())) {
			if (t instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) t;
				for (final Annotation a : at.getAnnotations()) {
					if (a.getKey().equals(":named")) {
						final String name = ((String) a.getValue()).intern();
						unsatcore.add(t.getTheory().term(name));
						break;
					}
				}
			}
		}
		return unsatcore.toArray(new Term[unsatcore.size()]);
	}

	/**
	 * Executes the ReMus algorithm on the currently asserted Terms, with the internal TerminationRequest. If
	 * termination is requested, all MUSes that have been found so far are returned.
	 */
	private ArrayList<MusContainer> executeReMus() {
		final Translator translator = new Translator();
		return executeReMus(translator);
	}

	private ArrayList<MusContainer> executeReMus(final Translator translator) {
		if (translator.getNumberOfConstraints() != 0) {
			throw new SMTLIBException("Translator must be new.");
		}

		final TimeoutHandler handlerForReMus = new TimeoutHandler(mHandler);
		final DPLLEngine engine = new DPLLEngine(mLogger, handlerForReMus);
		final Script scriptForReMus = createScriptForMuses((SMTInterpol) mScript, handlerForReMus);

		registerTermsForEnumeration(mRememberedAssertions, translator, engine, scriptForReMus);
		resetCustomNameId();

		final UnexploredMap unexploredMap = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(scriptForReMus, translator);
		final int nrOfConstraints = solver.getNumberOfConstraints();
		final BitSet workingSet = new BitSet(nrOfConstraints);
		workingSet.flip(0, nrOfConstraints);

		LogProxy logForReMus;
		if (mLogAdditionalInformation.getValue()) {
			logForReMus = mLogger;
		} else {
			logForReMus = null;
		}
		final ReMus remus = new ReMus(solver, unexploredMap, workingSet, handlerForReMus, 0, mRandom,
				mUnknownAllowed.getValue(), logForReMus);
		final ArrayList<MusContainer> muses = remus.enumerate();

		letScriptForReMusRetire(scriptForReMus, remus);

		return muses;
	}

	private ArrayList<MusContainer> shrinkVanillaUnsatCore(final Translator translator) {
		final Term[] unsatCore = mScript.getUnsatCore();
		final ArrayList<MusContainer> muses = new ArrayList<>();

		final TerminationRequest requestForShrinker = mHandler;
		final Script scriptForShrinker = createScriptForMuses((SMTInterpol) mScript, requestForShrinker);
		registerTermsForShrinking(mRememberedAssertions, translator, scriptForShrinker);
		resetCustomNameId();

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(scriptForShrinker, translator);

		final BitSet workingSet = translator.translateToBitSet(unsatCore);

		final MusContainer firstMus =
				Shrinking.shrink(solver, workingSet, requestForShrinker, mRandom, mUnknownAllowed.getValue());
		if (firstMus == null) {
			// leave muses empty
		} else {
			muses.add(firstMus);
			if (mLogAdditionalInformation.getValue()) {
				final MusContainer containsVanillaUc = new MusContainer(workingSet, null);
				final int sizeDiff = Heuristics.size(containsVanillaUc) - Heuristics.size(firstMus);
				final int depthDiff = Heuristics.depth(containsVanillaUc) - Heuristics.depth(firstMus);
				final int widthDiff = Heuristics.width(containsVanillaUc) - Heuristics.width(firstMus);
				mLogger.fatal("Difference in size: " + sizeDiff);
				mLogger.fatal("Difference in depth: " + depthDiff);
				mLogger.fatal("Difference in width: " + widthDiff);
			}
		}
		letScriptForShrinkerRetire(scriptForShrinker, solver);
		return muses;
	}

	/**
	 * Uses the cloning constructor of SMTInterpol to clone the given smtInterpol and thereby set up a new Script for
	 * MUS enumeration. The given TerminationRequest will be set for the newly created Script. The intended
	 * TerminationRequest is the TimeoutHandler that is given to ReMus.
	 *
	 * Be sure to use {@link #letScriptForReMusRetire(Script, ReMus)} or
	 * {@link #letScriptForShrinkerRetire(Script, ConstraintAdministrationSolver)} (depending on what you intended to do
	 * with the script) after you are done with this Script! Otherwise the original smtInterpol could become
	 * inconsistent.
	 */
	private Script createScriptForMuses(final SMTInterpol smtInterpol, final TerminationRequest terminationRequest) {
		final Map<String, Object> remusOptions = createSMTInterpolOptionsForReMus();
		final SMTInterpol scriptForReMus = new SMTInterpol(smtInterpol, remusOptions, CopyMode.CURRENT_VALUE);
		scriptForReMus.setTerminationRequest(terminationRequest);
		scriptForReMus.push(1);

		return scriptForReMus;
	}

	private Map<String, Object> createSMTInterpolOptionsForReMus() {
		final Map<String, Object> remusOptions = new HashMap<>();
		remusOptions.put(SMTLIBConstants.PRODUCE_MODELS, true);
		remusOptions.put(SMTLIBConstants.PRODUCE_PROOFS, true);
		remusOptions.put(SMTLIBConstants.INTERACTIVE_MODE, true);
		remusOptions.put(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		return remusOptions;
	}

	/**
	 * Use this method after you are done with using the Script that has been created for ReMus.
	 */
	private void letScriptForReMusRetire(final Script scriptForReMus, final ReMus remus) {
		remus.resetSolver();
		scriptForReMus.pop(1);
	}

	private void letScriptForShrinkerRetire(final Script scriptForShrinker,
			final ConstraintAdministrationSolver solver) {
		solver.reset();
		scriptForShrinker.pop(1);
	}

	private boolean hasName(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annoTerm = (AnnotatedTerm) term;
			final Annotation[] annotations = annoTerm.getAnnotations();
			final String name = findName(annotations);
			if (name == null) {
				return false;
			}
			return true;
		} else {
			return false;
		}
	}

	private String findName(final Annotation[] annotations) {
		String name = null;
		for (int i = 0; i < annotations.length; i++) {
			if (annotations[i].getKey().equals(":named")) {
				name = (String) annotations[i].getValue();
			}
		}
		return name;
	}

	private AnnotatedTerm nameTerm(final Term term, final Script script) {
		final Annotation name = new Annotation(":named", "constraint" + Integer.toString(mCustomNameId));
		mCustomNameId++;
		return (AnnotatedTerm) script.annotate(term, name);
	}

	/**
	 * Declares the given terms to the 3 components in a proper manner, so that the components "know" those terms. For
	 * the scriptForReMus, this means, it has to "know" all terms in the sense of "All terms are annotated with a name
	 * and scriptForReMus knows about their annotation". Currently, this means that either scriptForReMus or the script
	 * it was cloned of, mScript, annotated the term with a name. For the translator this means, that each of the terms
	 * (necessarily named AnnotatedTerms!) is wrapped in a {@link NamedAtom} and this atom is declared with
	 * {@link Translator#declareConstraint(NamedAtom)}. For the DPLLEngine, this means that the preferred status of the
	 * atom is set and locked, and the atom is added with
	 * {@link DPLLEngine#addAtom(de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom)}.
	 */
	private void registerTermsForEnumeration(final ArrayList<Term> terms, final Translator translator,
			final DPLLEngine engine, final Script scriptForReMus) {
		AnnotatedTerm annoTerm;
		for (final Term term : terms) {
			if (hasName(term)) {
				annoTerm = (AnnotatedTerm) term;
			} else {
				// annoTerm = nameTerm(term, scriptForReMus);
				// The terms that have been asserted without a name are axioms, and should not be minimized.
				// Therefore we assert them at the beginning, and don't let the ReMus-System know that they even exist.
				scriptForReMus.assertTerm(term);
				continue;
			}
			final NamedAtom atom = new NamedAtom(annoTerm, 0);
			atom.setPreferredStatus(atom.getAtom());
			atom.lockPreferredStatus();
			if (engine != null) {
				engine.addAtom(atom);
			}
			translator.declareConstraint(atom);
		}
	}

	/**
	 * Essentially, its {@link #registerTermsForEnumeration(ArrayList, Translator, DPLLEngine, Script)}, but without the
	 * DPLLEngine, because the registration at a DPLLEngine is not necessary if one only needs to shrink.
	 */
	private void registerTermsForShrinking(final ArrayList<Term> terms, final Translator translator,
			final Script scriptForReMus) {
		registerTermsForEnumeration(terms, translator, null, scriptForReMus);
	}

	private MusContainer chooseMusAccordingToHeuristic(final ArrayList<MusContainer> muses,
			final TerminationRequest request) {
		MusContainer chosenMus;
		double tolerance;
		switch (mInterpolationHeuristic.getValue()) {
		case FIRST:
			assert muses.size() == 1 : "In case of the FIRST heuristic, only one mus should have been enumerated.";
			chosenMus = muses.get(0);
		case RANDOM:
			chosenMus = Heuristics.chooseRandomMus(muses, mRandom);
			break;
		case SMALLEST:
			chosenMus = Heuristics.chooseSmallestMus(muses, mRandom, mHandler);
			break;
		case BIGGEST:
			chosenMus = Heuristics.chooseBiggestMus(muses, mRandom, mHandler);
			break;
		case LOWLEXORDER:
			chosenMus = Heuristics.chooseMusWithLowestLexicographicalOrder(muses, mRandom, mHandler);
			break;
		case HIGHLEXORDER:
			chosenMus = Heuristics.chooseMusWithHighestLexicographicalOrder(muses, mRandom, mHandler);
			break;
		case SHALLOWEST:
			chosenMus = Heuristics.chooseShallowestMus(muses, mRandom, mHandler);
			break;
		case DEEPEST:
			chosenMus = Heuristics.chooseDeepestMus(muses, mRandom, mHandler);
			break;
		case NARROWEST:
			chosenMus = Heuristics.chooseNarrowestMus(muses, mRandom, mHandler);
			break;
		case WIDEST:
			chosenMus = Heuristics.chooseWidestMus(muses, mRandom, mHandler);
			break;
		case SMALLESTAMONGWIDE:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseSmallestAmongWideMuses(muses, tolerance, mRandom, mHandler);
			break;
		case WIDESTAMONGSMALL:
			tolerance = (double) mTolerance.get();
			chosenMus = Heuristics.chooseWidestAmongSmallMuses(muses, tolerance, mRandom, mHandler);
			break;
		default:
			throw new SMTLIBException("Unknown Enum for Interpolation heuristic");
		}
		if (mLogAdditionalInformation.getValue() == true) {
			final String heuristic = mInterpolationHeuristic.getValue().toString();
			mLogger.fatal("Heuristic: " + heuristic);
			final HeuristicsType heurType = mInterpolationHeuristic.getValue();
			if (heurType == HeuristicsType.SMALLESTAMONGWIDE || heurType == HeuristicsType.WIDESTAMONGSMALL) {
				mLogger.fatal("Tolerance: " + (double) mTolerance.get());
			}
			mLogger.fatal("Chosen Mus has size: " + Heuristics.size(chosenMus));
			mLogger.fatal("Chosen Mus has depth: " + Heuristics.depth(chosenMus));
			mLogger.fatal("Chosen Mus has width: " + Heuristics.width(chosenMus));
		}
		return chosenMus;
	}

	@Override
	public LBool checkSat() {
		final LBool sat = mScript.checkSat();
		if (sat == LBool.UNSAT) {
			mAssertedTermsAreUnsat = true;
		}
		return sat;
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedAssertions.beginScope();
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		for (int i = 0; i < levels; i++) {
			mRememberedAssertions.endScope();
		}
		mAssertedTermsAreUnsat = false;
	}

	/**
	 * Explanation of MUSEnumerationScript-specific Options:
	 *
	 * To set the used heuristic, use {@link #setOption(String, Object)} with the
	 * {@link MusOptions#INTERPOLATION_HEURISTIC} key and the respective {@link HeuristicsType} value. If you choose
	 * {@link HeuristicsType#SMALLESTAMONGWIDE} or {@link HeuristicsType#WIDESTAMONGSMALL}, you may also want to specify
	 * the value for the key {@link MusOptions#TOLERANCE} (for information about the tolerance, see
	 * {@link Heuristics#chooseWidestAmongSmallMuses(ArrayList, double, Random, TerminationRequest)} or
	 * {@link Heuristics#chooseSmallestAmongWideMuses(ArrayList, double, Random, TerminationRequest)}). To set the
	 * timeout for the enumeration, the heuristic or the Interpolation, set the values of the the keys
	 * {@link MusOptions#ENUMERATION_TIMEOUT}, {@link MusOptions#HEURISTIC_TIMEOUT}, {@link SMTInterpolConstants#TIMEOUT}
	 * respectively (the timeout is treated as MILLISECONDS!).
	 *
	 * If the option ":log-additional-information" is set to true with {@link #setOption(String, Object)}, then
	 * additional information about the enumeration and the chosen muses is logged on the level "fatal".
	 *
	 * If the option ":unknown-allowed" is set to true, then LBool.UNKNOWN may occur in the enumeration process, without
	 * causing an error (or let's just say it shouldn't cause an error ;) ). This means, that one might assert a wider
	 * range of formulas and the enumeration still works. On the other hand, there is no guarantee for completeness (If
	 * given enough time, all MUSes will be enumerated) or minimality (MUSes are minimal wrt. satisfiability) anymore.
	 * However, these disadvantages might only show up, if there is indeed a subset of the asserted Terms for which
	 * {@link #checkSat()} returns LBool.UNKNOWN. Also, at the current date, (09.09.20), the satisfiable extension is
	 * not used in the internal shrinking process when this flag is set to true, which might impact the runtime of
	 * enumeration.
	 */
	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (opt.equals(MusOptions.INTERPOLATION_HEURISTIC)) {
			mInterpolationHeuristic.set(value);
		} else if (opt.equals(MusOptions.TOLERANCE)) {
			mTolerance.set(value);
		} else if (opt.equals(SMTLIBConstants.RANDOM_SEED)) {
			mScript.setOption(opt, value);
			mRandom = new Random(getRandomSeed());
		} else if (opt.equals(MusOptions.ENUMERATION_TIMEOUT)) {
			mEnumerationTimeout.set(value);
		} else if (opt.equals(MusOptions.HEURISTIC_TIMEOUT)) {
			mHeuristicTimeout.set(value);
		} else if (opt.equals(MusOptions.LOG_ADDITIONAL_INFORMATION)) {
			mLogAdditionalInformation.set(value);
		} else if (opt.equals(MusOptions.UNKNOWN_ALLOWED)) {
			mUnknownAllowed.set(value);
		} else {
			mScript.setOption(opt, value);
		}
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		if (opt.equals(MusOptions.INTERPOLATION_HEURISTIC)) {
			return mInterpolationHeuristic.get();
		} else if (opt.equals(MusOptions.TOLERANCE)) {
			return mTolerance.get();
		} else if (opt.equals(MusOptions.ENUMERATION_TIMEOUT)) {
			return mEnumerationTimeout.get();
		} else if (opt.equals(MusOptions.HEURISTIC_TIMEOUT)) {
			return mHeuristicTimeout.get();
		} else if (opt.equals(MusOptions.LOG_ADDITIONAL_INFORMATION)) {
			return mLogAdditionalInformation.getValue();
		} else if (opt.equals(MusOptions.UNKNOWN_ALLOWED)) {
			return mUnknownAllowed.getValue();
		} else {
			return mScript.getOption(opt);
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mRememberedAssertions.add(term);
		mAssertedTermsAreUnsat = false;
		return mScript.assertTerm(term);
	}

	@Override
	public void reset() {
		mScript.reset();
		mRememberedAssertions.clear();
		mCustomNameId = 0;
		mAssertedTermsAreUnsat = false;
		mInterpolationHeuristic.reset();
		mTolerance.reset();
		mEnumerationTimeout.reset();
		mHeuristicTimeout.reset();
		mLogAdditionalInformation.reset();
		mRandom = new Random(getRandomSeed());
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();
		mRememberedAssertions.clear();
		mAssertedTermsAreUnsat = false;
	}

	private void resetCustomNameId() {
		mCustomNameId = 0;
	}
}
