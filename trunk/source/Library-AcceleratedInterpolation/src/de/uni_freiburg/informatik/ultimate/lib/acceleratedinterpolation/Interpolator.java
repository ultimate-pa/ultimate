package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Interpolator<LETTER extends IIcfgTransition<?>> {

	public enum InterpolationMethod {
		POST, BINARY, TREE
	}

	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final PredicateHelper mPredHelper;
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

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
			final ManagedScript script, final IUltimateServiceProvider services, final PredicateHelper predHelper) {

		mPredicateUnifier = predicateUnifier;
		mPredTransformer = predTransformer;
		mPredHelper = predHelper;
		mScript = script;
		mLogger = logger;
		mServices = services;

	}

	public IPredicate[] generateInterpolants(final InterpolationMethod interpolationMethod,
			final List<LETTER> counterexample, final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {
		switch (interpolationMethod) {
		case POST:
			return generateInterpolantsPost(counterexample);
		case BINARY:
			return generateInterpolantsBinary(counterexample, accelerations);
		case TREE:
			return generateInterpolantsTree(counterexample, accelerations);

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
	private IPredicate[] generateInterpolantsPost(final List<LETTER> counterexample) {
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
	 * contains loops.
	 *
	 * @param counterexample
	 * @return
	 */
	private IPredicate[] generateInterpolantsBinary(final List<LETTER> counterexample,
			final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {
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
	 * Naive way of generating interpolants, by just applying the post operator
	 *
	 * @param counterexample
	 * @return
	 */
	private IPredicate[] generateInterpolantsTree(final List<LETTER> counterexample,
			final Map<IcfgLocation, Set<UnmodifiableTransFormula>> accelerations) {

		final Term[] partition = new ApplicationTerm[counterexample.size()];

		for (int i = 0; i < counterexample.size(); ++i) {
			final Term t = counterexample.get(i).getTransformula().getClosedFormula();
			final String str = Integer.toString(i);
			final Term tt = SmtUtils.annotateAndAssert(mScript.getScript(), t, str);
			partition[i] = tt;

		}
		mScript.getScript().push(1);
		final Term[] interpolants = mScript.getScript().getInterpolants(partition);

		final IPredicate[] interpolantsPred = new IPredicate[counterexample.size()];
		mScript.getScript().pop(1);
		return interpolantsPred;
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

	public IPredicate[] getInterpolantFromTraceSchemeSp() {
		final IPredicate[] interpolants = new IPredicate[0];
		return interpolants;
	}
}
