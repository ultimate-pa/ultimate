/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsQuantifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifierStatisticsGenerator.PredicateUnifierStatisticsType;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.CheckClosedTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Data structure that stores for each term a unique predicate. Initially a predicate unifier constructs a "true"
 * predicate and a "false" predicate.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class PredicateUnifier implements IPredicateUnifier {

	protected final ManagedScript mMgnScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final Map<Term, IPredicate> mTerm2Predicates;
	private final LinkedHashSet<IPredicate> mKnownPredicates = new LinkedHashSet<>();
	private final Map<IPredicate, IPredicate> mDeprecatedPredicates = new HashMap<>();
	private final CoverageRelation mCoverageRelation = new CoverageRelation();
	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final IIcfgSymbolTable mSymbolTable;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;

	private final PredicateUnifierStatisticsGenerator mPredicateUnifierBenchmarkGenerator;

	public PredicateUnifier(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory predicateFactory,
			final IIcfgSymbolTable symbolTable, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IPredicate... initialPredicates) {
		mPredicateUnifierBenchmarkGenerator = new PredicateUnifierStatisticsGenerator();
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mMgnScript = mgdScript;
		mPredicateFactory = predicateFactory;
		mScript = mgdScript.getScript();
		mSymbolTable = symbolTable;
		mServices = services;
		mLogger = logger;
		mImplicationChecker = new MonolithicImplicationChecker(mServices, mMgnScript);
		mTerm2Predicates = new HashMap<>();
		final Term trueTerm = mScript.term("true");
		IPredicate truePredicate = null;
		final Term falseTerm = mScript.term("false");
		IPredicate falsePredicate = null;
		for (final IPredicate pred : initialPredicates) {
			if (pred.getFormula().equals(trueTerm)) {
				truePredicate = pred;
			} else if (pred.getFormula().equals(falseTerm)) {
				falsePredicate = pred;
			}
		}
		if (truePredicate == null) {
			mTruePredicate = constructNewPredicate(mScript.term("true"), null);
		} else {
			mTruePredicate = truePredicate;
		}
		if (falsePredicate == null) {
			mFalsePredicate = constructNewPredicate(mScript.term("false"), null);
		} else {
			mFalsePredicate = falsePredicate;
		}
		declareTruePredicateAndFalsePredicate();
		for (final IPredicate pred : initialPredicates) {
			if (pred == mFalsePredicate || pred == mTruePredicate) {
				continue;
			}
			declarePredicate(pred);
		}
		logger.info("Initialized classic predicate unifier");
	}

	@Override
	public IPredicate getTruePredicate() {
		return mTruePredicate;
	}

	@Override
	public IPredicate getFalsePredicate() {
		return mFalsePredicate;
	}

	private void declareTruePredicateAndFalsePredicate() {
		final Map<IPredicate, Validity> impliedByTrue = Collections.emptyMap();
		final Map<IPredicate, Validity> expliedByTrue = Collections.emptyMap();
		addNewPredicate(mTruePredicate, mTruePredicate.getFormula(), mTruePredicate.getFormula(), impliedByTrue,
				expliedByTrue);
		final Map<IPredicate, Validity> impliedByFalse = Collections.singletonMap(mTruePredicate, Validity.VALID);
		final Map<IPredicate, Validity> expliedByFalse = Collections.singletonMap(mTruePredicate, Validity.INVALID);
		addNewPredicate(mFalsePredicate, mFalsePredicate.getFormula(), mFalsePredicate.getFormula(), impliedByFalse,
				expliedByFalse);
	}

	/**
	 * Return true iff pred is the representative IPredicate for the Term pred.getFormula().
	 */
	@Override
	public boolean isRepresentative(final IPredicate pred) {
		final IPredicate representative = mTerm2Predicates.get(pred.getFormula());
		return pred == representative;
	}

	/**
	 * Add predicate. Store this predicate without further simplification. Throw an exception if this PredicateUnifier
	 * stores already an equivalent predicate.
	 */
	void declarePredicate(final IPredicate predicate) {
		final PredicateComparison pc = new PredicateComparison(predicate.getFormula(), predicate.getVars(), null, null);
		if (pc.isEquivalentToExistingPredicateWithLeqQuantifiers()) {
			final IPredicate other = pc.getEquivalantLeqQuantifiedPredicate();
			if (other != predicate) {
				mLogger.fatal("Have " + other);
				mLogger.fatal("Want " + predicate);
				throw new AssertionError("There is already an" + " equivalent predicate");
			}
		} else if (pc.isEquivalentToExistingPredicateWithGtQuantifiers()) {
			if (pc.getEquivalantGtQuantifiedPredicate() != predicate) {
				throw new AssertionError("There is already an" + " equivalent predicate");
			}
		} else {
			addNewPredicate(predicate, predicate.getFormula(), predicate.getFormula(), pc.getImpliedPredicates(),
					pc.getExpliedPredicates());
		}
		mPredicateUnifierBenchmarkGenerator.incrementDeclaredPredicates();
	}

	/**
	 * GetOrConstruct a predicate that is a conjunction of IPredicates that were construction by (resp. declared in)
	 * this PredicateUnifier.
	 */
	@Override
	public IPredicate getOrConstructPredicateForConjunction(final Collection<IPredicate> conjunction) {
		final Set<IPredicate> minimalSubset =
				PosetUtils.filterMinimalElements(conjunction, mCoverageRelation.getPartialComperator())
						.collect(Collectors.toSet());
		if (minimalSubset.size() == 1) {
			return minimalSubset.iterator().next();
		}
		final HashMap<IPredicate, Validity> impliedPredicates = new HashMap<>();
		final HashMap<IPredicate, Validity> expliedPredicates = new HashMap<>();
		for (final IPredicate conjunct : minimalSubset) {
			// all predicates implied by the conjunct will also be implied
			// by the conjunction
			for (final IPredicate coverer : getCoverageRelation().getCoveringPredicates(conjunct)) {
				impliedPredicates.put(coverer, Validity.VALID);
			}

			// all predicates that do not imply the conjunct will also not imply
			// the conjunction
			for (final IPredicate noncoverer : ((CoverageRelation) getCoverageRelation())
					.getNonCoveredPredicates(conjunct)) {
				expliedPredicates.put(noncoverer, Validity.INVALID);
			}
		}
		return getOrConstructPredicateForConjunction(minimalSubset, impliedPredicates, expliedPredicates);
	}

	/**
	 * GetOrConstruct a predicate that is a disjunction of IPredicates that were constructed by (resp. declared in) this
	 * PredicateUnifier.
	 */
	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		final Set<IPredicate> minimalSubset =
				PosetUtils.filterMaximalElements(disjunction, mCoverageRelation.getPartialComperator())
						.collect(Collectors.toSet());
		if (minimalSubset.size() == 1) {
			return minimalSubset.iterator().next();
		}
		final HashMap<IPredicate, Validity> impliedPredicates = new HashMap<>();
		final HashMap<IPredicate, Validity> expliedPredicates = new HashMap<>();
		for (final IPredicate disjunct : minimalSubset) {
			for (final IPredicate knownPredicate : mKnownPredicates) {
				{
					// if (knownPredicate ==> disjunct) then the knownPredicate
					// will also imply the disjunction
					final Validity validity = getCoverageRelation().isCovered(knownPredicate, disjunct);
					if (validity == Validity.VALID) {
						expliedPredicates.put(knownPredicate, Validity.VALID);
					}
				}
				{
					// if !(disjunct ==> knownPredicate) then disjunction
					// will also not imply the knownPredicate
					final Validity validity = getCoverageRelation().isCovered(disjunct, knownPredicate);
					if (validity == Validity.INVALID) {
						impliedPredicates.put(knownPredicate, Validity.INVALID);
					}
				}
			}
		}
		return getOrConstructPredicateForDisjunction(minimalSubset, impliedPredicates, expliedPredicates);
	}

	/**
	 * Returns true iff each free variables corresponds to a BoogieVar in vars. Throws an Exception otherwise.
	 */
	private boolean varsIsSupersetOfFreeTermVariables(final Term term, final Set<IProgramVar> vars) {
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = mSymbolTable.getProgramVar(tv);
			if (bv == null) {
				throw new AssertionError("Variable " + tv + " has no corresponding BoogieVar, hence seems "
						+ "to be some auxiliary variable and may not "
						+ "occur unquantified in the formula of a predicate");
			}
			if (!vars.contains(bv)) {
				throw new AssertionError("Variable " + tv + " does not occur in vars");
			}
		}
		return true;
	}

	@Override
	public IPredicate getOrConstructPredicate(final IPredicate predicate) {
		if (mKnownPredicates.contains(predicate)) {
			return predicate;
		}
		return getOrConstructPredicate(predicate.getFormula(), null, null, predicate);
	}

	/**
	 * Get the predicate for term. If there is not yet a predicate for term, construct the predicate using vars.
	 *
	 * @param vars
	 *            The BoogieVars of the TermVariables contained in term.
	 * @param proc
	 *            All procedures of which vars contains local variables.
	 */
	@Override
	public IPredicate getOrConstructPredicate(final Term term) {
		return getOrConstructPredicate(term, null, null, null);
	}

	/**
	 * Variant of getOrConstruct methods where we can provide information about implied/explied predicates.
	 */
	private IPredicate getOrConstructPredicate(final Term term, final HashMap<IPredicate, Validity> impliedPredicates,
			final HashMap<IPredicate, Validity> expliedPredicates, final IPredicate originalPredicate) {

		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(term, mScript, mSymbolTable);
		mPredicateUnifierBenchmarkGenerator.continueTime();
		mPredicateUnifierBenchmarkGenerator.incrementGetRequests();
		assert varsIsSupersetOfFreeTermVariables(term, tvp.getVars());
		final Term withoutAnnotation = stripAnnotation(term);

		{
			IPredicate p = mTerm2Predicates.get(withoutAnnotation);
			if (p != null) {
				if (mDeprecatedPredicates.containsKey(p)) {
					p = mDeprecatedPredicates.get(p);
				}
				mPredicateUnifierBenchmarkGenerator.incrementSyntacticMatches();
				mPredicateUnifierBenchmarkGenerator.stopTime();
				return p;
			}
		}
		final Term commuNF = new CommuhashNormalForm(mServices, mScript).transform(withoutAnnotation);
		{
			IPredicate p = mTerm2Predicates.get(commuNF);
			if (p != null) {
				if (mDeprecatedPredicates.containsKey(p)) {
					p = mDeprecatedPredicates.get(p);
				}
				mPredicateUnifierBenchmarkGenerator.incrementSyntacticMatches();
				mPredicateUnifierBenchmarkGenerator.stopTime();
				return p;
			}
		}

		final PredicateComparison pc =
				new PredicateComparison(commuNF, tvp.getVars(), impliedPredicates, expliedPredicates);
		if (pc.isEquivalentToExistingPredicateWithLeqQuantifiers()) {
			mPredicateUnifierBenchmarkGenerator.incrementSemanticMatches();
			mPredicateUnifierBenchmarkGenerator.stopTime();
			return pc.getEquivalantLeqQuantifiedPredicate();
		}
		final IPredicate result;
		assert !SmtUtils.isTrueLiteral(commuNF) : "illegal predicate: true";
		assert !SmtUtils.isFalseLiteral(commuNF) : "illegal predicate: false";
		assert !mTerm2Predicates.containsKey(commuNF);
		final Term simplifiedTerm;
		if (pc.isIntricatePredicate()) {
			simplifiedTerm = commuNF;
		} else {
			try {
				final Term tmp = SmtUtils.simplify(mMgnScript, commuNF, mServices, mSimplificationTechnique);
				simplifiedTerm = new CommuhashNormalForm(mServices, mScript).transform(tmp);
			} catch (final ToolchainCanceledException tce) {
				tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), "unifying predicates"));
				throw tce;
			}
		}
		result = constructNewPredicate(simplifiedTerm, originalPredicate);
		if (pc.isEquivalentToExistingPredicateWithGtQuantifiers()) {
			mDeprecatedPredicates.put(pc.getEquivalantGtQuantifiedPredicate(), result);
			mPredicateUnifierBenchmarkGenerator.incrementDeprecatedPredicates();
		}
		addNewPredicate(result, term, simplifiedTerm, pc.getImpliedPredicates(), pc.getExpliedPredicates());
		assert new CheckClosedTerm().isClosed(result.getClosedFormula());
		assert varsIsSupersetOfFreeTermVariables(result.getFormula(), result.getVars());
		mPredicateUnifierBenchmarkGenerator.incrementConstructedPredicates();
		mPredicateUnifierBenchmarkGenerator.stopTime();
		return result;
	}

	protected IPredicate constructNewPredicate(final Term term, final IPredicate originalPredicate) {
		return mPredicateFactory.newPredicate(term);
	}

	protected IPredicate getOrConstructPredicateForConjunction(final Set<IPredicate> minimalSubset,
			final HashMap<IPredicate, Validity> impliedPredicates,
			final HashMap<IPredicate, Validity> expliedPredicates) {
		final IPredicate and = mPredicateFactory.and(minimalSubset);
		return getOrConstructPredicate(and.getFormula(), impliedPredicates, expliedPredicates, and);
	}

	protected IPredicate getOrConstructPredicateForDisjunction(final Set<IPredicate> minimalSubset,
			final HashMap<IPredicate, Validity> impliedPredicates,
			final HashMap<IPredicate, Validity> expliedPredicates) {
		final IPredicate or = mPredicateFactory.or(minimalSubset);
		return getOrConstructPredicate(or.getFormula(), impliedPredicates, expliedPredicates, or);
	}

	private static Term stripAnnotation(final Term term) {
		final Term withoutAnnotation;
		if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annotatedTerm = (AnnotatedTerm) term;
			final Annotation[] annotations = annotatedTerm.getAnnotations();
			if (annotations.length == 1) {
				if (":quoted".equals(annotations[0].getKey())) {
					withoutAnnotation = annotatedTerm.getSubterm();
				} else {
					throw new UnsupportedOperationException();
				}
			} else {
				throw new UnsupportedOperationException();
			}
		} else {
			withoutAnnotation = term;
		}
		return withoutAnnotation;
	}

	/**
	 * Add a new predicate.
	 *
	 * @param pred
	 * @param simplifiedTerm
	 * @param term
	 * @param implied
	 *            Set of pairs (p,val) such that val is the validity of the implication pred ==> p.
	 * @param explied
	 *            Set of pairs (p,val) such that val is the validity of the explication pred <== p.
	 */
	private void addNewPredicate(final IPredicate pred, final Term term, final Term simplifiedTerm,
			final Map<IPredicate, Validity> implied, final Map<IPredicate, Validity> explied) {
		mTerm2Predicates.put(term, pred);
		mTerm2Predicates.put(simplifiedTerm, pred);
		mCoverageRelation.addPredicate(pred, implied, explied);
		assert !mKnownPredicates.contains(pred) : "predicate already known";
		mKnownPredicates.add(pred);
	}

	// Matthias 2016-11-4: at the moment we believe that for the backward
	// predicates universal quantification is better than existential
	// quantification.
	private static boolean thisIsLessQuantifiedThanOther(final Term thisTerm, final Term otherTerm) {
		final ContainsQuantifier thisQuantifierCheck = new ContainsQuantifier();
		thisQuantifierCheck.containsQuantifier(thisTerm);
		final ContainsQuantifier otherQuantifierCheck = new ContainsQuantifier();
		otherQuantifierCheck.containsQuantifier(otherTerm);
		return thisQuantifierCheck.getFirstQuantifierFound() == QuantifiedFormula.FORALL
				&& otherQuantifierCheck.getFirstQuantifierFound() == QuantifiedFormula.EXISTS;
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		final StringBuilder builder = new StringBuilder();
		builder.append(PredicateUnifierStatisticsType.getInstance()
				.prettyprintBenchmarkData(mPredicateUnifierBenchmarkGenerator));
		builder.append(mCoverageRelation.getCoverageRelationStatistics());
		return builder.toString();
	}

	/**
	 * We call a predicate "intricate" if we were unable to find our if it is equivalent to "true" or if we were unable
	 * to find out it it is equivalent to "false".
	 */
	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		final Validity equivalentToTrue = getCoverageRelation().isCovered(mTruePredicate, pred);
		final Validity equivalentToFalse = getCoverageRelation().isCovered(pred, mFalsePredicate);
		return equivalentToTrue == Validity.UNKNOWN || equivalentToFalse == Validity.UNKNOWN;
	}

	/**
	 * Given a term "cut up" all its conjuncts. We bring the term in CNF and return an IPredicate for each conjunct.
	 */
	@Override
	public Set<IPredicate> cannibalize(final boolean splitNumericEqualities, final Term term) {
		final Term[] conjuncts = SmtUtils.cannibalize(mMgnScript, mServices, splitNumericEqualities, term);
		final Set<IPredicate> result = new HashSet<>();
		for (final Term conjunct : conjuncts) {
			final IPredicate predicate = getOrConstructPredicate(conjunct);
			result.add(predicate);
		}
		return result;
	}

	@Override
	public Set<IPredicate> cannibalizeAll(final boolean splitNumericEqualities,
			final Collection<IPredicate> predicates) {
		final Set<IPredicate> result = new HashSet<>();
		for (final IPredicate pred : predicates) {
			result.addAll(cannibalize(splitNumericEqualities, pred.getFormula()));
		}
		return result;
	}

	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		return mCoverageRelation;
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		return mPredicateUnifierBenchmarkGenerator;
	}

	/**
	 * @return the predicateFactory
	 */
	@Override
	public BasicPredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	/**
	 * Construct a new predicate for the given term.
	 *
	 * @param term
	 *            Term for which new predicate is constructed. This term has to be simplified (resp. will not be further
	 *            simplified) and has to be different (not semantically equivalent) from all predicates known by this
	 *            predicate unifier.
	 * @param impliedPredicates
	 *            Result of the implication (term ==> p) for each known predicate p.
	 * @param expliedPredicates
	 *            Result of the implication (p ==> term) for each known predicate p.
	 * @return The predicate that was constructed for the term p.
	 */
	@Override
	public IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
			final Map<IPredicate, Validity> expliedPredicates) {
		if (mTerm2Predicates.get(term) != null) {
			throw new AssertionError("PredicateUnifier already knows a predicate for " + term);
		}
		if (impliedPredicates.size() != mKnownPredicates.size()) {
			throw new AssertionError(
					"Inconsistent number of IPredicates known by PredicateUnifier and number of provided implications");
		}
		if (expliedPredicates.size() != mKnownPredicates.size()) {
			throw new AssertionError(
					"Inconsistent number of IPredicates known by PredicateUnifier and number of provided explications");
		}
		final IPredicate predicate = constructNewPredicate(term, null);
		addNewPredicate(predicate, term, term, impliedPredicates, expliedPredicates);
		mPredicateUnifierBenchmarkGenerator.incrementDeclaredPredicates();
		return predicate;
	}

	public class CoverageRelation implements IPredicateCoverageChecker {

		private final NestedMap2<IPredicate, IPredicate, Validity> mLhs2RhsValidity = new NestedMap2<>();
		private final HashRelation<IPredicate, IPredicate> mImpliedPredicates = new HashRelation<>();
		private final HashRelation<IPredicate, IPredicate> mExpliedPredicates = new HashRelation<>();
		private final HashRelation<IPredicate, IPredicate> mNotImpliedPredicates = new HashRelation<>();
		private final HashRelation<IPredicate, IPredicate> mNotExpliedPredicates = new HashRelation<>();

		void addPredicate(final IPredicate pred, final Map<IPredicate, Validity> implied,
				final Map<IPredicate, Validity> explied) {
			assert !mKnownPredicates.contains(pred) : "predicate already known";
			assert coverageMapIsComplete();
			for (final IPredicate known : mKnownPredicates) {
				final Validity implies = implied.get(known);
				assert implies != null : "unknown implies for " + known;
				final Validity explies = explied.get(known);
				assert explies != null : "unknown explies for " + known;
				final Validity oldimpl = mLhs2RhsValidity.put(pred, known, implies);
				assert oldimpl == null : "entry existed !";
				final Validity oldexpl = mLhs2RhsValidity.put(known, pred, explies);
				assert oldexpl == null : "entry existed !";
				if (implies == Validity.VALID) {
					mImpliedPredicates.addPair(pred, known);
					mExpliedPredicates.addPair(known, pred);
				} else if (implies == Validity.INVALID) {
					mNotImpliedPredicates.addPair(pred, known);
					mNotExpliedPredicates.addPair(known, pred);
				}
				if (explies == Validity.VALID) {
					mImpliedPredicates.addPair(known, pred);
					mExpliedPredicates.addPair(pred, known);
				} else if (implies == Validity.INVALID) {
					mNotImpliedPredicates.addPair(known, pred);
					mNotExpliedPredicates.addPair(pred, known);
				}
			}
			mImpliedPredicates.addPair(pred, pred);
			mExpliedPredicates.addPair(pred, pred);
			assert coverageMapIsComplete();
		}

		@Override
		public Validity isCovered(final IPredicate lhs, final IPredicate rhs) {
			if (lhs.equals(rhs)) {
				return Validity.VALID;
			}
			final Validity result = mLhs2RhsValidity.get(lhs, rhs);
			if (result == null) {
				throw new AssertionError("at least one of both input predicates is unknown: " + lhs + " or " + rhs);
			}
			return result;
		}

		@Override
		public Set<IPredicate> getCoveringPredicates(final IPredicate pred) {
			return mImpliedPredicates.getImage(pred);
		}

		public Set<IPredicate> getNonCoveringPredicates(final IPredicate pred) {
			return mNotImpliedPredicates.getImage(pred);
		}

		@Override
		public Set<IPredicate> getCoveredPredicates(final IPredicate pred) {
			return mExpliedPredicates.getImage(pred);
		}

		public Set<IPredicate> getNonCoveredPredicates(final IPredicate pred) {
			return mNotExpliedPredicates.getImage(pred);
		}

		public CoverageRelationStatistics getCoverageRelationStatistics() {
			return new CoverageRelationStatistics(mLhs2RhsValidity);
		}

		private boolean coverageMapIsComplete() {
			boolean nothingMissing = true;
			for (final IPredicate p1 : mKnownPredicates) {
				for (final IPredicate p2 : mKnownPredicates) {
					if (p1 != p2) {
						final Validity validity = mLhs2RhsValidity.get(p1, p2);
						assert validity != null : "value missing for pair " + p1 + ", " + p2;
						if (validity == null) {
							nothingMissing = false;
						}
					}
				}
			}
			return nothingMissing;
		}

		@Override
		public IPartialComparator<IPredicate> getPartialComperator() {
			return (o1, o2) -> {
				if (o1.equals(o2)) {
					return ComparisonResult.EQUAL;
				}
				final Validity implies = mLhs2RhsValidity.get(o1, o2);
				if (implies == null) {
					throwAssertionErrorWithMessage(o1, o2);
				}
				final Validity explies = mLhs2RhsValidity.get(o2, o1);
				if (explies == null) {
					throwAssertionErrorWithMessage(o1, o2);
				}
				if (implies == Validity.VALID) {
					if (explies == Validity.VALID) {
						return ComparisonResult.EQUAL;
					}
					return ComparisonResult.STRICTLY_SMALLER;
				}
				if (explies == Validity.VALID) {
					return ComparisonResult.STRICTLY_GREATER;
				}
				return ComparisonResult.INCOMPARABLE;
			};
		}

		/**
		 * In case the pair of input predicates is not in the coverage relation use this method to throw an
		 * AssertionError with a more detailed error message.
		 *
		 */
		private void throwAssertionErrorWithMessage(final IPredicate o1, final IPredicate o2) throws AssertionError {
			if (!mLhs2RhsValidity.keySet().contains(o1)) {
				throw new AssertionError(
						"PredicateUnifier does not know the following predicate " + String.valueOf(o1));
			}
			if (!mLhs2RhsValidity.keySet().contains(o2)) {
				throw new AssertionError(
						"PredicateUnifier does not know the following predicate " + String.valueOf(o2));
			}
			throw new AssertionError("PredicateUnifier is in inconsistent state");
		}

		@Override
		public HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation() {
			return new HashRelation<>(mImpliedPredicates);
		}
	}

	public class CoverageRelationStatistics {
		private final int mValidCoverageRelations;
		private final int mInvalidCoverageRelations;
		private final int mUnknownCoverageRelations;
		private final int mNotCheckedCoverageRelations;

		public CoverageRelationStatistics(final NestedMap2<IPredicate, IPredicate, Validity> lhs2RhsValidity) {
			int invalid = 0;
			int valid = 0;
			int unknown = 0;
			int notChecked = 0;
			for (final Triple<IPredicate, IPredicate, Validity> entry : lhs2RhsValidity.entrySet()) {
				switch (entry.getThird()) {
				case INVALID:
					invalid++;
					break;
				case NOT_CHECKED:
					notChecked++;
					break;
				case UNKNOWN:
					unknown++;
					break;
				case VALID:
					valid++;
					break;
				default:
					throw new AssertionError();
				}
			}
			mValidCoverageRelations = valid;
			mInvalidCoverageRelations = invalid;
			mUnknownCoverageRelations = unknown;
			mNotCheckedCoverageRelations = notChecked;
		}

		@Override
		public String toString() {
			return String.format("CoverageRelationStatistics Valid=%s, Invalid=%s, Unknown=%s, NotChecked=%s, Total=%s",
					mValidCoverageRelations, mInvalidCoverageRelations, mUnknownCoverageRelations,
					mNotCheckedCoverageRelations, mValidCoverageRelations + mInvalidCoverageRelations
							+ mUnknownCoverageRelations + mNotCheckedCoverageRelations);
		}

	}

	/**
	 * Compare Term term whose free variables represent the BoogieVars vars with all predicates that this Predicate
	 * unifier knows. If there exists a predicate for which we can prove that it is equivalent to term, this predicate
	 * is returned. Otherwise we return null and HashMaps impliedPredicats and expliedPredicates are filled with
	 * information about implications between term and existing Predicates. ImpliedPredicates will be filled with all
	 * IPredicates implied by term. ImpliedPredicates will be filled with all IPredicates that imply term.
	 *
	 * @return
	 */
	private final class PredicateComparison {
		private final Term mTerm;
		private final Term mClosedTerm;
		private final boolean mTermContainsQuantifiers;
		private final HashMap<IPredicate, Validity> mImpliedPredicates;
		private final HashMap<IPredicate, Validity> mExpliedPredicates;
		private final IPredicate mEquivalentLeqQuantifiedPredicate;
		private IPredicate mEquivalentGtQuantifiedPredicate;
		private boolean mIsIntricatePredicate;

		/**
		 * Compare a new term/vars with all known predicates of this PredicateUnifier. Information about predicates that
		 * are implied/explied by term can be provided as an input by the Maps impliedPredicates/expliedPredicates both
		 * maps will be modified by (new predicates added) by this method.
		 */
		PredicateComparison(final Term term, final Set<IProgramVar> vars,
				final HashMap<IPredicate, Validity> impliedPredicates,
				final HashMap<IPredicate, Validity> expliedPredicates) {
			if (impliedPredicates == null) {
				if (expliedPredicates != null) {
					throw new IllegalArgumentException("both or none null");
				}
				mImpliedPredicates = new HashMap<>();
				mExpliedPredicates = new HashMap<>();
			} else {
				mImpliedPredicates = impliedPredicates;
				mExpliedPredicates = expliedPredicates;
			}
			mTerm = term;
			mClosedTerm = PredicateUtils.computeClosedFormula(term, vars, mScript);
			mTermContainsQuantifiers = new ContainsQuantifier().containsQuantifier(term);

			mScript.echo(new QuotedObject("begin unification"));
			mEquivalentLeqQuantifiedPredicate = compare();
			mScript.echo(new QuotedObject("end unification"));
		}

		public Term getClosedTerm() {
			if (mEquivalentLeqQuantifiedPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}
			return mClosedTerm;
		}

		public HashMap<IPredicate, Validity> getImpliedPredicates() {
			if (mEquivalentLeqQuantifiedPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}
			return mImpliedPredicates;
		}

		public HashMap<IPredicate, Validity> getExpliedPredicates() {
			if (mEquivalentLeqQuantifiedPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}
			return mExpliedPredicates;
		}

		public IPredicate getEquivalantLeqQuantifiedPredicate() {
			if (mEquivalentLeqQuantifiedPredicate == null) {
				throw new IllegalAccessError("accessible only if equivalent to existing predicate");
			}
			return mEquivalentLeqQuantifiedPredicate;
		}

		public IPredicate getEquivalantGtQuantifiedPredicate() {
			if (mEquivalentGtQuantifiedPredicate == null) {
				throw new IllegalAccessError("accessible only if equivalent to existing predicate");
			}
			return mEquivalentGtQuantifiedPredicate;
		}

		public boolean isIntricatePredicate() {
			if (mEquivalentLeqQuantifiedPredicate != null) {
				throw new IllegalAccessError("not accessible, we found an equivalent predicate");
			}
			return mIsIntricatePredicate;
		}

		public boolean isEquivalentToExistingPredicateWithLeqQuantifiers() {
			return mEquivalentLeqQuantifiedPredicate != null;
		}

		public boolean isEquivalentToExistingPredicateWithGtQuantifiers() {
			return mEquivalentGtQuantifiedPredicate != null;
		}

		private IPredicate compare() {
			// check if false
			final Validity impliesFalse = mImplicationChecker.checkImplication(mTerm, mClosedTerm, false,
					mFalsePredicate.getFormula(), mFalsePredicate.getClosedFormula(), false);
			switch (impliesFalse) {
			case VALID:
				return mFalsePredicate;
			case INVALID:
				mImpliedPredicates.put(mFalsePredicate, Validity.INVALID);
				break;
			case UNKNOWN:
				mLogger.warn(new DebugMessage("unable to prove that {0} is different from false", mClosedTerm));
				mImpliedPredicates.put(mFalsePredicate, Validity.UNKNOWN);
				mIsIntricatePredicate = true;
				break;
			case NOT_CHECKED:
				throw new AssertionError("we wanted it checked");
			default:
				throw new AssertionError("unknown case");
			}
			// every predicate is implied by false
			mExpliedPredicates.put(mFalsePredicate, Validity.VALID);

			// check if true
			final Validity impliedByTrue = mImplicationChecker.checkImplication(mTruePredicate.getFormula(),
					mTruePredicate.getClosedFormula(), false, mTerm, mClosedTerm, false);
			switch (impliedByTrue) {
			case VALID:
				return mTruePredicate;
			case INVALID:
				mExpliedPredicates.put(mTruePredicate, Validity.INVALID);
				break;
			case UNKNOWN:
				mLogger.warn(new DebugMessage("unable to prove that {0} is different from true", mClosedTerm));
				mExpliedPredicates.put(mTruePredicate, Validity.UNKNOWN);
				mIsIntricatePredicate = true;
				break;
			case NOT_CHECKED:
				throw new AssertionError("we wanted it checked");
			default:
				throw new AssertionError("unknown case");
			}
			// every predicate implies true
			mImpliedPredicates.put(mTruePredicate, Validity.VALID);

			// if predicate is intricate we do not compare against others
			if (mIsIntricatePredicate) {
				for (final IPredicate other : mKnownPredicates) {
					if (other == mTruePredicate || other == mFalsePredicate) {
						continue;
					}
					mImpliedPredicates.put(other, Validity.NOT_CHECKED);
					mExpliedPredicates.put(other, Validity.NOT_CHECKED);
				}
				mPredicateUnifierBenchmarkGenerator.incrementIntricatePredicates();
				return null;
			}

			for (final IPredicate other : mKnownPredicates) {
				if (other == mTruePredicate || other == mFalsePredicate) {
					continue;
				}
				// we do not compare against intricate predicates
				if (PredicateUnifier.this.isIntricatePredicate(other)) {
					mImpliedPredicates.put(other, Validity.NOT_CHECKED);
					mExpliedPredicates.put(other, Validity.NOT_CHECKED);
					continue;
				}
				checkTimeout(mClosedTerm);
				final Term otherClosedTerm = other.getClosedFormula();
				Validity implies = mImpliedPredicates.get(other);
				if (implies == null) {
					implies = mImplicationChecker.checkImplication(mTerm, mClosedTerm, false, other.getFormula(),
							other.getClosedFormula(), false);
					if (implies == Validity.VALID) {
						// if (this ==> other) and (other ==> impliedByOther) then
						// we conclude (this ==> impliedByOther)
						for (final IPredicate impliedByOther : getCoverageRelation().getCoveringPredicates(other)) {
							if (impliedByOther != other) {
								final Validity oldValue = mImpliedPredicates.put(impliedByOther, Validity.VALID);
								if (oldValue == null || oldValue == Validity.UNKNOWN) {
									mPredicateUnifierBenchmarkGenerator.incrementImplicationChecksByTransitivity();
								} else {
									assert oldValue == Validity.VALID : "implication result by transitivity: "
											+ Validity.VALID + " old implication result: " + oldValue;
								}
							}
						}
					} else if (implies == Validity.INVALID) {
						// if !(this ==> other) and (expliedbyOther ==> other)
						// we conclude !(this ==> expliedbyOther)
						for (final IPredicate expliedByOther : getCoverageRelation().getCoveredPredicates(other)) {
							if (expliedByOther != other) {
								final Validity oldValue = mImpliedPredicates.put(expliedByOther, Validity.INVALID);
								if (oldValue == null || oldValue == Validity.UNKNOWN) {
									mPredicateUnifierBenchmarkGenerator.incrementImplicationChecksByTransitivity();
								} else {
									assert oldValue == Validity.INVALID : "implication result by transitivity: "
											+ Validity.INVALID + " old implication result: " + oldValue;
								}
							}
						}
					}
					mImpliedPredicates.put(other, implies);
				}
				Validity explies = mExpliedPredicates.get(other);
				if (explies == null) {
					explies = mImplicationChecker.checkImplication(other.getFormula(), other.getClosedFormula(), false,
							mTerm, mClosedTerm, false);
					if (explies == Validity.VALID) {
						// if (other ==> this) and (expliedByOther ==> other)
						// we conclude (expliedByOther ==> this)
						for (final IPredicate expliedByOther : getCoverageRelation().getCoveredPredicates(other)) {
							if (expliedByOther != other) {
								final Validity oldValue = mExpliedPredicates.put(expliedByOther, Validity.VALID);
								if (oldValue == null || oldValue == Validity.UNKNOWN) {
									mPredicateUnifierBenchmarkGenerator.incrementImplicationChecksByTransitivity();
								} else {
									assert oldValue == Validity.VALID : "explication result by transitivity: "
											+ Validity.VALID + " old explication result: " + oldValue;
								}
							}
						}
					} else if (explies == Validity.INVALID) {
						// if !(other ==> this) and (other ==> impliedByOther)
						// we conclude !(impliedByOther ==> this)
						for (final IPredicate impliedByOther : getCoverageRelation().getCoveringPredicates(other)) {
							if (impliedByOther != other) {
								final Validity oldValue = mExpliedPredicates.put(impliedByOther, Validity.INVALID);
								if (oldValue == null || oldValue == Validity.UNKNOWN) {
									mPredicateUnifierBenchmarkGenerator.incrementImplicationChecksByTransitivity();
								} else {
									assert oldValue == Validity.INVALID : "explication result by transitivity: "
											+ Validity.INVALID + " old explication result: " + oldValue;
								}
							}
						}
					}
					mExpliedPredicates.put(other, explies);
				}
				if (implies == Validity.VALID && explies == Validity.VALID) {
					if (mDeprecatedPredicates.containsKey(other)) {
						return mDeprecatedPredicates.get(other);
					}
					final boolean otherContainsQuantifiers =
							new ContainsQuantifier().containsQuantifier(other.getFormula());
					if (!otherContainsQuantifiers || mTermContainsQuantifiers
							&& !thisIsLessQuantifiedThanOther(mClosedTerm, otherClosedTerm)) {
						return other;
					}
					if (mEquivalentGtQuantifiedPredicate == null) {
						mEquivalentGtQuantifiedPredicate = other;
					} else {
						throw new AssertionError("at most one deprecated predicate");
					}
				}
			}
			// no predicate was equivalent
			return null;
		}

		private void checkTimeout(final Term closedTerm) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				final String quantifierInformation = generateQuantifierInformation(closedTerm);
				throw new ToolchainCanceledException(this.getClass(), "comparing new predicate ("
						+ quantifierInformation + ") to " + mKnownPredicates.size() + " known predicates");
			}
		}

		private String generateQuantifierInformation(final Term closedTerm) {
			final String result;
			final Term pnf = new PrenexNormalForm(mMgnScript).transform(closedTerm);
			if (pnf instanceof QuantifiedFormula) {
				final QuantifierSequence qs = new QuantifierSequence(mScript, pnf);
				result = "quantified with " + (qs.getNumberOfQuantifierBlocks() - 1) + "quantifier alternations";
			} else {
				result = "quantifier-free";
			}
			return result;
		}
	}

}
