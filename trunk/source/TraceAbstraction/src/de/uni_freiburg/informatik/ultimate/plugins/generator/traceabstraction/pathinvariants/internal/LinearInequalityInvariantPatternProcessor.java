/*
 * Copyright (C) 2015 David Zschocke
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * A {@link IInvariantPatternProcessor} using patterns composed of linear
 * inequalities on a linear approximation of the program.
 * 
 * The outer collection within the invariant pattern type represents a
 * disjunction, the inner one a conjunction. Within the inner conjunction, there
 * are strict and non-strict inequalities. These collections are generated
 * according to a {@link ILinearInequalityInvariantPatternStrategy}.
 * @author David Zschocke, Dirk Steinmetz, Matthias Heizmann, Betim Musa
 */
public final class LinearInequalityInvariantPatternProcessor
extends
AbstractSMTInvariantPatternProcessor<Collection<Collection<AbstractLinearInvariantPattern>>> {

	private static final String PREFIX = "liipp_";
	private static final String PREFIX_SEPARATOR = "_";

	private static final String ANNOT_PREFIX = "LIIPP_Annot";
	private int mAnnotTermCounter;
	/**
	 * Stores the mapping from annotation of a term to the original term. It is used to restore the original terms from the unsat core.
	 */
	private Map<String, Term> mAnnotTerm2OriginalTerm;
	/**
	 * @see {@link MotzkinTransformation}.mMotzkinCoeffiecients2LinearInequalities
	 */
	private final Map<String, LinearInequality> mMotzkinCoefficients2LinearInequalities;

	private final boolean mUseVarsFromUnsatCore;


	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mSolver;
	private final ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> mStrategy;
	private final LinearTransition mPrecondition;
	private final LinearTransition mPostcondition;
	private final CachedTransFormulaLinearizer mLinearizer;
	//	private final ControlFlowGraph cfg;

	// New CFG
	private final List<IcfgInternalAction> mTransitions;

	/**
	 * The pattern variables, that is the coefficients of program- and helper
	 * variables.
	 */
	private final Collection<Term> mPatternVariables;
	/**
	 * The pattern coefficients, that is the program- and helper variables.
	 */
	private final Set<IProgramVar> mPatternCoefficients;
	private Map<Term, Rational> mValuation;
	private Collection<Collection<AbstractLinearInvariantPattern>> mEntryInvariantPattern;
	private Collection<Collection<AbstractLinearInvariantPattern>> mExitInvariantPattern;
	private int mPrefixCounter;
	private int mCurrentRound;
	private int mMaxRounds;
	private final boolean mUseNonlinearConstraints; 
	private final boolean mSimplifySatisfyingAssignment = true;
	/**
	 * If set to true, we always construct two copies of each invariant
	 * pattern, one strict inequality and one non-strict inequality.
	 * If set to false we use only one non-strict inequality.
	 */
	private final boolean mAlwaysStrictAndNonStrictCopies = false;
	private Collection<TermVariable> mVarsFromUnsatCore;
	private final IcfgLocation mStartLocation;
	private final IcfgLocation mErrorLocation;
	
	private static final boolean PRINT_CONSTRAINTS = false;
	
	/**
	 * Maps a location to a set of program variables which are <i> live </i> at that location.
	 */
	private Map<IcfgLocation, Set<IProgramVar>> mLocs2LiveVariables;
	private final boolean mUseLiveVariables;



	/**
	 * Creates a pattern processor using linear inequalities as patterns.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager to use with the predicateUnifier
	 * @param solver
	 *            SMT solver to use
	 * @param cfg
	 *            the ControlFlowGraph to generate an invariant map on
	 * @param precondition
	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of
	 *            cfg
	 * @param postcondition
	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
	 * @param strategy
	 *            The strategy to generate invariant patterns with
	 * @param useNonlinearConstraints
	 * 			  Kind of constraints that are used to specify invariant.
	 * @param storage 
	 * @param simplicationTechnique 
	 * @param xnfConversionTechnique 
	 * @param axioms 
	 * @param errorLocation 
	 * @param startLocation 
	 */
	public LinearInequalityInvariantPatternProcessor(
			final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final PredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit, final Collection<Term> axioms, 
			final Script solver,
			final List<IcfgLocation> locations, final List<IcfgInternalAction> transitions, final IPredicate precondition,
			final IPredicate postcondition,
			IcfgLocation startLocation, IcfgLocation errorLocation, final ILinearInequalityInvariantPatternStrategy strategy,
			final boolean useNonlinearConstraints,
			final boolean useVarsFromUnsatCore,
			final boolean useLiveVars,
			final Map<IcfgLocation, Set<IProgramVar>> mLocs2LiveVariables2,
			final SimplificationTechnique simplicationTechnique, 
			final XnfConversionTechnique xnfConversionTechnique) {
		super(predicateUnifier, csToolkit);
		this.mServices = services;
		mLogger = services.getLoggingService().getLogger(
				Activator.PLUGIN_ID);
		this.mSolver = solver;
		this.mStrategy = strategy;
		//		this.cfg = null;
		mTransitions = transitions;
		mStartLocation = startLocation;
		mErrorLocation = errorLocation;

		mPatternVariables = new ArrayList<>();
		mPatternCoefficients = new HashSet<>();

		mLinearizer = new CachedTransFormulaLinearizer(services, 
				csToolkit, axioms, storage, simplicationTechnique, xnfConversionTechnique);
		this.mPrecondition = mLinearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(precondition, csToolkit.getManagedScript()));
		this.mPostcondition = mLinearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(postcondition, csToolkit.getManagedScript()));

		mCurrentRound = -1;
		mMaxRounds = strategy.getMaxRounds();
		mUseNonlinearConstraints = useNonlinearConstraints;
		mUseVarsFromUnsatCore = useVarsFromUnsatCore;
		mAnnotTermCounter = 0;
		mAnnotTerm2OriginalTerm = new HashMap<>();
		mMotzkinCoefficients2LinearInequalities = new HashMap<>();
		mLocs2LiveVariables = mLocs2LiveVariables2;
		mUseLiveVariables = useLiveVars;
	}
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void startRound(final int round, final boolean useVarsFromUnsatCore, final Set<IProgramVar> varsFromUnsatCore) {

		resetSettings();
		mPatternVariables.clear();
		mEntryInvariantPattern = null;
		mExitInvariantPattern = null;
		mPrefixCounter = 0;
		mCurrentRound = round;

		// In the first round, linearize and populate
		// {@link #patternCoefficients}.
		if (round == 0) {
			mLogger.info( "[LIIPP] First round, linearizing...");
			mPatternCoefficients.clear();
			for (final IcfgInternalAction transition : mTransitions) {
				final LinearTransition lTransition = mLinearizer
						.linearize(transition.getTransformula());
				mPatternCoefficients.addAll(lTransition.getInVars().keySet());
				mPatternCoefficients.addAll(lTransition.getOutVars().keySet());
			}
			mPatternCoefficients.addAll(mPrecondition.getInVars().keySet());
			mPatternCoefficients.addAll(mPrecondition.getOutVars().keySet());
			mPatternCoefficients.addAll(mPostcondition.getInVars().keySet());
			mPatternCoefficients.addAll(mPostcondition.getOutVars().keySet());
			if (PRINT_CONSTRAINTS) {
				mLogger.info("Program variables are:");
				mLogger.info(mPatternCoefficients);
			}
			mLogger.info( "[LIIPP] Linearization complete.");
		}
		if (useVarsFromUnsatCore && varsFromUnsatCore != null) {
			mPatternCoefficients.retainAll(varsFromUnsatCore);
		}
	}

	/**
	 * Reset the solver and additionally reset the annotation term counter and the map mAnnotTerm2OriginalTerm
	 */
	private void resetSettings() {
		reinitializeSolver();
		// Reset annotation term counter
		mAnnotTermCounter = 0;
		// Reset map that stores the mapping from the annotated term to the original term.
		mAnnotTerm2OriginalTerm = new HashMap<>();
		// Reset settings of strategy
		mStrategy.resetSettings();
	}

	/**
	 * Generates a new prefix, which is guaranteed (within prefixes generated
	 * through this method on one single instance) to be unique within the
	 * current round.
	 * 
	 * @return unique prefix (within this instance and round)
	 */
	protected String newPrefix() {
		return PREFIX + (mPrefixCounter++) + PREFIX_SEPARATOR;
	}



	/**
	 * Transforms a pattern into a DNF of linear inequalities relative to a
	 * given mapping of {@link IProgramVar}s involved.
	 * 
	 * @param pattern
	 *            the pattern to transform
	 * @param mapping
	 *            the mapping to use
	 * @return transformed pattern, equivalent to the pattern under the mapping
	 */
	private static Collection<Collection<LinearInequality>> mapPattern(
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern,
			final Map<IProgramVar, Term> mapping, Map<IProgramVar, Term> lastOccurrencesOfTermVariables) {
		final Collection<Collection<LinearInequality>> result = new ArrayList<>(
				pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<LinearInequality> mappedConjunct = new ArrayList<>(
					conjunct.size());
			for (final AbstractLinearInvariantPattern base : conjunct) {
//				if (base instanceof LinearPatternWithConstantCoefficients) {
//					mappedConjunct.add(((LinearPatternWithConstantCoefficients)base).getLinearInequality(mapping, lastOccurrencesOfTermVariables));
//				} else {
					mappedConjunct.add(base.getLinearInequality(mapping));
//				}
				
			}
			result.add(mappedConjunct);
		}
		return result;

	}

	/**
	 * Transforms and negates a pattern into a DNF of linear inequalities
	 * relative to a given mapping of {@link IProgramVar}s involved.
	 * 
	 * @param pattern
	 *            the pattern to transform
	 * @param mapping
	 *            the mapping to use
	 * @return transformed pattern, equivalent to the negated pattern under the
	 *         mapping
	 */
	private static Collection<Collection<LinearInequality>> mapAndNegatePattern(
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern,
			final Map<IProgramVar, Term> mapping, Map<IProgramVar, Term> lastOccurrencesOfTermVariables) {
		// This is the trivial algorithm (expanding). Feel free to optimize ;)
		// 1. map Pattern, result is dnf
		final Collection<Collection<LinearInequality>> mappedPattern = mapPattern(
				pattern, mapping, lastOccurrencesOfTermVariables);
		// 2. negate every LinearInequality, result is a cnf
		final Collection<Collection<LinearInequality>> cnfAfterNegation = new ArrayList<>(
				mappedPattern.size());
		for (final Collection<LinearInequality> conjunct : mappedPattern) {
			final Collection<LinearInequality> disjunctWithNegatedLinearInequalities = new ArrayList<>(
					conjunct.size());
			for (final LinearInequality li : conjunct) {
				// copy original linear inequality
				final LinearInequality negatedLi = new LinearInequality(li);
				negatedLi.negate();
				disjunctWithNegatedLinearInequalities.add(negatedLi);
			}
			cnfAfterNegation.add(disjunctWithNegatedLinearInequalities);
		}
		// 3. expand the cnf to get a dnf
		final Collection<Collection<LinearInequality>> mappedAndNegatedPattern = expandCnfToDnf(cnfAfterNegation);
		assert mappedAndNegatedPattern != null;
		// 4. return the resulting dnf as the solution
		return mappedAndNegatedPattern;
	}



	/**
	 * Transforms a conjunction to an equivalent term representing a disjunction
	 * of the motzkin transformations of the expanded DNF conjuncts.
	 * 
	 * @see #expandConjunction(Collection...)
	 * @see MotzkinTransformation
	 * @param dnfs
	 *            DNFs to conjunct together
	 * @return term equivalent to the negated term
	 */
	@SafeVarargs
	private final Term transformNegatedConjunction(
			final Collection<Collection<LinearInequality>>... dnfs) {
		mLogger.info( "[LIIPP] About to invoke motzkin:");
		for (final Collection<? extends Collection<LinearInequality>> dnf : dnfs) {
			mLogger.info( "[LIIPP] DNF to transform: " + dnf);
		}
		final Collection<Collection<LinearInequality>> conjunctionDNF = expandConjunction(dnfs);

		// Apply Motzkin and generate the conjunction of the resulting Terms
		final Collection<Term> resultTerms = new ArrayList<Term>(
				conjunctionDNF.size());
		final AnalysisType analysisType = mUseNonlinearConstraints ? 
				AnalysisType.NONLINEAR : AnalysisType.LINEAR;
		for (final Collection<LinearInequality> conjunct : conjunctionDNF) {
			mLogger.info( "[LIIPP] Transforming conjunct "
					+ conjunct);
			final MotzkinTransformation transformation = new MotzkinTransformation(
					mSolver, analysisType, false);
			transformation.add_inequalities(conjunct);
			resultTerms.add(transformation.transform(new Rational[0]));
			mMotzkinCoefficients2LinearInequalities.putAll(transformation.getMotzkinCoeffiecients2LinearInequalities());
		}
		return SmtUtils.and(mSolver, resultTerms);
	}

	/**
	 * Completes a given mapping by adding fresh auxiliary terms for any
	 * coefficient (see {@link #mPatternCoefficients}) which does not yet have a
	 * mapping.
	 * 
	 * After this method returned, the mapping is guaranteed to contain an entry
	 * for every coefficient.
	 * 
	 * @param mapping
	 *            mapping to add auxiliary terms to
	 */
	protected void completeMapping(final Map<IProgramVar, Term> mapping, final Set<IProgramVar> patternCoefficients) {
		final String prefix = newPrefix() + "replace_";
		int index = 0;
		for (final IProgramVar coefficient : patternCoefficients) {
			if (mapping.containsKey(coefficient)) {
				continue;
			}
			final Term replacement = SmtUtils.buildNewConstant(mSolver, prefix
					+ index++, "Real");
			mapping.put(coefficient, replacement);
		}
	}

	/**
	 * Completes a given mapping by adding auxiliary terms from another mapping
	 * for any coefficient (see {@link #mPatternCoefficients}) which does not yet
	 * have a mapping.
	 * 
	 * After this method returned, the mapping is guaranteed to contain an entry
	 * for every coefficient.
	 * 
	 * @param mapping
	 *            mapping to add auxiliary terms to
	 * @param source
	 *            mapping to get auxiliary terms from, must contain one entry
	 *            for each coefficient
	 */
	protected void completeMapping(final Map<IProgramVar, Term> mapping,
			final Map<IProgramVar, Term> source) {
		for (final IProgramVar coefficient : mPatternCoefficients) {
			if (mapping.containsKey(coefficient)) {
				continue;
			}
			mapping.put(coefficient, source.get(coefficient));
		}
	}

	/**
	 * Generates a {@link Term} that is true iff the given
	 * {@link LinearTransition} implies a given invariant pattern over the
	 * primed variables of the transition.
	 * 
	 * @see #mPrecondition
	 * @see #mPostcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre-
	 *            or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildImplicationTerm(final LinearTransition condition,
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern, IcfgLocation startLocation) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				condition.getOutVars());
		completeMapping(primedMapping, mStrategy.getPatternVariablesForLocation(startLocation, mCurrentRound));

		final Collection<List<LinearInequality>> conditionDNF_ = condition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> conditionDNF = new ArrayList<>();
		for (final List<LinearInequality> list : conditionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>();
			newList.addAll(list);
			conditionDNF.add(newList);
		}
		final Collection<Collection<LinearInequality>> negPatternDNF = mapAndNegatePattern(
				pattern, primedMapping, null);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : negPatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		mLogger.info( "[LIIPP] Got an implication term with "
				+ numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(conditionDNF, negPatternDNF);
	}

	/**
	 * Generates a {@link Term} that is true iff a given invariant pattern over
	 * the primed variables of the transition implies the given
	 * {@link LinearTransition}.
	 * 
	 * @see #mPrecondition
	 * @see #mPostcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre-
	 *            or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildBackwardImplicationTerm(final LinearTransition condition,
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern, IcfgLocation errorLocation) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				condition.getOutVars());
		completeMapping(primedMapping, mStrategy.getPatternVariablesForLocation(errorLocation, mCurrentRound));

		final Collection<List<LinearInequality>> conditionCNF_ = condition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> conditionCNF = new ArrayList<>();
		for (final List<LinearInequality> list : conditionCNF_) {
			final ArrayList<LinearInequality> newList = new ArrayList<>();
			for (final LinearInequality li : list) {
				final LinearInequality newLi = new LinearInequality(li);
				newLi.negate();
				newList.add(newLi);
			}
			conditionCNF.add(newList);
		}
		final Collection<Collection<LinearInequality>> newConditionDNF = expandCnfToDnf(conditionCNF);

		final Collection<Collection<LinearInequality>> PatternDNF = mapPattern(
				pattern, primedMapping, null);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : PatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		mLogger.info( "[LIIPP] Got an implication term with "
				+ numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(newConditionDNF, PatternDNF);
	}
	
	private static void completePatternVariablesMapping(Map<IProgramVar, Term> mapToComplete, Set<IProgramVar> varsShouldBeInMap, Map<IProgramVar, Term> mapToCompleteWith) {
		for (IProgramVar var : varsShouldBeInMap) {
			if (!mapToComplete.containsKey(var)) {
				mapToComplete.put(var, mapToCompleteWith.get(var));
			}
		}
	}

	/**
	 * Generates a {@link Term} that is true iff the given
	 * {@link InvariantTransitionPredicate} holds.
	 * 
	 * @param predicate
	 *            the predicate to build the term from
	 * @return term true iff the given predicate holds
	 */
	private Term buildPredicateTerm(
			final InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>> predicate,
			Map<IProgramVar, Term> lastOccurrencesOfTermVariables) {
		final LinearTransition transition = mLinearizer.linearize(predicate.getTransition());
		final Map<IProgramVar, Term> unprimedMapping = new HashMap<IProgramVar, Term>(
				transition.getInVars());
		lastOccurrencesOfTermVariables.putAll(unprimedMapping);
//		completeMapping(unprimedMapping);
		completePatternVariablesMapping(unprimedMapping, mStrategy.getPatternVariablesForLocation(predicate.getSourceLocation(), mCurrentRound),
				lastOccurrencesOfTermVariables);
		
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				transition.getOutVars());
		lastOccurrencesOfTermVariables.putAll(primedMapping);
		completePatternVariablesMapping(primedMapping, mStrategy.getPatternVariablesForLocation(predicate.getTargetLocation(), mCurrentRound),
				lastOccurrencesOfTermVariables);
//		completeMapping(primedMapping, unprimedMapping);
//		boolean useAllProgramVariables = true;
//		if (useAllProgramVariables) {
//			for (IProgramVar pv : lastOccurrencesOfTermVariables.keySet()) {
//				if (primedMapping.get(pv) == null)
//					primedMapping.put(pv, lastOccurrencesOfTermVariables.get(pv));
//			}
//		}
		
//		lastOccurrencesOfTermVariables.putAll(primedMapping);
		
		final Collection<Collection<LinearInequality>> startInvariantDNF = mapPattern(
				predicate.getInvStart(), unprimedMapping, lastOccurrencesOfTermVariables);
		final Collection<Collection<LinearInequality>> endInvariantDNF = mapAndNegatePattern(
				predicate.getInvEnd(), primedMapping, lastOccurrencesOfTermVariables);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : endInvariantDNF) {
			numberOfInequalities += conjunct.size();
		}
		mLogger.info( "[LIIPP] Got a predicate term with "
				+ numberOfInequalities + " conjuncts");
		final Collection<List<LinearInequality>> transitionDNF_ = transition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> transitionDNF = new ArrayList<>();
		for (final List<LinearInequality> list : transitionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>();
			newList.addAll(list);
			transitionDNF.add(newList);
		}
		if (PRINT_CONSTRAINTS) {
			StringBuilder sb = new StringBuilder();
			sb.append("StartPattern: ");
			startInvariantDNF.forEach(disjunct -> disjunct.forEach(lineq -> sb.append(lineq.toString() + " AND ")));
			sb.append("Transition: ");
			sb.append(predicate.getTransition());
			sb.append(" AND "); 
			sb.append("EndPattern: ");
			endInvariantDNF.forEach(disjunct -> disjunct.forEach(lineq -> sb.append(lineq.toString() + " AND ")));
			mLogger.info(sb.toString());
		}

		return transformNegatedConjunction(startInvariantDNF, endInvariantDNF,
				transitionDNF);
	}
	
	/**
	 * Generate constraints for invariant template as follows:
	 * 1. Generate a constraint s.t. the precondition implies the invariant template.
	 * 2. Generate for each predicate in predicates a constraint.
	 * 3. Generate a constraint s.t. the invariant template implies the post-condition.
	 * @param predicates - represent the transitions of the path program
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private void generateAndAssertTerms(final Collection<InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>>> predicates) {
		mSolver.assertTerm(buildImplicationTerm(mPrecondition,
				mEntryInvariantPattern, mStartLocation));
		mSolver.assertTerm(buildBackwardImplicationTerm(mPostcondition,
				mExitInvariantPattern, mErrorLocation));
		Map<IProgramVar, Term> lastOccurrencesOfTermVariables = new HashMap<>();
		for (final InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>> predicate : predicates) {
			mSolver.assertTerm(buildPredicateTerm(predicate, lastOccurrencesOfTermVariables));
		}
	}

	/**
	 * Split the given term in its conjunctions, annotate and assert each conjunction one by one, 
	 * and store the mapping annotated term -> original term in a map.
	 * @param term - the Term to be annotated and asserted
	 * @author Betim Musa (musab@informaitk.uni-freiburg.de)
	 */
	private void annotateAndAssertTermAndStoreMapping(final Term term) {
		assert term.getFreeVars().length == 0 : "Term has free vars";
		// Annotate and assert the conjuncts of the term one by one 
		final Term[] conjunctsOfTerm = SmtUtils.getConjuncts(term);
		final String termAnnotName = ANNOT_PREFIX + PREFIX_SEPARATOR + (mAnnotTermCounter++);
		for (int conjunctCounter = 0; conjunctCounter < conjunctsOfTerm.length; conjunctCounter++) {
			// Generate unique name for this term
			final String conjunctAnnotName = termAnnotName + PREFIX_SEPARATOR + (conjunctCounter); 
			// Store mapping termAnnotName -> original term
			mAnnotTerm2OriginalTerm.put(conjunctAnnotName, conjunctsOfTerm[conjunctCounter]);

			final Annotation annot = new Annotation(":named", conjunctAnnotName);
			final Term annotTerm = mSolver.annotate(conjunctsOfTerm[conjunctCounter], annot);
			mSolver.assertTerm(annotTerm);
		}
	}

	/**
	 * Generate constraints for invariant template as follows:
	 * 1. Generate a constraint s.t. the precondition implies the invariant template.
	 * 2. Generate for each predicate in predicates a constraint.
	 * 3. Generate a constraint s.t. the invariant template implies the post-condition.
	 * @param predicates - represent the transitions of the path program
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private void generateAndAnnotateAndAssertTerms(final Collection<InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>>> predicates) {
		// Generate and assert term for precondition
		annotateAndAssertTermAndStoreMapping(buildImplicationTerm(mPrecondition, mEntryInvariantPattern, mStartLocation));
		// Generate and assert term for post-condition
		annotateAndAssertTermAndStoreMapping(buildBackwardImplicationTerm(mPostcondition, mExitInvariantPattern, mErrorLocation));
		Map<IProgramVar, Term> lastOccurrencesOfTermVariables = new HashMap<>();
		// Generate and assert terms for intermediate transitions
		for (final InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>> predicate : predicates) {
			annotateAndAssertTermAndStoreMapping(buildPredicateTerm(predicate, lastOccurrencesOfTermVariables));
		}
	}
	/**
	 * Extract the Motzkin coefficients from the given term.
	 * @param t - term the Motzkin coefficients to be extracted from
	 * @return
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private Set<String> getTermVariablesFromTerm(final Term t) {
		final HashSet<String> result = new HashSet<>();
		if (t instanceof ApplicationTerm) {
			if (((ApplicationTerm)t).getFunction().getName().startsWith("motzkin_")) {
				result.add(((ApplicationTerm)t).getFunction().getName());
				return result;
			} else {
				final Term[] subterms = ((ApplicationTerm)t).getParameters();
				for (final Term st : subterms) {
					result.addAll(getTermVariablesFromTerm(st));
				}
			}
		} else if (t instanceof AnnotatedTerm) {
			final Term subterm = ((AnnotatedTerm)t).getSubterm();
			result.addAll(getTermVariablesFromTerm(subterm));
		} else if (t instanceof LetTerm) {
			final Term subterm = ((LetTerm)t).getSubTerm();
			result.addAll(getTermVariablesFromTerm(subterm));
		} else if (t instanceof TermVariable) {
			//			result.add((TermVariable)t);
		}
		return result;
	}

	/**
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 * @return
	 */
	public Collection<TermVariable> getVarsFromUnsatCore() {
		return mVarsFromUnsatCore;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean hasValidConfiguration(
			final Collection<InvariantTransitionPredicate<Collection<Collection<AbstractLinearInvariantPattern>>>> predicates,
			final int round) {
		mLogger.info( "[LIIPP] Start generating terms.");

		if (!mUseVarsFromUnsatCore) {
			generateAndAssertTerms(predicates);
		} else {
			generateAndAnnotateAndAssertTerms(predicates);
		}

		mLogger.info( "[LIIPP] Terms generated, checking SAT.");
		final LBool result = mSolver.checkSat();
		if (result == LBool.UNKNOWN) {
			mLogger.info("Got \"UNKNOWN\" for last check-sat, give up the invariant search.");
			// Prevent additional rounds
			mMaxRounds = mCurrentRound + 1;
		}
		if (result != LBool.SAT) {
			// No configuration found
			if (result == LBool.UNSAT && mUseVarsFromUnsatCore) {
				// Extract the variables from the unsatisfiable core by 
				// first extracting the motzkin variables and then using them
				// to get the corresponding program variables 
				final Term[] unsatCoreAnnots = mSolver.getUnsatCore();
				final Set<String> motzkinVariables = new HashSet<>();
				for (final Term t : unsatCoreAnnots) {
					final Term origTerm = mAnnotTerm2OriginalTerm.get(t.toStringDirect());
					motzkinVariables.addAll(getTermVariablesFromTerm(origTerm));
				}
				mVarsFromUnsatCore = new HashSet<>();
				for (final String motzkinVar : motzkinVariables) {
					final LinearInequality linq = mMotzkinCoefficients2LinearInequalities.get(motzkinVar);
					for (final Term varInLinq : linq.getVariables()) {
						if (varInLinq instanceof TermVariable) {
							mVarsFromUnsatCore.add((TermVariable)varInLinq);
						} 
//						else if (varInLinq instanceof ApplicationTerm) {
//							
//						} else {
//							throw new UnsupportedOperationException("Var in linear inequality is neither a TermVariable nor a Replacement-Variable.");
//						}

					}
				}
			}
			mLogger.info( "[LIIPP] No solution found.");
			return false;
		}

		mLogger.info( "[LIIPP] Solution found!");
		final Collection<Term> coefficientsOfAllInvariants = mPatternVariables;
		try {
			if (mSimplifySatisfyingAssignment) {
				mValuation = ModelExtractionUtils.getSimplifiedAssignment(
						mSolver, coefficientsOfAllInvariants, mLogger, mServices);
			} else {
				mValuation = ModelExtractionUtils.getValuation(mSolver,
						coefficientsOfAllInvariants);
			}
		} catch (final TermException e) {
			e.printStackTrace();
			throw new AssertionError("model extraction failed");
		}
		mLogger.info( "[LIIPP] Valuation: " + mValuation);

		return true;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return mMaxRounds;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected Term getTermForPattern(
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern) {
		final Map<IProgramVar, Term> definitionMap = new HashMap<IProgramVar, Term>(
				mPatternCoefficients.size());
		for (final IProgramVar coefficient : mPatternCoefficients) {
			final Term definition = ReplacementVarUtils.getDefinition(coefficient);
			definitionMap.put(coefficient, definition);
		}

		final Collection<Term> conjunctions = new ArrayList<Term>(
				pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<Term>(
					conjunct.size());
			for (final AbstractLinearInvariantPattern inequality : conjunct) {
				inequalities.add(inequality.getLinearInequality(definitionMap)
						.asTerm(mSolver));
			}
			conjunctions.add(SmtUtils.and(mSolver, inequalities));
		}
		return SmtUtils.or(mSolver, conjunctions);
	}

	/**
	 * Takes a pattern and generates a term with the csToolkit.getScript()
	 * script where the variables are valuated with the values in this.valuation
	 * @param pattern the pattern for which the term is generated
	 * @return a term corresponding to the cnf of LinearInequalites of
	 * the pattern, valuated with the values from this.valuation
	 */
	protected Term getValuatedTermForPattern(
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern) {
		final Script script = mCsToolkit.getManagedScript().getScript();
		final Collection<Term> conjunctions = new ArrayList<Term>(
				pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<Term>(
					conjunct.size());
			for (final AbstractLinearInvariantPattern inequality : conjunct) {
				Map<Term, Rational> valuation = null;
				try {
					if (mSimplifySatisfyingAssignment) {
						valuation = ModelExtractionUtils.getSimplifiedAssignment(
								mSolver, inequality.getCoefficients(), mLogger, mServices);
					} else {
						valuation = ModelExtractionUtils.getValuation(mSolver,
								inequality.getCoefficients());
					}
				}
				catch (TermException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
					mLogger.error("Getting values for coefficients for current pattern failed." +  inequality.toString());
				}
				
				final Term affineFunctionTerm = inequality.getAffineFunction(
						valuation).asTerm(script);
				if (inequality.isStrict()) {
					inequalities.add(SmtUtils.less(script, 
							constructZero(script, affineFunctionTerm.getSort()),
							affineFunctionTerm));
				} else {
					inequalities.add(SmtUtils.leq(script,
							constructZero(script, affineFunctionTerm.getSort()),
							affineFunctionTerm));
				}
			}
			conjunctions.add(SmtUtils.and(mCsToolkit.getManagedScript().getScript(), inequalities));
		}
		return SmtUtils.or(mCsToolkit.getManagedScript().getScript(), conjunctions);
	}

//	private static Term constructZero(final Script script, final Sort sort) {
//		if (sort.getRealSort().getName().equals("Int")) {
//			return script.numeral(BigInteger.ZERO);
//		} else if (sort.getRealSort().getName().equals("Real")) {
//			return script.decimal(BigDecimal.ZERO);
//		} else {
//			throw new IllegalArgumentException("unsupported sort " + sort);
//		}
//	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected TermTransformer getConfigurationTransformer() {
		throw new UnsupportedOperationException(
				"not needed, we directly extract Term, Rational mappings");
	}

	/**
	 * Reset solver and initialize it afterwards. For initializing, we set the
	 * option produce-models to true (this allows us to obtain a satisfying
	 * assignment) and we set the logic to QF_AUFNIRA. TODO: Matthias unsat
	 * cores might be helpful for debugging.
	 */
	private void reinitializeSolver() {
		mSolver.reset();
		mSolver.setOption(":produce-models", true);
		if (mUseVarsFromUnsatCore) {
			mSolver.setOption(":produce-unsat-cores", true);
		}
		final Logics logic;
		if (mUseNonlinearConstraints) {
			logic = Logics.QF_NRA;
		} else {
			logic = Logics.QF_LRA;
		}
		mSolver.setLogic(logic);
	}

	@Override
	public IPredicate applyConfiguration(
			final Collection<Collection<AbstractLinearInvariantPattern>> pattern) {
		final Term term = getValuatedTermForPattern(pattern);
		return predicateUnifier.getOrConstructPredicate(term);
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(final IcfgLocation location,
			final int round) {
		
		if (mStartLocation.equals(location)) {
			assert mEntryInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mEntryInvariantPattern;
		} else if (mErrorLocation.equals(location)) {
			assert mExitInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mExitInvariantPattern;
		} else {
//			final int[] dimensions = mStrategy.getDimensions(location, round);
//			// Build invariant pattern
//			final Collection<Collection<LinearPatternBase>> disjunction = new ArrayList<>(dimensions[0]);
//			Set<IProgramVar> variablesForThisPattern = mPatternCoefficients;
//			if (mUseLiveVariables) {
//				Set<IProgramVar> liveVars = mLocs2LiveVariables.get(location);
//				if (liveVars != null) {
//					// Remove all variables that are not live
//					variablesForThisPattern.retainAll(liveVars);
//				}
//			}
//			for (int i = 0; i < dimensions[0]; i++) {
//				final Collection<LinearPatternBase> conjunction = new ArrayList<>(
//						dimensions[1]);
//				for (int j = 0; j < dimensions[1]; j++) {
//					final boolean[] invariantPatternCopies;
//					if (mAlwaysStrictAndNonStrictCopies ) {
//						invariantPatternCopies = new boolean[] { false, true }; 
//					} else {
//						invariantPatternCopies = new boolean[] { false };
//					}
//					for (final boolean strict : invariantPatternCopies) {
//						final LinearPatternBase inequality = new LinearPatternBase (
//								mSolver, variablesForThisPattern, newPrefix(), strict);
//						Collection<Term> params = inequality.getVariables();
//						mPatternVariables.addAll(params);
//						conjunction.add(inequality);
//					}
//				}
//				disjunction.add(conjunction);
//			}
//			return disjunction;
			return mStrategy.getInvariantPatternForLocation(location, round, mSolver, newPrefix());
		}

	}
	
	
	
	@Override
	public void initializeEntryAndExitPattern() {
		// entry invariant pattern should be equivalent to true, so we create an empty conjunction
		final Collection<AbstractLinearInvariantPattern> emptyConjunction = Collections.emptyList();
		mEntryInvariantPattern = Collections.singleton(emptyConjunction);
		
		// exit pattern is equivalent to false, we create an empty disjunction
		mExitInvariantPattern = Collections.emptyList();
	}
	@Override		
	public Collection<Collection<AbstractLinearInvariantPattern>> getEntryInvariantPattern() {
		return mEntryInvariantPattern;
	}
	@Override	
	public Collection<Collection<AbstractLinearInvariantPattern>> getExitInvariantPattern() {
		return mExitInvariantPattern;
	}
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getEmptyInvariantPattern() {
		final Collection<Collection<AbstractLinearInvariantPattern>> emptyInvPattern;
		// empty invariant pattern should be equivalent to true, so we create an empty conjunction
		final Collection<AbstractLinearInvariantPattern> emptyConjunction = Collections.emptyList();
		emptyInvPattern = Collections.singleton(emptyConjunction);
		return emptyInvPattern;
	}
	
	
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> addTransFormulaToEachConjunctInPattern(final Collection<Collection<AbstractLinearInvariantPattern>> pattern, 
			final UnmodifiableTransFormula tf) {
		assert pattern != null : "pattern must not be null";
		assert tf != null : "TransFormula must  not be null";
		Collection<Collection<AbstractLinearInvariantPattern>> transFormulaAsLinIneqs = convertTransFormulaToPatternsForLinearInequalities(tf);
		Collection<Collection<AbstractLinearInvariantPattern>> result = new ArrayList<>();
		// Add conjuncts from transformula to each disjunct of the pattern as additional conjuncts
		for (Collection<AbstractLinearInvariantPattern> conjunctsInPattern : pattern) {
			for (Collection<AbstractLinearInvariantPattern> conjunctsInTransFormula : transFormulaAsLinIneqs) {
				Collection<AbstractLinearInvariantPattern> newConjuncts = new ArrayList<>();
				newConjuncts.addAll(conjunctsInPattern);
				newConjuncts.addAll(conjunctsInTransFormula);
				result.add(newConjuncts);
			}
			
		}
		return result;
	}
	
	private Collection<Collection<AbstractLinearInvariantPattern>> convertTransFormulaToPatternsForLinearInequalities(final UnmodifiableTransFormula tf) {
		Map<Term, IProgramVar> termVariables2ProgramVars = new HashMap<>();
		termVariables2ProgramVars.putAll(tf.getInVars().entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
		termVariables2ProgramVars.putAll(tf.getOutVars().entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
		
		// Transform the transformula into a disjunction of conjunctions, where each conjunct is a LinearInequality
		List<List<LinearInequality>> linearinequalities = mLinearizer.linearize(tf).getPolyhedra();
		Collection<Collection<AbstractLinearInvariantPattern>> result = new ArrayList<>(linearinequalities.size());
		for (List<LinearInequality> lineqs : linearinequalities) {
			Collection<AbstractLinearInvariantPattern> conjunctsFromTransFormula = new ArrayList<AbstractLinearInvariantPattern>(linearinequalities.size());
			for (LinearInequality lineq : lineqs) {
				Map<IProgramVar, AffineTerm> programVarsToConstantCoefficients = new HashMap<>();
				for (Term termVar : lineq.getVariables()) {
					programVarsToConstantCoefficients.put(termVariables2ProgramVars.get(termVar), lineq.getCoefficient(termVar));
				}
				LinearPatternWithConstantCoefficients lb = new LinearPatternWithConstantCoefficients(mSolver, programVarsToConstantCoefficients.keySet(), newPrefix(), lineq.isStrict(), 
						programVarsToConstantCoefficients, lineq.getConstant());
				
				conjunctsFromTransFormula.add(lb);
			}
			result.add(conjunctsFromTransFormula);
		}
		return result;
	}
	
	
	public Collection<Collection<AbstractLinearInvariantPattern>> addTransFormulaAsAdditionalDisjunctToPattern(Collection<Collection<AbstractLinearInvariantPattern>> pattern, 
			UnmodifiableTransFormula tf) {
		assert pattern != null : "pattern must not be null";
		assert tf != null : "TransFormula must  not be null";
		Collection<Collection<AbstractLinearInvariantPattern>> transFormulaAsLinIneqs = convertTransFormulaToPatternsForLinearInequalities(tf);
		Collection<Collection<AbstractLinearInvariantPattern>> result = new ArrayList<>();
		
		result.addAll(pattern);
		// Add conjuncts from transformula as additional disjuncts
		result.addAll(transFormulaAsLinIneqs);
		return result;
	}
}
