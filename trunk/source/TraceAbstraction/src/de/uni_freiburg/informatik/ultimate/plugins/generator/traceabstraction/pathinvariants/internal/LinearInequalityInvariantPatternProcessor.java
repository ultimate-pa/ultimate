/*
 * Copyright (C) 2015 David Zschocke
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2015-2017 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtSymbols;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf.Cnf;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf.Dnf;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf.XnfUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.ConstraintSynthesisUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.ConstraintSynthesisUtils.Linearity;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * A {@link IInvariantPatternProcessor} using patterns composed of linear inequalities on a linear approximation of the
 * program.
 *
 * The outer collection within the invariant pattern type represents a disjunction, the inner one a conjunction. Within
 * the inner conjunction, there may be strict and non-strict inequalities. These collections are generated according to
 * a {@link ILinearInequalityInvariantPatternStrategy}.
 *
 * @author David Zschocke, Dirk Steinmetz, Matthias Heizmann, Betim Musa
 */
public final class LinearInequalityInvariantPatternProcessor
		extends AbstractSMTInvariantPatternProcessor<Dnf<AbstractLinearInvariantPattern>> {

	public enum SimplificationType {
		NO_SIMPLIFICATION, SIMPLE, TWO_MODE
	}

	/**
	 * Produce transformed terms that are annotated with debugging information.
	 */
	private static final boolean ANNOTATE_TERMS_FOR_DEBUGGING = false;

	private static final String PREFIX = "lp_";
	private static final String PREFIX_SEPARATOR = "_";

	private static final String ANNOT_PREFIX = "LIIPP_Annot";

	private static final boolean ASSERT_INTEGER_COEFFICIENTS = false;

	private int mAnnotTermCounter;
	/**
	 * Stores the mapping from annotation of a term to the original motzkin term. It is used to restore the original
	 * terms from the annotations in unsat core.
	 */
	private Map<String, Term> mAnnotTerm2MotzkinTerm;

	/**
	 * Maps annotated terms to the locations (i.e. source and target locations) of corresponding transitions.
	 */
	private Map<String, Set<IcfgLocation>> mTermAnnotations2Locs;
	/**
	 * @see {@link MotzkinTransformation}.mMotzkinCoefficients2LinearInequalities
	 */
	private Map<String, LinearInequality> mMotzkinCoefficients2LinearInequalities;

	/**
	 * Maps the invariant patterns (the set of inequalities) to the locations on which they're used. E.g. Let IT_1 be an
	 * invariant pattern that is used for location loc_1, IT_2 is used for loc_2, and let stmt be the statement between
	 * loc_1 and loc_2, then the map stores the following: IT_1 -> [loc_1], IT_2 -> [loc_2], stmt -> [loc_1, loc_2].
	 */
	private Map<Set<LinearInequality>, List<IcfgLocation>> mLinearInequalities2Locations;

	private Set<IcfgLocation> mLocsInUnsatCore;

	private final boolean mUseUnsatCores;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mSolver;
	private final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> mStrategy;
	private final LinearTransition mPrecondition;
	private final LinearTransition mPostcondition;
	private final CachedTransFormulaLinearizer mLinearizer;

	private final Dnf<AbstractLinearInvariantPattern> mEntryInvariantPattern;
	private final Dnf<AbstractLinearInvariantPattern> mExitInvariantPattern;
	private int mPrefixCounter;
	private int mCurrentRound;
	private final int mMaxRounds;
	private final boolean mUseNonlinearConstraints;
	private final boolean mSynthesizeEntryPattern;
	private final KindOfInvariant mKindOfInvariant;
	/**
	 * The simplification type that is used to simplify the values of templates coefficients/parameters.
	 */
	private final SimplificationType mSimplifySatisfyingAssignment = SimplificationType.TWO_MODE;

	private Collection<TermVariable> mVarsFromUnsatCore;
	private final IcfgLocation mStartLocation;
	private final Set<IcfgLocation> mErrorLocations;

	private final boolean mUseUnderApproxAsAdditionalConstraint;
	private final boolean mUseOverApproxAsAdditionalConstraint;

	/**
	 * Contains all coefficients of all patterns from the current round.
	 */
	private Set<Term> mAllPatternCoefficients;
	private Set<Term> mIntegerCoefficients;
	/**
	 * If the current constraints are satisfiable, then this map contains the values of the pattern coefficients.
	 */
	private Map<Term, Rational> mPatternCoefficients2Values;
	private final Map<IcfgLocation, UnmodifiableTransFormula> mLoc2UnderApproximation;
	private final Map<IcfgLocation, UnmodifiableTransFormula> mLoc2OverApproximation;

	/**
	 * Statistics section - the following statistics are collected - the TreeSize of the constraints (normal and
	 * approximation constraints) - the number of Motzkin Transformations (for normal and approximation constraints) -
	 * the program size measured as the number of inequalities of all tranformulas - the size of largest template - the
	 * size of smallest template
	 */
	private int mDAGTreeSizeSumOfNormalConstraints;
	private int mDAGTreeSizeSumOfApproxConstraints;
	private int mMotzkinTransformationsForNormalConstraints;
	private int mMotzkinTransformationsForApproxConstraints;
	private int mMotzkinCoefficientsForNormalConstraints;
	private int mMotzkinCoefficientsForApproxConstraints;
	private int mProgramSizeConjuncts;
	private int mProgramSizeDisjuncts;
	/**
	 * Measured in ms
	 */
	private long mConstraintsSolvingTime;
	/**
	 * Measured in ms
	 */
	private long mConstraintsConstructionTime;

	public enum LinearInequalityPatternProcessorStatistics {
		ProgramSizeConjuncts,

		ProgramSizeDisjuncts,

		MotzkinTransformationsNormalConstraints,

		MotzkinTransformationsApproxConstraints,

		MotzkinCoefficientsNormalConstraints,

		MotzkinCoefficientsApproxConstraints,

		TreesizeNormalConstraints,

		TreesizeApproxConstraints,

		ConstraintsSolvingTime,

		ConstraintsConstructionTime
	}

	public enum ConstraintsType {
		/**
		 * normal means the constraints for the path program transitions
		 */
		Normal,
		/**
		 * Approximation means the constraints SP_i => IT_i and/or IT_i => WP_i (i.e. the constraints for
		 * Under-/Overapproximations)
		 */
		Approximation
	}

	/**
	 * TODO
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager to use with the predicateUnifier
	 * @param smtSymbols
	 * @param solver
	 *            SMT solver to use
	 * @param precondition
	 *            the invariant on the {@link ControlFlowGraph#getEntry()} of cfg
	 * @param postcondition
	 *            the invariant on the {@link ControlFlowGraph#getExit()} of cfg
	 * @param startLocation
	 * @param errorLocations
	 *            a set of error locations
	 * @param strategy
	 *            The strategy to generate invariant patterns with
	 * @param useNonlinearConstraints
	 *            Kind of constraints that are used to specify invariant.
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 * @param synthesizeEntryPattern
	 *            true if the the pattern for the start location need to be synthesized (instead of being inferred from
	 *            the precondition)
	 * @param kindOfInvariant
	 *            the kind of invariant to be generated
	 * @param cfg
	 *            the ControlFlowGraph to generate an invariant map on
	 * @param overApprox
	 * @param underApprox
	 */
	public LinearInequalityInvariantPatternProcessor(final IUltimateServiceProvider services,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit, final SmtSymbols smtSymbols,
			final Script solver, final List<IcfgLocation> locations, final List<IcfgInternalTransition> transitions,
			final IPredicate precondition, final IPredicate postcondition, final IcfgLocation startLocation,
			final Set<IcfgLocation> errorLocations,
			final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> strategy,
			final boolean useNonlinearConstraints, final boolean useUnsatCores,
			final SimplificationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Map<IcfgLocation, IPredicate> loc2underApprox, final Map<IcfgLocation, IPredicate> loc2overApprox,
			final boolean synthesizeEntryPattern, final KindOfInvariant kindOfInvariant) {
		super(predicateUnifier, csToolkit);
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSolver = solver;
		mStrategy = strategy;
		mStartLocation = startLocation;
		mErrorLocations = errorLocations;
		mSynthesizeEntryPattern = synthesizeEntryPattern;
		mKindOfInvariant = kindOfInvariant;

		mLinearizer = new CachedTransFormulaLinearizer(services, csToolkit, smtSymbols, simplicationTechnique,
				xnfConversionTechnique);
		mPrecondition = mLinearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(precondition, csToolkit.getManagedScript()));
		mPostcondition = mLinearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(postcondition, csToolkit.getManagedScript()));

		final ManagedScript script = new ManagedScript(mServices, mSolver);
		mEntryInvariantPattern = convertTransFormulaToPatternsForLinearInequalities(
				TransFormulaBuilder.constructTransFormulaFromPredicate(precondition, script));
		mExitInvariantPattern = convertTransFormulaToPatternsForLinearInequalities(
				TransFormulaBuilder.constructTransFormulaFromPredicate(postcondition, script));

		mCurrentRound = 0;
		mMaxRounds = strategy.getMaxRounds();
		mUseNonlinearConstraints = useNonlinearConstraints;
		mUseUnsatCores = useUnsatCores;
		if (mUseUnsatCores) {
			mUseUnderApproxAsAdditionalConstraint = true;
			mUseOverApproxAsAdditionalConstraint = true;
		} else {
			// If we don't use unsat cores, then the additional constraints are not needed
			mUseUnderApproxAsAdditionalConstraint = false;
			mUseOverApproxAsAdditionalConstraint = false;
		}
		mAnnotTermCounter = 0;
		mAnnotTerm2MotzkinTerm = new HashMap<>();
		mTermAnnotations2Locs = new HashMap<>();
		mMotzkinCoefficients2LinearInequalities = new HashMap<>();
		mLinearInequalities2Locations = new HashMap<>();
		mAllPatternCoefficients = null;
		mIntegerCoefficients = null;
		mPatternCoefficients2Values = null;
		mLoc2UnderApproximation = CFGInvariantsGenerator.convertMapToPredsToMapToUnmodTrans(loc2underApprox,
				mCsToolkit.getManagedScript());
		mLoc2OverApproximation = CFGInvariantsGenerator.convertMapToPredsToMapToUnmodTrans(loc2overApprox,
				mCsToolkit.getManagedScript());
		// Reset statistics
		resetStatistics();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void startRound(final int round) {
		mSolver.echo(new QuotedObject("Round " + round));
		resetSettings();
		// Reset statistics
		resetStatistics();
		mPrefixCounter = 0;
		mCurrentRound = round;
		mAllPatternCoefficients = new HashSet<>();
		mIntegerCoefficients = new HashSet<>();
		mLinearInequalities2Locations = new HashMap<>();
	}

	/**
	 * Reset the linear inequality invariant pattern processor statistics.
	 */
	private void resetStatistics() {
		mDAGTreeSizeSumOfNormalConstraints = 0;
		mDAGTreeSizeSumOfApproxConstraints = 0;
		mMotzkinTransformationsForNormalConstraints = 0;
		mMotzkinTransformationsForApproxConstraints = 0;
		mMotzkinCoefficientsForNormalConstraints = 0;
		mMotzkinCoefficientsForApproxConstraints = 0;
		mProgramSizeConjuncts = 0;
		mProgramSizeDisjuncts = 0;
		mConstraintsSolvingTime = 0;
		mConstraintsConstructionTime = 0;
	}

	/**
	 * Reset the solver and additionally reset the annotation term counter and the map mAnnotTerm2OriginalTerm
	 */
	private void resetSettings() {
		reinitializeSolver();
		// Reset annotation term counter
		mAnnotTermCounter = 0;
		// Reset map that stores the mapping from the annotated term to the original term.
		mAnnotTerm2MotzkinTerm = new HashMap<>();

		mTermAnnotations2Locs = new HashMap<>();
		// Reset map that stores motzkin coefficients to linear inequalities
		mMotzkinCoefficients2LinearInequalities = new HashMap<>();
		// Reset settings of strategy
		mStrategy.resetSettings();
	}

	/**
	 * Generates a new prefix, which is guaranteed (within prefixes generated through this method on one single
	 * instance) to be unique within the current round.
	 *
	 * @return unique prefix (within this instance and round)
	 */
	protected String newPrefix() {
		return PREFIX + (mPrefixCounter++);
	}

	/**
	 * Transforms a pattern into a DNF of linear inequalities relative to a given mapping of {@link IProgramVar}s
	 * involved.
	 *
	 * @param pattern
	 *            the pattern to transform
	 * @param mapping
	 *            the mapping to use
	 * @return transformed pattern, equivalent to the pattern under the mapping
	 */
	private static Dnf<LinearInequality> mapPattern(final Dnf<AbstractLinearInvariantPattern> pattern,
			final Map<IProgramVar, Term> mapping) {
		final Dnf<LinearInequality> result = new Dnf<>(pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<LinearInequality> mappedConjunct = new ArrayList<>(conjunct.size());
			for (final AbstractLinearInvariantPattern base : conjunct) {
				mappedConjunct.add(base.getLinearInequality(mapping));

			}
			result.add(mappedConjunct);
		}
		return result;

	}

	/**
	 * Transforms a transition pattern into a DNF of linear inequalities.
	 *
	 * @param pattern
	 *            a DNF of LinearTransitionPatterns
	 * @param inMapping
	 *            a mapping from IProgramVars to unprimed variables
	 * @param outMapping
	 *            a mapping from IProgramVars to primed variables
	 * @return a DNF of LinearInequalities
	 */
	private static Dnf<LinearInequality> mapTransitionPattern(final Dnf<AbstractLinearInvariantPattern> pattern,
			final Map<IProgramVar, Term> inMapping, final Map<IProgramVar, Term> outMapping) {
		final Dnf<LinearInequality> result = new Dnf<>(pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<LinearInequality> mappedConjunct = new ArrayList<>(conjunct.size());
			for (final AbstractLinearInvariantPattern base : conjunct) {
				assert base instanceof LinearTransitionPattern;
				final LinearTransitionPattern basePattern = (LinearTransitionPattern) base;
				mappedConjunct.add(basePattern.getLinearInequality(inMapping, outMapping));
			}
			result.add(mappedConjunct);
		}
		return result;
	}

	private static Dnf<LinearInequality> negatePatternAndConvertToDNF(final IUltimateServiceProvider services,
			final Dnf<LinearInequality> mappedPattern) {
		// 2. negate every LinearInequality, result is a cnf
		final Cnf<LinearInequality> cnfAfterNegation = new Cnf<>(mappedPattern.size());
		for (final Collection<LinearInequality> conjunct : mappedPattern) {
			final Collection<LinearInequality> disjunctWithNegatedLinearInequalities = new ArrayList<>(conjunct.size());
			for (final LinearInequality li : conjunct) {
				// copy original linear inequality
				final LinearInequality negatedLi = new LinearInequality(li);
				negatedLi.negate();
				disjunctWithNegatedLinearInequalities.add(negatedLi);
			}
			cnfAfterNegation.add(disjunctWithNegatedLinearInequalities);
		}
		// 3. expand the cnf to get a dnf
		final Dnf<LinearInequality> mappedAndNegatedPattern = cnfAfterNegation.toDnf(services);
		assert mappedAndNegatedPattern != null;
		// 4. return the resulting dnf as the solution
		return mappedAndNegatedPattern;
	}

	/**
	 * Transforms and negates a pattern into a DNF of linear inequalities relative to a given mapping of
	 * {@link IProgramVar}s involved.
	 *
	 * @param services
	 *
	 * @param pattern
	 *            the pattern to transform
	 * @param mapping
	 *            the mapping to use
	 * @return transformed pattern, equivalent to the negated pattern under the mapping
	 */
	private static Dnf<LinearInequality> mapAndNegatePattern(final IUltimateServiceProvider services,
			final Dnf<AbstractLinearInvariantPattern> pattern, final Map<IProgramVar, Term> mapping) {
		// This is the trivial algorithm (expanding). Feel free to optimize ;)
		// 1. map Pattern, result is dnf
		final Dnf<LinearInequality> mappedPattern = mapPattern(pattern, mapping);
		return negatePatternAndConvertToDNF(services, mappedPattern);
	}

	/**
	 * Transforms a conjunction to an equivalent term representing a disjunction of the motzkin transformations of the
	 * expanded DNF conjuncts.
	 *
	 * @see #expandConjunction(Collection...)
	 * @see MotzkinTransformation
	 * @param dnfs
	 *            DNFs to conjunct together
	 * @return term equivalent to the negated term
	 */
	@SafeVarargs
	private final Term transformNegatedConjunction(final ConstraintsType ct, final Dnf<LinearInequality>... dnfs) {
		mLogger.info("About to invoke motzkin:");
		if (mLogger.isDebugEnabled()) {
			for (final Collection<? extends Collection<LinearInequality>> dnf : dnfs) {
				mLogger.debug("DNF to transform: " + dnf);
			}
		}

		final Dnf<LinearInequality> conjunctionDNF = XnfUtils.and(mServices, dnfs);

		final int numOfMotzkinCoefficientsBeforeTransformation =
				mMotzkinCoefficients2LinearInequalities.keySet().size();
		// Apply Motzkin and generate the conjunction of the resulting Terms
		final Collection<Term> resultTerms = new ArrayList<>(conjunctionDNF.size());
		final AnalysisType analysisType = mUseNonlinearConstraints ? AnalysisType.NONLINEAR
				: (mKindOfInvariant == KindOfInvariant.DANGER ? AnalysisType.LINEAR_WITH_GUESSES : AnalysisType.LINEAR);
		for (final Collection<LinearInequality> conjunct : conjunctionDNF) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Transforming conjunct " + conjunct);
			}
			final MotzkinTransformation transformation =
					new MotzkinTransformation(mServices, mSolver, analysisType, ANNOTATE_TERMS_FOR_DEBUGGING);
			transformation.addInequalities(conjunct);
			resultTerms.add(transformation.transform(new Rational[0]));
			mMotzkinCoefficients2LinearInequalities.putAll(transformation.getMotzkinCoefficients2LinearInequalities());
		}
		final Term result = SmtUtils.and(mSolver, resultTerms);
		// Statistics section
		if (ct == ConstraintsType.Normal) {
			mDAGTreeSizeSumOfNormalConstraints += new DAGSize().treesize(result);
			mMotzkinTransformationsForNormalConstraints += conjunctionDNF.size();
			mMotzkinCoefficientsForNormalConstraints += (mMotzkinCoefficients2LinearInequalities.keySet().size()
					- numOfMotzkinCoefficientsBeforeTransformation);
		} else if (ct == ConstraintsType.Approximation) {
			mDAGTreeSizeSumOfApproxConstraints += new DAGSize().treesize(result);
			mMotzkinTransformationsForApproxConstraints += conjunctionDNF.size();
			mMotzkinCoefficientsForApproxConstraints += (mMotzkinCoefficients2LinearInequalities.keySet().size()
					- numOfMotzkinCoefficientsBeforeTransformation);
		}

		return result;
	}

	/**
	 * Completes a given mapping by adding fresh auxiliary terms for any coefficient (see {@link #mPatternCoefficients})
	 * which does not yet have a mapping.
	 *
	 * After this method returned, the mapping is guaranteed to contain an entry for every coefficient.
	 *
	 * @param mapping
	 *            mapping to add auxiliary terms to
	 */
	// protected void completeMapping(final Map<IProgramVar, Term> mapping, final Set<IProgramVar> patternCoefficients)
	// {
	// final String prefix = newPrefix() + "replace_";
	// int index = 0;
	// for (final IProgramVar coefficient : patternCoefficients) {
	// if (mapping.containsKey(coefficient)) {
	// continue;
	// }
	// final Term replacement = SmtUtils.buildNewConstant(mSolver, prefix
	// + index++, "Real");
	// mapping.put(coefficient, replacement);
	// }
	// }

	/**
	 * Completes a given mapping by adding auxiliary terms from another mapping for any coefficient (see
	 * {@link #mPatternCoefficients}) which does not yet have a mapping.
	 *
	 * After this method returned, the mapping is guaranteed to contain an entry for every coefficient.
	 *
	 * @param mapping
	 *            mapping to add auxiliary terms to
	 * @param source
	 *            mapping to get auxiliary terms from, must contain one entry for each coefficient
	 */
	// protected void completeMapping(final Map<IProgramVar, Term> mapping,
	// final Map<IProgramVar, Term> source) {
	// for (final IProgramVar coefficient : mPatternCoefficients) {
	// if (mapping.containsKey(coefficient)) {
	// continue;
	// }
	// mapping.put(coefficient, source.get(coefficient));
	// }
	// }

	/**
	 * Generates a {@link Term} that is true iff the given {@link LinearTransition} implies a given invariant pattern
	 * over the primed variables of the transition.
	 *
	 * @see #mPrecondition
	 * @see #mPostcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre- or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildImplicationTerm(final LinearTransition condition,
			final Dnf<AbstractLinearInvariantPattern> pattern, final IcfgLocation startLocation,
			final Map<IProgramVar, Term> programVarsRecentlyOccurred) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<>(condition.getOutVars());
		// completePatternVariablesMapping(primedMapping, mStrategy.getPatternVariablesForLocation(startLocation,
		// mCurrentRound), programVarsRecentlyOccurred);

		final Collection<List<LinearInequality>> conditionDNF_ = condition.getPolyhedra();
		final Dnf<LinearInequality> conditionDNF = new Dnf<>();
		for (final List<LinearInequality> list : conditionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>();
			newList.addAll(list);
			conditionDNF.add(newList);
		}
		final Dnf<LinearInequality> negPatternDNF = mapAndNegatePattern(mServices, pattern, primedMapping);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : negPatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		mLogger.info("Got an implication term with " + numberOfInequalities + " conjuncts");
		return transformNegatedConjunction(ConstraintsType.Normal, conditionDNF, negPatternDNF);
	}

	/**
	 * Generates a {@link Term} that is true iff a given invariant pattern over the primed variables of the transition
	 * implies the given {@link LinearTransition}.
	 *
	 * @see #mPrecondition
	 * @see #mPostcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre- or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildBackwardImplicationTerm(final LinearTransition condition,
			final Dnf<AbstractLinearInvariantPattern> pattern, final IcfgLocation errorLocation,
			final Map<IProgramVar, Term> programVarsRecentlyOccurred) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<>(condition.getOutVars());
		// completePatternVariablesMapping(primedMapping, mStrategy.getPatternVariablesForLocation(errorLocation,
		// mCurrentRound), programVarsRecentlyOccurred);

		final Collection<List<LinearInequality>> conditionCNF_ = condition.getPolyhedra();
		final Cnf<LinearInequality> conditionCNF = new Cnf<>();
		for (final List<LinearInequality> list : conditionCNF_) {
			final ArrayList<LinearInequality> newList = new ArrayList<>();
			for (final LinearInequality li : list) {
				final LinearInequality newLi = new LinearInequality(li);
				newLi.negate();
				newList.add(newLi);
			}
			conditionCNF.add(newList);
		}
		final Dnf<LinearInequality> newConditionDNF = conditionCNF.toDnf(mServices);

		final Dnf<LinearInequality> patternDNF = mapPattern(pattern, primedMapping);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : patternDNF) {
			numberOfInequalities += conjunct.size();
		}
		mLogger.info("Got an implication term with " + numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(ConstraintsType.Normal, newConditionDNF, patternDNF);
	}

	private void completePatternVariablesMapping(final Map<IProgramVar, Term> mapToComplete,
			final Set<IProgramVar> varsShouldBeInMap, final Map<IProgramVar, Term> mapToCompleteWith) {
		final String prefix = newPrefix() + "replace_";
		int index = 0;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Var-Map before completion: " + mapToComplete);
		}
		for (final IProgramVar var : varsShouldBeInMap) {
			if (!mapToComplete.containsKey(var)) {
				if (mapToCompleteWith.get(var) != null) {
					mapToComplete.put(var, mapToCompleteWith.get(var));
				} else {
					final Term replacement =
							SmtUtils.buildNewConstant(mSolver, prefix + var + "_" + (index++), SmtSortUtils.REAL_SORT);
					mapToComplete.put(var, replacement);
					mapToCompleteWith.put(var, replacement);
				}
			}
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Var-Map after completion: " + mapToComplete);
		}
	}

	/**
	 * Generates a {@link Term} that is true iff the given {@link TransitionConstraintIngredients} holds.
	 *
	 * @param predicate
	 *            the predicate to build the term from
	 * @return term true iff the given predicate holds
	 */
	private Term buildPredicateTerm(
			final TransitionConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> predicate,
			final Map<IProgramVar, Term> programVarsRecentlyOccurred) {
		if (mLogger.isDebugEnabled()) {
			final String transformulaAsString = predicate.getTransition().toString();
			mLogger.debug("Building constraints for transition (" + predicate.getSourceLocation() + ", "
					+ transformulaAsString.substring(0, transformulaAsString.indexOf("InVars")) + ", "
					+ predicate.getTargetLocation() + ")");
		}
		final LinearTransition transition = mLinearizer.linearize(predicate.getTransition());
		final Map<IProgramVar, Term> unprimedMapping = new HashMap<>(transition.getInVars());
		programVarsRecentlyOccurred.putAll(unprimedMapping);
		// completeMapping(unprimedMapping);
		completePatternVariablesMapping(unprimedMapping, predicate.getVariablesForSourcePattern(),
				programVarsRecentlyOccurred);

		final Map<IProgramVar, Term> primedMapping = new HashMap<>(transition.getOutVars());
		programVarsRecentlyOccurred.putAll(primedMapping);
		completePatternVariablesMapping(primedMapping, predicate.getVariablesForTargetPattern(),
				programVarsRecentlyOccurred);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of start-pattern before mapping to lin-inequalities: "
					+ getSizeOfPattern(predicate.getInvStart()));
		}
		final Dnf<LinearInequality> startInvariantDNF = mapPattern(predicate.getInvStart(), unprimedMapping);
		if (mUseUnsatCores) {
			final List<IcfgLocation> loc = new ArrayList<>();
			loc.add(predicate.getSourceLocation());
			// Store linear inequalities from startPattern, later we may use them to extract the locations from the
			// unsat core
			storeLinearInequalitiesToLocations(startInvariantDNF, loc);
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(
					"Size of start-pattern after mapping to lin-inequalities: " + getSizeOfPattern(startInvariantDNF));
			mLogger.debug("Size of end-pattern before mapping to lin-inequalities: "
					+ getSizeOfPattern(predicate.getInvEnd()));
		}
		final Dnf<LinearInequality> targetLocTemplateMappedDNF = mapPattern(predicate.getInvEnd(), primedMapping);
		final Dnf<LinearInequality> targetLocTemplateNegatedDNF =
				negatePatternAndConvertToDNF(mServices, targetLocTemplateMappedDNF);
		// mapAndNegatePattern(predicate.getInvEnd(), primedMapping);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of end-pattern after mapping to lin-inequalities and negating: "
					+ getSizeOfPattern(targetLocTemplateNegatedDNF));
		}
		if (mUseUnsatCores) {
			final List<IcfgLocation> loc = new ArrayList<>();
			loc.add(predicate.getTargetLocation());
			// Store linear inequalities from endPattern, later we may use them to extract the locations from the unsat
			// core
			storeLinearInequalitiesToLocations(targetLocTemplateNegatedDNF, loc);
		}
		final Dnf<LinearInequality> transitionDNF = convertTransitionToPattern(transition);
		if (transitionDNF.size() > 1) {
			mProgramSizeDisjuncts += transitionDNF.size();
		}
		if (mUseUnsatCores) {
			final List<IcfgLocation> locs = new ArrayList<>();
			locs.add(predicate.getSourceLocation());
			locs.add(predicate.getTargetLocation());
			// Store linear inequalities from the transition, later we may use them to extract the locations from the
			// unsat core
			storeLinearInequalitiesToLocations(transitionDNF, locs);

		}

		// Respect timeout / toolchain cancellation
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(LinearInequalityInvariantPatternProcessor.class);
		}
		if (mUseUnderApproxAsAdditionalConstraint && mCurrentRound >= 0) {
			final IcfgLocation loc = predicate.getTargetLocation();
			// Add constraint SP_i ==> IT_i
			if (!mErrorLocations.contains(loc) && mLoc2UnderApproximation.containsKey(loc)) {
				final Dnf<AbstractLinearInvariantPattern> spTemplate =
						convertTransFormulaToPatternsForLinearInequalities(mLoc2UnderApproximation.get(loc));
				final Set<IProgramVar> varsForPattern = extractVarsFromPattern(spTemplate);
				completePatternVariablesMapping(primedMapping, varsForPattern, programVarsRecentlyOccurred);
				final Dnf<LinearInequality> spTemplateDNF = mapPattern(spTemplate, primedMapping);
				if (mUseUnsatCores) {
					final List<IcfgLocation> locForSp = new ArrayList<>();
					locForSp.add(loc);
					// Store linear inequalities from SP, later we may use them to extract the locations from the unsat
					// core
					storeLinearInequalitiesToLocations(spTemplateDNF, locForSp);
				}
				if (mLogger.isDebugEnabled()) {
					final StringBuilder sb = new StringBuilder();
					appendConstraintToStringBuilder(sb, "\nSP-" + loc + ": ", "(true)", spTemplateDNF);
					appendConstraintToStringBuilder(sb, "\nnegatedPattern-" + loc + ": ", "()",
							targetLocTemplateNegatedDNF);
					printConstraintFromStringBuilder(sb);
				}
				final String transformulaAsString = mLoc2UnderApproximation.get(loc).toString();
				mSolver.echo(new QuotedObject("Assertion for SP: "
						+ transformulaAsString.substring(0, transformulaAsString.indexOf("InVars"))));
				annotateAndAssertTermAndStoreMapping(transformNegatedConjunction(ConstraintsType.Approximation,
						spTemplateDNF, targetLocTemplateNegatedDNF), new HashSet<>(Arrays.asList(loc)));
			}
		}
		if (mUseOverApproxAsAdditionalConstraint && mCurrentRound >= 0) {
			final IcfgLocation loc = predicate.getTargetLocation();
			// Add constraint IT_i ==> WP_i
			if (!mErrorLocations.contains(loc) && mLoc2OverApproximation.containsKey(loc)) {
				// First, negate predicate WP
				final UnmodifiableTransFormula negatedWp =
						TransFormulaUtils.negate(mLoc2OverApproximation.get(loc), super.mCsToolkit.getManagedScript(),
								mServices, mLogger, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
								SimplificationTechnique.SIMPLIFY_DDA);
				// Then convert the tranformula to linear inequalities
				final Dnf<AbstractLinearInvariantPattern> negatedWpTemplate =
						convertTransFormulaToPatternsForLinearInequalities(negatedWp);
				final Set<IProgramVar> varsForPattern = extractVarsFromPattern(negatedWpTemplate);
				completePatternVariablesMapping(primedMapping, varsForPattern, programVarsRecentlyOccurred);
				final Dnf<LinearInequality> wpTemplateNegatedDNF = mapPattern(negatedWpTemplate, primedMapping);
				if (mUseUnsatCores) {
					final List<IcfgLocation> locForWp = new ArrayList<>();
					locForWp.add(loc);
					// Store linear inequalities from WP, later we may use them to extract the locations from the unsat
					// core
					storeLinearInequalitiesToLocations(wpTemplateNegatedDNF, locForWp);
				}
				if (mLogger.isDebugEnabled()) {
					final StringBuilder sb = new StringBuilder();
					appendConstraintToStringBuilder(sb, "\nPattern-" + loc + ": ", "(true)",
							targetLocTemplateMappedDNF);
					appendConstraintToStringBuilder(sb, "\nnegatedWP-" + loc + ": ", "()", wpTemplateNegatedDNF);
					printConstraintFromStringBuilder(sb);
				}
				final String transformulaAsString = mLoc2OverApproximation.get(loc).toString();
				mSolver.echo(new QuotedObject("Assertion for WP: "
						+ transformulaAsString.substring(0, transformulaAsString.indexOf("InVars"))));
				annotateAndAssertTermAndStoreMapping(transformNegatedConjunction(ConstraintsType.Approximation,
						targetLocTemplateMappedDNF, wpTemplateNegatedDNF), new HashSet<>(Arrays.asList(loc)));
			}
		}
		if (mLogger.isDebugEnabled()) {
			final StringBuilder sb = new StringBuilder();
			appendConstraintToStringBuilder(sb, "\nStartPattern: ", "(true)", startInvariantDNF);
			appendConstraintToStringBuilder(sb, "\nTransition: ", "(true)", transitionDNF);
			appendConstraintToStringBuilder(sb, "\nEndPattern: ", "(false)", targetLocTemplateNegatedDNF);
			printConstraintFromStringBuilder(sb);
		}
		mSolver.echo(new QuotedObject(
				"Assertion for trans (" + predicate.getSourceLocation() + ", " + predicate.getTargetLocation() + ")"));
		return transformNegatedConjunction(ConstraintsType.Normal, startInvariantDNF, targetLocTemplateNegatedDNF,
				transitionDNF);
	}

	private void printConstraintFromStringBuilder(final StringBuilder sb) {
		String s = sb.toString();
		s = s.replaceAll("AND \\) OR", "\\) OR");
		s = s.replaceAll("OR \n", "\n");
		s = s.replaceAll("AND \n", "\n");
		// s = s.replaceAll("\\(\\)", "(true)");
		mLogger.debug(s);
	}

	private static void appendConstraintToStringBuilder(final StringBuilder sb, final String constraintName,
			final String toReplaceEmptyFormula, final Dnf<LinearInequality> patternDNF) {
		sb.append(constraintName);
		if (patternDNF.isEmpty()) {
			sb.append(toReplaceEmptyFormula);
		} else {
			patternDNF.forEach(disjunct -> {
				sb.append("(");
				disjunct.forEach(lineq -> sb.append(lineq.toString() + " AND "));
				sb.append(") OR ");
			});
		}

	}

	private static Set<IProgramVar> extractVarsFromPattern(final Dnf<AbstractLinearInvariantPattern> spTemplate) {
		final Set<IProgramVar> result = new HashSet<>();
		for (final Collection<AbstractLinearInvariantPattern> conjuncts : spTemplate) {
			for (final AbstractLinearInvariantPattern conjunct : conjuncts) {
				result.addAll(conjunct.getVariables());
			}
		}
		return result;
	}

	private void storeLinearInequalitiesToLocations(final Dnf<LinearInequality> lineqs, final List<IcfgLocation> locs) {
		final Set<LinearInequality> lineqsAsSet = new HashSet<>(lineqs.size());
		for (final Collection<LinearInequality> conjunct : lineqs) {
			lineqsAsSet.addAll(conjunct);
		}
		if (!lineqs.isEmpty() && locs.size() >= 1) {
			mLinearInequalities2Locations.put(lineqsAsSet, locs);
			// TODO: 2018-05-19 Matthias: The following code was used while analyzing
			// unsolved problems that we had with invariant synthesis
			// final List<IcfgLocation> locsOfLineqs = mLinearInequalities2Locations.get(lineqsAsSet);
			// if (locsOfLineqs != null) {
			// locs.addAll(locsOfLineqs);
			// } else {
			// mLinearInequalities2Locations.put(lineqsAsSet, locs);
			// }
		}
	}

	/**
	 * Generate constraints for invariant template as follows: 1. Generate a constraint s.t. the precondition implies
	 * the invariant template. 2. Generate for each predicate in predicates a constraint. 3. Generate a constraint s.t.
	 * the invariant template implies the post-condition.
	 *
	 * @param successorIngredients
	 *            - represent the transitions of the path program
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private void generateAndAssertTerms(
			final Collection<SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> successorIngredients) {
		/**
		 * Maps program vars to their recent occurrence in the program
		 */
		final Map<IProgramVar, Term> programVarsRecentlyOccurred = new HashMap<>();
		mSolver.assertTerm(buildImplicationTerm(mPrecondition, mEntryInvariantPattern, mStartLocation,
				programVarsRecentlyOccurred));
		for (final IcfgLocation errorLocation : mErrorLocations) {
			mSolver.assertTerm(buildBackwardImplicationTerm(mPostcondition, mExitInvariantPattern, errorLocation,
					programVarsRecentlyOccurred));
		}

		for (final SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> successorIngredient : successorIngredients) {
			final Set<TransitionConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> transitionIngredients =
					successorIngredient.buildTransitionConstraintIngredients();
			for (final TransitionConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> transitionIngredient : transitionIngredients) {
				mSolver.assertTerm(buildPredicateTerm(transitionIngredient, programVarsRecentlyOccurred));
			}
		}
	}

	/**
	 * Generates the constraints for danger invariants.
	 *
	 * @param successorIngredients
	 *            the SuccessorConstraintIngredients
	 */
	private void generateAndAssertDangerTerms(
			final Collection<SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> successorIngredients) {
		final Map<IProgramVar, Term> programVarsRecentlyOccurred = new HashMap<>();
		mSolver.assertTerm(buildImplicationTerm(mPrecondition, mEntryInvariantPattern, mStartLocation,
				programVarsRecentlyOccurred));
		for (final IcfgLocation errorLocation : mErrorLocations) {
			mSolver.assertTerm(buildBackwardImplicationTerm(mPostcondition, mExitInvariantPattern, errorLocation,
					programVarsRecentlyOccurred));
		}

		for (final SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> ingredient : successorIngredients) {
			final Dnf<AbstractLinearInvariantPattern> sourceInvariantPattern = ingredient.getInvStart();
			if (mErrorLocations.contains(ingredient.getSourceLocation())) {
				continue;
			}
			if (!ingredient.getSourceLocation().getOutgoingEdges().isEmpty()) {
				// Assert that a danger invariant is reachable in a successor state.
				Term constraint = mSolver.term("true");
				for (final Map.Entry<IcfgEdge, Dnf<AbstractLinearInvariantPattern>> entry : ingredient
						.getEdge2TargetInv().entrySet()) {
					final UnmodifiableTransFormula tf = entry.getKey().getTransformula();

					final LinearTransition transition = mLinearizer.linearize(tf);
					final Map<IProgramVar, Term> unprimedMapping = new HashMap<>(transition.getInVars());
					programVarsRecentlyOccurred.putAll(unprimedMapping);
					completePatternVariablesMapping(unprimedMapping, ingredient.getVariablesForSourcePattern(),
							programVarsRecentlyOccurred);

					final Map<IProgramVar, Term> primedMapping = new HashMap<>(transition.getOutVars());
					programVarsRecentlyOccurred.putAll(primedMapping);
					completePatternVariablesMapping(primedMapping,
							ingredient.getEdge2VariablesForTargetPattern().get(entry.getKey()),
							programVarsRecentlyOccurred);

					final Dnf<LinearInequality> negatedTargetInvariantDnf =
							mapAndNegatePattern(mServices, entry.getValue(), primedMapping);
					final Dnf<LinearInequality> sourceInvariantDnf =
							mapPattern(sourceInvariantPattern, unprimedMapping);

					final Dnf<LinearInequality> transitionDnf = convertTransitionToPattern(transition);
					final Dnf<AbstractLinearInvariantPattern> transitionPattern =
							ingredient.getEdge2Pattern().get(entry.getKey());
					final Dnf<LinearInequality> transitionPatternDnf =
							mapTransitionPattern(transitionPattern, unprimedMapping, primedMapping);

					final Term term = transformNegatedConjunction(ConstraintsType.Normal, sourceInvariantDnf,
							transitionDnf, transitionPatternDnf, negatedTargetInvariantDnf);

					constraint = SmtUtils.and(mSolver, constraint, term);
				}

				mLogger.debug("Asserting constraint: " + constraint);
				mSolver.assertTerm(constraint);
			}

			if (mStartLocation.equals(ingredient.getSourceLocation())) {
				final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
				ingredient.getVariablesForSourcePattern().forEach(var -> outVars.put(var, var.getTermVariable()));
				final TransFormulaBuilder builder =
						new TransFormulaBuilder(Collections.emptyMap(), outVars, true, null, true, null, true);
				builder.setFormula(mSolver.term("true"));
				builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
				final UnmodifiableTransFormula transFormula =
						builder.finishConstruction(new ManagedScript(mServices, mSolver));

				final IcfgEdge dummyEdge = mCsToolkit.getIcfgEdgeFactory().createInternalTransition(null,
						ingredient.getSourceLocation(), null, transFormula);
				final Dnf<AbstractLinearInvariantPattern> pattern = getPatternForTransition(dummyEdge, mCurrentRound);
				final Map<IProgramVar, Term> primedMapping = new HashMap<>(outVars);
				final Dnf<LinearInequality> patternDnf =
						mapTransitionPattern(pattern, Collections.emptyMap(), primedMapping);
				final Dnf<LinearInequality> negatedSourceInvariantDnf =
						mapAndNegatePattern(mServices, sourceInvariantPattern, primedMapping);
				final Term constraint =
						transformNegatedConjunction(ConstraintsType.Normal, patternDnf, negatedSourceInvariantDnf);
				mLogger.debug("Asserting constraint: " + constraint);
				mSolver.assertTerm(constraint);
			}

			final Map<IProgramVar, Term> unprimedMapping = new HashMap<>();
			for (final IcfgEdge transition : ingredient.getEdge2TargetInv().keySet()) {
				unprimedMapping.putAll(transition.getTransformula().getInVars());
			}
			programVarsRecentlyOccurred.putAll(unprimedMapping);
			completePatternVariablesMapping(unprimedMapping, ingredient.getVariablesForSourcePattern(),
					programVarsRecentlyOccurred);

			final Collection<Dnf<LinearInequality>> conjunction = new ArrayList<>();
			for (final IcfgEdge transition : ingredient.getEdge2TargetInv().keySet()) {
				final Map<TermVariable, TermVariable> subsitutionMapping = new HashMap<>();
				for (final Map.Entry<IProgramVar, TermVariable> entry : transition.getTransformula().getInVars()
						.entrySet()) {
					subsitutionMapping.put(entry.getValue(), (TermVariable) unprimedMapping.get(entry.getKey()));
				}
				final UnmodifiableTransFormula substitutedTf = TransFormulaUtils.substituteTermVars(
						transition.getTransformula(), mCsToolkit.getManagedScript(), subsitutionMapping);
				final UnmodifiableTransFormula guard = TransFormulaUtils.computeGuard(substitutedTf,
						mCsToolkit.getManagedScript(), mServices, mLogger);
				final UnmodifiableTransFormula negatedGuard =
						TransFormulaUtils.negate(guard, mCsToolkit.getManagedScript(), mServices, mLogger,
								XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
								SimplificationTechnique.SIMPLIFY_DDA);
				final LinearTransition linearTransition = mLinearizer.linearize(negatedGuard);
				final Dnf<LinearInequality> negatedTransitionDnf = convertTransitionToPattern(linearTransition);

				final Dnf<AbstractLinearInvariantPattern> transitionPattern =
						ingredient.getEdge2Pattern().get(transition);
				final Dnf<LinearInequality> mappedTransitionPattern = new Dnf<>();
				for (final Collection<AbstractLinearInvariantPattern> patternConjunction : transitionPattern) {
					final Collection<LinearInequality> conjuncts = new ArrayList<>();
					for (final AbstractLinearInvariantPattern pattern : patternConjunction) {
						assert pattern instanceof LinearTransitionPattern;
						final LinearTransitionPattern transPattern = (LinearTransitionPattern) pattern;
						if (!transPattern.containsOutVars()) {
							conjuncts.add(transPattern.getLinearInequality(unprimedMapping));
						}
					}
					mappedTransitionPattern.add(conjuncts);
				}

				final Dnf<LinearInequality> disjunction = new Dnf<>();
				disjunction.addAll(negatedTransitionDnf);
				disjunction.addAll(negatePatternAndConvertToDNF(mServices, mappedTransitionPattern));
				conjunction.add(disjunction);
			}

			final Dnf<LinearInequality> sourceInvariantDnf = mapPattern(sourceInvariantPattern, unprimedMapping);
			conjunction.add(sourceInvariantDnf);
			@SuppressWarnings("unchecked")
			final Term constraint =
					transformNegatedConjunction(ConstraintsType.Normal, conjunction.toArray(new Dnf[0]));

			mLogger.debug("Asserting constraint: " + constraint);
			mSolver.assertTerm(constraint);
		}
	}

	/**
	 * Split the given term in its conjunctions, annotate and assert each conjunction one by one, and store the mapping
	 * annotated term -> original term in a map.
	 *
	 * @param term
	 *            - the Term to be annotated and asserted
	 * @author Betim Musa (musab@informaitk.uni-freiburg.de)
	 */
	private void annotateAndAssertTermAndStoreMapping(final Term term, final Set<IcfgLocation> transitionLocs) {
		assert term.getFreeVars().length == 0 : "Term has free vars";
		// Annotate and assert the conjuncts of the term one by one
		final Term[] conjunctsOfTerm = SmtUtils.getConjuncts(term);
		final String termAnnotName = ANNOT_PREFIX + PREFIX_SEPARATOR + (mAnnotTermCounter++);
		for (int conjunctCounter = 0; conjunctCounter < conjunctsOfTerm.length; conjunctCounter++) {
			// Generate unique name for this term
			final String conjunctAnnotName = termAnnotName + PREFIX_SEPARATOR + (conjunctCounter);
			// Store mapping termAnnotName -> original term
			mAnnotTerm2MotzkinTerm.put(conjunctAnnotName, conjunctsOfTerm[conjunctCounter]);
			mTermAnnotations2Locs.put(conjunctAnnotName, transitionLocs);
			final Annotation annot = new Annotation(":named", conjunctAnnotName);
			final Term annotTerm = mSolver.annotate(conjunctsOfTerm[conjunctCounter], annot);
			mSolver.assertTerm(annotTerm);
		}
	}

	/**
	 * Generate constraints for invariant template as follows: 1. Generate a constraint s.t. the precondition implies
	 * the invariant template. 2. Generate for each predicate in predicates a constraint. 3. Generate a constraint s.t.
	 * the invariant template implies the post-condition.
	 *
	 * @param predicates
	 *            - represent the transitions of the path program
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private void generateAndAnnotateAndAssertTerms(
			final Collection<SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> successorIngredients) {
		/**
		 * Maps program vars to their recent occurrence in the program
		 */
		final Map<IProgramVar, Term> programVarsRecentlyOccurred = new HashMap<>();
		// Generate and assert term for precondition
		annotateAndAssertTermAndStoreMapping(buildImplicationTerm(mPrecondition, mEntryInvariantPattern, mStartLocation,
				programVarsRecentlyOccurred), new HashSet<>(Arrays.asList(mStartLocation)));
		// Generate and assert term for post-condition
		for (final IcfgLocation errorLocation : mErrorLocations) {
			annotateAndAssertTermAndStoreMapping(buildBackwardImplicationTerm(mPostcondition, mExitInvariantPattern,
					errorLocation, programVarsRecentlyOccurred), new HashSet<>(Arrays.asList(errorLocation)));
		}

		// Generate and assert terms for intermediate transitions
		for (final SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> successorIngredient : successorIngredients) {
			final Set<TransitionConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> transitionIngredients =
					successorIngredient.buildTransitionConstraintIngredients();
			for (final TransitionConstraintIngredients<Dnf<AbstractLinearInvariantPattern>> transitionIngredient : transitionIngredients) {
				final Set<IcfgLocation> transitionLocs = new HashSet<>(Arrays
						.asList(transitionIngredient.getSourceLocation(), transitionIngredient.getTargetLocation()));
				annotateAndAssertTermAndStoreMapping(
						buildPredicateTerm(transitionIngredient, programVarsRecentlyOccurred), transitionLocs);
				// final LBool smtResult = mSolver.checkSat();
				// mLogger.info("Check-sat result: " + smtResult);
			}
		}
	}

	/**
	 * Extract the Motzkin coefficients from the given term.
	 *
	 * @param t
	 *            - term the Motzkin coefficients to be extracted from
	 * @return
	 * @author Betim Musa (musab@informatik.uni-freiburg.de)
	 */
	private Set<String> getTermVariablesFromTerm(final Term t) {
		final HashSet<String> result = new HashSet<>();
		if (t instanceof ApplicationTerm) {
			if (((ApplicationTerm) t).getFunction().getName().startsWith("motzkin_")) {
				result.add(((ApplicationTerm) t).getFunction().getName());
				return result;
			}
			final Term[] subterms = ((ApplicationTerm) t).getParameters();
			for (final Term st : subterms) {
				result.addAll(getTermVariablesFromTerm(st));
			}
		} else if (t instanceof AnnotatedTerm) {
			final Term subterm = ((AnnotatedTerm) t).getSubterm();
			result.addAll(getTermVariablesFromTerm(subterm));
		} else if (t instanceof LetTerm) {
			final Term subterm = ((LetTerm) t).getSubTerm();
			result.addAll(getTermVariablesFromTerm(subterm));
		} else if (t instanceof TermVariable) {
			// result.add((TermVariable)t);
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

	public Map<LinearInequalityPatternProcessorStatistics, Object> getStatistics() {
		final Map<LinearInequalityPatternProcessorStatistics, Object> stats = new HashMap<>();
		stats.put(LinearInequalityPatternProcessorStatistics.ProgramSizeConjuncts, mProgramSizeConjuncts);
		stats.put(LinearInequalityPatternProcessorStatistics.ProgramSizeDisjuncts, mProgramSizeDisjuncts);
		stats.put(LinearInequalityPatternProcessorStatistics.TreesizeNormalConstraints,
				mDAGTreeSizeSumOfNormalConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.TreesizeApproxConstraints,
				mDAGTreeSizeSumOfApproxConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsNormalConstraints,
				mMotzkinTransformationsForNormalConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.MotzkinTransformationsApproxConstraints,
				mMotzkinTransformationsForApproxConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsNormalConstraints,
				mMotzkinCoefficientsForNormalConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.MotzkinCoefficientsApproxConstraints,
				mMotzkinCoefficientsForApproxConstraints);
		stats.put(LinearInequalityPatternProcessorStatistics.ConstraintsSolvingTime, mConstraintsSolvingTime);
		stats.put(LinearInequalityPatternProcessorStatistics.ConstraintsConstructionTime, mConstraintsConstructionTime);
		return stats;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public LBool checkForValidConfiguration(
			final Collection<SuccessorConstraintIngredients<Dnf<AbstractLinearInvariantPattern>>> successorConstraintIngredients,
			final int round) {
		mLogger.info("Start generating terms.");
		final long startTimeConstraintsConstruction = System.nanoTime();
		if (mKindOfInvariant == KindOfInvariant.SAFETY) {
			if (!mUseUnsatCores) {
				generateAndAssertTerms(successorConstraintIngredients);
			} else {
				generateAndAnnotateAndAssertTerms(successorConstraintIngredients);
			}
		} else {
			assert mKindOfInvariant == KindOfInvariant.DANGER;
			generateAndAssertDangerTerms(successorConstraintIngredients);
		}

		if (ASSERT_INTEGER_COEFFICIENTS) {
			for (final Term coefficient : mIntegerCoefficients) {
				mSolver.assertTerm(mSolver.term("is_int", coefficient));
			}
		}

		// Convert ns to ms
		mConstraintsConstructionTime = (System.nanoTime() - startTimeConstraintsConstruction) / 1_000_000L;
		mLogger.info("Terms generated, checking SAT.");
		final long startTimeConstraintsSolving = System.nanoTime();
		final LBool smtResult = mSolver.checkSat();
		// Convert ns to ms
		mConstraintsSolvingTime = (System.nanoTime() - startTimeConstraintsSolving) / 1_000_000L;
		mLogger.info("Check-sat result: " + smtResult);

		if (smtResult == LBool.UNSAT && mUseUnsatCores) {
			// No configuration found
			// Extract the variables from the unsatisfiable core by
			// first extracting the motzkin variables and then using them
			// to get the corresponding program variables
			final Term[] unsatCoreAnnots = mSolver.getUnsatCore();
			final Set<String> motzkinVariables = new HashSet<>();
			final Set<IcfgLocation> locsInUnsatCore = new HashSet<>();
			for (final Term t : unsatCoreAnnots) {
				final Term origMotzkinTerm = mAnnotTerm2MotzkinTerm.get(t.toStringDirect());
				motzkinVariables.addAll(getTermVariablesFromTerm(origMotzkinTerm));
				// Extract the corresponding locations for the current annotated term
				locsInUnsatCore.addAll(mTermAnnotations2Locs.get(t.toStringDirect()));
			}
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("UnsatCoreAnnots: " + Arrays.toString(unsatCoreAnnots));
				mLogger.debug("MotzkinVars in unsat core: " + motzkinVariables);
			}
			mVarsFromUnsatCore = new HashSet<>();
			// Extract variables from terms which have been part of unsat core
			for (final String motzkinVar : motzkinVariables) {
				final LinearInequality linq = mMotzkinCoefficients2LinearInequalities.get(motzkinVar);
				for (final Term term : linq.getVariables()) {
					if (term instanceof TermVariable) {
						mVarsFromUnsatCore.add((TermVariable) term);
					} else {
						// throw new UnsupportedOperationException("Linear inequality (" + term + ")is not a
						// TermVariable");
						mLogger.warn("Linear inequality (" + term + ")is not a TermVariable");
					}
				}
			}
			mLocsInUnsatCore = locsInUnsatCore;
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("LocsInUnsatCore: " + locsInUnsatCore);
			}
			// Change for all locations the corresponding invariant patterns (i.e. increase conjuncts and/or
			// disjuncts)
			if (round >= 0) {
				for (final IcfgLocation loc : locsInUnsatCore) {
					if (((loc != mStartLocation) || mSynthesizeEntryPattern) && !mErrorLocations.contains(loc)) {
						mStrategy.changePatternSettingForLocation(loc, mCurrentRound, locsInUnsatCore);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("changed setting for loc: " + loc);
						}
					}
				}
			}
		}

		if (!ASSERT_INTEGER_COEFFICIENTS && smtResult == LBool.SAT && !mIntegerCoefficients.isEmpty()) {
			// Check that all integer coefficients are integers
			try {
				final Map<Term, Rational> valuation = ModelExtractionUtils.getSimplifiedAssignment_TwoMode(mSolver,
						mIntegerCoefficients, mLogger, mServices);
				for (final Map.Entry<Term, Rational> entry : valuation.entrySet()) {
					final Rational value = entry.getValue();
					final Term coefficient = entry.getKey();
					// We try to use the ceiled value if the value is not integral
					mSolver.assertTerm(mSolver.term("=", coefficient, value.ceil().toTerm(coefficient.getSort())));
				}
				return mSolver.checkSat();
			} catch (final TermException e) {
				e.printStackTrace();
				mLogger.error("Getting values for integer coefficients failed.");
				return LBool.UNKNOWN;
			}
		}

		return smtResult;
	}

	public Set<IcfgLocation> getLocationsInUnsatCore() {
		assert mLocsInUnsatCore != null : "locations in unsat not existing";
		return mLocsInUnsatCore;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return mMaxRounds;
	}

	/**
	 * Takes a pattern and generates a term with the csToolkit.getScript() script where the variables are valuated with
	 * the values in this.valuation
	 *
	 * @param pattern
	 *            the pattern for which the term is generated
	 * @return a term corresponding to the cnf of LinearInequalites of the pattern, valuated with the values from
	 *         this.valuation
	 */
	protected Term getValuatedTermForPattern(final Dnf<AbstractLinearInvariantPattern> pattern) {
		assert mPatternCoefficients2Values != null : "Call method extractValuesForPatternCoefficients"
				+ " before applying configurations for the patterns.";
		final Script script = mCsToolkit.getManagedScript().getScript();
		final Collection<Term> conjunctions = new ArrayList<>(pattern.size());
		for (final Collection<AbstractLinearInvariantPattern> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<>(conjunct.size());
			for (final AbstractLinearInvariantPattern inequality : conjunct) {
				final Map<Term, Rational> valuation = new HashMap<>(inequality.getCoefficients().size());
				for (final Term coeff : inequality.getCoefficients()) {
					valuation.put(coeff, mPatternCoefficients2Values.get(coeff));
				}
				final Term affineFunctionTerm = inequality.getAffineFunction(valuation).asTerm(script);
				final Term zero = Rational.ZERO.toTerm(affineFunctionTerm.getSort());
				if (inequality.isStrict()) {
					inequalities.add(SmtUtils.less(script, zero, affineFunctionTerm));
				} else {
					inequalities.add(SmtUtils.leq(script, zero, affineFunctionTerm));
				}
			}
			conjunctions.add(SmtUtils.and(mCsToolkit.getManagedScript().getScript(), inequalities));
		}
		return SmtUtils.or(mCsToolkit.getManagedScript().getScript(), conjunctions);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected TermTransformer getConfigurationTransformer() {
		throw new UnsupportedOperationException("not needed, we directly extract Term, Rational mappings");
	}

	/**
	 * Reset solver and initialize it afterwards. For initializing, we set the option produce-models to true (this
	 * allows us to obtain a satisfying assignment) and we set the logic to QF_AUFNIRA. TODO: Matthias unsat cores might
	 * be helpful for debugging.
	 */
	private void reinitializeSolver() {
		mSolver.reset();
		mSolver.setOption(":produce-models", true);
		if (mUseUnsatCores) {
			mSolver.setOption(":produce-unsat-cores", true);
		}

		final boolean useAlsoIntegers;
		// 2017-11-05 Matthias:
		// seems like we always need integers since program variables can have sort Int.
		// useAlsoIntegers = (mKindOfInvariant == KindOfInvariant.DANGER);
		useAlsoIntegers = true;
		final Linearity linearity = mUseNonlinearConstraints ? Linearity.NONLINEAR : Linearity.LINEAR;
		final Logics logic = ConstraintSynthesisUtils.getLogic(linearity, useAlsoIntegers);
		mSolver.setLogic(logic);
	}

	@Override
	public IPredicate applyConfiguration(final Dnf<AbstractLinearInvariantPattern> pattern) {
		final Term term = getValuatedTermForPattern(pattern);
		return mPedicateUnifier.getOrConstructPredicate(term);
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getPatternForTransition(final IcfgEdge transition, final int round) {
		final Dnf<AbstractLinearInvariantPattern> pattern =
				mStrategy.getPatternForTransition(transition, round, mSolver, newPrefix());
		mIntegerCoefficients.addAll(mStrategy.getIntegerCoefficientsForTransition(transition));
		return pattern;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round) {

		if (mStartLocation.equals(location) && !mSynthesizeEntryPattern) {
			assert mEntryInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mEntryInvariantPattern;
		} else if (mErrorLocations.contains(location)) {
			assert mExitInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mExitInvariantPattern;
		} else {

			final Dnf<AbstractLinearInvariantPattern> p =
					mStrategy.getInvariantPatternForLocation(location, round, mSolver, newPrefix());
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("InvariantPattern for Location " + location + " is:  " + getSizeOfPattern(p));
			}
			// Add the coefficients of this pattern to the set of all coefficients
			mAllPatternCoefficients.addAll(mStrategy.getPatternCoefficientsForLocation(location));
			return p;
		}
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Set<IProgramVar> vars) {

		if (mStartLocation.equals(location) && !mSynthesizeEntryPattern) {
			assert mEntryInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mEntryInvariantPattern;
		} else if (mErrorLocations.contains(location)) {
			assert mExitInvariantPattern != null : "call initializeEntryAndExitPattern() before this";
			return mExitInvariantPattern;
		} else {

			final Dnf<AbstractLinearInvariantPattern> p =
					mStrategy.getInvariantPatternForLocation(location, round, mSolver, newPrefix(), vars);
			if (mLogger.isInfoEnabled()) {
				mLogger.info("InvariantPattern for Location " + location + " is:  " + getSizeOfPattern(p));
			}
			// Add the coefficients of this pattern to the set of all coefficients
			mAllPatternCoefficients.addAll(mStrategy.getPatternCoefficientsForLocation(location));
			return p;
		}
	}

	@Override
	public final Set<IProgramVar> getVariablesForInvariantPattern(final IcfgLocation location, final int round) {
		if (mStartLocation.equals(location) && !mSynthesizeEntryPattern) {
			return Collections.emptySet();
		} else if (mErrorLocations.contains(location)) {
			return Collections.emptySet();
		} else {
			return mStrategy.getPatternVariablesForLocation(location, round);
		}
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getEntryInvariantPattern() {
		return mEntryInvariantPattern;
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getExitInvariantPattern() {
		return mExitInvariantPattern;
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getEmptyInvariantPattern() {
		// empty invariant pattern should be equivalent to true, so we create an empty conjunction
		final Collection<AbstractLinearInvariantPattern> emptyConjunction = Collections.emptyList();
		return new Dnf<>(emptyConjunction);
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> addTransFormulaToEachConjunctInPattern(
			final Dnf<AbstractLinearInvariantPattern> pattern, final UnmodifiableTransFormula tf) {
		assert pattern != null : "pattern must not be null";
		assert tf != null : "TransFormula must  not be null";
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of pattern before adding WP: " + getSizeOfPattern(pattern));
		}
		final Dnf<AbstractLinearInvariantPattern> transFormulaAsLinIneqs =
				convertTransFormulaToPatternsForLinearInequalities(tf);
		final Dnf<AbstractLinearInvariantPattern> result = new Dnf<>();
		// Add conjuncts from transformula to each disjunct of the pattern as additional conjuncts
		for (final Collection<AbstractLinearInvariantPattern> conjunctsInPattern : pattern) {
			for (final Collection<AbstractLinearInvariantPattern> conjunctsInTransFormula : transFormulaAsLinIneqs) {
				final Collection<AbstractLinearInvariantPattern> newConjuncts = new ArrayList<>();
				newConjuncts.addAll(conjunctsInPattern);
				newConjuncts.addAll(conjunctsInTransFormula);
				result.add(newConjuncts);
			}

		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of pattern after adding WP: " + getSizeOfPattern(result));
		}
		return result;
	}

	private static <E> String getSizeOfPattern(final Dnf<E> pattern) {
		int totalNumOfConjuncts = 0;
		final int[] conjunctsEachDisjunct = new int[pattern.size()];
		int totalNumOfDisjuncts = 0;
		for (final Collection<?> conjuncts : pattern) {
			totalNumOfConjuncts += conjuncts.size();
			conjunctsEachDisjunct[totalNumOfDisjuncts] = conjuncts.size();
			totalNumOfDisjuncts++;
		}
		return totalNumOfDisjuncts + " disjuncts with each " + Arrays.toString(conjunctsEachDisjunct)
				+ " conjuncts (Total: " + totalNumOfConjuncts + " cojuncts)";
	}

	public int getTotalNumberOfConjunctsInPattern(final Dnf<AbstractLinearInvariantPattern> pattern) {
		int totalNumOfConjuncts = 0;
		for (final Collection<?> conjuncts : pattern) {
			totalNumOfConjuncts = totalNumOfConjuncts + conjuncts.size();
		}

		return totalNumOfConjuncts;
	}

	private Dnf<AbstractLinearInvariantPattern>
			convertTransFormulaToPatternsForLinearInequalities(final UnmodifiableTransFormula tf) {
		final Map<Term, IProgramVar> termVariables2ProgramVars = new HashMap<>();
		termVariables2ProgramVars.putAll(
				tf.getInVars().entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
		termVariables2ProgramVars.putAll(
				tf.getOutVars().entrySet().stream().collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));

		// Transform the transformula into a disjunction of conjunctions, where each conjunct is a LinearInequality
		final List<List<LinearInequality>> linearinequalities = mLinearizer.linearize(tf).getPolyhedra();
		final Dnf<AbstractLinearInvariantPattern> result = new Dnf<>(linearinequalities.size());
		for (final List<LinearInequality> lineqs : linearinequalities) {
			final Collection<AbstractLinearInvariantPattern> conjunctsFromTransFormula =
					new ArrayList<>(linearinequalities.size());
			for (final LinearInequality lineq : lineqs) {
				final Map<IProgramVar, AffineTerm> programVarsToConstantCoefficients = new HashMap<>();
				final Map<Term, AffineTerm> auxVarsToConstantCoefficients = new HashMap<>();
				for (final Term termVar : lineq.getVariables()) {
					if (termVariables2ProgramVars.containsKey(termVar)) {
						programVarsToConstantCoefficients.put(termVariables2ProgramVars.get(termVar),
								lineq.getCoefficient(termVar));
					} else {
						auxVarsToConstantCoefficients.put(termVar, lineq.getCoefficient(termVar));
					}
				}
				final LinearPatternWithConstantCoefficients lb = new LinearPatternWithConstantCoefficients(mSolver,
						programVarsToConstantCoefficients.keySet(), newPrefix(), lineq.isStrict(),
						programVarsToConstantCoefficients, auxVarsToConstantCoefficients, lineq.getConstant());

				conjunctsFromTransFormula.add(lb);
			}
			result.add(conjunctsFromTransFormula);
		}
		return result;
	}

	/**
	 * Converts a linear transition into a pattern of linear inequalities.
	 *
	 * @param transition
	 *            a linear transition
	 * @return a pattern in DNF
	 */
	private Dnf<LinearInequality> convertTransitionToPattern(final LinearTransition transition) {
		final Collection<List<LinearInequality>> transitionDNF_ = transition.getPolyhedra();
		final Dnf<LinearInequality> transitionDNF = new Dnf<>();
		for (final List<LinearInequality> list : transitionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>(list);
			transitionDNF.add(newList);
			// statistics section
			mProgramSizeConjuncts += list.size();
		}
		return transitionDNF;
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> addTransFormulaAsAdditionalDisjunctToPattern(
			final Dnf<AbstractLinearInvariantPattern> pattern, final UnmodifiableTransFormula tf) {
		assert pattern != null : "pattern must not be null";
		assert tf != null : "TransFormula must  not be null";
		final Dnf<AbstractLinearInvariantPattern> transFormulaAsLinIneqs =
				convertTransFormulaToPatternsForLinearInequalities(tf);
		final Dnf<AbstractLinearInvariantPattern> result = new Dnf<>();

		result.addAll(pattern);
		// Add conjuncts from transformula as additional disjuncts
		result.addAll(transFormulaAsLinIneqs);
		return result;
	}

	@Override
	public void extractValuesForPatternCoefficients() {
		assert mAllPatternCoefficients != null : "mAllPatternCoefficients must not be null!";
		try {
			if (mSimplifySatisfyingAssignment == SimplificationType.NO_SIMPLIFICATION) {
				mPatternCoefficients2Values = ModelExtractionUtils.getValuation(mSolver, mAllPatternCoefficients);
			} else if (mSimplifySatisfyingAssignment == SimplificationType.SIMPLE) {
				mPatternCoefficients2Values = ModelExtractionUtils.getSimplifiedAssignment(mSolver,
						mAllPatternCoefficients, mLogger, mServices);
			} else {
				mPatternCoefficients2Values = ModelExtractionUtils.getSimplifiedAssignment_TwoMode(mSolver,
						mAllPatternCoefficients, mLogger, mServices);
			}
		} catch (final TermException e) {
			e.printStackTrace();
			mLogger.error("Getting values for coefficients failed.");
		}
	}
}
