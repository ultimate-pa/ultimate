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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * A {@link IInvariantPatternProcessor} using patterns composed of linear
 * inequalities on a linear approximation of the program.
 * 
 * The outer collection within the invariant pattern type represents a
 * disjunction, the inner one a conjunction. Within the inner conjunction, there
 * are strict and non-strict inequalities. These collections are generated
 * according to a {@link ILinearInequalityInvariantPatternStrategy}.
 */
public final class LinearInequalityInvariantPatternProcessor
		extends
		AbstractSMTInvariantPatternProcessor<Collection<Collection<LinearPatternBase>>> {

	private static final String PREFIX = "liipp_";
	private static final String PREFIX_SEPARATOR = "_";
	
	private final IUltimateServiceProvider services;
	private final ILogger logger;
	private final Script solver;
	private final ILinearInequalityInvariantPatternStrategy strategy;
	private final LinearTransition precondition;
	private final LinearTransition postcondition;
	private final CachedTransFormulaLinearizer linearizer;
	private final ControlFlowGraph cfg;

	/**
	 * The pattern variables, that is the coefficients of program- and helper
	 * variables.
	 */
	private final Collection<Term> patternVariables;
	/**
	 * The pattern coefficients, that is the program- and helper variables.
	 */
	private final Set<IProgramVar> patternCoefficients;
	private Map<Term, Rational> valuation;
	private Collection<Collection<LinearPatternBase>> entryInvariantPattern;
	private Collection<Collection<LinearPatternBase>> exitInvariantPattern;
	private int prefixCounter;
	private int currentRound;
	private int maxRounds;
	private final boolean mUseNonlinearConstraints; 
	private final boolean mSimplifySatisfyingAssignment = true;
	/**
	 * If set to true, we always construct two copies of each invariant
	 * pattern, one strict inequality and one non-strict inequality.
	 * If set to false we use only one non-strict inequality.
	 */
	private final boolean mAlwaysStrictAndNonStrictCopies = false;

	/**
	 * Creates a pattern processor using linear inequalities as patterns.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param predicateScript
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
	 */
	public LinearInequalityInvariantPatternProcessor(
			final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final PredicateUnifier predicateUnifier,
			final ManagedScript predicateScript, final Collection<Term> axioms, 
			final Script solver,
			final ControlFlowGraph cfg, final IPredicate precondition,
			final IPredicate postcondition,
			final ILinearInequalityInvariantPatternStrategy strategy,
			final boolean useNonlinearConstraints, 
			final SimplificationTechnique simplicationTechnique, 
			final XnfConversionTechnique xnfConversionTechnique) {
		super(predicateUnifier, predicateScript);
		this.services = services;
		logger = services.getLoggingService().getLogger(
				Activator.PLUGIN_ID);
		this.solver = solver;
		this.strategy = strategy;
		this.cfg = cfg;

		patternVariables = new ArrayList<>();
		patternCoefficients = new HashSet<>();

		linearizer = new CachedTransFormulaLinearizer(services, 
				predicateScript, axioms, storage, simplicationTechnique, xnfConversionTechnique);
		this.precondition = linearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(precondition, predicateScript));
		this.postcondition = linearizer.linearize(
				TransFormulaBuilder.constructTransFormulaFromPredicate(postcondition, predicateScript));
		
		currentRound = -1;
		maxRounds = strategy.getMaxRounds();
		mUseNonlinearConstraints = useNonlinearConstraints;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void startRound(final int round, boolean useLiveVariables, final Set<IProgramVar> liveVariables) {
		reinitializeSolver();
		patternVariables.clear();
		entryInvariantPattern = null;
		exitInvariantPattern = null;
		prefixCounter = 0;
		currentRound = round;

		// In the first round, linearize and populate
		// {@link #patternCoefficients}.
		if (round == 0) {
			logger.info( "[LIIPP] First round, linearizing...");
			patternCoefficients.clear();
			for (final Transition transition : cfg.getTransitions()) {
				final LinearTransition lTransition = linearizer
						.linearize(transition.getTransFormula());
				patternCoefficients.addAll(lTransition.getInVars().keySet());
				patternCoefficients.addAll(lTransition.getOutVars().keySet());
			}
			patternCoefficients.addAll(precondition.getInVars().keySet());
			patternCoefficients.addAll(precondition.getOutVars().keySet());
			patternCoefficients.addAll(postcondition.getInVars().keySet());
			patternCoefficients.addAll(postcondition.getOutVars().keySet());
			if (useLiveVariables) {
				patternCoefficients.retainAll(liveVariables);
			}
			logger.info( "[LIIPP] Linearization complete.");
		}
	}

	/**
	 * Generates a new prefix, which is guaranteed (within prefixes generated
	 * through this method on one single instance) to be unique within the
	 * current round.
	 * 
	 * @return unique prefix (within this instance and round)
	 */
	protected String newPrefix() {
		return PREFIX + (prefixCounter++) + PREFIX_SEPARATOR;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Collection<Collection<LinearPatternBase>> getInvariantPatternForLocation(
			final Location location, final int round) {
		// Build invariant pattern
		
		final Collection<Collection<LinearPatternBase>> disjunction;
		if (cfg.getEntry().equals(location)) {
			// entry pattern is equivalent to true
			final Collection<LinearPatternBase> emptyConjunction = Collections.emptyList();
			disjunction = Collections.singleton(emptyConjunction);
		} else if (cfg.getExit().equals(location)) {
			// exit pattern is equivalent to false
			disjunction = Collections.emptyList();
		} else {
			final int[] dimensions = strategy.getDimensions(location, round);
			disjunction = new ArrayList<>(dimensions[0]);
			for (int i = 0; i < dimensions[0]; i++) {
				final Collection<LinearPatternBase> conjunction = new ArrayList<>(
						dimensions[1]);
				for (int j = 0; j < dimensions[1]; j++) {
					final boolean[] invariantPatternCopies;
					if (mAlwaysStrictAndNonStrictCopies ) {
						invariantPatternCopies = new boolean[] { false, true }; 
					} else {
						invariantPatternCopies = new boolean[] { false };
					}
					for (final boolean strict : invariantPatternCopies) {
						final LinearPatternBase inequality = new LinearPatternBase(
								solver, patternCoefficients, newPrefix(), strict);
						patternVariables.addAll(inequality.getVariables());
						conjunction.add(inequality);
					}
				}
				disjunction.add(conjunction);
			}
		}

		// Keep track of entry and exit patterns, as we need them separately
		if (cfg.getEntry().equals(location)) {
			entryInvariantPattern = disjunction;
		} else if (cfg.getExit().equals(location)) {
			exitInvariantPattern = disjunction;
		}

		return disjunction;
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
			final Collection<Collection<LinearPatternBase>> pattern,
			final Map<IProgramVar, Term> mapping) {
		final Collection<Collection<LinearInequality>> result = new ArrayList<>(
				pattern.size());
		for (final Collection<LinearPatternBase> conjunct : pattern) {
			final Collection<LinearInequality> mappedConjunct = new ArrayList<>(
					conjunct.size());
			for (final LinearPatternBase base : conjunct) {
				mappedConjunct.add(base.getLinearInequality(mapping));
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
			final Collection<Collection<LinearPatternBase>> pattern,
			final Map<IProgramVar, Term> mapping) {
		// This is the trivial algorithm (expanding). Feel free to optimize ;)
		// 1. map Pattern, result is dnf
		final Collection<Collection<LinearInequality>> mappedPattern = mapPattern(
				pattern, mapping);
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
	 * Performs a single expandation, meaning transforming
	 * conjunct /\ dnf to an equivalent dnf
	 * @param dnf the dnf the conjunct is conjuncted to
	 * @param conjunct the conjunct that is conjuncted to the dnf
	 * @param <E> : the type of Literals in the cnf/dnf
	 * @return a new dnf equivalent to conjunct /\ dnf
	 */
	private static <E> Collection<Collection<E>> expandCnfToDnfSingle(
			final Collection<Collection<E>> dnf, final Collection<E> conjunct) {
		final Collection<Collection<E>> result = new ArrayList<>();
		for (final Collection<E> disjunct : dnf) {
			for (final E item : conjunct) {
				final Collection<E> resultItem = new ArrayList<>();
				resultItem.addAll(disjunct);
				resultItem.add(item);
				result.add(resultItem);
			}
		}
		return result;

	}

	/**
	 * Transforms a cnf (given as two nested Collections of atoms (usually linear inequalites))
	 * into dnf (given as two nested Collections of atoms (usually linear inequalites)).
	 * @param <E> type of the atoms
	 * 
	 * @param cnf
	 *            the collection of conjuncts consisting of disjuncts of linear
	 *            inequalities
	 * @return a dnf (Collection of disjuncts consisting of conjuncts of linear
	 *         inequalities), equivalent to the given cnf
	 */
	private static <E> Collection<Collection<E>> expandCnfToDnf(
			final Collection<Collection<E>> cnf) {
		if (cnf.isEmpty()) {
			final Collection<E> empty = Collections.emptyList();
			return Collections.singleton(empty);
		}
		boolean firstElement = true;
		Collection<Collection<E>> expandedDnf = null;
		for (final Collection<E> conjunct : cnf) {
			if (firstElement) {
				expandedDnf = new ArrayList<>();
				for(final E e : conjunct){
					final Collection<E> conjunctSingleton = new ArrayList<>();
					conjunctSingleton.add(e);
					expandedDnf.add(conjunctSingleton);
				}
				firstElement = false;
			} else {
				expandedDnf = expandCnfToDnfSingle(expandedDnf, conjunct);
			}
		}
		assert expandedDnf != null;
		return expandedDnf;
	}

	/**
	 * Given two disjunctions a and b of conjunctions, this method calculates a
	 * new disjunction of conjunctions equivalent to a /\ b
	 * @param a the first dnf
	 * @param b the second dnf
	 * @param <E> the type of the literals in the dnf
	 * @return a new dnf equivalent to a /\ b
	 */
	private static <E> Collection<Collection<E>> expandConjunctionSingle(
			final Collection<Collection<E>> a, final Collection<Collection<E>> b) {
		final Collection<Collection<E>> result = new ArrayList<>();
		for (final Collection<E> aItem : a) {
			for (final Collection<E> bItem : b) {
				final Collection<E> resultItem = new ArrayList<>();
				resultItem.addAll(aItem);
				resultItem.addAll(bItem);
				result.add(resultItem);
			}
		}
		return result;
	}

	/**
	 * Calculates a DNF of the conjunction of an arbitrary set of DNFs.
	 * 
	 * @param <E> the type of the literals in the dnfs
	 * 
	 * @param dnfs
	 *            DNFs to conjunct together
	 * @return DNF representing the conjunction of the DNFs provided, returns
	 *         NULL if no DNFs were given.
	 */
	private static <E> Collection<Collection<E>> expandConjunction(
			final Collection<Collection<E>>... dnfs) {
		boolean firstElement = true;
		Collection<Collection<E>> expandedDnf = null;
		for (final Collection<Collection<E>> currentDnf : dnfs) {
			if (firstElement) {
				expandedDnf = currentDnf;
				firstElement = false;
			} else {
				expandedDnf = expandConjunctionSingle(currentDnf, expandedDnf);
			}
		}
		return expandedDnf;
		/**
		 * boolean firstElement = true; Collection<Collection<LinearInequality>>
		 * expandedDnf = null; for (Collection<? extends
		 * Collection<LinearInequality>> currentDnf : dnfs) { if (firstElement)
		 * { expandedDnf = (Collection<Collection<LinearInequality>>)
		 * currentDnf; firstElement = false; } else { final
		 * Collection<Collection<LinearInequality>> newDnf = new ArrayList<>();
		 * for (Collection<LinearInequality> currentDisjunct : currentDnf) {
		 * newDnf.addAll(singleExpandationCnfToDnf(currentDisjunct,
		 * expandedDnf)); } expandedDnf = newDnf; }
		 * 
		 * } return expandedDnf;
		 */
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
		logger.info( "[LIIPP] About to invoke motzkin:");
		for (final Collection<? extends Collection<LinearInequality>> dnf : dnfs) {
			logger.info( "[LIIPP] DNF to transform: " + dnf);
		}
		final Collection<Collection<LinearInequality>> conjunctionDNF = expandConjunction(dnfs);

		// Apply Motzkin and generate the conjunction of the resulting Terms
		final Collection<Term> resultTerms = new ArrayList<Term>(
				conjunctionDNF.size());
		final AnalysisType analysisType = mUseNonlinearConstraints ? 
				AnalysisType.NONLINEAR : AnalysisType.LINEAR;
		for (final Collection<LinearInequality> conjunct : conjunctionDNF) {
			logger.info( "[LIIPP] Transforming conjunct "
					+ conjunct);
			final MotzkinTransformation transformation = new MotzkinTransformation(
					solver, analysisType, false);
			transformation.add_inequalities(conjunct);
			resultTerms.add(transformation.transform(new Rational[0]));
		}
		return SmtUtils.and(solver, resultTerms);
	}

	/**
	 * Completes a given mapping by adding fresh auxiliary terms for any
	 * coefficient (see {@link #patternCoefficients}) which does not yet have a
	 * mapping.
	 * 
	 * After this method returned, the mapping is guaranteed to contain an entry
	 * for every coefficient.
	 * 
	 * @param mapping
	 *            mapping to add auxiliary terms to
	 */
	protected void completeMapping(final Map<IProgramVar, Term> mapping) {
		final String prefix = newPrefix() + "replace_";
		int index = 0;
		for (final IProgramVar coefficient : patternCoefficients) {
			if (mapping.containsKey(coefficient)) {
				continue;
			}
			final Term replacement = SmtUtils.buildNewConstant(solver, prefix
					+ index++, "Real");
			mapping.put(coefficient, replacement);
		}
	}

	/**
	 * Completes a given mapping by adding auxiliary terms from another mapping
	 * for any coefficient (see {@link #patternCoefficients}) which does not yet
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
		for (final IProgramVar coefficient : patternCoefficients) {
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
	 * @see #precondition
	 * @see #postcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre-
	 *            or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildImplicationTerm(final LinearTransition condition,
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				condition.getOutVars());
		completeMapping(primedMapping);

		final Collection<List<LinearInequality>> conditionDNF_ = condition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> conditionDNF = new ArrayList<>();
		for (final List<LinearInequality> list : conditionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>();
			newList.addAll(list);
			conditionDNF.add(newList);
		}
		final Collection<Collection<LinearInequality>> negPatternDNF = mapAndNegatePattern(
				pattern, primedMapping);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : negPatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		logger.info( "[LIIPP] Got an implication term with "
				+ numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(conditionDNF, negPatternDNF);
	}

	/**
	 * Generates a {@link Term} that is true iff a given invariant pattern over
	 * the primed variables of the transition implies the given
	 * {@link LinearTransition}.
	 * 
	 * @see #precondition
	 * @see #postcondition
	 * @param condition
	 *            transition to build the implication term from, usually a pre-
	 *            or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildBackwardImplicationTerm(final LinearTransition condition,
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				condition.getOutVars());
		completeMapping(primedMapping);

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
				pattern, primedMapping);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : PatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		logger.info( "[LIIPP] Got an implication term with "
				+ numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(newConditionDNF, PatternDNF);
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
			final InvariantTransitionPredicate<Collection<Collection<LinearPatternBase>>> predicate) {
		final LinearTransition transition = linearizer.linearize(predicate
				.getTransition());
		final Map<IProgramVar, Term> unprimedMapping = new HashMap<IProgramVar, Term>(
				transition.getInVars());
		completeMapping(unprimedMapping);
		final Map<IProgramVar, Term> primedMapping = new HashMap<IProgramVar, Term>(
				transition.getOutVars());
		completeMapping(primedMapping, unprimedMapping);

		final Collection<Collection<LinearInequality>> startInvariantDNF = mapPattern(
				predicate.getInvStart(), unprimedMapping);
		final Collection<Collection<LinearInequality>> endInvariantDNF = mapAndNegatePattern(
				predicate.getInvEnd(), primedMapping);
		int numberOfInequalities = 0;
		for (final Collection<LinearInequality> conjunct : endInvariantDNF) {
			numberOfInequalities += conjunct.size();
		}
		logger.info( "[LIIPP] Got a predicate term with "
				+ numberOfInequalities + " conjuncts");
		final Collection<List<LinearInequality>> transitionDNF_ = transition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> transitionDNF = new ArrayList<>();
		for (final List<LinearInequality> list : transitionDNF_) {
			final Collection<LinearInequality> newList = new ArrayList<>();
			newList.addAll(list);
			transitionDNF.add(newList);
		}

		return transformNegatedConjunction(startInvariantDNF, endInvariantDNF,
				transitionDNF);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean hasValidConfiguration(
			final Collection<InvariantTransitionPredicate<Collection<Collection<LinearPatternBase>>>> predicates,
			final int round) {
		logger.info( "[LIIPP] Start generating terms.");
		solver.assertTerm(buildImplicationTerm(precondition,
				entryInvariantPattern));
		solver.assertTerm(buildBackwardImplicationTerm(postcondition,
				exitInvariantPattern));
		for (final InvariantTransitionPredicate<Collection<Collection<LinearPatternBase>>> predicate : predicates) {
			solver.assertTerm(buildPredicateTerm(predicate));
		}

		logger.info( "[LIIPP] Terms generated, checking SAT.");
		final LBool result = solver.checkSat();
		if (result == LBool.UNKNOWN) {
			// Prevent additional rounds
			maxRounds = currentRound + 1;
		}
		if (result != LBool.SAT) {
			// No configuration found
			logger.info( "[LIIPP] No solution found.");
			return false;
		}

		logger.info( "[LIIPP] Solution found!");
		final Collection<Term> coefficientsOfAllInvariants = patternVariables;
		try {
			if (mSimplifySatisfyingAssignment) {
				valuation = ModelExtractionUtils.getSimplifiedAssignment(
						solver, coefficientsOfAllInvariants, logger, services);
			} else {
				valuation = ModelExtractionUtils.getValuation(solver,
						coefficientsOfAllInvariants);
			}
		} catch (final TermException e) {
			e.printStackTrace();
			throw new AssertionError("model extraction failed");
		}
		logger.info( "[LIIPP] Valuation: " + valuation);

		return true;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return maxRounds;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected Term getTermForPattern(
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Map<IProgramVar, Term> definitionMap = new HashMap<IProgramVar, Term>(
				patternCoefficients.size());
		for (final IProgramVar coefficient : patternCoefficients) {
			final Term definition = ReplacementVarUtils.getDefinition(coefficient);
			definitionMap.put(coefficient, definition);
		}

		final Collection<Term> conjunctions = new ArrayList<Term>(
				pattern.size());
		for (final Collection<LinearPatternBase> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<Term>(
					conjunct.size());
			for (final LinearPatternBase inequality : conjunct) {
				inequalities.add(inequality.getLinearInequality(definitionMap)
						.asTerm(solver));
			}
			conjunctions.add(SmtUtils.and(solver, inequalities));
		}
		return SmtUtils.or(solver, conjunctions);
	}

	/**
	 * Takes a pattern and generates a term with the smtManager.getScript()
	 * script where the variables are valuated with the values in this.valuation
	 * @param pattern the pattern for which the term is generated
	 * @return a term corresponding to the cnf of LinearInequalites of
	 * the pattern, valueted with the values from this.valuation
	 */
	protected Term getValuatedTermForPattern(
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Script script = mScript.getScript();
		final Collection<Term> conjunctions = new ArrayList<Term>(
				pattern.size());
		for (final Collection<LinearPatternBase> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<Term>(
					conjunct.size());
			for (final LinearPatternBase inequality : conjunct) {
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
			conjunctions.add(SmtUtils.and(mScript.getScript(), inequalities));
		}
		return SmtUtils.or(mScript.getScript(), conjunctions);
	}
	
	private static Term constructZero(final Script script, final Sort sort) {
		if (sort.getRealSort().getName().equals("Int")) {
			return script.numeral(BigInteger.ZERO);
		} else if (sort.getRealSort().getName().equals("Real")) {
			return script.decimal(BigDecimal.ZERO);
		} else {
			throw new IllegalArgumentException("unsupported sort " + sort);
		}
	}

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
		solver.reset();
		solver.setOption(":produce-models", true);
		final boolean someExtendedDebugging = false;
		if (someExtendedDebugging) {
			solver.setOption(":produce-unsat-cores", true);
		}
		final Logics logic;
		if (mUseNonlinearConstraints) {
			logic = Logics.QF_NRA;
		} else {
			logic = Logics.QF_LRA;
		}
		solver.setLogic(logic);
	}

	@Override
	public IPredicate applyConfiguration(
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Term term = getValuatedTermForPattern(pattern);
		return predicateUnifier.getOrConstructPredicate(term);
	}

}
