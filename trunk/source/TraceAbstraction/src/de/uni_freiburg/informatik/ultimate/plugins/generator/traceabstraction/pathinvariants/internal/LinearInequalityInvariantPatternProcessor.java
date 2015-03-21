package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Transition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * A {@link IInvariantPatternProcessor} using patterns composed of linear
 * inequalities on a linear approximation of the program.
 * 
 * The outer collection within the invariant pattern type represents a
 * disjunction, the inner one a conjunction.
 */
public final class LinearInequalityInvariantPatternProcessor
		extends
		AbstractSMTInvariantPatternProcessor<Collection<Collection<AffineFunctionGenerator>>> {

	private static final String PREFIX = "liipp_";
	private static final String PREFIX_SEPARATOR = "_";

	private final Logger logger;
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
	private final Set<RankVar> patternCoefficients;
	private Map<Term, Term> validConfiguration;
	private Collection<Collection<AffineFunctionGenerator>> entryInvariantPattern;
	private Collection<Collection<AffineFunctionGenerator>> exitInvariantPattern;
	private int prefixCounter;

	/**
	 * Creates a pattern processor using linear inequalities as patterns.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param smtManager
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
	 */
	public LinearInequalityInvariantPatternProcessor(
			final IUltimateServiceProvider services,
			final PredicateUnifier predicateUnifier,
			final SmtManager smtManager, final Script solver,
			final ControlFlowGraph cfg, final IPredicate precondition,
			final IPredicate postcondition,
			final ILinearInequalityInvariantPatternStrategy strategy) {
		super(predicateUnifier, smtManager);
		this.logger = services.getLoggingService().getLogger(
				Activator.s_PLUGIN_ID);
		this.solver = solver;
		this.strategy = strategy;
		this.cfg = cfg;

		this.patternVariables = new ArrayList<>();
		this.patternCoefficients = new HashSet<>();

		this.linearizer = new CachedTransFormulaLinearizer(services, smtManager);
		final Boogie2SMT boogie2smt = smtManager.getBoogie2Smt();
		this.precondition = linearizer.linearize(new TransFormula(precondition,
				boogie2smt));
		this.postcondition = linearizer.linearize(new TransFormula(
				postcondition, boogie2smt));
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void startRound(int round) {
		reinitializeSolver();
		patternVariables.clear();
		validConfiguration = null;
		entryInvariantPattern = null;
		exitInvariantPattern = null;
		prefixCounter = 0;

		// In the first round, linearize and populate
		// {@link #patternCoefficients}.
		if (round == 0) {
			logger.log(Level.INFO, "[LIIPP] First round, linearizing...");
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
			logger.log(Level.INFO, "[LIIPP] Linearization complete.");
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
	public Collection<Collection<AffineFunctionGenerator>> getInvariantPatternForLocation(
			final Location location, final int round) {
		// Build invariant pattern
		final int[] dimensions = strategy.getDimensions(location, round);
		final Collection<Collection<AffineFunctionGenerator>> disjunction = new ArrayList<>(
				dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<AffineFunctionGenerator> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				final AffineFunctionGenerator inequality = new AffineFunctionGenerator(
						solver, patternCoefficients, newPrefix());
				patternVariables.addAll(inequality.getVariables());
				conjunction.add(inequality);
			}
			disjunction.add(conjunction);
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
	 * Example code provided by Matthias. DO NOT CALL. TODO: Remove once
	 * everything is used elsewhere.
	 * 
	 * @deprecated
	 */
	private void matthiasExampleCode() {
		MotzkinTransformation mt = new MotzkinTransformation(solver,
				AnalysisType.Nonlinear, false);
		Collection<LinearInequality> linearInequalities = null;
		mt.add_inequalities(linearInequalities);
		mt.transform(new Rational[0]);

		// construct new 0-ary function symbol
		solver.declareFun("coefficient", new Sort[0], solver.sort("Real"));
		// statt dessen lieber
		Term zeroary = SmtUtils.buildNewConstant(solver, "coefficient", "Real");
		Term t1 = null;
		Term t2 = null;
		solver.term("and", t1, t2);
		Util.and(solver, t1, t2);
		solver.term("<=", t1, t2);
		SmtUtils.leq(solver, t1, t2);

		Term contraint = null;
		solver.assertTerm(contraint);
		LBool sat = solver.checkSat();
		switch (sat) {
		case SAT: {
			// extract values
			Collection<Term> coefficientsOfAllInvariants = null;
			Map<Term, Rational> valuation;
			boolean simplifiedValuation = false;
			try {
				if (simplifiedValuation) {
					valuation = ModelExtractionUtils.getSimplifiedAssignment(
							solver, coefficientsOfAllInvariants, logger);
				} else {
					valuation = ModelExtractionUtils.getValuation(solver,
							coefficientsOfAllInvariants);
				}
			} catch (TermException e) {
				e.printStackTrace();
				throw new AssertionError("model extraction failed");
			}
		}
			break;
		case UNKNOWN:
		case UNSAT:
		default:
			break;
		}
	}

	/**
	 * Generates a {@link Term} that is true iff the given
	 * {@link LinearTransition} is equivalent to a given invariant pattern over
	 * the primed variables of the transition.
	 * 
	 * @see #precondition
	 * @see #postcondition
	 * @param condition
	 *            transition to build the equivalence term from, usually a pre-
	 *            or postcondition
	 * @param pattern
	 *            pattern to build the equivalence term from
	 * @return equivalence term
	 */
	private Term buildEquivalenceTerm(final LinearTransition condition,
			final Collection<Collection<AffineFunctionGenerator>> pattern) {
		// TODO: implement
		throw new UnsupportedOperationException("not implemented");
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
			final InvariantTransitionPredicate<Collection<Collection<AffineFunctionGenerator>>> predicate) {
		// TODO: implement
		throw new UnsupportedOperationException("not implemented");
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public boolean hasValidConfiguration(
			final Collection<InvariantTransitionPredicate<Collection<Collection<AffineFunctionGenerator>>>> predicates,
			final int round) {
		logger.log(Level.INFO, "[LIIPP] Start generating terms.");
		solver.assertTerm(buildEquivalenceTerm(precondition,
				entryInvariantPattern));
		solver.assertTerm(buildEquivalenceTerm(postcondition,
				exitInvariantPattern));
		for (final InvariantTransitionPredicate<Collection<Collection<AffineFunctionGenerator>>> predicate : predicates) {
			solver.assertTerm(buildPredicateTerm(predicate));
		}

		logger.log(Level.INFO, "[LIIPP] Terms generated, checking SAT.");
		if (solver.checkSat() != LBool.SAT) {
			// No configuration found
			logger.log(Level.INFO, "[LIIPP] No solution found.");
			return false;
		}

		logger.log(Level.INFO, "[LIIPP] Solution found!");
		validConfiguration = solver.getValue(patternVariables
				.toArray(new Term[patternVariables.size()]));

		throw new UnsupportedOperationException("not implemented");
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return strategy.getMaxRounds();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected Term getTermForPattern(
			final Collection<Collection<AffineFunctionGenerator>> pattern) {
		final Map<RankVar, Term> definitionMap = new HashMap<RankVar, Term>(
				patternCoefficients.size());
		for (final RankVar coefficient : patternCoefficients) {
			definitionMap.put(coefficient, coefficient.getDefinition());
		}

		final Collection<Term> conjunctions = new ArrayList<Term>(
				pattern.size());
		for (final Collection<AffineFunctionGenerator> conjunct : pattern) {
			final Collection<Term> inequalities = new ArrayList<Term>(
					conjunct.size());
			for (final AffineFunctionGenerator inequality : conjunct) {
				inequalities.add(inequality.generate(definitionMap).asTerm(
						solver));
			}
			conjunctions.add(SmtUtils.and(solver, inequalities));
		}
		return SmtUtils.or(solver, conjunctions);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected TermTransformer getConfigurationTransformer() {
		return new SafeSubstitution(solver, validConfiguration);
	}

	/**
	 * Reset solver and initialize it afterwards. For initializing, we set the
	 * option produce-models to true (this allows us to obtain a satisfying
	 * assignment) and we set the logic to QF_NRA (nonlinear real arithmetic).
	 * TODO: Matthias unsat cores might be helpful for debugging.
	 */
	private void reinitializeSolver() {
		solver.reset();
		solver.setOption(":produce-models", true);
		boolean someExtendedDebugging = false;
		if (someExtendedDebugging) {
			solver.setOption(":produce-unsat-cores", true);
		}
		solver.setLogic(Logics.QF_NRA);
	}

}
