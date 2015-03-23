package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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
 * disjunction, the inner one a conjunction. Within the inner conjunction, there
 * are strict and non-strict inequalities. These collections are generated
 * according to a {@link ILinearInequalityInvariantPatternStrategy}.
 */
public final class LinearInequalityInvariantPatternProcessor
		extends
		AbstractSMTInvariantPatternProcessor<Collection<Collection<LinearPatternBase>>> {

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
	private Collection<Collection<LinearPatternBase>> entryInvariantPattern;
	private Collection<Collection<LinearPatternBase>> exitInvariantPattern;
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
	public Collection<Collection<LinearPatternBase>> getInvariantPatternForLocation(
			final Location location, final int round) {
		// Build invariant pattern
		final int[] dimensions = strategy.getDimensions(location, round);
		final Collection<Collection<LinearPatternBase>> disjunction = new ArrayList<>(
				dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<LinearPatternBase> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				for (final boolean strict : new boolean[] { true, false }) {
					final LinearPatternBase inequality = new LinearPatternBase(
							solver, patternCoefficients, newPrefix(), strict);
					patternVariables.addAll(inequality.getVariables());
					conjunction.add(inequality);
				}
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
	 * Transforms a pattern into a DNF of linear inequalities relative to a
	 * given mapping of {@link RankVar}s involved.
	 * 
	 * @param pattern
	 *            the pattern to transform
	 * @param mapping
	 *            the mapping to use
	 * @return transformed pattern, equivalent to the pattern under the mapping
	 */
	private static Collection<Collection<LinearInequality>> mapPattern(
			final Collection<Collection<LinearPatternBase>> pattern,
			final Map<RankVar, Term> mapping) {
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
	 * relative to a given mapping of {@link RankVar}s involved.
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
			final Map<RankVar, Term> mapping) {
		// This is the trivial algorithm (expanding). Feel free to optimize ;)
		// 1. map Pattern, result is dnf
		final Collection<Collection<LinearInequality>> mappedPattern = 
				mapPattern(pattern, mapping);
		// 2. negate every LinearInequality, result is a cnf
		final Collection<Collection<LinearInequality>> cnfAfterNegation = 
				new ArrayList<>(mappedPattern.size());
		for (final Collection<LinearInequality> conjunct : mappedPattern) {
			final Collection<LinearInequality> disjunctWithNegatedLinearInequalities =
					new ArrayList<>(conjunct.size());
			for (final LinearInequality li : conjunct) {
				// copy original linear inequality
				final LinearInequality negatedLi = new LinearInequality(li);
				negatedLi.negate();
				disjunctWithNegatedLinearInequalities.add(negatedLi);
			}
			cnfAfterNegation.add(disjunctWithNegatedLinearInequalities);
		}
		// 3. expand the cnf to get a dnf
		final Collection<Collection<LinearInequality>> mappedAndNegatedPattern =
				expandCnfToDnf(cnfAfterNegation);
		// 4. return the resulting dnf as the solution
		return mappedAndNegatedPattern;
	}

	/**
	 * Transforms a cnf (given as two nested Collections of linear inequalites)
	 * into dnf (given as two nested Collections of linear inequalites).
	 * 
	 * @param cnf
	 *            the collection of conjuncts consisting of disjuncts of linear
	 *            inequalities
	 * @return a dnf (Collection of disjuncts consisting of conjuncts of linear
	 *         inequalities), equivalent to the given cnf
	 */
	private static Collection<Collection<LinearInequality>> expandCnfToDnf(
			final Collection<Collection<LinearInequality>> cnf) {
		Iterator<Collection<LinearInequality>> cnfIterator = cnf.iterator();
		if (!cnfIterator.hasNext()) {
			throw new IllegalArgumentException(
					"Could not convert cnf into dnf,"
					+ " because empty cnf was given");
		}
		// the first disjunct is the initial dnf
		Collection<LinearInequality> initialDisjunct = cnfIterator.next();
		Collection<Collection<LinearInequality>> initialDnf = new ArrayList<>(
				initialDisjunct.size());
		for (LinearInequality li : initialDisjunct) {
			Collection<LinearInequality> unitClause = new ArrayList<>(1);
			unitClause.add(li);
			initialDnf.add(unitClause);
		}
		Collection<Collection<LinearInequality>> resultDnf = initialDnf;
		while (cnfIterator.hasNext()) {
			resultDnf = singleExpandationCnfToDnf(cnfIterator.next(), resultDnf);
		}
		return resultDnf;

	}

	/**
	 * Performs a single expandation on the way from a cnf to an equivalent dnf:
	 * given: disjunct /\ dnf output: new dnf equivalnt to disjunct /\ dnf
	 * 
	 * @param firstDisjunct
	 *            the first disjunct (conjuncted with the second disjunct they
	 *            form the cnf given)
	 * @param cnf
	 *            the cnf so far
	 * @return a dnf from this cnf
	 */
	private static Collection<Collection<LinearInequality>> singleExpandationCnfToDnf(
			Collection<LinearInequality> disjunct,
			Collection<Collection<LinearInequality>> dnf) {
		// there are disjunct.size() * dnf.size() conjuncts afterwards
		final Collection<Collection<LinearInequality>> resultDnf = 
				new ArrayList<>(disjunct.size() * dnf.size());
		for (LinearInequality linearInequalityInFirstDisjunct : disjunct) {
			for (Collection<LinearInequality> conjunctInDnf : dnf) {
				Collection<LinearInequality> conjunctInResultDnf = 
						new ArrayList<LinearInequality>(conjunctInDnf.size()+1);
				conjunctInResultDnf.addAll(conjunctInDnf);
				conjunctInResultDnf.add(linearInequalityInFirstDisjunct);
				resultDnf.add(conjunctInResultDnf);
			}
		}
		return resultDnf;
	}

	/**
	 * Calculates a DNF of the conjunction of an arbitrary set of DNFs.
	 * 
	 * @param dnfs
	 *            DNFs to conjunct together
	 * @return DNF representing the conjunction of the DNFs provided, returns
	 *         NULL if no DNFs were given.
	 */
	@SafeVarargs
	private static Collection<Collection<LinearInequality>> expandConjunction(
			final Collection<? extends Collection<LinearInequality>>... dnfs) {
		boolean firstElement = true;
		Collection<Collection<LinearInequality>> expandedDnf = null;
		for (Collection<? extends Collection<LinearInequality>> currentDnf : dnfs) {
			if (firstElement) {
				expandedDnf = (Collection<Collection<LinearInequality>>) currentDnf;
				firstElement = false;
			} else {
				for (Collection<LinearInequality> currentDisjunct : currentDnf) {
					expandedDnf = singleExpandationCnfToDnf(currentDisjunct,
							expandedDnf);
				}
			}

		}
		return expandedDnf;
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
			final Collection<? extends Collection<LinearInequality>>... dnfs) {
		final Collection<Collection<LinearInequality>> conjunctionDNF = 
				expandConjunction(dnfs);

		// Apply Motzkin and generate the conjunction of the resulting Terms
		final Collection<Term> resultTerms = new ArrayList<Term>(
				conjunctionDNF.size());
		for (final Collection<LinearInequality> conjunct : conjunctionDNF) {
			final MotzkinTransformation transformation = 
					new MotzkinTransformation(
							solver, AnalysisType.Nonlinear, false);
			transformation.add_inequalities(conjunct);
			resultTerms.add(transformation.transform(new Rational[0]));
		}
		return SmtUtils.and(solver, resultTerms);
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
		final Map<RankVar, Term> primedMapping = condition.getOutVars();

		final Collection<List<LinearInequality>> conditionDNF = condition
				.getPolyhedra();
		final Collection<Collection<LinearInequality>> negPatternDNF = 
				mapAndNegatePattern(pattern, primedMapping);
		int numberOfInequalities = 0;
		for (Collection<LinearInequality> conjunct : negPatternDNF) {
			numberOfInequalities += conjunct.size();
		}
		this.logger.log(Level.INFO, "[LIIPP] Got an implication term with "
				+ numberOfInequalities + " conjuncts");

		return transformNegatedConjunction(conditionDNF, negPatternDNF);
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
		final Map<RankVar, Term> unprimedMapping = transition.getInVars();
		final Map<RankVar, Term> primedMapping = transition.getOutVars();

		final Collection<Collection<LinearInequality>> startInvariantDNF = 
				mapPattern(predicate.getInvStart(), unprimedMapping);
		final Collection<Collection<LinearInequality>> endInvariantDNF = 
				mapAndNegatePattern(predicate.getInvEnd(), primedMapping);
		int numberOfInequalities = 0;
		for (Collection<LinearInequality> conjunct : endInvariantDNF) {
			numberOfInequalities += conjunct.size();
		}
		this.logger.log(Level.INFO, "[LIIPP] Got a predicate term with "
				+ numberOfInequalities + " conjuncts");
		final Collection<List<LinearInequality>> transitionDNF = transition
				.getPolyhedra();

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
		logger.log(Level.INFO, "[LIIPP] Start generating terms.");
		solver.assertTerm(buildImplicationTerm(precondition,
				entryInvariantPattern));
		solver.assertTerm(buildImplicationTerm(postcondition,
				exitInvariantPattern));
		for (final InvariantTransitionPredicate<Collection<Collection<LinearPatternBase>>> predicate : predicates) {
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

		return true;
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
			final Collection<Collection<LinearPatternBase>> pattern) {
		final Map<RankVar, Term> definitionMap = new HashMap<RankVar, Term>(
				patternCoefficients.size());
		for (final RankVar coefficient : patternCoefficients) {
			definitionMap.put(coefficient, coefficient.getDefinition());
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
