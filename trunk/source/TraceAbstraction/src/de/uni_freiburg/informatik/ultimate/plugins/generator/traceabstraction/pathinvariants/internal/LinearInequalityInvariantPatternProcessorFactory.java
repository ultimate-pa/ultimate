package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ScriptWithTermConstructionChecks;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Factory producing {@link LinearInequalityInvariantPatternProcessor}s.
 */
public class LinearInequalityInvariantPatternProcessorFactory
		implements
		IInvariantPatternProcessorFactory<Collection<Collection<LinearPatternBase>>> {

	protected final IUltimateServiceProvider services;
	protected final IToolchainStorage storage;
	protected final PredicateUnifier predUnifier;
	protected final SmtManager smtManager;
	protected final ILinearInequalityInvariantPatternStrategy strategy;

	/**
	 * Constructs a new factory for
	 * {@link LinearInequalityInvariantPatternProcessor}s.
	 * 
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param predUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param smtManager
	 *            the smt manager to use with the predicateUnifier
	 * @param strategy
	 *            the invariant strategy to pass to the produced processor
	 */
	public LinearInequalityInvariantPatternProcessorFactory(
			final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final PredicateUnifier predUnifier, final SmtManager smtManager,
			final ILinearInequalityInvariantPatternStrategy strategy) {
		this.services = services;
		this.storage = storage;
		this.predUnifier = predUnifier;
		this.smtManager = smtManager;
		this.strategy = strategy;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public LinearInequalityInvariantPatternProcessor produce(
			ControlFlowGraph cfg, IPredicate precondition,
			IPredicate postcondition) {
		return new LinearInequalityInvariantPatternProcessor(services,
				predUnifier, smtManager, produceSmtSolver(), cfg, precondition,
				postcondition, strategy);
	}

	/**
	 * Produces a SMT solver instance.
	 * 
	 * @return SMT solver instance to use
	 */
	protected Script produceSmtSolver() {
		Script script = SolverBuilder.buildScript(services, storage,
				produceSolverSettings());
		script = new ScriptWithTermConstructionChecks(script);
		return script;
	}

	/**
	 * Produces SMT solver settings to be used within
	 * {@link #produceSmtSolver()}.
	 * 
	 * @return SMT solver settings to use
	 */
	protected Settings produceSolverSettings() {
		boolean dumpSmtScriptToFile = !true;
		String pathOfDumpedScript = "~";
		String baseNameOfDumpedScript = "contraintSolving";
		return new Settings(true,
				"z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000", -1, null,
				dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
	}

}
