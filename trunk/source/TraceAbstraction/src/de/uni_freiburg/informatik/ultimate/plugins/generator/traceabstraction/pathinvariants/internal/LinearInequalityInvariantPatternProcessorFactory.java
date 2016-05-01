/*
 * Copyright (C) 2015 David Zschocke
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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ScriptWithTermConstructionChecks;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
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
	private final boolean m_UseNonlinearConstraints;
	private final Settings m_SolverSettings;

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
			final ILinearInequalityInvariantPatternStrategy strategy, boolean useNonlinerConstraints, Settings solverSettings) {
		this.services = services;
		this.storage = storage;
		this.predUnifier = predUnifier;
		this.smtManager = smtManager;
		this.strategy = strategy;
		this.m_UseNonlinearConstraints = useNonlinerConstraints;
		this.m_SolverSettings = solverSettings;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public LinearInequalityInvariantPatternProcessor produce(
			ControlFlowGraph cfg, IPredicate precondition,
			IPredicate postcondition) {
		return new LinearInequalityInvariantPatternProcessor(services,
				storage, predUnifier, smtManager, produceSmtSolver(), cfg, precondition,
				postcondition, strategy, m_UseNonlinearConstraints);
	}

	/**
	 * Produces a SMT solver instance.
	 * 
	 * @return SMT solver instance to use
	 */
	protected Script produceSmtSolver() {
		final Logics logic;
		if (m_UseNonlinearConstraints) {
			logic = Logics.QF_NRA;
		} else {
			logic = Logics.QF_LRA;
		}
		Script script = SolverBuilder.buildAndInitializeSolver(services, storage, 
				SolverMode.External_DefaultMode, m_SolverSettings, 
				false, false, logic.toString(), "InvariantSynthesis"); 
		script = new ScriptWithTermConstructionChecks(script);
		return script;
	}

	/**
	 * Produces SMT solver settings to be used within
	 * {@link #produceSmtSolver()}.
	 * 
	 * @return SMT solver settings to use
	 */
	@Deprecated
	private Settings produceSolverSettings() {
		boolean dumpSmtScriptToFile = false;
		String pathOfDumpedScript = ".";
		String baseNameOfDumpedScript = "contraintSolving";
		final String solverCommand;
		if (m_UseNonlinearConstraints) {
			solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
		} else {
			solverCommand = "yices-smt2 --incremental";
		}
		return new Settings(true,
				solverCommand, -1, null,
				dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
	}

}
