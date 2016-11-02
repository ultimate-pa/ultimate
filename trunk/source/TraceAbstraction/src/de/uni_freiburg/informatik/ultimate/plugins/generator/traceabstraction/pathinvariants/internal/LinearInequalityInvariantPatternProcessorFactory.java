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

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ScriptWithTermConstructionChecks;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Factory producing {@link LinearInequalityInvariantPatternProcessor}s.
 */
public class LinearInequalityInvariantPatternProcessorFactory
		implements
		IInvariantPatternProcessorFactory<Collection<Collection<LinearPatternBase>>> {

	protected final IUltimateServiceProvider services;
	protected final IToolchainStorage storage;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	protected final PredicateUnifier predUnifier;
	protected final ManagedScript csToolkit;
	protected final ILinearInequalityInvariantPatternStrategy strategy;
	private final boolean mUseNonlinearConstraints;
	private final Settings mSolverSettings;
	private final Collection<Term> mAxioms;

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
	 * @param csToolkit
	 *            the smt manager to use with the predicateUnifier
	 * @param strategy
	 *            the invariant strategy to pass to the produced processor
	 * @param simplificationTechnique 
	 * @param xnfConversionTechnique 
	 * @param axioms 
	 */
	public LinearInequalityInvariantPatternProcessorFactory(
			final IUltimateServiceProvider services,
			final IToolchainStorage storage,
			final PredicateUnifier predUnifier, final ManagedScript csToolkit,
			final ILinearInequalityInvariantPatternStrategy strategy, final boolean useNonlinerConstraints, final Settings solverSettings, final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique, final Collection<Term> axioms) {
		this.services = services;
		this.storage = storage;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		this.predUnifier = predUnifier;
		this.csToolkit = csToolkit;
		mAxioms = axioms;
		this.strategy = strategy;
		mUseNonlinearConstraints = useNonlinerConstraints;
		mSolverSettings = solverSettings;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public LinearInequalityInvariantPatternProcessor produce(
			final ControlFlowGraph cfg, final IPredicate precondition,
			final IPredicate postcondition) {
		return new LinearInequalityInvariantPatternProcessor(services,
				storage, predUnifier, csToolkit, mAxioms, produceSmtSolver(), cfg, precondition,
				postcondition, strategy, mUseNonlinearConstraints, mSimplificationTechnique, mXnfConversionTechnique);
	}

	/**
	 * Produces a SMT solver instance.
	 * 
	 * @return SMT solver instance to use
	 */
	protected Script produceSmtSolver() {
		final Logics logic;
		if (mUseNonlinearConstraints) {
			logic = Logics.QF_NRA;
		} else {
			logic = Logics.QF_LRA;
		}
		Script script = SolverBuilder.buildAndInitializeSolver(services, storage, 
				SolverMode.External_DefaultMode, mSolverSettings, 
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
		final boolean dumpSmtScriptToFile = false;
		final String pathOfDumpedScript = ".";
		final String baseNameOfDumpedScript = "contraintSolving";
		final String solverCommand;
		if (mUseNonlinearConstraints) {
			solverCommand = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
		} else {
			solverCommand = "yices-smt2 --incremental";
		}
		final boolean fakeNonIncrementalSolver = false;
		return new Settings(fakeNonIncrementalSolver , true,
				solverCommand, -1, null,
				dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript);
	}

}
