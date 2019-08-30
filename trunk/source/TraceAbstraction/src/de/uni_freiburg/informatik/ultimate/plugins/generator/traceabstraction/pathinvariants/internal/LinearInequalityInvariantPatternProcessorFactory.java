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

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ScriptWithTermConstructionChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf.Dnf;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.ConstraintSynthesisUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.ConstraintSynthesisUtils.Linearity;

/**
 * Factory producing {@link LinearInequalityInvariantPatternProcessor}s.
 */
public class LinearInequalityInvariantPatternProcessorFactory
		implements IInvariantPatternProcessorFactory<Dnf<AbstractLinearInvariantPattern>> {

	protected final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	protected final IPredicateUnifier predUnifier;
	protected final CfgSmtToolkit mCsToolkit;
	protected final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> mStrategy;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseUnsatCores;
	private final boolean mSynthesizeEntryPattern;
	private final KindOfInvariant mKindOfInvariant;
	private final SolverSettings mSolverSettings;
	private final SmtFunctionsAndAxioms mSmtSymbols;
	private final Map<IcfgLocation, IPredicate> mLoc2underApprox;
	private final Map<IcfgLocation, IPredicate> mLoc2overApprox;

	/**
	 * Constructs a new factory for {@link LinearInequalityInvariantPatternProcessor}s.
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager to use with the predicateUnifier
	 * @param strategy
	 *            the invariant strategy to pass to the produced processor
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 * @param smtSymbols
	 * @param synthesizeEntryPattern
	 *            true if the the pattern for the start location need to be synthesized (instead of being inferred from
	 *            the precondition)
	 * @param kindOfInvariant
	 *            the kind of invariant to be generated
	 * @param overapprox
	 * @param underapprox
	 */
	public LinearInequalityInvariantPatternProcessorFactory(final IUltimateServiceProvider services,
			final IPredicateUnifier predUnifier, final CfgSmtToolkit csToolkit,
			final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> strategy,
			final boolean useNonlinerConstraints, final boolean useUnsatCores, final SolverSettings solverSettings,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final SmtFunctionsAndAxioms smtSymbols, final Map<IcfgLocation, IPredicate> loc2underApprox,
			final Map<IcfgLocation, IPredicate> loc2overApprox, final boolean synthesizeEntryPattern,
			final KindOfInvariant kindOfInvariant) {
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		this.predUnifier = predUnifier;
		mCsToolkit = csToolkit;
		mSmtSymbols = smtSymbols;
		mStrategy = strategy;
		mUseNonlinearConstraints = useNonlinerConstraints;
		mUseUnsatCores = useUnsatCores;
		mSynthesizeEntryPattern = synthesizeEntryPattern;
		mKindOfInvariant = kindOfInvariant;
		mSolverSettings = solverSettings;
		mLoc2underApprox = loc2underApprox;
		mLoc2overApprox = loc2overApprox;
	}

	/**
	 * Produces a SMT solver instance.
	 *
	 * @return SMT solver instance to use
	 */
	protected Script produceSmtSolver() {
		final boolean useAlsoIntegers;
		// 2017-11-05 Matthias:
		// seems like we always need integers since program variables can have sort Int.
		// useAlsoIntegers = (mKindOfInvariant == KindOfInvariant.DANGER);
		useAlsoIntegers = true;
		final Linearity linearity = mUseNonlinearConstraints ? Linearity.NONLINEAR : Linearity.LINEAR;
		final Logics logic = ConstraintSynthesisUtils.getLogic(linearity, useAlsoIntegers);

		Script script = SolverBuilder.buildAndInitializeSolver(mServices, SolverMode.External_DefaultMode,
				mSolverSettings, false, false, logic.toString(), "InvariantSynthesis");
		script = new ScriptWithTermConstructionChecks(script);
		return script;
	}

	/**
	 * Produces SMT solver settings to be used within {@link #produceSmtSolver()}.
	 *
	 * @return SMT solver settings to use
	 */
	@Deprecated
	private SolverSettings produceSolverSettings() {
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
		return new SolverSettings(fakeNonIncrementalSolver, true, solverCommand, -1, null, dumpSmtScriptToFile,
				pathOfDumpedScript, baseNameOfDumpedScript);
	}

	@Override
	public IInvariantPatternProcessor<Dnf<AbstractLinearInvariantPattern>> produce(final List<IcfgLocation> locations,
			final List<IcfgInternalTransition> transitions, final IPredicate precondition,
			final IPredicate postcondition, final IcfgLocation startLocation, final Set<IcfgLocation> errorLocations) {
		return new LinearInequalityInvariantPatternProcessor(mServices, predUnifier, mCsToolkit, mSmtSymbols, produceSmtSolver(),
				locations, transitions, precondition, postcondition, startLocation, errorLocations, mStrategy,
				mUseNonlinearConstraints, mUseUnsatCores, mSimplificationTechnique, mXnfConversionTechnique, mLoc2underApprox,
				mLoc2overApprox, mSynthesizeEntryPattern, mKindOfInvariant);
	}
}
