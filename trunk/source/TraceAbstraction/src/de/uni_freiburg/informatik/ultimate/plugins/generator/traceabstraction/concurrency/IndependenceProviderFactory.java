/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.IRefinableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.RefinableCachedAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction.TransFormulaAuxVarEliminator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.VariableAbstraction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.util.Lazy;

/**
 * Creates {@link IRefinableIndependenceProvider} instances from given settings. This involves setting up
 * {@link ManagedScript}s, building {@link IRefinableAbstraction}s, and finally constructing the actual
 * {@link IIndependenceRelation}s.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class IndependenceProviderFactory<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final TAPreferences mPref;
	private final ICopyActionFactory<L> mCopyFactory;

	private ManagedScript mIndependenceScript;

	public IndependenceProviderFactory(final IUltimateServiceProvider services, final TAPreferences pref,
			final ICopyActionFactory<L> copyFactory) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(IndependenceProviderFactory.class);
		mPref = pref;
		mCopyFactory = copyFactory;
	}

	public List<IRefinableIndependenceProvider<L>> createProviders(final IIcfg<?> icfg,
			final PredicateFactory predicateFactory) {
		final int numIndependenceRelations = mPref.getNumberOfIndependenceRelations();
		final List<IRefinableIndependenceProvider<L>> independenceProviders = new ArrayList<>(numIndependenceRelations);

		for (int i = 0; i < numIndependenceRelations; ++i) {
			final IndependenceSettings settings = mPref.porIndependenceSettings(i);
			mLogger.info("Independence Relation #%d: %s", i + 1, settings);

			final var container = constructIndependenceProvider(icfg, settings, predicateFactory);
			independenceProviders.add(container);
		}

		return independenceProviders;
	}

	private IRefinableIndependenceProvider<L> constructIndependenceProvider(final IIcfg<?> icfg,
			final IndependenceSettings settings, final PredicateFactory predicateFactory) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		if (settings.getAbstractionType() == AbstractionType.LOOPER) {
			return new IndependenceProviderForLoopers<>(mServices, csToolkit,
					new Lazy<>(() -> constructIndependenceScript(settings)), settings.getIndependenceType());
		}

		// Construct the script used for independence checks.
		// TODO Only construct this if an independence relation actually needs a script!
		// TODO Independence relations might have different settings for the script!
		if (mIndependenceScript == null) {
			mIndependenceScript = constructIndependenceScript(settings);
		}

		// We need to transfer given transition formulas and condition predicates to the independenceScript.
		final TransferrerWithVariableCache transferrer =
				new TransferrerWithVariableCache(csToolkit.getManagedScript().getScript(), mIndependenceScript);

		if (settings.getAbstractionType() == AbstractionType.NONE) {
			// Construct the independence relation (without abstraction). It is the responsibility of the independence
			// relation to transfer any terms (transition formulas and condition predicates) to the independenceScript.
			final var independence =
					constructIndependence(settings, mIndependenceScript, transferrer, false, predicateFactory);
			return new StaticIndependenceProvider<>(independence);
		}

		// Construct the abstraction function.
		final var letterAbstraction = constructAbstraction(icfg, settings, mIndependenceScript, transferrer);
		final var cachedAbstraction = new RefinableCachedAbstraction<>(letterAbstraction);

		// Construct the independence relation (still without abstraction).
		// It is the responsibility of the abstraction function to transfer the transition formulas. But we leave it to
		// the independence relation to transfer conditions.
		final var independence =
				constructIndependence(settings, mIndependenceScript, transferrer, true, predicateFactory);

		return new IndependenceProviderWithAbstraction<>(cachedAbstraction, independence);
	}

	private IIndependenceRelation<IPredicate, L> constructIndependence(final IndependenceSettings settings,
			final ManagedScript independenceScript, final TransferrerWithVariableCache transferrer,
			final boolean tfsAlreadyTransferred, final PredicateFactory predicateFactory) {
		if (settings.getIndependenceType() == IndependenceType.SYNTACTIC) {
			return IndependenceBuilder.<L, IPredicate> syntactic().cached().threadSeparated().build();
		}

		assert settings.getIndependenceType() == IndependenceType.SEMANTIC : "unsupported independence type";
		return IndependenceBuilder
				// Semantic independence forms the base.
				// If transition formulas are already transferred to the independenceScript, we need not transfer them
				// here. Otherwise, pass on the transferrer. Conditions are handled below.
				.<L> semantic(mServices, independenceScript, tfsAlreadyTransferred ? null : transferrer,
						settings.useConditional(), !settings.useSemiCommutativity())
				// If TFs have already been transferred and the relation is conditional, then we need to also transfer
				// the condition predicates to the independenceScript.
				.ifThen(tfsAlreadyTransferred && settings.useConditional(),
						b -> b.withTransformedPredicates(transferrer::transferPredicate))
				// Protect the SMT solver against checks with quantifiers that are unlikely to succeed anyway.
				.protectAgainstQuantifiers()
				// Add syntactic independence check (cheaper sufficient condition).
				.withSyntacticCheck()
				// Cache independence query results.
				.cached()
				// Setup condition optimization (if conditional independence is enabled).
				// =========================================================================
				// NOTE: Soundness of the condition elimination here depends on the fact that all inconsistent
				// predicates are syntactically equal to "false". Here, this is achieved by usage of
				// #withDisjunctivePredicates: The only predicates we use as conditions are the original interpolants
				// (i.e., not conjunctions of them), where we assume this constraint holds.
				.withConditionElimination(PartialOrderCegarLoop::isFalseLiteral)
				// We ignore "don't care" conditions stemming from the initial program automaton states.
				.withFilteredConditions(p -> !predicateFactory.isDontCare(p))
				.withDisjunctivePredicates(PartialOrderCegarLoop::getConjuncts)
				// =========================================================================
				// Never consider letters of the same thread to be independent.
				.threadSeparated()
				//debug
				.ignoreDebugPredicates()
				// Retrieve the constructed relation.
				.build();
	}

	private ManagedScript constructIndependenceScript(final IndependenceSettings settings) {
		SolverSettings solverSettings = SolverBuilder.constructSolverSettings().setDumpSmtScriptToFile(
				mPref.dumpIndependenceScript(), mPref.independenceScriptDumpPath(), "commutativity", false);
		if (settings.getSolver() == ExternalSolver.SMTINTERPOL) {
			solverSettings = solverSettings.setSolverMode(SolverMode.Internal_SMTInterpol)
					.setSmtInterpolTimeout(settings.getSolverTimeout());
		} else {
			solverSettings = solverSettings.setSolverMode(SolverMode.External_DefaultMode)
					.setUseExternalSolver(settings.getSolver(), settings.getSolverTimeout());
		}

		// Intentionally do not use CfgSmtToolkit::createFreshManagedScript:
		// That method transfers all declared constants to the new script, including for auxiliary variables in
		// transition formulas. This leads to conflicts later when operations on the independence script create new
		// auxiliary variables they believe to be fresh.
		// TODO This might cause problems in programs with uninterpreted functions or axioms. Transfer (only) those.
		return new ManagedScript(mServices,
				SolverBuilder.buildAndInitializeSolver(mServices, solverSettings, "SemanticIndependence"));
	}

	private IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, ?, L> constructAbstraction(final IIcfg<?> icfg,
			final IndependenceSettings settings, final ManagedScript abstractionScript,
			final TransferrerWithVariableCache transferrer) {
		if (settings.getAbstractionType() == AbstractionType.NONE) {
			return null;
		}

		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(icfg.getCfgSmtToolkit());

		// We eliminate auxiliary variables.
		// This is useful both for semantic independence (ease the load on the SMT solver),
		// but even more so for syntactic independence (often allows shrinking the set of "read" variables).
		final TransFormulaAuxVarEliminator tfEliminator =
				(ms, fm, av) -> TransFormulaUtils.tryAuxVarEliminationLight(mServices, ms, fm, av);

		switch (settings.getAbstractionType()) {
		case VARIABLES_GLOBAL:
			return new VariableAbstraction<>(mCopyFactory, abstractionScript, transferrer, tfEliminator, allVariables);
		case VARIABLES_LOCAL:
			if (mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE) {
				throw new UnsupportedOperationException(
						"specific variable abstraction is only supported with interpolant automaton enhancement NONE");
			}

			// TODO Should this be replaced with mAbstraction.getAlphabet()?
			// Note that this would require changes to ThreadBasedPersistentSets, because it also considers
			// commutativity of forkCurrent and joinCurrent transitions, which are not in the alphabet.
			final Set<L> allLetters = new IcfgEdgeIterator(icfg).asStream().map(x -> (L) x).collect(Collectors.toSet());
			return new SpecificVariableAbstraction<>(mCopyFactory, abstractionScript, transferrer, tfEliminator,
					allLetters, allVariables);
		default:
			throw new UnsupportedOperationException("Unknown abstraction type: " + settings.getAbstractionType());
		}
	}

	public void shutdown() {
		if (mIndependenceScript != null) {
			// Shutdown the script
			// TODO Share independence script and independence relation (including cache) between CEGAR loop instances!
			mIndependenceScript.getScript().exit();
		}
	}
}
