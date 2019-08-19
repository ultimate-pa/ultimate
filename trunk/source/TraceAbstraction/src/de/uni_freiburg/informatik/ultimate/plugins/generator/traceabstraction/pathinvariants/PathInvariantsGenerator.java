/*
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.CFGInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.KindOfInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.InvariantSynthesisStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Represents a map of invariants to a run that has been generated using a {@link IInvariantPatternProcessor} on the
 * run-projected CFG.
 *
 * @author Dirk Steinmetz, Matthias Heizmann, Betim Musa
 */
public final class PathInvariantsGenerator<LETTER extends IAction> implements IInterpolantGenerator<LETTER> {

	private final NestedRun<LETTER, IPredicate> mRun;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicate[] mInterpolants;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final InterpolantComputationStatus mInterpolantComputationStatus;

	private final InvariantSynthesisStatisticsGenerator mPathInvariantsStats;

	/**
	 * Generates a map of invariants to a given run, using an {@link IInvariantPatternProcessor} produced by the default
	 * {@link IInvariantPatternProcessorFactory} (with default settings).
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param run
	 *            an infeasible run to project into a CFG. Must only contain {@link ISLPredicate}s as states.
	 * @param precondition
	 *            the predicate to use for the first program point in the run
	 * @param postcondition
	 *            the predicate to use for the last program point in the run
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param icfg
	 * @param xnfConversionTechnique
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 */
	public PathInvariantsGenerator(final IUltimateServiceProvider services, final NestedRun<LETTER, IPredicate> run,
			final IPredicate precondition, final IPredicate postcondition, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final IIcfg<?> icfg, final InvariantSynthesisSettings invSynthSettings,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mRun = run;

		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPredicateUnifier = predicateUnifier;

		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

		mLogger.info("Current run: " + run);
		final Set<? extends IcfgEdge> allowedTransitions =
				extractTransitionsFromRun(run, icfg.getCfgSmtToolkit().getIcfgEdgeFactory());

		final PathProgram.PathProgramConstructionResult ppResult =
				PathProgram.constructPathProgram("PathInvariantsPathProgram", icfg, allowedTransitions);
		final IIcfg<IcfgLocation> pathProgram = ppResult.getPathProgram();
		final Map<IcfgLocation, IcfgLocation> inputIcfgLocs2PathProgramLocs = ppResult.getLocationMapping();

		// Generate invariants
		final CFGInvariantsGenerator cfgInvGenerator = new CFGInvariantsGenerator(pathProgram, services, precondition,
				postcondition, predicateFactory, predicateUnifier, invSynthSettings, icfg.getCfgSmtToolkit(),
				KindOfInvariant.SAFETY);
		final Map<IcfgLocation, IPredicate> invariants = cfgInvGenerator.synthesizeInvariants();
		// Get invariant synthesis statistics
		mPathInvariantsStats = cfgInvGenerator.getInvariantSynthesisStatistics();

		if (invariants != null) {
			// Populate resulting array
			mInterpolants = new IPredicate[mRun.getLength()];
			for (int i = 0; i < mRun.getLength(); i++) {
				final IcfgLocation originalLoc = ((ISLPredicate) mRun.getStateAtPosition(i)).getProgramPoint();
				final IcfgLocation locFromPathProgram = inputIcfgLocs2PathProgramLocs.get(originalLoc);
				// invariants.keySet().stream().filter(loc -> loc.toString().endsWith(originalLoc.toString()))
				// .collect(Collectors.toList()).get(0);
				mInterpolants[i] = invariants.get(locFromPathProgram);
				mLogger.info("Interpolant no " + i + " " + mInterpolants[i].toString());
			}
			mLogger.info("Invariants found and " + "processed.");
			mLogger.info("Got a Invariant map of length " + mInterpolants.length);
			mInterpolantComputationStatus = new InterpolantComputationStatus(true, null, null);
		} else {
			mInterpolants = null;
			mLogger.info("No invariants found.");
			mInterpolantComputationStatus =
					new InterpolantComputationStatus(false, ItpErrorStatus.ALGORITHM_FAILED, null);
		}
	}

	public static Set<? extends IcfgEdge> extractTransitionsFromRun(final NestedRun<? extends IAction, IPredicate> run,
			final IcfgEdgeFactory edgeFac) {
		final int len = run.getLength();
		final LinkedHashSet<IcfgInternalTransition> transitions = new LinkedHashSet<>(len - 1);
		IcfgLocation previousLocation = null;

		for (int i = 0; i < len; i++) {
			final ISLPredicate pred = (ISLPredicate) run.getStateAtPosition(i);
			final IcfgLocation currentLocation = pred.getProgramPoint();
			if (i > 0) {
				if (!run.getWord().isInternalPosition(i - 1)) {
					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
				}
				final UnmodifiableTransFormula transFormula =
						((IInternalAction) run.getSymbol(i - 1)).getTransformula();
				transitions.add(edgeFac.createInternalTransition(previousLocation, currentLocation,
						currentLocation.getPayload(), transFormula));
			}
			previousLocation = currentLocation;
		}
		return transitions;
	}

	@Override
	public List<LETTER> getTrace() {
		return mRun.getWord().asList();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	/**
	 * Returns a sequence of interpolants (see definition in {@link IInterpolantGenerator}) the trace which is
	 * mRun.getWord() with an additional property. If the ProgramPoint and position i and k coincide then the
	 * interpolants at position i and k coincide.
	 *
	 * @return sequence of interpolants according to the run provided in the constructor or null if no such sequence has
	 *         been found; without first interpolant (the precondition)
	 */
	@Override
	public IPredicate[] getInterpolants() {
		if (mInterpolants == null) {
			return null;
		}
		final IPredicate[] interpolantMapWithOutFirstInterpolant = new IPredicate[mInterpolants.length - 2];
		System.arraycopy(mInterpolants, 1, interpolantMapWithOutFirstInterpolant, 0, mInterpolants.length - 2);
		return interpolantMapWithOutFirstInterpolant;
	}

	@Override
	public boolean isPerfectSequence() {
		final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices, this, mLogger);
		final boolean isPerfect = bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
		return isPerfect;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

	public InvariantSynthesisStatisticsGenerator getPathInvariantsBenchmarks() {
		return mPathInvariantsStats;
	}

	// Benchmarks Section
	@SuppressWarnings("squid:S00115")
	public enum InvariantSynthesisStatisticsDefinitions implements IStatisticsElement {
		// the sum of path program size (measured as the number of inequalities of all transformulas) for each overall
		// iteration
		ProgramSizeConjuncts(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		ProgramSizeDisjuncts(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of path program locations for each overall iteration
		ProgramLocs(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of path program locations for each overall iteration after Lbe has been applied
		ProgramLocsLbe(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of path program variables for each overall iteration
		ProgramVars(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of template inequalities per location per round per iteration
		SumOfTemplateInequalities(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the minimum size of all templates occurring in the most recent round
		SizeOfLargestTemplate(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// the minimum size of all templates occurring in the most recent round
		SizeOfSmallestTemplate(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// the maximum of the sum of template inequalities per round
		MaxNumOfInequalities(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// the maximum number of rounds
		MaxRound(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// the sum of variables per location per round
		SumVarsPerLoc(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of the difference of all variables and the live variables per location per round
		SumNonLiveVarsPerLoc(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of the difference of all variables and the variables from the unsat core per location per round
		SumNonUnsatCoreLocs(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of the difference of all variables and the variables from the unsat core per location per round
		SumNonUnsatCoreVars(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the maximum DAG-size of (the sum of template inequalities per location per round) for normal constraints
		TreeSizeNormalConstr(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// the maximum DAG-size of (the sum of template inequalities per location per round) for constraints of Under-
		// and/or Overapproximations
		TreeSizeApproxConstr(Integer.class, StatisticsType.INTEGER_MAX, StatisticsType.KEY_BEFORE_DATA),
		// Number of Motzkin Transformations for normal constraints
		MotzkinTransformationsNormalConstr(Integer.class, StatisticsType.INTEGER_ADDITION,
				StatisticsType.KEY_BEFORE_DATA),
		// Number of Motzkin Transformations for constraints of Under- and/or Overapproximations
		MotzkinTransformationsApproxConstr(Integer.class, StatisticsType.INTEGER_ADDITION,
				StatisticsType.KEY_BEFORE_DATA),
		// Number of Motzkin Coefficients needed for normal constraints
		MotzkinCoefficientsNormalConstr(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// Number of Motzkin Coefficients needed for constraints of Under- and/or Overapproximations
		MotzkinCoefficientsApproxConstr(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of the time needed per round to solve the constraints
		ConstraintsSolvingTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// the sum of the time needed per round to construct the constraints
		ConstraintsConstructionTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_DATA),
		// Sat status
		SatStatus(String.class, s1 -> s2 -> new String((String) s1 + "; " + (String) s2),
				StatisticsType.KEY_BEFORE_DATA);

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		InvariantSynthesisStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(name()).apply(o);
		}

	}
}
