/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;

/**
 * Transform an {@link Icfg} using large block encoding. (Back)transform a proof for the large block encoded
 * {@link Icfg} to a proof for the original {@link Icfg} by computing {@link IPredicate}s for the intermediate locations
 * using interpolation or a SP-based wordaround.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class LargeBlockEncodingIcfgTransformer {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	/**
	 * Map that assigns to each large block encoded icfg location the corresponding location in the orginal icfg
	 */
	private Map<IcfgLocation, IcfgLocation> mLbeBacktranslation;
	private IIcfg<IcfgLocation> mInputIcfg;

	public LargeBlockEncodingIcfgTransformer(final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
	}

	public IIcfg<IcfgLocation> transform(final IIcfg<IcfgLocation> inputIcfg) {
		mInputIcfg = inputIcfg;
		final IUltimateServiceProvider beServices =
				mServices.registerPreferenceLayer(getClass(), BlockEncodingPreferences.PLUGIN_ID);
		final IPreferenceProvider ups = beServices.getPreferenceProvider(BlockEncodingPreferences.PLUGIN_ID);
		ups.put(BlockEncodingPreferences.FXP_INTERPROCEDURAL_COMPOSITION, false);
		ups.put(BlockEncodingPreferences.FXP_MINIMIZE_STATES, MinimizeStates.MULTI);
		// ups.put(BlockEncodingPreferences.PRE_SBE, true);
		// ups.put(BlockEncodingPreferences.POST_USE_PARALLEL_COMPOSITION, false);

		// TODO: If you remove infeasible edges, you may end up with an empty program. Either disable this or deal
		// with it.
		ups.put(BlockEncodingPreferences.FXP_REMOVE_INFEASIBLE_EDGES, false);
		ups.put(BlockEncodingPreferences.FXP_REMOVE_SINK_STATES, false);
		final BlockEncoder blockEncoder = new BlockEncoder(mLogger, beServices, inputIcfg,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final IIcfg<IcfgLocation> outputIcfg = blockEncoder.getResult();
		assert !outputIcfg.getInitialNodes().isEmpty() : "LBE ICFG is emtpy";
		mLbeBacktranslation = blockEncoder.getBacktranslator().getLocationMapping();
		return outputIcfg;
	}

	public Map<IcfgLocation, IPredicate> transform(final Map<IcfgLocation, IPredicate> hoareAnnotation) {
		final Map<IcfgLocation, IPredicate> result = computeIntermediateInvariants(mInputIcfg, hoareAnnotation,
				mLbeBacktranslation, mPredicateUnifier, mInputIcfg.getCfgSmtToolkit());
		mLbeBacktranslation = null;
		mInputIcfg = null;
		return result;
	}

	/**
	 * Given invariants for an LBE encoded {@link Icfg}, compute invariants for the original {@link Icfg} by filling the
	 * gaps using interpolation or an SP-based workaround.
	 *
	 * @param inputIcfg
	 *            {@link Icfg} for which we want to compute invariants.
	 * @param lbeInvariants
	 *            Invariants of an {@link Icfg} that was obtained by large block encoding.
	 * @param lbeBacktranslation
	 *            Backtranslation from {@link IcfgLocation}s of the LBE {@link Icfg} to inputIcfg.
	 * @return An invariant mapping for input icfg.
	 */
	private Map<IcfgLocation, IPredicate> computeIntermediateInvariants(final IIcfg<IcfgLocation> inputIcfg,
			final Map<IcfgLocation, IPredicate> lbeInvariants, final Map<IcfgLocation, IcfgLocation> lbeBacktranslation,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit) {
		// add invariants for non-intermedicate locations directly
		final Map<IcfgLocation, IPredicate> resultInvariantMapping = new HashMap<>();
		for (final Entry<IcfgLocation, IPredicate> entry : lbeInvariants.entrySet()) {
			resultInvariantMapping.put(lbeBacktranslation.get(entry.getKey()), entry.getValue());
		}

		// try to add intermediate invariants using interpolation
		for (final IcfgLocation lbeLoc : lbeInvariants.keySet()) {
			final IcfgLocation origLoc = lbeBacktranslation.get(lbeLoc);
			if (!origLoc.getOutgoingEdges().isEmpty()) {
				tryToAddInvariantsUsingInterpolation(origLoc, resultInvariantMapping, predicateUnifier, csToolkit);
			}
		}
		final Set<IcfgLocation> inputIcfgLocations = extractAllIcfgLocations(inputIcfg);
		mLogger.info("path program has " + inputIcfgLocations.size() + " locations");
		mLogger.info(lbeInvariants.size() + " invariants obtained by synthesis");
		mLogger.info(resultInvariantMapping.size() - lbeInvariants.size() + " invariants obtained by interpolation");
		int numberSpInvariants = 0;
		final ArrayDeque<IcfgLocation> inputIcfgLocationsWithoutInvariants = new ArrayDeque<>();
		for (final IcfgLocation loc : inputIcfgLocations) {
			if (!resultInvariantMapping.keySet().contains(loc)) {
				inputIcfgLocationsWithoutInvariants.add(loc);
			}
		}
		int iterationsWithoutProgress = 0;
		while (!inputIcfgLocationsWithoutInvariants.isEmpty()) {
			final IcfgLocation some = inputIcfgLocationsWithoutInvariants.removeFirst();
			if (allPredecessorsHaveInvariants(some, resultInvariantMapping)) {
				iterationsWithoutProgress = 0;
				final IPredicate invar = computeInvariantUsingSp(some, resultInvariantMapping,
						csToolkit.getManagedScript(), predicateUnifier);
				resultInvariantMapping.put(some, invar);
				numberSpInvariants++;
			} else {
				iterationsWithoutProgress++;
				inputIcfgLocationsWithoutInvariants.add(some);
			}
			if (iterationsWithoutProgress > inputIcfgLocationsWithoutInvariants.size()) {
				throw new AssertionError("No Progress! Cycle or unreachable locations in Icfg.");
			}
		}
		mLogger.info("remaining " + numberSpInvariants + " invariants computed via SP");
		return resultInvariantMapping;
	}

	/**
	 * Check if loc has an outgoing run of branchless locations compute missing invariants along this runs using
	 * interpolation.
	 */
	private void tryToAddInvariantsUsingInterpolation(final IcfgLocation loc,
			final Map<IcfgLocation, IPredicate> invariants, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit) {
		final NestedRun<IAction, IcfgLocation> run = extractRunOfBranchlessLocs(loc, invariants.keySet());
		if (run == null) {
			return;
		}
		final IPredicate precondition = invariants.get(run.getStateAtPosition(0));
		final IPredicate postcondition = invariants.get(run.getStateAtPosition(run.getLength() - 1));
		final IPredicate[] interpolants =
				computeInterpolantsAlongRun(run, precondition, postcondition, predicateUnifier, csToolkit);
		for (int i = 1; i < run.getLength() - 1; i++) {
			invariants.put(run.getStateAtPosition(i), interpolants[i - 1]);
		}
	}

	/**
	 * @return set that contains all {@link IcfgLocation}s of an icfg.
	 */
	private static Set<IcfgLocation> extractAllIcfgLocations(final IIcfg<IcfgLocation> icfg) {
		final Set<IcfgLocation> result = new HashSet<>();
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		while (iter.hasNext()) {
			result.add(iter.next());
		}
		return result;
	}

	/**
	 * @return Invariant for {@link IcfgLocation} loc computed as the disjunction of the postconditions of the
	 *         invariants of all predecessor locations
	 */
	private IPredicate computeInvariantUsingSp(final IcfgLocation loc, final Map<IcfgLocation, IPredicate> invariants,
			final ManagedScript mgdScript, final IPredicateUnifier predicateUnifier) {
		final PredicateTransformer<Term, IPredicate, TransFormula> pt =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(mServices, mgdScript));
		final List<Term> disjuncts = new ArrayList<>();
		for (final IcfgEdge edge : loc.getIncomingEdges()) {
			final IcfgLocation pred = edge.getSource();
			final IPredicate predInv = invariants.get(pred);
			final Term post = pt.strongestPostcondition(predInv, edge.getTransformula());
			disjuncts.add(post);
		}
		final Term disjunction = SmtUtils.or(mgdScript.getScript(), disjuncts);
		final IPredicate invar = predicateUnifier.getOrConstructPredicate(disjunction);
		return invar;
	}

	/**
	 * @return true iff each predecessors of loc is in the keySet of the invariants Map.
	 */
	private static boolean allPredecessorsHaveInvariants(final IcfgLocation loc,
			final Map<IcfgLocation, IPredicate> invariants) {
		for (final IcfgLocation pred : loc.getIncomingNodes()) {
			if (!invariants.containsKey(pred)) {
				return false;
			}
		}
		return true;
	}

	private IPredicate[] computeInterpolantsAlongRun(final NestedRun<IAction, IcfgLocation> run,
			final IPredicate precondition, final IPredicate postcondition, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit) {
		final SortedMap<Integer, IPredicate> pendingContexts = Collections.emptySortedMap();
		final AssertCodeBlockOrder assertCodeBlocksIncrementally = AssertCodeBlockOrder.NOT_INCREMENTALLY;
		final UnsatCores unsatCores = UnsatCores.CONJUNCT_LEVEL;
		final boolean useLiveVariables = true;
		final boolean computeRcfgProgramExecution = false;
		final InterpolationTechnique interpolation = InterpolationTechnique.ForwardPredicates;
		final ManagedScript mgdScriptTc = csToolkit.getManagedScript();
		final SimplificationTechnique simplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConversionTechnique =
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		final TraceCheckSpWp<? extends IAction> tc = new TraceCheckSpWp<>(precondition, postcondition, pendingContexts,
				run.getWord(), csToolkit, assertCodeBlocksIncrementally, unsatCores, useLiveVariables, mServices,
				computeRcfgProgramExecution, mPredicateFactory, predicateUnifier, interpolation, mgdScriptTc,
				xnfConversionTechnique, simplificationTechnique, run.getStateSequence(), false);
		return tc.getInterpolants();
	}

	/**
	 * Try to construct a run (whose letters are {@link IAction}s and whose states are {@link IcfgLocation}) that starts
	 * in loc and ends in some element of goalLocs. Each intermediate {@link IcfgLocation} of the run must have exactly
	 * one predecessor and one successor. Return null if no such run exists.
	 */
	private static <T extends IAction> NestedRun<T, IcfgLocation> extractRunOfBranchlessLocs(final IcfgLocation loc,
			final Set<IcfgLocation> goalLocs) {
		NestedRun<T, IcfgLocation> run = new NestedRun<>(loc);
		IcfgLocation currentLoc = loc;
		while (true) {
			if (currentLoc.getOutgoingEdges().isEmpty()) {
				throw new AssertionError("no outgoing edge");
			} else if (currentLoc.getOutgoingEdges().size() == 1) {
				final IcfgEdge edge = currentLoc.getOutgoingEdges().get(0);
				@SuppressWarnings("unchecked")
				final NestedRun<T, IcfgLocation> suffix =
						new NestedRun<>(edge.getSource(), (T) edge, NestedWord.INTERNAL_POSITION, edge.getTarget());
				run = run.concatenate(suffix);
				currentLoc = edge.getTarget();
				if (goalLocs.contains(currentLoc)) {
					return run;
				}
				if (currentLoc.getIncomingEdges().size() > 1) {
					return null;
				}
			} else if (currentLoc.getOutgoingEdges().size() > 1) {
				return null;
			}
		}
	}

}
