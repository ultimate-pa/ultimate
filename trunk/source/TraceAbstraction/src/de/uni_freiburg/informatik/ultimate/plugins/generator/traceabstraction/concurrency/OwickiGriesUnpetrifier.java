/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Backtranslates an Owicki-Gries annotation of a Petri program derived from an {@link IIcfg} to an Owicki-Gries
 * annotation of the original {@link IIcfg}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of transitions in the {@link IIcfg}, which are also used as letters of the Petri program
 * @param <P>
 *            The type of places in the Petri program
 * @param <LOC>
 *            The type of locations in the {@link IIcfg}
 */
public class OwickiGriesUnpetrifier<L extends IIcfgTransition<LOC>, P, LOC extends IcfgLocation> {
	private final ManagedScript mMgdScript;
	private final BasicPredicateFactory mPredicateFactory;

	private final Function<P, LOC> mPlaceToLocation;
	private final UnaryOperator<L> mUnpetrifyAction;
	private final Set<P> mThreadUsageMonitorPlaces;

	private final Map<String, ILocalProgramVar> mThreadIdVars = new HashMap<>();
	private final Map<ILocalProgramVar, IProgramNonOldVar> mGhostMirrors = new HashMap<>();

	private final IPossibleInterferences<L, LOC> mPossibleInterferences;
	private final OwickiGriesAnnotation<L, LOC> mOwickiGries;

	// TODO ConcurrencyInformation of petrified CFG?
	public OwickiGriesUnpetrifier(final IIcfg<LOC> originalIcfg, final IPetriNet<L, P> petrifiedProgram,
			final IPossibleInterferences<Transition<L, P>, P> petrifiedPossibleInterferences,
			final OwickiGriesAnnotation<Transition<L, P>, P> annotation, final Function<P, LOC> placeToLocation,
			final UnaryOperator<L> unpetrifyAction, final Set<P> threadUsageMonitorPlaces,
			final BasicPredicateFactory predicateFactory) {
		mMgdScript = originalIcfg.getCfgSmtToolkit().getManagedScript();
		mPredicateFactory = predicateFactory;

		mPlaceToLocation = placeToLocation;
		mUnpetrifyAction = unpetrifyAction;
		mThreadUsageMonitorPlaces = threadUsageMonitorPlaces;

		mPossibleInterferences = translatePossibleInterferences(petrifiedProgram, petrifiedPossibleInterferences);

		// compute formula mapping, and collect newly needed ghost variables on the fly
		final Map<LOC, IPredicate> formulaMapping = computeFormulaMapping(petrifiedProgram, annotation);

		// collect old and new ghost variables
		final var ghostVars = new HashSet<>(annotation.getGhostVariables());
		ghostVars.addAll(mGhostMirrors.values());
		ghostVars.addAll(mThreadIdVars.values());

		// collect initial values of old and new ghost variables
		final Map<IProgramVar, Term> ghostInits = new HashMap<>(annotation.getGhostAssignment());
		for (final var entry : mGhostMirrors.entrySet()) {
			ghostInits.put(entry.getValue(), entry.getKey().getTerm());
		}

		final IIcfgSymbolTable symbolTable = buildSymbolTable(originalIcfg, ghostVars);
		final Map<L, GhostUpdate> ghostUpdates = computeUpdates(petrifiedProgram, annotation);

		mOwickiGries = new OwickiGriesAnnotation<>(symbolTable, formulaMapping, ghostVars, ghostInits, ghostUpdates);
	}

	public OwickiGriesAnnotation<L, LOC> getResult() {
		return mOwickiGries;
	}

	public IPossibleInterferences<L, LOC> getPossibleInterferences() {
		return mPossibleInterferences;
	}

	private IPossibleInterferences<L, LOC> translatePossibleInterferences(final IPetriNet<L, P> petrifiedProgram,
			final IPossibleInterferences<Transition<L, P>, P> petrifiedPossibleInterferences) {
		final var result = new HashRelation<LOC, L>();
		for (final var p : petrifiedProgram.getPlaces()) {
			if (isThreadUsageMonitorPlace(p)) {
				continue;
			}
			final var loc = getLocation(p);
			result.addAllPairs(loc, petrifiedPossibleInterferences.getInterferingActions(p).stream()
					.map(Transition::getSymbol).map(mUnpetrifyAction).collect(Collectors.toSet()));
		}
		return IPossibleInterferences.fromRelation(result);
	}

	private Map<LOC, IPredicate> computeFormulaMapping(final IPetriNet<L, P> petrifiedProgram,
			final OwickiGriesAnnotation<Transition<L, P>, P> annotation) {
		final var result = new HashMap<LOC, IPredicate>();
		for (final var entry : annotation.getFormulaMapping().entrySet()) {
			final P place = entry.getKey();
			if (isThreadUsageMonitorPlace(place)) {
				continue;
			}

			final var loc = getLocation(place);
			if (result.containsKey(loc)) {
				// TODO support this, by introducing local ghost variables for thread IDs and using conjunctions
				throw new UnsupportedOperationException("Multiple instances of thread not yet supported: " + place);
			}

			final var predicate = entry.getValue();

			// create ghost variables that mirror local variables
			final var substitution = new HashMap<TermVariable, Term>();
			for (final var pv : predicate.getVars()) {
				if (pv.isGlobal() || pv.getProcedure() == loc.getProcedure()) {
					continue;
				}

				// create ghost variable for original if needed
				final var ghost = mGhostMirrors.computeIfAbsent((ILocalProgramVar) pv, x -> ProgramVarUtils
						.constructGlobalProgramVarPair(x.getIdentifier() + "~ghost", x.getSort(), mMgdScript, null));
				substitution.put(pv.getTermVariable(), ghost.getTerm());
			}

			// apply substitution if necessary
			final IPredicate newPredicate;
			if (substitution.isEmpty()) {
				newPredicate = predicate;
			} else {
				newPredicate = mPredicateFactory
						.newPredicate(Substitution.apply(mMgdScript, substitution, predicate.getFormula()));
			}
			result.put(loc, newPredicate);
		}
		return result;
	}

	private Map<L, GhostUpdate> computeUpdates(final IPetriNet<L, P> petrifiedProgram,
			final OwickiGriesAnnotation<Transition<L, P>, P> annotation) {
		final var result = new HashMap<L, GhostUpdate>();
		for (final var entry : annotation.getAssignmentMapping().entrySet()) {
			final var transition = entry.getKey();
			final var edge = transition.getSymbol();
			final var originalEdge = mUnpetrifyAction.apply(edge);
			if (result.containsKey(originalEdge)) {
				// TODO support this, by case split over local thread ID
				throw new UnsupportedOperationException("Multiple instances of thread not yet supported: " + edge);
			}

			final var newUpdates = new HashMap<IProgramVar, Term>();

			// update ghost mirrors to reflect the updated value of the mirrored variable
			for (final var pv : edge.getTransformula().getAssignedVars()) {
				if (pv.isGlobal() || !mGhostMirrors.containsKey(pv)) {
					continue;
				}
				final var ghost = mGhostMirrors.get(pv);
				assert ghost != null;
				newUpdates.put(ghost, pv.getTerm());
			}

			// TODO add updates of new ghost variables for thread IDs when edge is entryEdge of template
			assert mThreadIdVars.isEmpty() : "missing update of ghost variables: " + mThreadIdVars;

			final var combinedUpdate = GhostUpdate.combine(entry.getValue(), newUpdates);
			if (combinedUpdate != null) {
				result.put(originalEdge, combinedUpdate);
			}
		}
		return result;
	}

	private IIcfgSymbolTable buildSymbolTable(final IIcfg<LOC> originalIcfg, final Set<IProgramVar> ghostVars) {
		final var symbolTable = new DefaultIcfgSymbolTable(originalIcfg.getCfgSmtToolkit().getSymbolTable(),
				originalIcfg.getCfgSmtToolkit().getProcedures());
		for (final var ghost : ghostVars) {
			symbolTable.add(ghost);
		}
		symbolTable.finishConstruction();
		return symbolTable;
	}

	private LOC getLocation(final P place) {
		final var loc = mPlaceToLocation.apply(place);
		assert loc != null : "No location for place " + place;
		return loc;
	}

	private boolean isThreadUsageMonitorPlace(final P place) {
		return mThreadUsageMonitorPlaces.contains(place);
	}
}
