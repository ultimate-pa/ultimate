/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Construct an Owicki-Gries-Annotation from an EmpireAnnotation.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of places in the Petri program
 * @param <PLACE>
 *            The type of statements in the Petri program
 */
public class EmpireToOwickiGries<LETTER, PLACE> {
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final BasicPredicateFactory mFactory;

	private final IPetriNet<LETTER, PLACE> mNet;

	private final EmpireAnnotation<PLACE> mEmpireAnnotation;

	private final DefaultIcfgSymbolTable mSymbolTable;
	private final Map<Region<PLACE>, IProgramVar> mGhostVariables;
	private final Map<Territory<PLACE>, IPredicate> mTerritoryFormulaMap = new HashMap<>();

	private final OwickiGriesAnnotation<LETTER, PLACE> mOwickiGriesAnnotation;

	/**
	 * Constructs the Owicki-Gries-Annotation for empireAnnotation.
	 *
	 * @param services
	 *            IUltimateServiceProvider object
	 * @param mgdScript
	 *            ManagedScript object
	 * @param net
	 *            Net corresponding to the Empire Annotation
	 * @param symbolTable
	 *            IIcfgSymbolTable object
	 * @param procedures
	 *            Set of string procedures
	 * @param empireAnnotation
	 *            Corresponding EmpireAnnotation
	 */
	public EmpireToOwickiGries(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<LETTER, PLACE> net, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final EmpireAnnotation<PLACE> empireAnnotation) {
		mManagedScript = mgdScript;
		mScript = mManagedScript.getScript();
		mSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		mFactory = new BasicPredicateFactory(services, mManagedScript, mSymbolTable);

		mNet = net;
		mEmpireAnnotation = empireAnnotation;

		mGhostVariables = getGhostVariables();
		final Map<PLACE, IPredicate> formulaMapping = getFormulaMap();
		final Map<Transition<LETTER, PLACE>, GhostUpdate> assignmentMapping = getAssignmentMapping();
		final Map<IProgramVar, Term> ghostInitAssignment = getGhostInitAssignment();

		mOwickiGriesAnnotation = new OwickiGriesAnnotation<>(mNet, mSymbolTable, formulaMapping,
				new HashSet<>(mGhostVariables.values()), ghostInitAssignment, assignmentMapping);
	}

	/**
	 * @return map of regions to their corresponding ghost variables
	 */
	private Map<Region<PLACE>, IProgramVar> getGhostVariables() {
		final Map<Region<PLACE>, IProgramVar> ghostVars = new HashMap<>();
		final Collection<Region<PLACE>> regions = mEmpireAnnotation.getColony();
		mManagedScript.lock(this);
		try {
			for (final Region<PLACE> region : regions) {
				final TermVariable tVar = mManagedScript.constructFreshTermVariable(region.toString(),
						SmtSortUtils.getBoolSort(mManagedScript));
				final IProgramVar pVar = ProgramVarUtils.constructGlobalProgramVarPair(tVar.getName(),
						SmtSortUtils.getBoolSort(mManagedScript), mManagedScript, this);
				mSymbolTable.add(pVar);
				ghostVars.put(region, pVar);
			}
			return ghostVars;
		} finally {
			mManagedScript.unlock(this);
		}
	}

	/**
	 * @return Map of place to the corresponding formula for each place in net
	 */
	private Map<PLACE, IPredicate> getFormulaMap() {
		final Map<PLACE, IPredicate> formulaMap = new HashMap<>();
		final IPredicate territoryImplications = getTerritoryImplications();
		for (final PLACE place : mNet.getPlaces()) {
			final IPredicate ghostFormula = getPlacesGhostVariableFormula(place);
			final IPredicate territoryFormula = getPlacesTerritoryFormula(place);
			final IPredicate placeFormula = mFactory.and(territoryImplications, ghostFormula, territoryFormula);
			formulaMap.put(place, placeFormula);
		}
		return formulaMap;
	}

	/**
	 * @return Map of transition to the corresponding formula for each transition in net
	 */
	private Map<Transition<LETTER, PLACE>, GhostUpdate> getAssignmentMapping() {
		final Map<Transition<LETTER, PLACE>, GhostUpdate> assignmentMapping = new HashMap<>();
		for (final Transition<LETTER, PLACE> transition : mNet.getTransitions()) {
			final var assignment = getTransitionAssignment(transition);
			if (assignment != null) {
				assignmentMapping.put(transition, assignment);
			}
		}
		return assignmentMapping;
	}

	/**
	 * @return Map of ghost variable to its init assignment for each ghost variable
	 */
	private Map<IProgramVar, Term> getGhostInitAssignment() {
		final HashMap<IProgramVar, Term> initAssignments = new HashMap<>();
		final Set<PLACE> initPlaces = mNet.getInitialPlaces();
		Term initTerm;
		for (final Region<PLACE> region : mEmpireAnnotation.getColony()) {
			if (DataStructureUtils.haveEmptyIntersection(region.getPlaces(), initPlaces)) {
				initTerm = mScript.term("false");
			} else {
				initTerm = mScript.term("true");
			}
			initAssignments.put(mGhostVariables.get(region), initTerm);
		}
		return initAssignments;
	}

	private Term computeTerritoryTerm(final Territory<PLACE> territory) {
		final Set<Term> positiveClauses =
				mGhostVariables.keySet().stream().filter(r -> territory.getRegions().contains(r))
						.map(r -> mGhostVariables.get(r).getTerm()).collect(Collectors.toSet());
		final Set<Region<PLACE>> outRegions = mEmpireAnnotation.getOutlanderRegions(territory);
		final Set<Term> negativeClauses = outRegions.stream()
				.map(r -> SmtUtils.not(mScript, mGhostVariables.get(r).getTerm())).collect(Collectors.toSet());
		return SmtUtils.and(mScript, DataStructureUtils.union(positiveClauses, negativeClauses));
	}

	private IPredicate getTerritoryFormula(final Territory<PLACE> territory) {
		final IPredicate territoryFormula =
				mTerritoryFormulaMap.computeIfAbsent(territory, t -> mFactory.newPredicate(computeTerritoryTerm(t)));
		return territoryFormula;
	}

	private Set<Territory<PLACE>> getPlacesTerritories(final PLACE place) {
		final Set<Territory<PLACE>> placesTerritories = mEmpireAnnotation.getTerritories().stream()
				.filter(t -> t.getPlaces().contains(place)).collect(Collectors.toSet());
		return placesTerritories;
	}

	IPredicate getTerritoryImplications() {
		final Set<IPredicate> implicationSet = new HashSet<>();
		for (final Territory<PLACE> territory : mEmpireAnnotation.getTerritories()) {
			final IPredicate territoryImplication = mFactory.or(mFactory.not(getTerritoryFormula(territory)),
					mFactory.and(mEmpireAnnotation.getLawSet(territory)));
			implicationSet.add(territoryImplication);
		}
		return mFactory.and(implicationSet);
	}

	IPredicate getPlacesGhostVariableFormula(final PLACE place) {
		final Set<Term> terms = new HashSet<>();
		for (final Entry<Region<PLACE>, IProgramVar> entry : mGhostVariables.entrySet()) {
			if (entry.getKey().contains(place)) {
				terms.add(entry.getValue().getTerm());
			}
		}
		return mFactory.newPredicate(SmtUtils.and(mScript, terms));
	}

	IPredicate getPlacesTerritoryFormula(final PLACE place) {
		final Set<Territory<PLACE>> placesTerritories = getPlacesTerritories(place);
		final Set<IPredicate> placesTerritoriesFormula =
				placesTerritories.stream().map(t -> getTerritoryFormula(t)).collect(Collectors.toSet());
		return mFactory.or(placesTerritoriesFormula);
	}

	private GhostUpdate getTransitionAssignment(final Transition<LETTER, PLACE> transition) {
		final Map<IProgramVar, Term> assignments = new HashMap<>();

		final Set<PLACE> predecessors = transition.getPredecessors();
		final Set<Region<PLACE>> predecessorRegions = mEmpireAnnotation.getColony().stream()
				.filter(r -> DataStructureUtils.haveNonEmptyIntersection(r.getPlaces(), predecessors))
				.collect(Collectors.toSet());

		final Set<PLACE> successors = transition.getSuccessors();
		final Set<Region<PLACE>> successorRegions = mEmpireAnnotation.getColony().stream()
				.filter(r -> DataStructureUtils.haveNonEmptyIntersection(r.getPlaces(), successors))
				.collect(Collectors.toSet());

		// Remove regions from both sets which are both predecessors and successors
		final Set<Region<PLACE>> intersectingRegions =
				DataStructureUtils.intersection(predecessorRegions, successorRegions);
		predecessorRegions.removeAll(intersectingRegions);
		successorRegions.removeAll(intersectingRegions);

		final var falseTerm = mScript.term(SMTLIBConstants.FALSE);
		for (final Region<PLACE> region : predecessorRegions) {
			assignments.put(mGhostVariables.get(region), falseTerm);
		}

		final var trueTerm = mScript.term(SMTLIBConstants.TRUE);
		for (final Region<PLACE> region : successorRegions) {
			assignments.put(mGhostVariables.get(region), trueTerm);
		}

		if (assignments.isEmpty()) {
			return null;
		}
		return new GhostUpdate(assignments);
	}

	public OwickiGriesAnnotation<LETTER, PLACE> getAnnotation() {
		return mOwickiGriesAnnotation;
	}
}
