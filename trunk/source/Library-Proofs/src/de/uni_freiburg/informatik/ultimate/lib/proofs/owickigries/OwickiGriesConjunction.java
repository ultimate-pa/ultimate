/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OwickiGriesConjunction<L, P> {
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mFactory;

	private final IPetriNet<L, P> mNet;

	final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mAnnotation1;
	final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mAnnotation2;

	private final DefaultIcfgSymbolTable mSymbolTable;
	private final Map<String, IProgramVar> mGhostVariables;

	private final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGriesAnnotation;

	public OwickiGriesConjunction(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> net, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation1,
			final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> annotation2,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		mManagedScript = mgdScript;
		mManagedScript.getScript();
		mSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		mFactory = new BasicPredicateFactory(services, mManagedScript, mSymbolTable);

		mNet = net;
		mAnnotation1 = annotation1;
		mAnnotation2 = annotation2;

		mGhostVariables = getGhostVariables();
		if (mAnnotation1 != null && mAnnotation2 != null) {
			final Map<P, IPredicate> formulaMapping = getFormulaMap();
			final Map<Transition<L, P>, GhostUpdate> assignmentMapping = getAssignmentMapping();
			final Map<IProgramVar, Term> ghostInitAssignment = getGhostInitAssignment();

			mOwickiGriesAnnotation =
					new OwickiGriesAnnotation<>(OwickiGriesConstruction.getSpecificationForPetriNet(mNet, mFactory),
							possibleInterferences, mSymbolTable, formulaMapping,
							new HashSet<>(mGhostVariables.values()), ghostInitAssignment, assignmentMapping);
		} else if (mAnnotation1 == null) {
			mOwickiGriesAnnotation = mAnnotation2;
		} else {
			mOwickiGriesAnnotation = mAnnotation1;
		}
	}

	/**
	 * @return union map of ghost variables of annotation1 and annotation2
	 */
	private Map<String, IProgramVar> getGhostVariables() {
		final Map<String, IProgramVar> ghostVars = new HashMap<>();
		final var vars = new HashSet<IProgramVar>();
		if (mAnnotation1 != null) {
			vars.addAll(mAnnotation1.getGhostVariables());
		}
		if (mAnnotation2 != null) {
			vars.addAll(mAnnotation2.getGhostVariables());
		}
		for (final IProgramVar iProgramVar : vars) {
			mSymbolTable.add(iProgramVar);
			ghostVars.put(iProgramVar.toString(), iProgramVar);
		}
		return ghostVars;
	}

	/**
	 * @return Map of P to the conjunction of the corresponding formulae of P of the annotations for each P in net
	 */
	private Map<P, IPredicate> getFormulaMap() {
		final Map<P, IPredicate> formulaMap = new HashMap<>();
		final var map1 = mAnnotation1.getFormulaMapping();
		final var map2 = mAnnotation2.getFormulaMapping();
		for (final P P : mNet.getPlaces()) {
			final var formula = mFactory.and(map1.get(P), map2.get(P));
			formulaMap.put(P, formula);
		}
		return formulaMap;
	}

	/**
	 * @return Union of the assignments of both annotation for each transition
	 */
	private Map<Transition<L, P>, GhostUpdate> getAssignmentMapping() {
		final var assignments1 = mAnnotation1.getAssignmentMapping();
		final var assignments2 = mAnnotation2.getAssignmentMapping();
		final Map<Transition<L, P>, GhostUpdate> assignmentMapping = new HashMap<>();
		for (final Transition<L, P> transition : mNet.getTransitions()) {
			final var assignment = combineGhostUpdates(assignments1.get(transition), assignments2.get(transition));
			if (assignment != null) {
				assignmentMapping.put(transition, assignment);
			}
		}
		return assignmentMapping;
	}

	/**
	 * @return Combine the two initial ghost assignments
	 */
	private Map<IProgramVar, Term> getGhostInitAssignment() {
		final HashMap<IProgramVar, Term> initAssignments = new HashMap<>(mAnnotation1.getGhostAssignment());
		initAssignments.putAll(mAnnotation2.getGhostAssignment());
		return initAssignments;
	}

	private static GhostUpdate combineGhostUpdates(final GhostUpdate update1, final GhostUpdate update2) {
		final Map<IProgramVar, Term> assignments = new HashMap<>();
		if (update1 == null) {
			return update2;
		}
		if (update2 == null) {
			return update1;
		}

		final var assignmentVars1 = update1.getAssignedVariables();
		final var assignmentVars2 = update2.getAssignedVariables();
		for (final IProgramVar iProgramVar : assignmentVars1) {
			assignments.put(iProgramVar, update1.getExpressionFor(iProgramVar));
		}
		for (final IProgramVar iProgramVar : assignmentVars2) {
			assignments.put(iProgramVar, update2.getExpressionFor(iProgramVar));
		}
		return new GhostUpdate(assignments);
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getAnnotation() {
		return mOwickiGriesAnnotation;
	}
}
