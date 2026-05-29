/*
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.naive;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.IFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HittingSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs an Owicki-Gries annotation for a Petri program from a Floyd/Hoare annotation of the reachability graph of
 * the Petri net, by introducing a boolean ghost variable for each place in the Petri net.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <P>
 *            The type of places in the Petri program
 * @param <L>
 *            The type of statements in the Petri program
 */
public class OwickiGriesConstruction<L, P> {
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final BasicPredicateFactory mFactory;

	private final IPetriNet<L, P> mNet;
	private final Collection<Marking<P>> mReachableMarkings;
	private final IFloydHoareAnnotation<Marking<P>> mFloydHoareAnnotation;
	private final DefaultIcfgSymbolTable mSymbolTable;

	private final Set<P> mHittingSet;
	private final Map<P, IProgramVar> mGhostVariables;
	private final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mAnnotation;

	public OwickiGriesConstruction(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IPetriNet<L, P> net, final Collection<Marking<P>> reachableMarkings,
			final IFloydHoareAnnotation<Marking<P>> floydHoare, final boolean useHittingSets) {
		this(services, csToolkit.getManagedScript(), csToolkit.getSymbolTable(), csToolkit.getProcedures(), net,
				reachableMarkings, floydHoare, useHittingSets);
	}

	public OwickiGriesConstruction(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable, final Set<String> procedures, final IPetriNet<L, P> net,
			final Collection<Marking<P>> reachableMarkings, final IFloydHoareAnnotation<Marking<P>> floydHoare,
			final boolean useHittingSets) {
		mManagedScript = mgdScript;
		mScript = mManagedScript.getScript();

		mNet = net;
		mReachableMarkings = reachableMarkings;
		mFloydHoareAnnotation = floydHoare;
		mSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);

		// TODO let callers pass predicate factory
		mFactory = new BasicPredicateFactory(services, mManagedScript, mSymbolTable);

		mGhostVariables = getGhostVariables();
		mHittingSet = useHittingSets ? getHittingSet() : null;
		final Map<P, IPredicate> formulaMapping = getFormulaMapping();
		final Map<Transition<L, P>, GhostUpdate> assignmentMapping = getAssignmentMapping();
		final Map<IProgramVar, Term> ghostInitAssignment = getGhostInitAssignment();

		mAnnotation = new OwickiGriesAnnotation<>(getSpecificationForPetriNet(net, mFactory),
				getPossibleInterferences(), mSymbolTable, formulaMapping, new HashSet<>(mGhostVariables.values()),
				ghostInitAssignment, assignmentMapping);
	}

	/**
	 * Constructs the mapping from places to formulas. A place is mapped to a disjunction of marking predicates, where
	 * each marking predicate is a conjunction of ghost variables and a Floyd/Hoare predicate.
	 *
	 * @return a map with a predicate for each place in the Petri net
	 */
	private Map<P, IPredicate> getFormulaMapping() {
		final Map<P, IPredicate> mapping = new HashMap<>();
		for (final P place : mNet.getPlaces()) {
			final Map<IPredicate, List<Term>> disjunctsByLaw =
					mReachableMarkings.stream().filter(m -> m.contains(place))
							// As an optimization of the formula structure, we group markings with the same law.
							.collect(Collectors.groupingBy(mFloydHoareAnnotation::getAnnotation,
									Collectors.mapping(this::getGhostFormulaForMarking, Collectors.toList())));

			final var disjuncts = disjunctsByLaw.entrySet().stream()
					.map(e -> SmtUtils.and(mScript, e.getKey().getFormula(), SmtUtils.or(mScript, e.getValue())))
					.toList();

			mapping.put(place, mFactory.newPredicate(SmtUtils.or(mScript, disjuncts)));
		}

		return mapping;
	}

	private Term getGhostFormulaForMarking(final Marking<P> marking) {
		final Set<Term> terms = new HashSet<>();
		Set<P> posPlaces = marking.stream().collect(Collectors.toSet());
		if (mHittingSet != null) {
			posPlaces = DataStructureUtils.intersection(mHittingSet, posPlaces);
		}
		for (final P otherPlace : posPlaces) {
			final Term ghost = mGhostVariables.get(otherPlace).getTerm();
			terms.add(ghost);
		}
		if (mHittingSet == null) {
			terms.addAll(getAllNotMarking(marking));
		} else {
			terms.addAll(getHitNotMarking(marking));
		}
		return SmtUtils.and(mScript, terms);
	}

	/**
	 *
	 * @param marking
	 * @return Formula MethodA:Predicate with GhostVariables of all other places not in marking
	 */
	private Set<Term> getAllNotMarking(final Marking<P> marking) {
		final Set<P> markPlaces = marking.stream().collect(Collectors.toSet());
		final Set<P> notMarking = DataStructureUtils.difference(new HashSet<>(mNet.getPlaces()), markPlaces);
		final Set<Term> predicates = new HashSet<>();
		for (final P place : notMarking) {
			final Term ghost = mGhostVariables.get(place).getTerm();
			predicates.add(SmtUtils.not(mScript, ghost));
		}
		return predicates;
	}

	/**
	 *
	 * @param marking
	 * @return Formula MethodB:Predicate with GhostVariables of hitting set of other places not in marking
	 */
	private Set<Term> getHitNotMarking(final Marking<P> marking) {
		// TODO: remove places from hittingSet than are in current marking.
		final Set<P> notMarking =
				DataStructureUtils.difference(mHittingSet, marking.stream().collect(Collectors.toSet()));
		final Set<Term> predicates = new HashSet<>();
		for (final P place : notMarking) {
			final Term ghost = mGhostVariables.get(place).getTerm();
			predicates.add(SmtUtils.not(mScript, ghost));
		}
		return predicates;
	}

	private Set<P> getHittingSet() {
		final Set<Set<P>> reachableMarkings = new HashSet<>();
		for (final Marking<P> mark : mReachableMarkings) {
			reachableMarkings.add(mark.stream().collect(Collectors.toSet()));
		}
		final HittingSet<P> hitSet = new HittingSet<>(reachableMarkings);
		return hitSet.getSymmHittingSet();
	}

	/**
	 *
	 * @param marking
	 * @return Formula MethodA: GhostVariables if marking is subset of other marking
	 */
	private Set<Term> getSubsetMarking(final Marking<P> marking) {
		final Set<P> markPlaces = marking.stream().collect(Collectors.toSet());
		final Set<P> notInMarking = new HashSet<>();
		for (final Marking<P> otherMarking : mReachableMarkings) {
			notInMarking.addAll(getSupPlaces(otherMarking, markPlaces));
		}
		final Set<Term> predicates = new HashSet<>();
		for (final P place : notInMarking) {
			final Term ghost = mGhostVariables.get(place).getTerm();
			predicates.add(SmtUtils.not(mScript, ghost));
		}
		return predicates;
	}

	private Set<P> getSupPlaces(final Marking<P> otherMarking, final Set<P> markPlaces) {
		Set<P> subPlaces = new HashSet<>();
		final Set<P> otherPlaces = otherMarking.stream().collect(Collectors.toSet());
		if (otherPlaces.containsAll(markPlaces)) {
			subPlaces = DataStructureUtils.difference(otherPlaces, markPlaces);
		}
		return subPlaces;
	}

	/**
	 * @return map of places to ghost variables
	 */
	private Map<P, IProgramVar> getGhostVariables() {
		final Map<P, IProgramVar> ghostVars = new HashMap<>();
		int i = 0;
		final Collection<P> places = mNet.getPlaces();
		mManagedScript.lock(this);
		try {
			for (final P place : places) {
				// TODO (Dominik 2021-01-27) Name ghost variables by place for easier debugging
				final TermVariable tVar =
						mManagedScript.constructFreshTermVariable("np" + i, SmtSortUtils.getBoolSort(mManagedScript));
				final IProgramVar pVar = ProgramVarUtils.constructGlobalProgramVarPair(tVar.getName(),
						SmtSortUtils.getBoolSort(mManagedScript), mManagedScript, this);
				mSymbolTable.add(pVar);
				ghostVars.put(place, pVar);
				i++;
			}
			return ghostVars;
		} finally {
			mManagedScript.unlock(this);
		}
	}

	/**
	 * @return initial value assignment of all ghost variables.
	 */
	private Map<IProgramVar, Term> getGhostInitAssignment() {
		final HashMap<IProgramVar, Term> initAssignments = new HashMap<>();
		for (final P place : mNet.getInitialPlaces()) {
			initAssignments.put(mGhostVariables.get(place), mScript.term("true"));
		}
		final Set<IProgramVar> notInitGhostVariables =
				DataStructureUtils.difference(new HashSet<>(mGhostVariables.values()), initAssignments.keySet());
		for (final IProgramVar variable : notInitGhostVariables) {
			initAssignments.put(variable, mScript.term("false"));
		}
		return initAssignments;
	}

	/**
	 *
	 * @return Map of Places' Ghost Variables assignments to Transitions
	 *
	 */
	private Map<Transition<L, P>, GhostUpdate> getAssignmentMapping() {
		final Map<Transition<L, P>, GhostUpdate> assignmentMapping = new HashMap<>();
		for (final Transition<L, P> transition : mNet.getTransitions()) {
			final var assignment = getTransitionAssignment(transition);
			if (assignment != null) {
				assignmentMapping.put(transition, assignment);
			}
		}
		return assignmentMapping;
	}

	/**
	 *
	 * @param transition
	 * @return TransFormula of sequential compositions of GhostVariables assignments. GhostVariables of Predecessors
	 *         Places are assign to false, GhostVariables of Successors Places are assign to true.
	 */
	private GhostUpdate getTransitionAssignment(final Transition<L, P> transition) {
		final Map<IProgramVar, Term> assignments = new HashMap<>();

		final Set<P> predecessors = transition.getPredecessors();
		final Set<P> successors = transition.getSuccessors();

		final var falseTerm = mScript.term(SMTLIBConstants.FALSE);
		for (final P place : predecessors) {
			if ((mHittingSet == null || mHittingSet.contains(place)) && !successors.contains(place)) {
				assignments.put(mGhostVariables.get(place), falseTerm);
			}
		}

		final var trueTerm = mScript.term(SMTLIBConstants.TRUE);
		for (final P place : successors) {
			if ((mHittingSet == null || mHittingSet.contains(place)) && !predecessors.contains(place)) {
				assignments.put(mGhostVariables.get(place), trueTerm);
			}
		}

		if (assignments.isEmpty()) {
			return null;
		}
		return new GhostUpdate(assignments);
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getResult() {
		return mAnnotation;
	}

	private IPossibleInterferences<Transition<L, P>, P> getPossibleInterferences() {
		final HashRelation<P, Transition<L, P>> relation = new HashRelation<>();
		for (final Transition<L, P> transition : mNet.getTransitions()) {
			final Set<P> predecessors = transition.getPredecessors();
			final Set<Marking<P>> enabledMarkings = mReachableMarkings.stream()
					.filter(marking -> marking.containsAll(predecessors)).collect(Collectors.toSet());
			for (final Marking<P> marking : enabledMarkings) {
				for (final P place : marking) {
					// places that are not predecessors of transition
					if (!predecessors.contains(place)) {
						relation.addPair(place, transition);
					}
				}
			}
		}
		return IPossibleInterferences.fromRelation(relation);
	}

	public static <L, P> ThreadModularPrePostSpecification<P, Marking<P>>
			getSpecificationForPetriNet(final IPetriNet<L, P> net, final BasicPredicateFactory factory) {
		final var preconditions = Map.of(Marking.initial(net), factory.and());
		return new ThreadModularPrePostSpecification<>(preconditions, net::isAccepting, factory.or());
	}
}
