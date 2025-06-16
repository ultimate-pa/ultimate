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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesConstruction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EmpireToOG<S, L, P> {
	private static final String GHOST = "ghost";

	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IPetriNet<L, P> mProgram;

	private final IExplicitEmpireAutomaton<L, P, S> mEmpireAutomaton;
	private final ILegalFocusFunction<S, P> mLegalFocus;

	private final BasicPredicateFactory mFactory;
	private final IProgramVar mGhostVariable;
	private final Map<S, Term> mStateTerms;

	private final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGriesAnnotation;

	public EmpireToOG(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> program, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final IExplicitEmpireAutomaton<L, P, S> empire,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		this(services, mgdScript, program, symbolTable, procedures, empire, possibleInterferences,
				new ILegalFocusFunction.TrivialFocus<>(empire));
	}

	public EmpireToOG(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> program, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final IExplicitEmpireAutomaton<L, P, S> empire,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences,
			final ILegalFocusFunction<S, P> legalFocus) {
		mProgram = program;
		mManagedScript = mgdScript;
		mScript = mManagedScript.getScript();

		mEmpireAutomaton = empire;
		mLegalFocus = legalFocus;

		mGhostVariable = createGhostVariable();
		final var newSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		newSymbolTable.add(mGhostVariable);

		mFactory = new BasicPredicateFactory(services, mManagedScript, newSymbolTable);
		mStateTerms = getStateTerms();
		final Map<P, IPredicate> placeAnnotations = computePlaceAnnotations();
		final Map<Transition<L, P>, GhostUpdate> ghostUpdates = computeGhostUpdateMapping();
		final Map<IProgramVar, Term> initialGhostValuation = computeInitialGhostValuation();

		mOwickiGriesAnnotation = new OwickiGriesAnnotation<>(
				OwickiGriesConstruction.getSpecificationForPetriNet(mProgram, mFactory), possibleInterferences,
				newSymbolTable, placeAnnotations, Set.of(mGhostVariable), initialGhostValuation, ghostUpdates);
	}

	private IProgramVar createGhostVariable() {
		mManagedScript.lock(this);
		try {
			final TermVariable tVar =
					mManagedScript.constructFreshTermVariable(GHOST, SmtSortUtils.getIntSort(mManagedScript));
			return ProgramVarUtils.constructGlobalProgramVarPair(tVar.getName(),
					SmtSortUtils.getIntSort(mManagedScript), mManagedScript, this);
		} finally {
			mManagedScript.unlock(this);
		}
	}

	/**
	 * @return Map of places to the corresponding formula for each place
	 */
	private Map<P, IPredicate> computePlaceAnnotations() {
		final Map<P, IPredicate> formulaMap = new HashMap<>();
		final var empireStates = mEmpireAutomaton.getStates();
		for (final P place : mProgram.getPlaces()) {
			final var states = empireStates.stream().filter(s -> mEmpireAutomaton.containsPlace(s, place)).toList();
			assert noErrorPlaceInStates(place, states) : "Accepting place in state";

			final var disjuncts = new ArrayList<Term>(states.size());
			for (final S state : states) {
				final var placeRegion = mEmpireAutomaton.getTerritory(state).getPlaceRegion(place);
				final var conjuncts = new ArrayList<Term>();

				final Term ghostEquation =
						SmtUtils.binaryEquality(mScript, mGhostVariable.getTerm(), mStateTerms.get(state));
				conjuncts.add(ghostEquation);

				final var focusedLaws = mLegalFocus.getFocusedLaws(state, placeRegion).stream()
						.map(IPredicate::getFormula).collect(Collectors.toList());
				conjuncts.addAll(focusedLaws);

				final var conjunction = SmtUtils.and(mScript, conjuncts);
				disjuncts.add(conjunction);
			}
			formulaMap.put(place, mFactory.newPredicate(SmtUtils.or(mScript, disjuncts)));
		}
		return formulaMap;
	}

	private boolean noErrorPlaceInStates(final P place, final Collection<S> states) {
		return !mProgram.isAccepting(place) || states.isEmpty();
	}

	/**
	 * @return Map of ghost variable to its init assignment (which is the numeral of the init state)
	 */
	private Map<IProgramVar, Term> computeInitialGhostValuation() {
		final var initState = DataStructureUtils.getOneAndOnly(mEmpireAutomaton.getInitialStates(), "initial state");
		return Map.of(mGhostVariable, mStateTerms.get(initState));
	}

	/**
	 * @return Map of transition to the corresponding formula for each transition in net
	 */
	private Map<Transition<L, P>, GhostUpdate> computeGhostUpdateMapping() {
		final var mapping = new HashMap<Transition<L, P>, GhostUpdate>();
		for (final var transition : mProgram.getTransitions()) {
			final var update = computeGhostUpdateForTransition(transition);
			if (update != null) {
				mapping.put(transition, update);
			}
		}
		return mapping;
	}

	private GhostUpdate computeGhostUpdateForTransition(final Transition<L, P> transition) {
		final var updatePairs = new ArrayList<Pair<S, S>>();

		for (final S state : mEmpireAutomaton.getStates()) {
			final var edge = DataStructureUtils.getOnly(mEmpireAutomaton.internalSuccessors(state, transition),
					"More than one successor in automaton for a transition");
			if (!edge.isPresent()) {
				// The state does not have an edge for the given transition.
				// This either means that the state's territory does not enable the transition,
				// or that the edge would lead to a law "false".
				// In either case, no ghost update is needed.
				continue;
			}

			final S successor = edge.orElseThrow().getSucc();
			if (state.equals(successor)) {
				// The edge is a self-loop. Thus, it does not have to be handled explicitly in the ghost update.
				// Instead, self-loops are handled in the default case of the ghost update's case distinction.
				continue;
			}

			updatePairs.add(new Pair<>(state, successor));
		}

		if (updatePairs.isEmpty()) {
			// Avoid returning a trivial ghost update.
			return null;
		}

		final Term caseDistinction = getGhostUpdateTerm(updatePairs);
		return new GhostUpdate(Map.of(mGhostVariable, caseDistinction));
	}

	private Term getGhostUpdateTerm(final List<Pair<S, S>> statePairs) {
		Term updateTerm = mGhostVariable.getTerm();
		for (final var pair : statePairs) {
			final var pred = pair.getFirst();
			final var succ = pair.getSecond();
			final var equalsTerm =
					mScript.term(SMTLIBConstants.EQUALS, mGhostVariable.getTerm(), mStateTerms.get(pred));
			updateTerm = mScript.term(SMTLIBConstants.ITE, equalsTerm, mStateTerms.get(succ), updateTerm);
		}
		return updateTerm;
	}

	private Map<S, Term> getStateTerms() {
		final var stateTerms = new LinkedHashMap<S, Term>();

		var num = 1;
		for (final S state : mEmpireAutomaton.getStates()) {
			stateTerms.put(state, mScript.numeral(String.valueOf(num)));
			num++;
		}

		return stateTerms;
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getAnnotation() {
		return mOwickiGriesAnnotation;
	}
}
