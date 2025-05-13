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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
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
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LegalEmpireToOG<L, P> {
	private static final String GHOST = "g";

	private final IPetriNet<L, P> mNet;
	private final ManagedScript mManagedScript;
	private final Script mScript;

	private final BasicPredicateFactory mFactory;
	private final NestedWordAutomatonReachableStates<Transition<L, P>, List<State<L, P>>> mProductAutomaton;
	private final IProgramVar mGhostVariable;
	private final Map<List<State<L, P>>, Term> mStateTerms;
	private final HashRelation<List<State<L, P>>, P> mStateToPlaces;
	private final LegalFocus<L, P> mLegalFocus;
	private final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> mOwickiGriesAnnotation;

	public LegalEmpireToOG(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IPetriNet<L, P> net, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final INwaOutgoingTransitionProvider<Transition<L, P>, List<State<L, P>>> empireProduct,
			final LegalFocus<L, P> legalFocus,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		mNet = net;
		mManagedScript = mgdScript;
		mScript = mManagedScript.getScript();
		mLegalFocus = legalFocus;

		mGhostVariable = createGhostVariable();
		final var newSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		newSymbolTable.add(mGhostVariable);
		mFactory = new BasicPredicateFactory(services, mManagedScript, newSymbolTable);

		final var logger = services.getLoggingService().getLogger(getClass());
		try {
			logger.info("Exploring product empire...");
			mProductAutomaton =
					new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(services), empireProduct);
			logger.info("Product empire has %s", mProductAutomaton.sizeInformation());
		} catch (final AutomataOperationCanceledException aoce) {
			throw new ToolchainCanceledException(aoce,
					new RunningTaskInfo(getClass(), "collecting reachable states of empire automaton"));
		}
		mStateToPlaces = getStatePlaces();
		mStateTerms = getStateTerms();
		final Map<P, IPredicate> formulaMapping = getFormulaMap();
		final Map<Transition<L, P>, GhostUpdate> assignmentMapping = getAssignmentMapping();
		final Map<IProgramVar, Term> ghostInitAssignment = getGhostInitAssignment();

		mOwickiGriesAnnotation = new OwickiGriesAnnotation<>(
				OwickiGriesConstruction.getSpecificationForPetriNet(mNet, mFactory), possibleInterferences,
				newSymbolTable, formulaMapping, Set.of(mGhostVariable), ghostInitAssignment, assignmentMapping);
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
	 * @return Map of P to the corresponding formula for each P depending on the legal focus
	 */
	private Map<P, IPredicate> getFormulaMap() {
		final Map<P, IPredicate> formulaMap = new HashMap<>();
		for (final P place : mNet.getPlaces()) {
			final var states = mStateToPlaces.entrySet().stream().filter(p -> p.getValue().contains(place))
					.map(Entry::getKey).collect(Collectors.toSet());
			assert noErrorPlaceInStates(place, states) : "Accepting place in intersection of the states";
			final var disjuncts = new ArrayList<Term>();
			for (final List<State<L, P>> stateList : states) {
				final var conjuncts = new ArrayList<Term>();
				conjuncts.add(SmtUtils.binaryEquality(mScript, mGhostVariable.getTerm(), mStateTerms.get(stateList)));
				final var focusedLaws = stateList.stream().filter(s -> mLegalFocus.isFocused(place, s))
						.map(s -> s.law().getFormula()).toList();
				conjuncts.addAll(focusedLaws);
				final var conjunction = SmtUtils.and(mScript, conjuncts);
				disjuncts.add(conjunction);
			}
			formulaMap.put(place, mFactory.newPredicate(SmtUtils.or(mScript, disjuncts)));
		}
		return formulaMap;
	}

	private boolean noErrorPlaceInStates(final P place, final Set<List<State<L, P>>> states) {
		return mNet.isAccepting(place) && !states.isEmpty() ? false : true;
	}

	/**
	 * @return Map of transition to the corresponding formula for each transition in net
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

	private GhostUpdate getTransitionAssignment(final Transition<L, P> transition) {
		final var states = mProductAutomaton.getStates();
		final var enablingStates =
				states.stream().filter(s -> mProductAutomaton.internalSuccessors(s, transition).iterator().hasNext())
						.collect(Collectors.toSet());
		if (enablingStates.isEmpty()) {
			return null;
		}

		final var pairs = new HashSet<Pair<List<State<L, P>>, List<State<L, P>>>>();
		for (final List<State<L, P>> state : enablingStates) {
			final var successors = mProductAutomaton.internalSuccessors(state, transition).iterator();
			if (successors.hasNext()) {
				final var succ = successors.next();
				pairs.add(new Pair<>(state, succ.getSucc()));
			}
			assert !successors.hasNext() : "More than one successors in automaton for a transition";
		}

		final var noUpdates = pairs.stream().allMatch(s -> s.getFirst().equals(s.getSecond()));
		if (noUpdates) {
			return null;
		}

		final Term term = getGhostUpdateTerm(new ArrayList<>(pairs));
		return new GhostUpdate(Map.of(mGhostVariable, term));
	}

	private Term getGhostUpdateTerm(final List<Pair<List<State<L, P>>, List<State<L, P>>>> statePairs) {
		Term updateTerm;
		final var pair = statePairs.get(0);
		final var pred = pair.getFirst();
		final var succ = pair.getSecond();
		final var equalsTerm = mScript.term(SMTLIBConstants.EQUALS, mGhostVariable.getTerm(), mStateTerms.get(pred));
		if (statePairs.size() == 1) {
			updateTerm = mScript.term(SMTLIBConstants.ITE, equalsTerm, mStateTerms.get(succ), mGhostVariable.getTerm());
		} else {
			updateTerm = mScript.term(SMTLIBConstants.ITE, equalsTerm, mStateTerms.get(succ),
					getGhostUpdateTerm(statePairs.subList(1, statePairs.size())));
		}
		return updateTerm;
	}

	private Map<List<State<L, P>>, Term> getStateTerms() {
		final var stateTerms = new LinkedHashMap<List<State<L, P>>, Term>();

		var num = 1;
		for (final List<State<L, P>> state : mProductAutomaton.getStates()) {
			stateTerms.put(state, mScript.numeral(String.valueOf(num)));
			num++;
		}

		return stateTerms;
	}

	private HashRelation<List<State<L, P>>, P> getStatePlaces() {
		final var stateToPlaces = new HashRelation<List<State<L, P>>, P>();
		final var states = mProductAutomaton.getStates();
		for (final List<State<L, P>> list : states) {
			final var intersection =
					list.stream().<Set<P>> map(s -> s.territory().getPlaces()).reduce(DataStructureUtils::intersection);
			assert intersection.isPresent() : "Places of the state list is empty";
			final var interOrEmpty = intersection.orElseGet(Set::of);
			stateToPlaces.addAllPairs(list, interOrEmpty);
		}

		return stateToPlaces;
	}

	/**
	 * @return Map of ghost variable to its init assignment (which is the numeral of the init state)
	 */
	private Map<IProgramVar, Term> getGhostInitAssignment() {
		final HashMap<IProgramVar, Term> initAssignments = new HashMap<>();
		final var initState = DataStructureUtils.getOneAndOnly(mProductAutomaton.getInitialStates(), "initial state");
		initAssignments.put(mGhostVariable, mStateTerms.get(initState));
		return initAssignments;
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getAnnotation() {
		return mOwickiGriesAnnotation;
	}
}
