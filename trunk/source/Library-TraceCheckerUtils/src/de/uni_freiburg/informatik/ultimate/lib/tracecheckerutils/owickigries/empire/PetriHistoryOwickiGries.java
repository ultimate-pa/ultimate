/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

// TODO refactor to simplify code (and make it more efficient) e.g. by extracting findCoSets etc to another class
public class PetriHistoryOwickiGries<LETTER, PLACE> {
	private final ManagedScript mManagedScript;
	private final DefaultIcfgSymbolTable mSymbolTable;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final BranchingProcess<LETTER, PLACE> mBranchingProcess;
	private final Function<PLACE, IPredicate> mPlaceToAssertion;

	private final List<? extends INestedWordAutomaton<LETTER, PLACE>> mProofs;
	private final Map<PLACE, Integer> mProofPlaces;

	private final List<IProgramVar> mGhostVariables;
	private final BasicPredicateFactory mFactory;

	private final OwickiGriesAnnotation<LETTER, PLACE> mResult;

	public PetriHistoryOwickiGries(final IUltimateServiceProvider services, final BranchingProcess<LETTER, PLACE> bp,
			final IPetriNet<LETTER, PLACE> net, final Function<PLACE, IPredicate> placeToAssertion,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final List<? extends INestedWordAutomaton<LETTER, PLACE>> proofs) {
		mManagedScript = mgdScript;
		mSymbolTable = new DefaultIcfgSymbolTable(symbolTable, procedures);
		mNet = net;
		mBranchingProcess = bp;
		mPlaceToAssertion = placeToAssertion;
		mProofs = proofs;

		mFactory = new BasicPredicateFactory(services, mManagedScript, mSymbolTable);

		// create one ghost variable for each automaton
		final int numOfAutomata = proofs.size();
		mGhostVariables = createGhostVariables(numOfAutomata);

		mProofPlaces = new HashMap<>();
		final var initialGhostAssignment = new HashMap<IProgramVar, Term>();
		int proofIndex = 0;
		for (final var proof : proofs) {
			final var ghost = mGhostVariables.get(proofIndex);
			int placeIndex = 0;
			for (final var place : proof.getStates()) {
				mProofPlaces.put(place, placeIndex);
				if (proof.isInitial(place)) {
					assert !initialGhostAssignment.containsKey(ghost);
					initialGhostAssignment.put(ghost, SmtUtils.constructIntegerValue(mManagedScript.getScript(),
							ghost.getSort(), BigInteger.valueOf(placeIndex)));
				}
				placeIndex++;
			}
			proofIndex++;
		}

		// create formulas for each place
		final var formulaMap =
				mNet.getPlaces().stream().collect(Collectors.toMap(Function.identity(), this::getPlaceAssertion));

		// create ghost updates for transitions if they may change automata states
		final var ghostAssignments = getAssignmentMapping();

		mResult = new OwickiGriesAnnotation<>(net, mSymbolTable, formulaMap, Set.copyOf(mGhostVariables),
				initialGhostAssignment, ghostAssignments);
	}

	public OwickiGriesAnnotation<LETTER, PLACE> getResult() {
		return mResult;
	}

	private List<IProgramVar> createGhostVariables(final int numOfAutomata) {
		final List<IProgramVar> ghostVars = new ArrayList<>();
		mManagedScript.lock(this);
		try {
			for (int i = 0; i < numOfAutomata; ++i) {
				final var sort = SmtSortUtils.getIntSort(mManagedScript);
				final var tVar = mManagedScript.constructFreshTermVariable("aut" + i, sort);
				final var pVar =
						ProgramVarUtils.constructGlobalProgramVarPair(tVar.getName(), sort, mManagedScript, this);
				mSymbolTable.add(pVar);
				ghostVars.add(pVar);
			}
			return ghostVars;
		} finally {
			mManagedScript.unlock(this);
		}
	}

	private IPredicate getPlaceAssertion(final PLACE place) {
		final var coenabledAutomataPlaces = getCoEnabledAutomatonPlaces(place);
		System.out.printf("Automata places for %s: %s\n", place, coenabledAutomataPlaces);
		final var script = mManagedScript.getScript();

		// construct disjunction over possible combinations of automata places
		final var disjuncts = new ArrayList<Term>();
		for (final var combination : coenabledAutomataPlaces) {
			int proof = 0;
			final var conjuncts = new ArrayList<Term>();
			for (final var proofPlace : combination) {
				// final int proof = IntStream.range(0, mProofs.size())
				// .filter(i -> mProofs.get(i).getStates().contains(proofPlace)).findAny().getAsInt();
				conjuncts.add(getGhostEquation(proof, proofPlace));
				proof++;
			}
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		final var automataPlaceDisjunction = SmtUtils.or(script, disjuncts);

		// construct implications
		final var implications = new ArrayList<Term>();
		for (int proof = 0; proof < mGhostVariables.size(); ++proof) {
			final int currentProof = proof;

			final var relevantPlaces = coenabledAutomataPlaces.stream().map(l -> l.get(currentProof)).distinct()
					.collect(Collectors.toList());
			for (final var proofPlace : relevantPlaces) {
				implications.add(SmtUtils.implies(script, getGhostEquation(proof, proofPlace),
						mPlaceToAssertion.apply(proofPlace).getFormula()));
			}
		}
		final var relevantInvariant = SmtUtils.and(script, implications);

		// combine implications and disjunction to get assertion for place
		final var formula = SmtUtils.and(script, relevantInvariant, automataPlaceDisjunction);
		return mFactory.newPredicate(formula);
	}

	private final Term getGhostEquation(final int proof, final PLACE proofPlace) {
		final var script = mManagedScript.getScript();
		final var ghostVar = mGhostVariables.get(proof);
		return SmtUtils.equality(script, ghostVar.getTerm(), SmtUtils.constructIntegerValue(script, ghostVar.getSort(),
				BigInteger.valueOf(mProofPlaces.get(proofPlace))));
	}

	private List<List<PLACE>> getCoEnabledAutomatonPlaces(final PLACE place) {
		final var comparator = Comparator.<PLACE> comparingInt(p -> IntStream.range(0, mProofs.size())
				.filter(i -> mProofs.get(i).getStates().contains(p)).findAny().getAsInt());
		return getCoEnabledSets(Set.of(place), mProofPlaces.keySet())
				.map(l -> l.stream().filter(mProofPlaces::containsKey).sorted(comparator).collect(Collectors.toList()))
				.collect(Collectors.toList());
	}

	private Stream<List<PLACE>> getCoEnabledSets(final Set<PLACE> seed, final Collection<PLACE> admissible) {
		// find co-sets of places, one condition for each place in seed
		return findCoSets(ImmutableList.empty(), seed, false)
				// find super-co-sets where all additional conditions are admissible; and sets are maximal wrt. this
				.flatMap(seedCoSet -> maximizeCoSet(seedCoSet, admissible))
				// project to places corresponding to conditions
				.map(this::projectCoSetToPlaces);
	}

	private List<PLACE> projectCoSetToPlaces(final ImmutableList<Condition<LETTER, PLACE>> coSet) {
		return coSet.stream().map(Condition::getPlace).collect(Collectors.toList());
	}

	// TODO find all co-sets with exactly one condition per place in placeSet
	private Stream<ImmutableList<Condition<LETTER, PLACE>>> findCoSets(
			final ImmutableList<Condition<LETTER, PLACE>> baseSet, final Collection<PLACE> admissiblePlaces,
			final boolean allowSkips) {
		final var result = new ArrayList<ImmutableList<Condition<LETTER, PLACE>>>();

		final var places = new ArrayList<>(admissiblePlaces);
		final var corelation = mBranchingProcess.getCoRelation();

		final var worklist =
				new ArrayDeque<Triple<Integer, ImmutableList<Condition<LETTER, PLACE>>, ImmutableList<PLACE>>>();
		worklist.push(new Triple<>(-1, baseSet, ImmutableList.empty()));

		while (!worklist.isEmpty()) {
			final var current = worklist.pop();
			final int currentIndex = current.getFirst();
			final var currentSet = current.getSecond();
			final var currentSkipped = current.getThird();

			assert currentIndex < places.size();
			final int nextIndex = currentIndex + 1;
			if (nextIndex >= places.size()) {
				// check that nothing in currentSkipped is co-related
				final boolean isMaximal =
						currentSkipped.stream().flatMap(skipped -> mBranchingProcess.getConditions(skipped).stream())
								.noneMatch(sc -> corelation.isCoset(currentSet, sc));
				if (isMaximal) {
					// yield currentSet
					result.add(currentSet);
				}

				continue;
			}

			final var nextPlace = places.get(nextIndex);
			for (final var cond : mBranchingProcess.getConditions(nextPlace)) {
				if (corelation.isCoset(currentSet, cond)) {
					final var nextSet = new ImmutableList<>(cond, currentSet);
					worklist.push(new Triple<>(nextIndex, nextSet, currentSkipped));
				}
			}
			if (allowSkips) {
				worklist.push(new Triple<>(nextIndex, currentSet, new ImmutableList<>(nextPlace, currentSkipped)));
			}
		}
		return result.stream();
	}

	private Stream<ImmutableList<Condition<LETTER, PLACE>>>
			maximizeCoSet(final ImmutableList<Condition<LETTER, PLACE>> coSet, final Collection<PLACE> admissible) {
		return findCoSets(coSet, admissible, true);
	}

	private Map<Transition<LETTER, PLACE>, GhostUpdate> getAssignmentMapping() {
		final Map<Transition<LETTER, PLACE>, GhostUpdate> assignmentMapping = new HashMap<>();
		for (final Transition<LETTER, PLACE> transition : mNet.getTransitions()) {
			final var update = new HashMap<IProgramVar, Term>();
			for (int proof = 0; proof < mGhostVariables.size(); ++proof) {
				// TODO optimize: if the transition is a looper for this automaton, we don't need to do all this

				final Set<PLACE> proofPlaces = mProofs.get(proof).getStates();

				// TODO "allowSkips=true" is very inefficient here; indeed we must always skip all but one (fix this)
				final var possibleStates = getCoEnabledSets(transition.getPredecessors(), proofPlaces)
						.flatMap(l -> l.stream().filter(proofPlaces::contains)).collect(Collectors.toSet());

				final var ghost = mGhostVariables.get(proof);
				final var term =
						getGhostUpdate(proof, ghost, mProofs.get(proof), possibleStates, transition.getSymbol());
				if (term != null) {
					update.put(ghost, term);
				}
			}

			if (!update.isEmpty()) {
				assignmentMapping.put(transition, new GhostUpdate(update));
			}
		}
		return assignmentMapping;
	}

	private final Term getGhostUpdate(final int proofIndex, final IProgramVar ghost,
			final INestedWordAutomaton<LETTER, PLACE> proof, final Set<PLACE> possibleStates, final LETTER letter) {
		// for each possible state, see if the transition is a self loop or not
		final var successors = new ArrayList<Pair<PLACE, Integer>>();
		for (final var state : possibleStates) {
			final var succ = DataStructureUtils.getOneAndOnly(proof.internalSuccessors(state, letter),
					"outgoing transition for " + letter + " at state " + state).getSucc();
			if (!Objects.equals(state, succ)) {
				successors.add(new Pair<>(state, mProofPlaces.get(succ)));
			}
		}

		// if yes, then no update is needed
		if (successors.isEmpty()) {
			return null;
		}

		// if at least one is not a self-loop, encode the update
		// to do so, make a case distinction over all possible states and assign the next state
		// all the states where it is a self loop can be handled together as last case ("else unchanged")
		Term result = ghost.getTerm();
		final var script = mManagedScript.getScript();
		for (final var pair : successors) {
			result = SmtUtils.ite(script, getGhostEquation(proofIndex, pair.getFirst()),
					SmtUtils.constructIntegerValue(script, ghost.getSort(), BigInteger.valueOf(pair.getSecond())),
					result);
		}
		return result;
	}
}
