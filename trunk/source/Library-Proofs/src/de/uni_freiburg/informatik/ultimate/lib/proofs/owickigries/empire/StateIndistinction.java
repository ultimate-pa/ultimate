/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 Ecole Polytechnique
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.IPossibleInterferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 * This class computes a <em>state indistinction relation</em>, i.e., an equivalence relation between states of an
 * empire such that the imperial Owicki-Gries annotation need not distinguish between equivalent states.
 *
 * The ghost variable of the imperial Owicki-Gries relation tracks the equivalence class of the current empire state.
 *
 * An indistinction relation must satisfy the following conditions:
 *
 * TODO Update these descriptions, they are out-of-date.
 * <ol>
 * <li>If two states are equivalent, and there exists a transition with more than one successor enabled in both their
 * territories, then the states must have the same law.</li>
 * <li>If two states are equivalent, and there exists a transition and a co-marked place such that the transition is
 * enabled in both states' territories, and the place is also contained in both territories, then the states must have
 * the same law.
 * <li>If two states are equivalent, and both enable some transition t, then the respective successor states under t
 * must again be equivalent.</li>
 * </ol>
 *
 * TODO Check if "same laws" is really enough, and update code/description accordingly.
 */
class StateIndistinction<L, P, S> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IPetriNet<L, P> mProgram;
	private final IExplicitEmpire<L, P, S> mEmpire;
	private final IPossibleInterferences<Transition<L, P>, P> mPossibleInterferences;

	// A list of all states, used to establish a clear iteration order.
	private final List<S> mStates;

	// A symmetric relation of state pairs that cannot possibly be equivalent.
	// Its complement is an overapproximation of the state indistinction relation.
	// During the computation, additional pairs are added, tightening the overapproximation.
	private final SymmetricHashRelation<S> mExplicitDistinctions = new SymmetricHashRelation<>();

	// A partition (equivalence relation) relating states that will definitely be considered equivalent.
	// This is an underapproximation of the state indistinction relation that will be gradually increased until we
	// arrive at the desired indistinction relation.
	private final UnionFind<S> mPartition = new UnionFind<>();

	public StateIndistinction(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final IExplicitEmpire<L, P, S> empire,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(StateIndistinction.class);

		mProgram = program;
		mEmpire = empire;
		mPossibleInterferences = possibleInterferences;

		mStates = List.copyOf(mEmpire.getStates());
	}

	public Map<S, Integer> computePartition() {
		mLogger.info("Computing state indistinction between %d states", mStates.size());

		// initialize according to rules (join-laws) and (nonint-laws)
		initializeDistinctions();

		// propagate necessary distinctions according to rule (pseudo-simulation)
		propagateDistinctions();

		// determine a pair of states with unclear distinction, decide, and then propagate the resulting distinctions
		// repeat this until no more decisions need to be made
		while (decideDistinction() >= 0) {
			propagateDistinctions();
		}

		// represent partition as map from S to integers
		final var result = new HashMap<S, Integer>();
		int num = 0;
		for (final Set<S> eqvClass : mPartition.getAllEquivalenceClasses()) {
			for (final S member : eqvClass) {
				result.put(member, num);
			}
			num++;
		}

		mLogger.info("Grouped %d states into %d partitions.", mStates.size(), num);
		mLogger.debug(mPartition.getAllEquivalenceClasses());

		assert validate(result);
		return result;
	}

	// Utility functions to access the data structures correctly.
	// ==========================================================

	private void distinguish(final S state1, final S state2) {
		mLogger.debug("distinguishing %s and %s", state1, state2);

		final S repr1 = getRepresentative(state1);
		final S repr2 = getRepresentative(state2);
		assert !repr1.equals(repr2) : "splitting equivalent states";

		mExplicitDistinctions.addPair(repr1, repr2);
	}

	private boolean mustBeDistinguished(final S state1, final S state2) {
		return mExplicitDistinctions.containsPair(getRepresentative(state1), getRepresentative(state2));
	}

	private void merge(final S state1, final S state2) {
		mLogger.debug("merging %s and %s", state1, state2);
		mLogger.debug("  representatives: %s and %s", getRepresentative(state1), getRepresentative(state2));

		mPartition.union(state1, state2);
		final S representative = getRepresentative(state1);
		mExplicitDistinctions.addAllPairs(representative, mExplicitDistinctions.getImage(state1));
		mExplicitDistinctions.addAllPairs(representative, mExplicitDistinctions.getImage(state2));

		mLogger.debug("  distinctions: %s", mExplicitDistinctions);
		mLogger.debug("  equivalence classes: %s", mPartition.getAllEquivalenceClasses());
		mLogger.debug("  new representative: %s", getRepresentative(state1));
	}

	private boolean areEquivalent(final S state1, final S state2) {
		return getRepresentative(state1).equals(getRepresentative(state2));
	}

	private S getRepresentative(final S state) {
		return mPartition.find(state);
	}

	// Computation steps
	// =================

	private void initializeDistinctions() {
		mLogger.debug("Initializing indistinction...");

		for (final S state : mStates) {
			mPartition.makeEquivalenceClass(state);
		}

		for (int i = 0; i < mStates.size(); ++i) {
			final S q1 = mStates.get(i);

			final Territory<P, Region<P>> terr1 = mEmpire.getTerritory(q1);
			// final IPredicate law1 = mEmpire.getLaw(q1);

			for (int j = i + 1; j < mStates.size(); j++) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(getClass());
				}

				final S q2 = mStates.get(j);

				// states with equal laws need not be distinguished
				// TODO currently unclear if this is sound, so disabled for now
				// if (mEmpire.getLaw(q2).equals(law1)) {
				// continue;
				// }

				final Territory<P, Region<P>> terr2 = mEmpire.getTerritory(q2);
				if (haveCommonJoin(terr1, terr2) || haveCommonInterference(terr1, terr2)) {
					distinguish(q1, q2);
				}
			}
		}
	}

	private boolean haveCommonJoin(final Territory<P, Region<P>> terr1, final Territory<P, Region<P>> terr2) {
		return mProgram.getTransitions().stream()
				.anyMatch(t -> t.getPredecessors().size() > 1
						&& DataStructureUtils.haveNonEmptyIntersection(t.getPredecessors(), terr1.getPlaces())
						&& DataStructureUtils.haveNonEmptyIntersection(t.getPredecessors(), terr2.getPlaces())) /* ) */;
	}

	private boolean haveCommonInterference(final Territory<P, Region<P>> terr1, final Territory<P, Region<P>> terr2) {
		return mProgram.getPlaces().stream()
				.anyMatch(p -> mPossibleInterferences.getInterferingActions(p).stream()
						.anyMatch(t -> DataStructureUtils.haveNonEmptyIntersection(terr1.getPlaces(),
								DataStructureUtils.union(t.getPredecessors(), Set.of(p)))
								&& DataStructureUtils.haveNonEmptyIntersection(terr2.getPlaces(),
										DataStructureUtils.union(t.getPredecessors(), Set.of(p)))))/* ) */;
	}

	private boolean propagateDistinctions() {
		mLogger.debug("Propagating distinctions...");
		boolean changed;
		do {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass());
			}

			changed = propagateDistinctionsOneStep();
			if (changed) {
				mLogger.debug("propagated one step");
			} else {
				mLogger.debug("nothing to propagate");
			}
		} while (changed);
		return changed;
	}

	private boolean propagateDistinctionsOneStep() {
		boolean changed = false;

		for (int i = 0; i < mStates.size(); ++i) {
			final S q1 = mStates.get(i);
			final var transitions = mEmpire.getTerritory(q1).getEnabledTransitions(mProgram).toList();
			for (int j = i + 1; j < mStates.size(); ++j) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(getClass());
				}

				final S q2 = mStates.get(j);

				// already non-equivalent
				if (mustBeDistinguished(q1, q2)) {
					continue;
				}

				// rule (pseudo-simulation)
				for (final var t : transitions) {
					final Optional<S> succ1 = DataStructureUtils
							.getOnly(mEmpire.internalSuccessors(q1, t), "successor state").map(e -> e.getSucc());
					if (succ1.isEmpty()) {
						continue;
					}
					final Optional<S> succ2 = DataStructureUtils
							.getOnly(mEmpire.internalSuccessors(q2, t), "successor state").map(e -> e.getSucc());
					if (succ2.isEmpty()) {
						continue;
					}

					// If the successors must be distinguished, then so must s1 and s2.
					if (mustBeDistinguished(succ1.get(), succ2.get())) {
						distinguish(q1, q2);
						changed = true;
					}
				}
			}
		}

		return changed;
	}

	// TODO the point of returning the position is to speed up future searches (not yet implemented; return pair <i,j>)
	private int decideDistinction() {
		for (int i = 0; i < mStates.size(); ++i) {
			final S s1 = mStates.get(i);
			for (int j = i + 1; j < mStates.size(); ++j) {
				final S s2 = mStates.get(j);

				if (areEquivalent(s1, s2) || mustBeDistinguished(s1, s2)) {
					continue;
				}

				merge(s1, s2);
				return i;
			}
		}
		return -1;
	}

	private boolean validate(final Map<S, Integer> partition) {
		for (final S s1 : mStates) {
			for (final S s2 : mStates) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(getClass());
				}

				assert partition.get(s1) != null : "missing entry";
				assert partition.get(s2) != null : "missing entry";
				if (!partition.get(s1).equals(partition.get(s2))) {
					continue;
				}

				final var terr1 = mEmpire.getTerritory(s1);
				final var terr2 = mEmpire.getTerritory(s2);
				final boolean equalLaws = mEmpire.getLaw(s1).equals(mEmpire.getLaw(s2));
				assert equalLaws || !haveCommonJoin(terr1, terr2)
						: "condition join-laws violated for " + s1 + " and " + s2;
				assert equalLaws || !haveCommonInterference(terr1, terr2)
						: "condition nonint-laws violated for " + s1 + " and " + s2;

				terr1.getEnabledTransitions(mProgram).filter(terr2::enables).allMatch(t -> {
					assert terr1.enables(t);
					final Optional<S> succ1 = DataStructureUtils
							.getOnly(mEmpire.internalSuccessors(s1, t), "successor state").map(e -> e.getSucc());
					final Optional<S> succ2 = DataStructureUtils
							.getOnly(mEmpire.internalSuccessors(s2, t), "successor state").map(e -> e.getSucc());
					if (succ1.isEmpty() || succ2.isEmpty()) {
						return true;
					}
					assert partition.get(succ1.get()) != null : "missing entry for successor #1: " + succ1.get()
							+ " (index: " + mStates.indexOf(succ1.get()) + ")";
					assert partition.get(succ2.get()) != null : "missing entry for successor #2: " + succ2.get()
							+ " (index: " + mStates.indexOf(succ2.get()) + ")";
					final boolean valid = partition.get(succ1.get()).equals(partition.get(succ2.get()));
					assert valid
							: "pseudo-simulation violated for %s and %s under transition %s: successors %s and %s are non-equivalent"
									.formatted(s1, s2, t, succ1.get(), succ2.get());
					return valid;
				});
			}
		}
		return true;
	}
}
