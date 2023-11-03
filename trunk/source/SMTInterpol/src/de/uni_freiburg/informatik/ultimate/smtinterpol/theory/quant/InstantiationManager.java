/*
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstanceOrigin;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstantiationMethod;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.SubstitutionHelper.SubstitutionResult;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.dawg.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching.SubstitutionInfo;

/**
 * This class takes care of clause, literal and term instantiation.
 *
 * Literals are pre-evaluated in order to create less false literals and clauses containing true literals.
 *
 * TODO Rework methods that do almost the same.
 *
 * @author Tanja Schindler
 *
 */
public class InstantiationManager {

	private final Clausifier mClausifier;
	private final QuantifierTheory mQuantTheory;
	private final EMatching mEMatching;

	private final Map<QuantClause, Map<List<Term>, InstClause>> mClauseInstances;

	private final InstanceValue mDefaultValueForLitDawgs;
	private final List<InstanceValue> mRelevantValuesForCheckpoint;

	private int mSubsAgeForFinalCheck = 0;

	public InstantiationManager(final QuantifierTheory quantTheory) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();
		mEMatching = quantTheory.getEMatching();
		mClauseInstances = new HashMap<>();
		mDefaultValueForLitDawgs =
				mQuantTheory.mUseUnknownTermValueInDawgs ? InstanceValue.UNKNOWN_TERM : InstanceValue.ONE_UNDEF;
		mRelevantValuesForCheckpoint = new ArrayList<>();
		mRelevantValuesForCheckpoint.add(InstanceValue.FALSE);
		mRelevantValuesForCheckpoint.add(InstanceValue.ONE_UNDEF);
		if (mQuantTheory.mInstantiationMethod == InstantiationMethod.E_MATCHING_EAGER
				|| mQuantTheory.mInstantiationMethod == InstantiationMethod.E_MATCHING_LAZY) {
			mRelevantValuesForCheckpoint.add(InstanceValue.OTHER);
		} else if (mQuantTheory.mPropagateNewTerms) {
			mRelevantValuesForCheckpoint.add(InstanceValue.UNKNOWN_TERM);
		}
	}

	/**
	 * Add the clause to the instantiation manager.
	 *
	 * @param qClause
	 *            the quantified clause.
	 */
	public void addClause(final QuantClause qClause) {
		mClauseInstances.put(qClause, new LinkedHashMap<>());
	}

	/**
	 * Remove the clause from the instantiation manager.
	 *
	 * @param clause
	 *            the quantified clause.
	 */
	public void removeClause(final QuantClause clause) {
		assert mClauseInstances.containsKey(clause);
		mClauseInstances.remove(clause);
	}

	/**
	 * Remove all existing InstClauses from the instantiation manager.
	 */
	public void removeAllInstClauses() {
		for (final Map<List<Term>, InstClause> instClauses : mClauseInstances.values()) {
			instClauses.clear();
		}
	}

	/**
	 * Reset the interesting substitution terms for all clauses.
	 */
	public void resetInterestingTerms() {
		for (final QuantClause qClause : mQuantTheory.getQuantClauses()) {
			qClause.clearInterestingTerms();
		}
	}

	public void resetSubsAgeForFinalCheck() {
		mSubsAgeForFinalCheck = 0;
	}

	/**
	 * Find instances of quant clauses that would be conflict or unit instances. This will actually compute the clause
	 * instances, i.e., it will create the ground literals. We prefer conflict instances, only if there are none, unit
	 * instances are computed.
	 *
	 * @return the clause instances.
	 */
	public Set<InstClause> findConflictAndUnitInstancesWithEMatching() {
		final Set<InstClause> conflictAndUnitClauses = new LinkedHashSet<>();
		final Map<QuantClause, Collection<List<Term>>> unitSubs = new LinkedHashMap<>();

		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());

		for (final QuantClause qClause : currentQuantClauses) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return Collections.emptySet();
			}
			if (qClause.hasTrueGroundLits()) {
				continue;
			}
			final Dawg<Term, InstantiationInfo> dawg = computeClauseDawg(qClause);
			for (final InstantiationInfo subsWithVal : getRelevantSubsFromDawg(qClause, dawg)) {
				if (mQuantTheory.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				final List<Term> subs = subsWithVal.getSubs();
				final InstanceValue val = subsWithVal.getInstValue();
				if (val == InstanceValue.FALSE) {
					final InstClause inst = computeClauseInstance(qClause, subs, InstanceOrigin.CONFLICT);
					if (inst != null) {
						conflictAndUnitClauses.add(inst);
					}
				} else {
					assert val == InstanceValue.ONE_UNDEF || val == InstanceValue.UNKNOWN_TERM;
					if (!unitSubs.containsKey(qClause)) {
						unitSubs.put(qClause, new ArrayList<List<Term>>());
					}
					unitSubs.get(qClause).add(subs);
				}
			}
		}
		if (conflictAndUnitClauses.isEmpty()) {
			for (final Entry<QuantClause, Collection<List<Term>>> e : unitSubs.entrySet()) {
				final QuantClause clause = e.getKey();
				for (final List<Term> subs : e.getValue()) {
					if (mQuantTheory.getEngine().isTerminationRequested()) {
						return Collections.emptySet();
					}
					final InstClause inst = computeClauseInstance(clause, subs, InstanceOrigin.CONFLICT);
					if (inst != null) {
						conflictAndUnitClauses.add(inst);
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * Find instances of quant clauses that would be conflict or unit instances. This will actually compute the clause
	 * instances, i.e., it will create the ground literals. We prefer conflict instances, only if there are none, unit
	 * instances are computed.
	 *
	 * @return A Set of potentially conflicting and unit instances.
	 */
	public Set<InstClause> findConflictAndUnitInstances() {
		final Set<InstClause> conflictAndUnitClauses = new LinkedHashSet<>();
		final Map<QuantClause, Collection<List<Term>>> unitSubs = new LinkedHashMap<>();
		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (final QuantClause quantClause : currentQuantClauses) {
			if (mClausifier.getEngine().isTerminationRequested()) {
				return null;
			}
			if (quantClause.hasTrueGroundLits()) {
				continue;
			}
			quantClause.updateInterestingTermsAllVars();
			final Set<List<Term>> allSubstitutions = computeAllSubstitutions(quantClause);
			for (final List<Term> subs : allSubstitutions) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				// TODO Don't evaluate existing instances
				final InstanceValue clauseValue = evaluateClauseInstance(quantClause, subs);
				if (clauseValue != InstanceValue.IRRELEVANT) {
					if (clauseValue == InstanceValue.FALSE) {
						final InstClause inst = computeClauseInstance(quantClause, subs, InstanceOrigin.CONFLICT);
						if (inst != null) {
							conflictAndUnitClauses.add(inst);
						}
					} else {
						assert clauseValue == InstanceValue.ONE_UNDEF || clauseValue == InstanceValue.UNKNOWN_TERM;
						if (!unitSubs.containsKey(quantClause)) {
							unitSubs.put(quantClause, new ArrayList<List<Term>>());
						}
						unitSubs.get(quantClause).add(subs);
					}
				}
			}
		}
		if (conflictAndUnitClauses.isEmpty()) {
			for (final Entry<QuantClause, Collection<List<Term>>> e : unitSubs.entrySet()) {
				final QuantClause clause = e.getKey();
				for (final List<Term> subs : e.getValue()) {
					if (mQuantTheory.getEngine().isTerminationRequested()) {
						return Collections.emptySet();
					}
					final InstClause inst = computeClauseInstance(clause, subs, InstanceOrigin.CONFLICT);
					if (inst != null) {
						conflictAndUnitClauses.add(inst);
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}


	/**
	 * Compute clause instances found by E-matching. This method does not build instances of quant clauses containing
	 * ground literals that are currently set to true, or instances producing new terms (i.e., without equivalent known
	 * terms).
	 *
	 * @return the computed InstClauses, except the ones resulting in trivially true clauses.
	 */
	public Set<InstClause> computeEMatchingInstances() {
		final Set<InstClause> newInstances = new LinkedHashSet<>();

		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		outer: for (final QuantClause clause : currentQuantClauses) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return Collections.emptySet();
			}
			if (clause.hasTrueGroundLits()) {
				continue;
			}

			// Intersect the literal dawgs to find out for which substitutions all triggers were matched.
			Dawg<Term, InstantiationInfo> clauseDawg = Dawg.createConst(clause.getVars().length,
					new InstantiationInfo(InstanceValue.FALSE, new ArrayList<>()));
			for (final QuantLiteral lit : clause.getQuantLits()) {
				if (mQuantTheory.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				Dawg<Term, InstantiationInfo> instDawg = null;
				final QuantLiteral atom = lit.getAtom();
				if (mEMatching.isUsingEmatching(lit) || mEMatching.isPartiallyUsingEmatching(lit)) {
					if (mQuantTheory.mPropagateNewAux && atom instanceof QuantEquality) {
						// If this option is set, don't treat aux-terms as new terms.
						// TODO: Rename the option
						final Term lhs = ((QuantEquality) atom).getLhs();
						if (QuantUtil.isAuxApplication(lhs)) {
							instDawg = Dawg.createConst(clause.getVars().length,
									new InstantiationInfo(InstanceValue.ONE_UNDEF, new ArrayList<>()));
						}
					}
					if (instDawg == null) {
						final Dawg<Term, SubstitutionInfo> subsDawg = mEMatching.getSubstitutionInfos(atom);
						// Map keys to representative, and map non-empty SubstitutionInfo to one_undef
						final Dawg<Term, SubstitutionInfo> representativeSubsDawg = getRepresentativeSubsDawg(subsDawg);
						instDawg = representativeSubsDawg.map(v -> v.equals(mEMatching.getEmptySubs()) && !QuantUtil.isVarEq(lit.getAtom())
								? new InstantiationInfo(InstanceValue.IRRELEVANT, new ArrayList<>())
										: new InstantiationInfo(InstanceValue.ONE_UNDEF,
												getTermSubsFromSubsInfo(lit, v)));
					}
				} else if (lit.mIsArithmetical) {
					instDawg = Dawg.createConst(clause.getVars().length,
							new InstantiationInfo(InstanceValue.ONE_UNDEF, new ArrayList<>()));
				}
				// TODO Should we do something for the other literals, similar to "otherlits" in computeClauseDawg for
				// E-matching based conflict and unit search?

				if (instDawg == null) {
					// No substitution found for this clause literal
					continue outer;
				}
				// NOTE: For lazy E-matching, combineForCheckpoint also works for final check TODO rename it
				clauseDawg = clauseDawg.combine(instDawg, (v1, v2) -> combineForCheckpoint(v1, v2));
			}
			// Compute instances that do not produce new terms, i.e., where the E-matching multi-pattern was matched
			for (final InstantiationInfo subs : getRelevantSubsFromDawg(clause, clauseDawg)) {
				if (mQuantTheory.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				final InstClause inst = computeClauseInstance(clause, subs.getSubs(), InstanceOrigin.EMATCHING);
				if (inst != null) {
					newInstances.add(inst);
				}
			}
		}
		return newInstances;
	}

	/**
	 * Map the given substitution dawg to a substitution dawg using only the representative terms as keys.
	 */
	private Dawg<Term, SubstitutionInfo> getRepresentativeSubsDawg(final Dawg<Term, SubstitutionInfo> dawg) {
		return dawg.mapKeys(l -> mQuantTheory.getRepresentativeTerm(l), (v1, v2) -> mapToFirstChecked(v1, v2));
	}

	/**
	 * In the final check, check if all interesting substitutions of all clauses lead to satisfied instances. As soon as
	 * an instance is found that is not yet satisfied, stop. The newly created literals will be decided by the ground
	 * theories next and may lead to new conflicts.
	 *
	 * @return a singleton set containing the new instance, if one was found; null else.
	 */
	public Set<InstClause> instantiateSomeNotSat() {

		// Collect the QuantClauses that are not yet satisfied and check if existing instances lead to conflicts.
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		for (final QuantClause clause : mQuantTheory.getQuantClauses()) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return Collections.emptySet();
			}
			if (!clause.hasTrueGroundLits()) {
				assert mClauseInstances.containsKey(clause);
				for (final Entry<List<Term>, InstClause> existingInst : mClauseInstances.get(clause).entrySet()) {
					final InstClause instClause = existingInst.getValue();
					if (instClause != null) {
						final int numUndef = instClause.countAndSetUndefLits();
						assert numUndef == -1 || numUndef == 0;
						if (numUndef == 0) {
							mQuantTheory.getLogger().info(
									"Conflict on existing clause instance hasn't been detected in checkpoint(): ",
									instClause);
							return Collections.singleton(instClause);
						}
					}
				}
				currentQuantClauses.add(clause);
			}
		}

		// Check all interesting substitutions ordered by age to avoid creating new (in particular nested) terms early.
		final Map<QuantClause, List<Term>[]> interestingTermsSortedByAge = new HashMap<>();
		int oldest = 0;
		for (final QuantClause clause : currentQuantClauses) {
			if (mClausifier.getEngine().isTerminationRequested()) {
				return null;
			}
			clause.updateInterestingTermsAllVars();
			final Pair<List<Term>[], Integer> termsSortedByAge =
					sortInterestingTermsByAge(clause.getInterestingTerms());
			oldest = Math.max(oldest, termsSortedByAge.getSecond());
			interestingTermsSortedByAge.put(clause, termsSortedByAge.getFirst());
		}
		mQuantTheory.getLogger().debug("Quant: Max term age %d", oldest);
		for (; mSubsAgeForFinalCheck <= oldest; mSubsAgeForFinalCheck++) {
			mQuantTheory.getLogger().debug("Searching for instances of age %d", mSubsAgeForFinalCheck);
			if (mClausifier.getEngine().isTerminationRequested()) {
				return null;
			}

			final List<Pair<QuantClause, List<Term>>> otherValueInstancesOnKnownTerms = new ArrayList<>();
			final List<Pair<QuantClause, List<Term>>> unitValueInstancesNewTerms = new ArrayList<>();
			final List<Pair<QuantClause, List<Term>>> otherValueInstancesNewTerms = new ArrayList<>();

			for (final QuantClause clause : currentQuantClauses) {
				if (mQuantTheory.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				final Set<List<Term>> subsForAge =
						computeSubstitutionsForAge(interestingTermsSortedByAge.get(clause), mSubsAgeForFinalCheck);
				for (final List<Term> subs : subsForAge) {
					assert getMaxAge(subs) == mSubsAgeForFinalCheck;
					if (mClausifier.getEngine().isTerminationRequested()) {
						return null;
					}
					if (mClauseInstances.containsKey(clause) && mClauseInstances.get(clause).containsKey(subs)) {
						continue; // Checked in the first loop over the quant clauses.
					}
					final Pair<InstanceValue, Boolean> candVal = evaluateNewClauseInstanceFinalCheck(clause, subs);
					if (candVal.getFirst() == InstanceValue.TRUE) {
						continue;
					} else if (candVal.getFirst() == InstanceValue.FALSE
							|| candVal.getFirst() == InstanceValue.ONE_UNDEF) {
						// Always build conflict or unit clauses on known terms
						assert candVal.getSecond().booleanValue();
						final InstClause unitClause = computeClauseInstance(clause, subs, InstanceOrigin.ENUMERATION);
						if (unitClause != null) { // TODO Some true literals are not detected at the moment.
							final int numUndef = unitClause.countAndSetUndefLits();
							if (numUndef >= 0) {
								assert !Config.EXPENSIVE_ASSERTS || getMaxAge(subs) == mSubsAgeForFinalCheck;
								mQuantTheory.getLogger().debug("Found inst of age %d", mSubsAgeForFinalCheck);
								return Collections.singleton(unitClause);
							}
						}
					} else {
						final Pair<QuantClause, List<Term>> clauseSubsPair = new Pair<>(clause, subs);
						if (candVal.getFirst() == InstanceValue.UNKNOWN_TERM) {
							assert !candVal.getSecond().booleanValue();
							unitValueInstancesNewTerms.add(clauseSubsPair);
						} else {
							assert candVal.getFirst() == InstanceValue.OTHER;
							if (candVal.getSecond().booleanValue()) {
								otherValueInstancesOnKnownTerms.add(clauseSubsPair);
							} else {
								otherValueInstancesNewTerms.add(clauseSubsPair);
							}
						}
					}
				}
			}
			// If we haven't found a conflict or unit instance on known terms, first check other non-sat instances on
			// known terms, then unit instances producing new terms, then other non-sat instances on new terms.
			final List<Pair<QuantClause, List<Term>>> sortedInstances = new ArrayList<>();
			sortedInstances.addAll(unitValueInstancesNewTerms);
			sortedInstances.addAll(otherValueInstancesOnKnownTerms);
			sortedInstances.addAll(otherValueInstancesNewTerms);
			for (final Pair<QuantClause, List<Term>> cand : sortedInstances) {
				if (mQuantTheory.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				final InstClause inst =
						computeClauseInstance(cand.getFirst(), cand.getSecond(), InstanceOrigin.ENUMERATION);
				if (inst != null) {
					final int numUndef = inst.countAndSetUndefLits();
					if (numUndef >= 0) {
						assert !Config.EXPENSIVE_ASSERTS || getMaxAge(cand.getSecond()) == mSubsAgeForFinalCheck;
						mQuantTheory.getLogger().debug("Found inst of age %d", mSubsAgeForFinalCheck);
						return Collections.singleton(inst);
					}
				}
			}
		}
		return null;
	}

	@SuppressWarnings("unchecked")
	private Pair<List<Term>[], Integer> sortInterestingTermsByAge(final Map<Term, Term>[] interestingTermsForClause) {
		final List<Term>[] sortedTerms = new ArrayList[interestingTermsForClause.length];
		int oldest = 0;
		for (int i = 0; i < sortedTerms.length; i++) {
			sortedTerms[i] = sortInterestingTermsByAge(interestingTermsForClause[i].values());
			assert !sortedTerms[i].isEmpty();
			oldest = Math.max(oldest, getTermAge(sortedTerms[i].get(sortedTerms[i].size() - 1)));
		}
		return new Pair<>(sortedTerms, oldest);
	}

	private List<Term> sortInterestingTermsByAge(final Collection<Term> terms) {
		final List<Term> termList = new ArrayList<>();
		termList.addAll(terms);
		Collections.sort(termList, new Comparator<Term>() {
			@Override
			public int compare(final Term t1, final Term t2) {
				return getTermAge(t1) - getTermAge(t2);
			}
		});
		return termList;
	}

	/**
	 * From the given terms, compute all substitutions from the given age, i.e., that contain at least one term from the
	 * given age, and only terms from the given or an earlier age.
	 *
	 * @param sortedSubstitutionTerms
	 *            an array of lists of substitution terms sorted by age (an array entry corresponds to a variable
	 *            position)
	 * @param age
	 *            the term generation that the substitutions to compute should be from
	 * @return all substitutions resulting from the given terms from the given age.
	 */
	private Set<List<Term>> computeSubstitutionsForAge(final List<Term>[] sortedSubstitutionTerms, final int age) {
		final int length = sortedSubstitutionTerms.length;
		final Map<List<Term>, Integer> allSubs = new LinkedHashMap<>();
		allSubs.put(new ArrayList<Term>(length), 0);
		for (int i = 0; i < length; i++) {
			assert !sortedSubstitutionTerms[i].isEmpty();
			assert !Config.EXPENSIVE_ASSERTS
					|| sortedSubstitutionTerms[i].equals(sortInterestingTermsByAge(sortedSubstitutionTerms[i]));
			final Map<List<Term>, Integer> partialSubs = new LinkedHashMap<>();
			for (final Entry<List<Term>, Integer> oldSub : allSubs.entrySet()) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				final int oldSubAge = oldSub.getValue();
				for (final Term ground : sortedSubstitutionTerms[i]) {
					final int groundAge = getTermAge(ground);
					if (groundAge > age) {
						break;
					}
					if (i != length - 1 || oldSubAge == age || groundAge == age) {
						final List<Term> newSub = new ArrayList<>(length);
						newSub.addAll(oldSub.getKey());
						newSub.add(ground);
						final int newAge = oldSub.getValue() > groundAge ? oldSub.getValue() : groundAge;
						partialSubs.put(newSub, newAge);
					}
				}
			}
			allSubs.clear();
			allSubs.putAll(partialSubs);
		}
		return allSubs.keySet();
	}

	/**
	 * Get the term age for a given term.
	 *
	 * @param t
	 *            a term.
	 * @return the age of the CCTerm if the term has a CCTerm, 0 else.
	 */
	private int getTermAge(final Term t) {
		final CCTerm cc = mClausifier.getCCTerm(t);
		return cc != null ? cc.getAge() : 0;
	}

	/**
	 * Get the maximum term age for the given terms.
	 *
	 * @param terms
	 *            a list of terms.
	 * @return the maximum age of the given terms.
	 */
	private int getMaxAge(final List<Term> terms) {
		int age = 0;
		for (final Term t : terms) {
			age = Math.max(age, getTermAge(t));
		}
		return age;
	}

	/**
	 * Compute a clause dawg.
	 *
	 * @param qClause
	 *            the quantified clause.
	 * @return the dawg that contains the evaluations of different potential instances.
	 */
	private Dawg<Term, InstantiationInfo> computeClauseDawg(final QuantClause qClause) {
		final int numVars = qClause.getVars().length;
		final List<Term> emptySubs = new ArrayList<>();
		final Dawg<Term, InstantiationInfo> constIrrelDawg =
				Dawg.createConst(qClause.getVars().length,
						new InstantiationInfo(InstanceValue.IRRELEVANT, emptySubs));

		// Initialize clause value to false for correct combination.
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first
		for (final Literal groundLit : qClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.TRUE);
			} else if (groundLit.getAtom().getDecideStatus() == groundLit.negate()) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.FALSE);
			} else {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.ONE_UNDEF);
			}
			if (clauseValue == InstanceValue.IRRELEVANT) {
				break;
			}
		}

		// Create the partial clause dawg.
		Dawg<Term, InstantiationInfo> clauseDawg =
				Dawg.createConst(numVars, new InstantiationInfo(clauseValue, emptySubs));

		// Only check quant literals for clauses where all or all but one ground literals are false.
		if (clauseValue != InstanceValue.IRRELEVANT) {
			final BiFunction<InstantiationInfo, InstantiationInfo, InstantiationInfo> combinator =
					(v1, v2) -> combineForCheckpoint(v1, v2);
			final Collection<QuantLiteral> unknownLits = new ArrayList<>(qClause.getQuantLits().length);
			final Collection<QuantLiteral> arithLits = new ArrayList<>(qClause.getQuantLits().length);
			final Collection<QuantLiteral> partialEMLits = new ArrayList<>(qClause.getQuantLits().length);
			// First update and combine the literals that are not arithmetical
			for (final QuantLiteral qLit : qClause.getQuantLits()) {
				if (clauseDawg == constIrrelDawg || mQuantTheory.getEngine().isTerminationRequested()) {
					return constIrrelDawg;
				}
				if (qLit.isArithmetical()) { // will be treated later
					arithLits.add(qLit);
				} else if (mEMatching.isUsingEmatching(qLit)) {
					final Dawg<Term, InstantiationInfo> litDawg = computeEMatchingLitDawg(qLit);
					clauseDawg = clauseDawg.combine(litDawg, combinator);
				} else if (mEMatching.isPartiallyUsingEmatching(qLit)) {
					partialEMLits.add(qLit);
				} else {
					unknownLits.add(qLit);
				}
			}

			if (clauseDawg != constIrrelDawg && !partialEMLits.isEmpty()) {
				for (final QuantLiteral lit : partialEMLits) {
					if (clauseDawg == constIrrelDawg || mQuantTheory.getEngine().isTerminationRequested()) {
						return constIrrelDawg;
					}
					final Dawg<Term, SubstitutionInfo> info = mEMatching.getSubstitutionInfos(lit.getAtom());
					final Dawg<Term, SubstitutionInfo> rep = getRepresentativeSubsDawg(info);

					clauseDawg = clauseDawg.combine(rep,
							(v1, v2) -> combineForCheckpoint(v1, evaluateLitForPartialEMatchingSubsInfo(lit, v1, v2)));
				}
					}
			if (clauseDawg != constIrrelDawg && !unknownLits.isEmpty()) {
				// Consider all substitutions where the partial clause Dawg is not already true
				for (final QuantLiteral lit : unknownLits) {
					if (clauseDawg == constIrrelDawg || mQuantTheory.getEngine().isTerminationRequested()) {
						return constIrrelDawg;
					}
					clauseDawg = clauseDawg.mapWithKey((key, value) -> (combineForCheckpoint(value,
							new InstantiationInfo(evaluateLitInstance(lit, key), value.getSubs()))));
				}
					}
			if (clauseDawg != constIrrelDawg && !arithLits.isEmpty()) {
				// Compute relevant terms from dawg and from bounds for arithmetical literals, update and combine dawgs.
				final Term[][] interestingSubsForArith = computeSubsForArithmetical(qClause, arithLits, clauseDawg);
				// Consider all substitutions where the partial clause Dawg is not already true
				for (final QuantLiteral arLit : arithLits) {
					if (clauseDawg == constIrrelDawg || mQuantTheory.getEngine().isTerminationRequested()) {
						return constIrrelDawg;
					}
					final Dawg<Term, InstantiationInfo> litDawg = computeArithLitDawg(arLit, interestingSubsForArith);
					clauseDawg = clauseDawg.combine(litDawg, combinator);
				}
					}
		}
		return clauseDawg;
	}

	/**
	 * Combine two InstanceValue keeping only the values defined relevant for the checkpoint.
	 *
	 * @param first
	 *            the first InstanceValue
	 * @param second
	 *            the second InstanceValue
	 * @return the combined InstanceValue if it is among the relevant values for checkpoint, irrelevant else.
	 */
	private InstanceValue combineForCheckpoint(final InstanceValue first, final InstanceValue second) {
		return first.combine(second).keepOnlyRelevant(mRelevantValuesForCheckpoint);
	}

	/**
	 * Combine two InstantiationInfo for the checkpoint. The values are combined as usual in checkpoint, and the
	 * (partial) substitutions are combined by preferring the term of the first substitution if both have a term for a
	 * variable (in this case, they must have the same representative).
	 *
	 * @param first
	 *            the first InstantiationInfo
	 * @param second
	 *            the second InstantiationInfo
	 * @return the combined InstantiationInfo if their combined value is among the relevant values for checkpoint, an
	 *         InstantiationInfo with empty substitution else.
	 */
	private InstantiationInfo combineForCheckpoint(final InstantiationInfo first, final InstantiationInfo second) {
		final InstanceValue combinedValue = combineForCheckpoint(first.getInstValue(), second.getInstValue());
		if (combinedValue == InstanceValue.IRRELEVANT) {
			return new InstantiationInfo(combinedValue, new ArrayList<>());
		}
		final List<Term> combinedSubs = combineSubs(first.getSubs(), second.getSubs());
		return new InstantiationInfo(combinedValue, combinedSubs);
	}

	private List<Term> combineSubs(final List<Term> firstSubs, final List<Term> secondSubs) {
		assert firstSubs.isEmpty() || secondSubs.isEmpty() || firstSubs.size() == secondSubs.size();
		final List<Term> combinedSubs = new ArrayList<>();
		if (firstSubs.isEmpty()) {
			combinedSubs.addAll(secondSubs);
		} else if (secondSubs.isEmpty()) {
			combinedSubs.addAll(firstSubs);
		} else {
			for (int i = 0; i < firstSubs.size(); i++) {
				if (firstSubs.get(i) == null) {
					combinedSubs.add(secondSubs.get(i));
				} else {
					assert secondSubs.get(i) == null || !Config.EXPENSIVE_ASSERTS
							|| mQuantTheory.getRepresentativeTerm(firstSubs.get(i)) == mQuantTheory
									.getRepresentativeTerm(secondSubs.get(i));
					combinedSubs.add(firstSubs.get(i));
				}
			}
		}
		return combinedSubs;
	}

	private boolean isUsedValueForCheckpoint(final InstanceValue value) {
		if (value == InstanceValue.IRRELEVANT) {
			return true;
		}
		for (final InstanceValue relVal : mRelevantValuesForCheckpoint) {
			if (value == relVal) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Compute the evaluation dawg for a given literal handled by E-matching.
	 *
	 * @param qLit
	 *            a quantified literal that is handled by E-matching.
	 * @return the evaluation dawg for the literal, of depth |clausevars|.
	 */
	private Dawg<Term, InstantiationInfo> computeEMatchingLitDawg(final QuantLiteral qLit) {
		assert mEMatching.isUsingEmatching(qLit);
		final Dawg<Term, SubstitutionInfo> atomSubsDawg = mEMatching.getSubstitutionInfos(qLit.getAtom());
		// First map keys to representative
		final Dawg<Term, SubstitutionInfo> representativeSubsDawg = getRepresentativeSubsDawg(atomSubsDawg);
		// Then evaluate
		final Function<SubstitutionInfo, InstantiationInfo> evaluationMap =
				v1 -> new InstantiationInfo(evaluateLitForEMatchingSubsInfo(qLit, v1),
						getTermSubsFromSubsInfo(qLit, v1));
		return representativeSubsDawg.map(evaluationMap);
	}

	private SubstitutionInfo mapToFirstChecked(final SubstitutionInfo first, final SubstitutionInfo second) {
		if (Config.EXPENSIVE_ASSERTS) {
			assert first.getEquivalentCCTerms().keySet().equals(second.getEquivalentCCTerms().keySet());
			for (final Entry<Term, CCTerm> equi : first.getEquivalentCCTerms().entrySet()) {
				assert first.getEquivalentCCTerms().get(equi.getKey()).getRepresentative() == second
						.getEquivalentCCTerms().get(equi.getKey()).getRepresentative();
			}
		}
		return first;
	}

	private List<Term> getTermSubsFromSubsInfo(final QuantLiteral qLit, final SubstitutionInfo info) {
		final int length = qLit.getClause().getVars().length;
		final List<Term> termSubs = new ArrayList<>();
		if (!info.equals(mEMatching.getEmptySubs())) {
			final List<CCTerm> ccSubs = info.getVarSubs();
			assert ccSubs.size() == length;
			for (int i = 0; i < length; i++) {
				final CCTerm ccTerm = ccSubs.get(i);
				termSubs.add(ccTerm == null ? null : ccTerm.getFlatTerm());
			}
		}
		return termSubs;
	}

	/**
	 * Evaluate a literal for a given SubstitutionInfo.
	 *
	 * @param qLit
	 *            a quantified literal.
	 * @param info
	 *            the substitution info, containing variable substitutions and equivalent CCTerms for EU terms in the
	 *            literal.
	 * @return the InstanceValue of the literal for the substitution.
	 */
	private InstanceValue evaluateLitForEMatchingSubsInfo(final QuantLiteral qLit, final SubstitutionInfo info) {
		final QuantLiteral qAtom = qLit.getAtom();
		if (info.equals(mEMatching.getEmptySubs())) {
			if (mQuantTheory.mPropagateNewAux && !mQuantTheory.mPropagateNewTerms && qAtom instanceof QuantEquality) {
				if (QuantUtil.isAuxApplication(((QuantEquality) qAtom).getLhs())) {
					return InstanceValue.ONE_UNDEF;
				}
			}
			return mDefaultValueForLitDawgs;
		}

		InstanceValue val;
		if (qAtom instanceof QuantBoundConstraint) {
			final Map<Term, Term> sharedForQuantSmds = buildSharedMapFromCCMap(info.getEquivalentCCTerms());
			val = evaluateBoundConstraintKnownShared((QuantBoundConstraint) qAtom, sharedForQuantSmds);
		} else {
			// First try if we can get an equality value in CC.
			final QuantEquality qEq = (QuantEquality) qAtom;
			val = evaluateCCEqualityKnownShared(qEq, info.getEquivalentCCTerms());

			// If the eq value is unknown in CC, and the terms are numeric, check for equality in LinAr.
			if ((val == InstanceValue.ONE_UNDEF || val == InstanceValue.UNKNOWN_TERM)
					&& qEq.getLhs().getSort().isNumericSort()) {
				final Map<Term, Term> sharedForQuantSmds = buildSharedMapFromCCMap(info.getEquivalentCCTerms());
				val = evaluateLAEqualityKnownShared(qEq, sharedForQuantSmds);
			}
		}

		if (qLit.isNegated()) {
			val = val.negate();
		}
		return val;
	}

	/**
	 * Evaluate a literal that partially uses E-Matching. That is, it contains arithmetic only on top level and there
	 * are variables that do not appear under an uninterpreted function. E.g. for f(x)=y or f(x)+y<=0, E-Matching only
	 * uses the pattern f(x), but the literal can be evaluated for any substitution of y.
	 *
	 * @param lit
	 *            the quantified literal to evaluate.
	 * @param subs
	 *            the variable substitution.
	 * @param info
	 *            the substitution info found by E-matching.
	 * @return the value of the literal under the given substitution.
	 */
	private InstantiationInfo evaluateLitForPartialEMatchingSubsInfo(final QuantLiteral lit,
			final InstantiationInfo clauseInstInfo, final SubstitutionInfo litSubsInfo) {
		InstanceValue val = mDefaultValueForLitDawgs;
		final TermVariable[] clauseVars = lit.getClause().getVars();
		final List<Term> clauseVarSubs = clauseInstInfo.getSubs();
		if (clauseInstInfo.getInstValue() != InstanceValue.IRRELEVANT && !clauseVarSubs.isEmpty()) {
			// Complete the equivalent term map from info by adding the variable substitution from the key
			final Map<Term, CCTerm> equivalentTerms = new HashMap<>();
			equivalentTerms.putAll(litSubsInfo.getEquivalentCCTerms());
			for (int i = 0; i < clauseVars.length; i++) {
				final CCTerm clauseSubs = mClausifier.getCCTerm(clauseVarSubs.get(i));
				if (clauseSubs != null) {
					final CCTerm litSubs =
							litSubsInfo.equals(mEMatching.getEmptySubs()) ? null : litSubsInfo.getVarSubs().get(i);
					if (litSubs != null) { // If the substitutionInfo has a substitution for the variable, keep it.
						assert litSubs.getRepresentative().equals(clauseSubs.getRepresentative());
					} else { // Use the subs from the clause.
						equivalentTerms.put(clauseVars[i], clauseSubs);
					}
				}
			}
			// Evaluate
			final QuantLiteral atom = lit.getAtom();
			if (atom instanceof QuantBoundConstraint) {
				final Map<Term, Term> sharedForQuantSmds = buildSharedMapFromCCMap(equivalentTerms);
				val = evaluateBoundConstraintKnownShared((QuantBoundConstraint) atom, sharedForQuantSmds);
			} else {
				// First try if we can get an equality value in CC.
				final QuantEquality qEq = (QuantEquality) atom;
				val = evaluateCCEqualityKnownShared(qEq, equivalentTerms);

				// If the eq value is unknown in CC, and the terms are numeric, check for equality in LinAr.
				if ((val == InstanceValue.ONE_UNDEF || val == InstanceValue.UNKNOWN_TERM)
						&& qEq.getLhs().getSort().isNumericSort()) {
					final Map<Term, Term> sharedForQuantSmds = buildSharedMapFromCCMap(equivalentTerms);
					val = evaluateLAEqualityKnownShared(qEq, sharedForQuantSmds);
				}
			}
			if (lit.isNegated()) {
				val = val.negate();
			}
		}
		return new InstantiationInfo(val,
				val == InstanceValue.IRRELEVANT ? new ArrayList<>() : getTermSubsFromSubsInfo(lit, litSubsInfo));
	}

	/**
	 * Evaluate a literal for a given substitution.
	 *
	 * @param quantLit
	 *            a quantified literal.
	 * @param substitution
	 *            a term substitution for the variables in quantLit
	 * @return the InstanceValue of the literal for the substitution.
	 */
	private InstanceValue evaluateLitInstance(final QuantLiteral quantLit, final List<Term> substitution) {
		InstanceValue litValue = mDefaultValueForLitDawgs;
		final boolean isNeg = quantLit.isNegated();
		final QuantLiteral atom = quantLit.getAtom();
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			litValue = evaluateCCEquality(eq, substitution);
			if ((litValue == InstanceValue.ONE_UNDEF || litValue == InstanceValue.UNKNOWN_TERM) && eq.getLhs().getSort().isNumericSort()) {
				litValue = evaluateLAEquality(eq, substitution);
			}
		} else {
			litValue = evaluateBoundConstraint((QuantBoundConstraint) atom, substitution);
		}

		if (isNeg) {
			litValue = litValue.negate();
		}
		return litValue;
	}

	/**
	 * Compute the literal evaluation dawg for arithmetical literals.
	 *
	 * @param arLit
	 *            the arithmetical literal.
	 * @param interestingSubs
	 *            the potentially interesting substitutions for the variables in the clause.
	 * @return am evaluation dawg for the literal, its depth corresponds to the number of variables in the clause.
	 */
	private Dawg<Term, InstantiationInfo> computeArithLitDawg(final QuantLiteral arLit,
			final Term[][] interestingSubs) {
		final QuantLiteral qAtom = arLit.getAtom();
		final int numVarsInClause = arLit.getClause().getVars().length;
		final TermVariable[] varsInLit = qAtom.getTerm().getFreeVars();
		assert varsInLit.length == 1 || varsInLit.length == 2;

		TermVariable var = varsInLit[0];
		TermVariable otherVar = varsInLit.length == 2 ? varsInLit[1] : null;
		int varPosInClause = arLit.getClause().getVarIndex(varsInLit[0]);
		int firstVarPosInClause = otherVar == null ? varPosInClause : arLit.getClause().getVarIndex(varsInLit[1]);
		// the other variable position must be the smaller one according to the variable order in the clause
		if (otherVar != null && firstVarPosInClause > varPosInClause) {
			final int temp = varPosInClause;
			varPosInClause = firstVarPosInClause;
			firstVarPosInClause = temp;
			final TermVariable tempVar = var;
			var = otherVar;
			otherVar = tempVar;
		}

		final int nOuterLoops = otherVar == null ? 1 : interestingSubs[firstVarPosInClause].length;
		final Map<Term, Dawg<Term, InstantiationInfo>> transitionsFromOtherVar = new LinkedHashMap<>();

		final int remainderDawgLengthForVar = numVarsInClause - varPosInClause - 1;
		Dawg<Term, InstantiationInfo> remainderDawgAllVars = null;

		for (int i = 0; i < nOuterLoops; i++) {
			final Term otherSubs = otherVar != null ? interestingSubs[firstVarPosInClause][i] : null;
			final List<Term> partialSubs = new ArrayList<>();
			for (int j = 0; j < numVarsInClause; j++) {
				partialSubs.add(null);
			}
			partialSubs.set(firstVarPosInClause, otherSubs);

			final Map<Term, Dawg<Term, InstantiationInfo>> transitionsFromVar = new LinkedHashMap<>();
			for (final Term subs : interestingSubs[varPosInClause]) {
				InstanceValue val = InstanceValue.ONE_UNDEF;

				// Build substitution map.
				final Map<Term, Term> subsMap = new HashMap<>();
				subsMap.put(var, subs);
				if (otherVar != null) {
					subsMap.put(otherVar, otherSubs);
				}
				// Evaluate
				if (qAtom instanceof QuantBoundConstraint) {
					val = evaluateBoundConstraintKnownShared((QuantBoundConstraint) qAtom, subsMap);
				} else {
					val = evaluateLAEqualityKnownShared((QuantEquality) qAtom, subsMap);
				}
				if (arLit.isNegated()) {
					val = val.negate();
				}

				final long time = System.nanoTime();
				if (val != mDefaultValueForLitDawgs) {
					partialSubs.set(varPosInClause, subs);
					final Dawg<Term, InstantiationInfo> remainderDawgForVarSub =
							Dawg.createConst(remainderDawgLengthForVar,
									new InstantiationInfo(val, new ArrayList<>(partialSubs)));
					transitionsFromVar.put(subs, remainderDawgForVarSub);
				}
				mQuantTheory.addDawgTime(System.nanoTime() - time);
			}
			final long time = System.nanoTime();
			final Dawg<Term, InstantiationInfo> dawgForVar =
					Dawg.createDawg(transitionsFromVar, Dawg.createConst(remainderDawgLengthForVar,
							new InstantiationInfo(mDefaultValueForLitDawgs, new ArrayList<>())));
			if (otherVar != null) {
				transitionsFromOtherVar.put(otherSubs,
						createAncestorDawg(dawgForVar, varPosInClause - firstVarPosInClause - 1));
			} else {
				remainderDawgAllVars = dawgForVar;
			}
			mQuantTheory.addDawgTime(System.nanoTime() - time);
		}
		final long time = System.nanoTime();
		if (otherVar != null) {
			remainderDawgAllVars = Dawg.createDawg(transitionsFromOtherVar, Dawg.createConst(
					arLit.getClause().getVars().length - firstVarPosInClause - 1,
					new InstantiationInfo(mDefaultValueForLitDawgs, new ArrayList<>())));
		}
		final Dawg<Term, InstantiationInfo> litDawg =
				createAncestorDawg(remainderDawgAllVars, firstVarPosInClause);
		mQuantTheory.addDawgTime(System.nanoTime() - time);
		return litDawg;
	}

	/**
	 * Create an ancestor dawg for a given dawg and a given level. All transitions from the root until the given level
	 * are else-transitions, and the transition at the given level maps to the input dawg.
	 *
	 * @param dawg
	 *            the remainder dawg.
	 * @param level
	 *            the number of levels the new dawg will be deeper than the given dawg.
	 * @return a new dawg with the given dawg as (only) sub-dawg at the given level.
	 */
	private Dawg<Term, InstantiationInfo> createAncestorDawg(final Dawg<Term, InstantiationInfo> dawg,
			final int level) {

		Dawg<Term, InstantiationInfo> prepended = dawg;
		for (int i = 0; i < level; i++) {
			prepended = Dawg.createDawg(Collections.emptyMap(), prepended);
		}
		return prepended;
	}

	/**
	 * Get all substitutions for this clause which evaluate to an InstanceValue other than IRRELEVANT, and which are
	 * complete, i.e., there is a substitution for each variable.
	 *
	 * @param qClause
	 *            the quantified clause.
	 * @param clauseDawg
	 *            the corresponding clause evaluation dawg.
	 * @return the complete variable substitutions for the clause with InstanceValue != IRRELEVANT.
	 */
	private Collection<InstantiationInfo> getRelevantSubsFromDawg(final QuantClause qClause,
			final Dawg<Term, InstantiationInfo> clauseDawg) {
		final Collection<InstantiationInfo> relevantSubs = new ArrayList<>();
		for (final InstantiationInfo info : clauseDawg.values()) {
			if (mQuantTheory.getEngine().isTerminationRequested()) {
				return Collections.emptySet();
			}
			final List<Term> subs = info.getSubs();
			final InstanceValue val = info.getInstValue();
			assert !Config.EXPENSIVE_ASSERTS || isUsedValueForCheckpoint(val);
			if (val != InstanceValue.IRRELEVANT && !subs.isEmpty()) {
				boolean isComplete = true;
				for (int i = 0; i < subs.size(); i++) {
					if (subs.get(i) == null) {
						isComplete = false;
						break;
					}
				}
				if (isComplete) {
					relevantSubs.add(info);
				}
			}
		}
		return relevantSubs;
	}

	/**
	 * Helper method to build a map from Term to Term, given a map from Term to CCTerm.
	 */
	private Map<Term, Term> buildSharedMapFromCCMap(final Map<Term, CCTerm> ccMap) {
		final Map<Term, Term> sharedMap = new HashMap<>();
		for (final Entry<Term, CCTerm> entry : ccMap.entrySet()) {
			final CCTerm ccTerm = entry.getValue();
			final Term term = ccTerm.getFlatTerm();
			sharedMap.put(entry.getKey(), term);
		}
		return sharedMap;
	}

	/**
	 * Build a MutableAffineTerm from an SMTAffineTerm that may contain quantifiers, using a map that contains
	 * equivalent terms for the quantified summands.
	 *
	 * @param smtAff
	 *            an SMTAffineTerm including quantified terms.
	 * @param sharedForQuantSmds
	 *            the equivalent shared terms for the quantified summands.
	 * @return a MutableAffineTerm if each summand of the SMTAffineTerm either is ground or has an equivalent Term
	 *         storing a LinVar, null otherwise.
	 */
	private MutableAffineTerm buildMutableAffineTerm(final SMTAffineTerm smtAff,
			final Map<Term, Term> sharedForQuantSmds) {
		final MutableAffineTerm at = new MutableAffineTerm();
		for (final Entry<Term, Rational> entry : smtAff.getSummands().entrySet()) {
			final Term sharedTerm;
			if (entry.getKey().getFreeVars().length == 0) {
				sharedTerm = entry.getKey();
			} else {
				sharedTerm = sharedForQuantSmds.get(entry.getKey());
				if (sharedTerm == null) {
					return null;
				}
			}
			final LASharedTerm laTerm = mClausifier.getLATerm(sharedTerm);
			final Rational coeff = entry.getValue();
			if (laTerm != null) {
				for (final Map.Entry<LinVar, Rational> summand : laTerm.getSummands().entrySet()) {
					at.add(coeff.mul(summand.getValue()), summand.getKey());
				}
				at.add(coeff.mul(laTerm.getOffset()));
			} else {
				return null;
			}
		}
		at.add(smtAff.getConstant());
		return at;
	}

	/**
	 * Compute the substitutions for an arithmetical literal from a partial clause dawg, and from the bounds on the
	 * variables.
	 *
	 * @param clause
	 *            the clause containing the arithmetical literals.
	 * @param arLits
	 *            the arithmetical literals in the clause.
	 * @param clauseDawg
	 *            the partial clause dawg containing information for all literals but the arithmetical ones.
	 * @return for each variable in the clause, the interesting substitutions.
	 */
	@SuppressWarnings("unchecked")
	private Term[][] computeSubsForArithmetical(final QuantClause clause, final Collection<QuantLiteral> arLits,
			final Dawg<Term, InstantiationInfo> clauseDawg) {
		// TODO Rework this method

		// Collect all variables occurring in arithmetical literals, i.e., check which of them have any lower or upper
		// bounds
		final TermVariable[] clauseVars = clause.getVars();
		final int nClauseVars = clauseVars.length;
		final TermVariable[] clauseVarsInArLits = new TermVariable[nClauseVars];
		for (int i = 0; i < nClauseVars; i++) {
			final TermVariable var = clauseVars[i];
			if (!clause.getGroundBounds(var).isEmpty() || !clause.getVarBounds(var).isEmpty()) {
				clauseVarsInArLits[i] = var;
			}
		}

		// TODO Make sure that only representatives are added, similar to addAllInteresting
		final Set<Term>[] interestingTerms = new LinkedHashSet[nClauseVars];
		// All ground bounds are interesting terms
		for (int i = 0; i < nClauseVars; i++) {
			interestingTerms[i] = new LinkedHashSet<>();
			if (clauseVarsInArLits[i] != null) {
				interestingTerms[i].addAll(clause.getGroundBounds(clauseVarsInArLits[i]));
			}
		}
		// The substitutions for which the partial clause instance value is not yet true are interesting
		for (final Dawg.Entry<Term, InstantiationInfo> entry : clauseDawg.entrySet()) {
			if (entry.getValue().getInstValue() != InstanceValue.IRRELEVANT) {
				for (int i = 0; i < nClauseVars; i++) {
					if (clauseVarsInArLits[i] != null) {
						interestingTerms[i].add(entry.getKey().get(i));
					}
				}
			}
		}
		// Synchronize sets of variables which depend on another
		// TODO Use one method for this and synchronize... in clause
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i < clauseVarsInArLits.length; i++) {
				final TermVariable var = clauseVarsInArLits[i];
				if (var != null) {
					for (final TermVariable t : clause.getVarBounds(var)) {
						final int j = clause.getVarIndex(t);
						changed = interestingTerms[i].addAll(interestingTerms[j]);
					}
				}
			}
		}

		final Term[][] interestingTermArrays = new Term[nClauseVars][];
		for (int i = 0; i < nClauseVars; i++) {
			interestingTermArrays[i] = interestingTerms[i].toArray(new Term[interestingTerms[i].size()]);
		}
		return interestingTermArrays;
	}

	/**
	 * Compute all interesting substitutions for a given clause.
	 *
	 * This should only be called after updating the interesting terms for the clause.
	 *
	 * @param quantClause
	 *            the quantified clause.
	 * @return a Set containing interesting substitutions for the clause.
	 */
	private Set<List<Term>> computeAllSubstitutions(final QuantClause quantClause) {
		final int nVars = quantClause.getVars().length;
		final Set<List<Term>> allSubs = new LinkedHashSet<>();
		allSubs.add(new ArrayList<Term>(nVars));
		for (int i = 0; i < nVars; i++) {
			final Set<List<Term>> partialSubs = new LinkedHashSet<>();
			for (final List<Term> oldSub : allSubs) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				assert !quantClause.getInterestingTerms()[i].isEmpty();
				for (final Term ground : quantClause.getInterestingTerms()[i].values()) {
					final List<Term> newSub = new ArrayList<>(nVars);
					newSub.addAll(oldSub);
					newSub.add(ground);
					partialSubs.add(newSub);
				}
			}
			allSubs.clear();
			allSubs.addAll(partialSubs);
		}
		return allSubs;
	}

	/**
	 * Evaluate which value a potential instance of a given clause would have.
	 *
	 * @param quantClause
	 *            the quantified clause which we evaluate an instance for.
	 * @param substitution
	 *            the ground substitution producing this instance.
	 * @return the InstanceValue of the potential instance.
	 */
	private InstanceValue evaluateClauseInstance(final QuantClause quantClause, final List<Term> substitution) {
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first.
		for (final Literal groundLit : quantClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return combineForCheckpoint(clauseValue, InstanceValue.TRUE);
			} else if (groundLit.getAtom().getDecideStatus() == null) {
				clauseValue = combineForCheckpoint(clauseValue, InstanceValue.ONE_UNDEF);
			} else {
				assert groundLit.getAtom().getDecideStatus() != groundLit;
			}
		}
		// Only check clauses where all or all but one ground literals are set to false.
		if (clauseValue == InstanceValue.IRRELEVANT) {
			return clauseValue;
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		for (final QuantLiteral quantLit : quantClause.getQuantLits()) {
			final InstanceValue litValue = evaluateLitInstance(quantLit, substitution);
			clauseValue = combineForCheckpoint(clauseValue, litValue);
			if (clauseValue == InstanceValue.IRRELEVANT) {
				return clauseValue;
			}
		}
		return clauseValue;
	}

	/**
	 * Evaluate which value a potential instance of a given clause would have. This method must only be used for new
	 * instances.
	 *
	 * @param quantClause
	 *            the quantified clause which we evaluate an instance for.
	 * @param substitution
	 *            the ground substitution producing this instance.
	 * @return a pair containing the InstanceValue of the potential instance and a Boolean which is true iff the
	 *         instance contains only known terms.
	 */
	private Pair<InstanceValue, Boolean> evaluateNewClauseInstanceFinalCheck(final QuantClause quantClause,
			final List<Term> substitution) {
		assert !mClauseInstances.containsKey(quantClause)
				|| !mClauseInstances.get(quantClause).containsKey(substitution);
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check for true ground literals first.
		for (final Literal groundLit : quantClause.getGroundLits()) {
			assert groundLit.getAtom().getDecideStatus() != null;
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return new Pair<>(InstanceValue.TRUE, null);
			}
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		boolean hasOnlyKnownTerms = true;
		for (final QuantLiteral quantLit : quantClause.getQuantLits()) {
			final InstanceValue litValue = evaluateLitInstance(quantLit, substitution);
			// TODO evaluateLitInstanceFinalCheck
			if (litValue == InstanceValue.UNKNOWN_TERM) {
				hasOnlyKnownTerms = false;
			}
			clauseValue = clauseValue.combine(litValue);
			if (clauseValue == InstanceValue.TRUE) {
				return new Pair<>(clauseValue, null);
			}
		}
		return new Pair<>(clauseValue, hasOnlyKnownTerms);
	}

	/**
	 * Instantiate a clause with a given substitution.
	 *
	 * @param clause
	 *            a clause containing at least one quantified literal.
	 * @param subs
	 *            the substitution terms for the variables in the clause.
	 * @param origin
	 *            the InstanceOrigin determining if the instance was produced in checkpoint or finalcheck
	 *
	 * @return the resulting InstClause, or null if the clause would be trivially true.
	 */
	private InstClause computeClauseInstance(final QuantClause clause, final List<Term> subs,
			final InstanceOrigin origin) {
		assert mClauseInstances.containsKey(clause);
		if (mClauseInstances.get(clause).containsKey(subs)) {
			return mClauseInstances.get(clause).get(subs);
		}

		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		for (int i = 0; i < subs.size(); i++) {
			sigma.put(clause.getVars()[i], subs.get(i));
		}
		final SubstitutionHelper instHelper = new SubstitutionHelper(mQuantTheory, clause.getGroundLits(),
				clause.getQuantLits(), clause.getQuantSource(), sigma);
		final SubstitutionResult result = instHelper.substituteInClause();
		final InstClause inst;
		if (result.isTriviallyTrue()) {
			// return null;
			inst = null;
		} else {
			assert result.isGround();
			mQuantTheory.getLogger().debug("Quant: instantiating quant clause %s results in %s", clause,
					Arrays.asList(result.mGroundLits));
			inst = new InstClause(clause, subs, Arrays.asList(result.mGroundLits), -1, origin, result.mSimplified);
		}
		mClauseInstances.get(clause).put(subs, inst);
		mQuantTheory.mNumInstancesProduced++;
		if (origin.equals(InstanceOrigin.CONFLICT)) {
			mQuantTheory.mNumInstancesProducedConfl++;
		} else if (origin.equals(InstanceOrigin.EMATCHING)) {
			mQuantTheory.mNumInstancesProducedEM++;
		} else if (origin.equals(InstanceOrigin.ENUMERATION)) {
			mQuantTheory.mNumInstancesProducedEnum++;
		}
		recordSubstAgeForStats(getMaxAge(subs), origin.equals(InstanceOrigin.ENUMERATION));
		return inst;
	}

	/**
	 * Determine the value that an equality literal would have in CC for the given substitution.
	 *
	 * @param qEq
	 *            the quantified equality literal.
	 * @param info
	 *            the substitution info containing the known ground terms for the quantified terms in the literal.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateCCEqualityKnownShared(final QuantEquality qEq, final Map<Term, CCTerm> equivalentCCTerms) {
		final CCTerm leftCC, rightCC;
		if (qEq.getLhs().getFreeVars().length == 0) {
			leftCC = mClausifier.getCCTerm(qEq.getLhs());
		} else {
			leftCC = equivalentCCTerms.get(qEq.getLhs());
		}
		if (qEq.getRhs().getFreeVars().length == 0) {
			rightCC = mClausifier.getCCTerm(qEq.getRhs());
		} else {
			rightCC = equivalentCCTerms.get(qEq.getRhs());
		}
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an equality literal would have in CC for the given substitution.
	 *
	 * @param qEq
	 *            the quantified equality literal.
	 * @param subs
	 *            the variable substitution.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateCCEquality(final QuantEquality qEq, final List<Term> subs) {
		final QuantClause qClause = qEq.getClause();
		final TermFinder finder = new TermFinder(qClause.getVars(), subs);
		final Term left = finder.findEquivalentShared(qEq.getLhs());
		final Term right = finder.findEquivalentShared(qEq.getRhs());
		if (left != null && right != null) {
			final CCTerm leftCC = mClausifier.getCCTerm(left);
			final CCTerm rightCC = mClausifier.getCCTerm(right);
			if (leftCC != null && rightCC != null) {
				if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
					return InstanceValue.TRUE;
				} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
					return InstanceValue.FALSE;
				}
			}
			return InstanceValue.ONE_UNDEF;
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an equality literal would have in LA for the given substitution.
	 *
	 * @param qEq
	 *            the quantified equality literal.
	 * @param sharedForQuant
	 *            a map containing the known ground terms for the quantified terms in the literal.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateLAEqualityKnownShared(final QuantEquality qEq, final Map<Term, Term> sharedForQuant) {
		final SMTAffineTerm diff = new SMTAffineTerm(qEq.getLhs());
		diff.add(Rational.MONE, new SMTAffineTerm(qEq.getRhs()));

		final MutableAffineTerm at = buildMutableAffineTerm(diff, sharedForQuant);
		if (at != null) {
			final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			at.negate();
			final InfinitesimalNumber negLowerBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			if (upperBound.signum() == 0 && negLowerBound.signum() == 0) {
				return InstanceValue.TRUE;
			} else if (upperBound.signum() < 0 || negLowerBound.signum() < 0) {
				return InstanceValue.FALSE;
			}
			return InstanceValue.ONE_UNDEF;
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an equality literal would have in LA for the given substitution.
	 *
	 * @param qEq
	 *            the quantified equality literal.
	 * @param subs
	 *            the variable substitution.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateLAEquality(final QuantEquality qEq, final List<Term> subs) {
		final SMTAffineTerm diff = new SMTAffineTerm(qEq.getLhs());
		diff.add(Rational.MONE, qEq.getRhs());

		final QuantClause qClause = qEq.getClause();
		final TermFinder finder = new TermFinder(qClause.getVars(), subs);
		final SMTAffineTerm smtAff = finder.findEquivalentAffine(diff);
		if (smtAff != null) {
			final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			smtAff.negate();
			final InfinitesimalNumber negLowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
			if (upperBound.signum() == 0 && negLowerBound.signum() == 0) {
				return InstanceValue.TRUE;
			} else if (upperBound.signum() < 0 || negLowerBound.signum() < 0) {
				return InstanceValue.FALSE;
			}
			return InstanceValue.ONE_UNDEF;
		}
		return mDefaultValueForLitDawgs;
	}

	/**
	 * Determine the value that an inequality literal would have for the given substitution.
	 *
	 * @param qBc
	 *            the quantified bound constraint.
	 * @param sharedForQuant
	 *            a map containing the known ground terms for the quantified terms in the literal.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateBoundConstraintKnownShared(final QuantBoundConstraint qBc,
			final Map<Term, Term> sharedForQuant) {
		final MutableAffineTerm at =
				buildMutableAffineTerm(qBc.getAffineTerm(), sharedForQuant);
		if (at == null) {
			return mDefaultValueForLitDawgs;
		}
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(at);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else {
			at.negate();
			final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(at);
			if (lowerBound.less(InfinitesimalNumber.ZERO)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
	}

	/**
	 * Determine the value that an inequality literal would have for the given substitution.
	 *
	 * @param qBc
	 *            the quantified bound constraint.
	 * @param subs
	 *            the variable substitution.
	 * @return the InstanceValue of the substituted literal.
	 */
	private InstanceValue evaluateBoundConstraint(final QuantBoundConstraint qBc, final List<Term> subs) {
		final TermFinder finder = new TermFinder(qBc.getClause().getVars(), subs);
		final SMTAffineTerm affine = finder.findEquivalentAffine(qBc.getAffineTerm());
		if (affine == null) {
			return mDefaultValueForLitDawgs;
		}
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, affine);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else {
			affine.negate();
			final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, affine);
			if (lowerBound.less(InfinitesimalNumber.ZERO)) {
				return InstanceValue.FALSE;
			} else {
				return InstanceValue.ONE_UNDEF;
			}
		}
	}

	private void recordSubstAgeForStats(final int age, final boolean isProducedByEnumeration) {
		assert age >= 0;
		final int index = Integer.SIZE - Integer.numberOfLeadingZeros(age);
		mQuantTheory.mNumInstancesOfAge[index]++;
		if (isProducedByEnumeration) {
			mQuantTheory.mNumInstancesOfAgeEnum[index]++;
		}
	}

	/**
	 * This class is used to find an equivalent known term for a given (possibly quantified) term under a given ground
	 * substitution.
	 */
	private class TermFinder extends NonRecursive {
		private final List<TermVariable> mVars;
		private final List<Term> mSubstitution;
		private final Map<Term, Term> mTerms;

		TermFinder(final TermVariable[] vars, final List<Term> substitution) {
			mVars = Arrays.asList(vars);
			mSubstitution = substitution;
			mTerms = new HashMap<>();
		}

		Term findEquivalentShared(final Term term) {
			enqueueWalker(new FindTerm(term));
			run();
			return mTerms.get(term);
		}

		SMTAffineTerm findEquivalentAffine(final SMTAffineTerm smtAff) {
			for (final Term smd : smtAff.getSummands().keySet()) {
				enqueueWalker(new FindTerm(smd));
			}
			run();
			return buildEquivalentAffine(smtAff);
		}

		private SMTAffineTerm buildEquivalentAffine(final SMTAffineTerm smtAff) {
			final SMTAffineTerm instAff = new SMTAffineTerm();
			for (final Entry<Term, Rational> smd : smtAff.getSummands().entrySet()) {
				final Term inst = mTerms.get(smd.getKey());
				if (inst == null) {
					return null;
				}
				instAff.add(smd.getValue(), inst);
			}
			instAff.add(smtAff.getConstant());
			return instAff;
		}

		class FindTerm implements Walker {
			private final Term mTerm;

			public FindTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void walk(final NonRecursive engine) {
				if (!mTerms.containsKey(mTerm)) {
					if (mTerm.getFreeVars().length == 0) {
						mTerms.put(mTerm, mTerm);
					} else if (mTerm instanceof TermVariable) {
						mTerms.put(mTerm, mSubstitution.get(mVars.indexOf(mTerm)));
					} else {
						assert mTerm instanceof ApplicationTerm;
						final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
						final FunctionSymbol func = appTerm.getFunction();
						if (Clausifier.needCCTerm(appTerm)) {
							final Term[] params = appTerm.getParameters();
							enqueueWalker(new FindSharedAppTerm(mTerm, func, params));
							for (final Term arg : params) {
								enqueueWalker(new FindTerm(arg));
							}
						} else if (func.getName() == "+" || func.getName() == "*" || func.getName() == "-") {
							final SMTAffineTerm smtAff = new SMTAffineTerm(mTerm);
							enqueueWalker(new FindSharedAffine(mTerm, smtAff));
							for (final Term smd : smtAff.getSummands().keySet()) {
								enqueueWalker(new FindTerm(smd));
							}
						}
					}
				}
			}
		}

		class FindSharedAppTerm implements Walker {
			private final Term mTerm;
			private final FunctionSymbol mFunc;
			private final Term[] mParams;

			public FindSharedAppTerm(final Term term, final FunctionSymbol func, final Term[] params) {
				mTerm = term;
				mFunc = func;
				mParams = params;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final Term[] instArgs = new Term[mParams.length];
				for (int i = 0; i < mParams.length; i++) {
					final Term sharedArg = mTerms.get(mParams[i]);
					if (sharedArg == null) {
						return;
					} else {
						instArgs[i] = sharedArg;
					}
				}
				final Term instAppTerm = mClausifier.getTheory().term(mFunc, instArgs);
				final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instAppTerm);
				if (ccTermRep != null) {
					mTerms.put(mTerm, ccTermRep.getFlatTerm());
				}
			}
		}

		class FindSharedAffine implements Walker {
			private final Term mTerm;
			private final SMTAffineTerm mSmtAff;

			FindSharedAffine(final Term term, final SMTAffineTerm smtAff) {
				mTerm = term;
				mSmtAff = smtAff;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final SMTAffineTerm instAffine = buildEquivalentAffine(mSmtAff);
				if (instAffine != null) {
					final Term instTerm = instAffine.toTerm(mClausifier.getTermCompiler(), mTerm.getSort());
					// Note: This will often not find a CC term.
					final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instTerm);
					if (ccTermRep != null) {
						mTerms.put(mTerm, ccTermRep.getFlatTerm());
					}
				}
			}
		}
	}

	/**
	 * Container class to store a substitution together with the corresponding instance value.
	 */
	private class InstantiationInfo {
		private final InstanceValue mValue;
		private final List<Term> mSubs;

		private InstantiationInfo(final InstanceValue val, final List<Term> subs) {
			mValue = val;
			mSubs = subs;
		}

		InstanceValue getInstValue() {
			return mValue;
		}

		List<Term> getSubs() {
			return mSubs;
		}

		@Override
		public String toString() {
			return "InstInfo: [" + mValue + mSubs + "]";
		}

		@Override
		public int hashCode() {
			return mSubs.hashCode();
		}

		@Override
		public boolean equals(final Object other) {
			if (other instanceof InstantiationInfo) {
				final InstantiationInfo otherInfo = (InstantiationInfo) other;
				return mValue == otherInfo.getInstValue() && mSubs.equals(otherInfo.getSubs());
			}
			return false;
		}
	}

	/**
	 * For pre-evaluation of QuantLiteral and QuantClause instances, we define the following values: TRUE if at least
	 * one literal evaluates to true, FALSE if all literals evaluate to false, ONE_UNDEF if all but one literal evaluate
	 * to false, and for this one all terms are known but not the value, UNKNOWN similarly but the terms are not known,
	 * OTHER for all other cases. An additional value IRRELEVANT can be used to mark instances that are not useful for a
	 * certain purpose.
	 */
	private enum InstanceValue {
		TRUE, FALSE, ONE_UNDEF, UNKNOWN_TERM, OTHER, IRRELEVANT;

		private InstanceValue combine(final InstanceValue other) {
			if (this == IRRELEVANT || other == IRRELEVANT) {
				return IRRELEVANT;
			} else if (this == TRUE || other == TRUE) {
				return TRUE;
			} else if (this == FALSE) {
				return other;
			} else if (other == FALSE) {
				return this;
			} else {
				return OTHER;
			}
		}

		private InstanceValue negate() {
			if (this == TRUE) {
				return FALSE;
			} else if (this == FALSE) {
				return TRUE;
			} else {
				return this;
			}
		}

		/**
		 * Restrict instance values to the given relevant values plus IRRELEVANT.
		 *
		 * @param values
		 *            the relevant values.
		 * @return the InstanceValue itself, if contained in the relevant values, or IRRELEVANT else.
		 */
		private InstanceValue keepOnlyRelevant(final List<InstanceValue> values) {
			for (final InstanceValue val : values) {
				if (this == val) {
					return this;
				}
			}
			return IRRELEVANT;
		}
	}
}
