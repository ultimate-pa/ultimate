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
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.dawg.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching.EMatching.SubstitutionInfo;

/**
 * This class takes care of clause, literal and term instantiation.
 *
 * Literals and clauses are only created if necessary, in particular, false literals as well as clauses that would
 * contain true literals are not created.
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

	// TODO: Remember old dawgs
	private final Map<QuantLiteral, Dawg<SharedTerm, InstanceValue>> mLitInstanceValues;
	private final Map<QuantClause, Dawg<SharedTerm, InstanceValue>> mClauseInstanceValues;

	public InstantiationManager(Clausifier clausifier, QuantifierTheory quantTheory) {
		mClausifier = clausifier;
		mQuantTheory = quantTheory;
		mEMatching = quantTheory.getEMatching();
		mLitInstanceValues = new HashMap<>();
		mClauseInstanceValues = new HashMap<>();
	}

	/**
	 * Add the clause and literal dawgs for a quant clause.
	 * 
	 * @param qClause
	 *            the quantified clause.
	 */
	public void addDawgs(final QuantClause qClause) {
		assert !mClauseInstanceValues.containsKey(qClause);
		// Initialize clause dawgs to true, meaning we are not interested in them yet.
		mClauseInstanceValues.put(qClause, getDefaultClauseDawg(qClause));
		for (final QuantLiteral qLit : qClause.getQuantLits()) {
			assert !mLitInstanceValues.containsKey(qLit);
			// Initialize lit dawgs to undef, meaning we don't have any information on them yet.
			mLitInstanceValues.put(qLit, getDefaultLiteralDawg(qLit));
		}
	}
	
	/**
	 * Reset the clause dawgs to their default dawgs.
	 * 
	 * This should be used after backtracking.
	 * 
	 * TODO Should we remember the dawgs for each decision level and use them to reset?
	 */
	public void resetDawgs() {
		for (final QuantClause qClause : mClauseInstanceValues.keySet()) {
			mClauseInstanceValues.put(qClause, getDefaultClauseDawg(qClause));
		}
	}

	private Dawg<SharedTerm, InstanceValue> getDefaultClauseDawg(final QuantClause qClause) {
		return Dawg.createConst(qClause.getVars().length, InstanceValue.TRUE);
	}
	
	private Dawg<SharedTerm, InstanceValue> getDefaultLiteralDawg(final QuantLiteral qLit) {
		return Dawg.createConst(qLit.mClause.getVars().length, InstanceValue.ONE_UNDEF);
	}

	/**
	 * Find all current instances of quant clauses that would be conflict or unit instances. This will actually compute
	 * the clause instances, i.e., it will create the ground literals.
	 * 
	 * @return the clause instances.
	 */
	public Set<List<Literal>> findConflictAndUnitInstancesWithNewEMatching() {
		final Set<List<Literal>> conflictAndUnitClauses = new LinkedHashSet<>();

		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());

		for (final QuantClause qClause : currentQuantClauses) {
			if (updateClauseInstanceValues(qClause)) {
				final Collection<Collection<SharedTerm>> conflictOrUnitSubs = getConflictAndUnitSubsFromDawg(qClause);

				if (conflictOrUnitSubs != null) {
					for (final Collection<SharedTerm> subs : conflictOrUnitSubs) {
						final SharedTerm[] subsArr = subs.toArray(new SharedTerm[subs.size()]);
						final Literal[] instLits = computeClauseInstance(qClause, subsArr);
						if (instLits != null) {
							conflictAndUnitClauses.add(Arrays.asList(instLits));
							mQuantTheory.getLogger().debug("Quant: instantiating quant clause %1s results in %2s",
									qClause, Arrays.asList(instLits));
						}
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * Update the clause dawgs.
	 * 
	 * @param qClause
	 * @return true if something changed, false otherwise.
	 */
	private boolean updateClauseInstanceValues(final QuantClause qClause) {
		final Dawg<SharedTerm, InstanceValue> oldDawg = mClauseInstanceValues.get(qClause);

		// Initialize clause value to false for correct combination.
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first
		for (Literal groundLit : qClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				clauseValue = clauseValue.combine(InstanceValue.TRUE);
			} else if (groundLit.getAtom().getDecideStatus() == groundLit.negate()) {
				clauseValue = clauseValue.combine(InstanceValue.FALSE);
			} else {
				clauseValue = clauseValue.combine(InstanceValue.ONE_UNDEF);
			}
			if (clauseValue == InstanceValue.TRUE) {
				break;
			}
		}

		// Create the partial clause dawg.
		final int length = qClause.getVars().length;
		Dawg<SharedTerm, InstanceValue> clauseDawg = Dawg.createConst(length, clauseValue);

		// Only check quant literals for clauses where all or all but one ground literals are false.
		if (!clauseValue.equals(InstanceValue.TRUE)) {
			final BiFunction<InstanceValue, InstanceValue, InstanceValue> combinator = (v1, v2) -> v1.combine(v2);
			final Collection<QuantLiteral> arithLits = new ArrayList<>();
			// First update and combine the literals that are not arithmetical
			for (final QuantLiteral qLit : qClause.getQuantLits()) {
				if (!isConst(clauseDawg, length, InstanceValue.TRUE)) {
					if (qLit.isArithmetical()) { // will be treated later
						arithLits.add(qLit);
					} else {
						if (qLit.isEssentiallyUninterpreted()) {
							updateEULitInstanceValues(qLit);
						}
						clauseDawg = clauseDawg.combine(mLitInstanceValues.get(qLit), combinator);
					}
				}
			}

			// Compute relevant terms from dawg and from bounds for arithmetical literals, update and combine them.
			if (!isConst(clauseDawg, length, InstanceValue.TRUE)) {
				final Map<QuantLiteral, Collection<SharedTerm[]>> interestingSubsForArith =
						computeSubsForArithmetical(qClause, arithLits, clauseDawg);
				for (final QuantLiteral arLit : arithLits) {
					if (!isConst(clauseDawg, length, InstanceValue.TRUE)) {
						updateArithLitInstanceValue(arLit, interestingSubsForArith.get(arLit));
						clauseDawg = clauseDawg.combine(mLitInstanceValues.get(arLit), combinator);
					}
				}
			}
		}
		mClauseInstanceValues.put(qClause, clauseDawg);
		return oldDawg != clauseDawg;
	}

	private boolean isConst(final Dawg<SharedTerm, InstanceValue> dawg, final int length, final InstanceValue value) {
		final Dawg<SharedTerm, InstanceValue> constDawg = Dawg.createConst(length, value);
		return dawg.equals(constDawg);
	}

	private void updateEULitInstanceValues(final QuantLiteral qLit) {
		assert qLit.isEssentiallyUninterpreted(); // Use the information from E-Matching
		final QuantLiteral qAtom = qLit.getAtom();
		final Collection<SubstitutionInfo> infos = mEMatching.getSubstitutionInfos(qAtom);
		final SourceAnnotation source = qLit.mClause.getSource();

		Dawg<SharedTerm, InstanceValue> litDawg = getDefaultLiteralDawg(qLit);
		if (infos != null) {
			for (final SubstitutionInfo info : infos) {
				InstanceValue val = InstanceValue.ONE_UNDEF;

				if (qAtom instanceof QuantBoundConstraint) {
					final QuantBoundConstraint qBc = (QuantBoundConstraint) qAtom;
					final MutableAffineTerm at = buildMutableAffineTerm(qBc.getAffineTerm(), info, source);
					if (at != null) {
						val = evaluateBoundConstraint(at);
					}
				} else {
					final QuantEquality qEq = (QuantEquality) qAtom;

					// First try if we can get an equality value in CC.
					final CCTerm lhs, rhs;
					if (qEq.getLhs().getFreeVars().length == 0) {
						lhs = mClausifier.getSharedTerm(qEq.getLhs(), qLit.mClause.getSource()).getCCTerm();
					} else {
						lhs = info.getEquivalentCCTerms().get(qEq.getLhs());
					}
					if (qEq.getRhs().getFreeVars().length == 0) {
						rhs = mClausifier.getSharedTerm(qEq.getRhs(), qLit.mClause.getSource()).getCCTerm();
					} else {
						rhs = info.getEquivalentCCTerms().get(qEq.getRhs());
					}
					val = evaluateCCEquality(lhs, rhs);

					// If the eq value is unknown in CC, and the terms are numeric, check for equality in
					// LinAr.
					if (val == InstanceValue.ONE_UNDEF && qEq.getLhs().getSort().isNumericSort()) {
						final MutableAffineTerm at =
								buildMutableAffineTerm(new SMTAffineTerm(qEq.getLhs()), info, source);
						if (at != null) {
							final MutableAffineTerm atRight =
									buildMutableAffineTerm(new SMTAffineTerm(qEq.getRhs()), info, source);
							if (atRight != null) {
								at.add(Rational.MONE, atRight);
								val = evaluateLAEquality(at);
							}
						}
					}
				}

				if (qLit.isNegated()) {
					val = val.negate();
				}

				final List<SharedTerm> sharedSubs = new ArrayList<>();
				for (int i = 0; i < info.getVarSubs().length; i++) {
					final CCTerm ccSubs = info.getVarSubs()[i];
					if (ccSubs == null) {
						sharedSubs.add(null); // will result in the default case in the dawg
					} else {
						final SharedTerm shared =
								ccSubs.getSharedTerm() != null ? ccSubs.getSharedTerm() : ccSubs.getFlatTerm();
						assert shared != null;
						sharedSubs.add(shared);
					}
				}
				long time = System.nanoTime();
				litDawg = litDawg.insert(sharedSubs, val);
				mQuantTheory.mDawgTime += System.nanoTime() - time;
			}
		}
		mLitInstanceValues.put(qLit, litDawg);
	}

	private void updateArithLitInstanceValue(final QuantLiteral arLit, final Collection<SharedTerm[]> interestingSubs) {
		final QuantLiteral qAtom = arLit.getAtom();
		final SourceAnnotation source = arLit.mClause.getSource();

		Dawg<SharedTerm, InstanceValue> litDawg = getDefaultLiteralDawg(arLit);
		for (final SharedTerm[] subs : interestingSubs) {
			InstanceValue val = InstanceValue.ONE_UNDEF;

			// Build substitution map. // TODO outsource
			final Map<Term, SharedTerm> subsMap = new HashMap<>();
			for (int i = 0; i < subs.length; i++) {
				if (subs[i] != null) {
					subsMap.put(arLit.mClause.getVars()[i], subs[i]);
				}
			}

			if (qAtom instanceof QuantBoundConstraint) {
				final QuantBoundConstraint qBc = (QuantBoundConstraint) qAtom;
				final MutableAffineTerm at =
						buildMutableAffineTerm(qBc.getAffineTerm(), subsMap, source);
				if (at != null) {
					val = evaluateBoundConstraint(at);
				}
			} else {
				final QuantEquality qEq = (QuantEquality) qAtom;
				assert qEq.getLhs().getSort().isNumericSort();
				final MutableAffineTerm at = buildMutableAffineTerm(new SMTAffineTerm(qEq.getLhs()), subsMap, source);
				if (at != null) {
					final MutableAffineTerm atRight =
							buildMutableAffineTerm(new SMTAffineTerm(qEq.getRhs()), subsMap, source);
					if (atRight != null) {
						at.add(Rational.MONE, atRight);
						val = evaluateLAEquality(at);
					}
				}
			}

			if (arLit.isNegated()) {
				val = val.negate();
			}
			long time = System.nanoTime();
			litDawg = litDawg.insert(Arrays.asList(subs), val);
			mQuantTheory.mDawgTime += System.nanoTime() - time;
		}
		mLitInstanceValues.put(arLit, litDawg);
	}

	/**
	 * Get all substitutions for this clause that result in a conflict or unit clause.
	 * 
	 * @param quantClause
	 * @return
	 */
	private Collection<Collection<SharedTerm>> getConflictAndUnitSubsFromDawg(final QuantClause qClause) {
		final Collection<Collection<SharedTerm>> conflictAndUnitSubs = new ArrayList<>();
		final Dawg<SharedTerm, InstanceValue> clauseDawg = mClauseInstanceValues.get(qClause);
		for (final Dawg.Entry<SharedTerm, InstanceValue> entry : clauseDawg.entrySet()) {
			if (entry.getValue() != InstanceValue.TRUE) {
				// Replace the nulls (standing for the "else" case) with the suitable lambda
				boolean containsLambdas = false;
				final List<SharedTerm> subsWithNulls = entry.getKey();
				final List<SharedTerm> subs = new ArrayList<>();
				for (int i = 0; i < qClause.getVars().length; i++) {
					if (subsWithNulls.get(i) != null) {
						subs.add(subsWithNulls.get(i));
					} else {
						subs.add(mQuantTheory.getLambda(qClause.getVars()[i].getSort()));
						containsLambdas = true;
					}
				}
				assert containsLambdas || clauseDawg.getValue(subs) != InstanceValue.TRUE;
				if (!containsLambdas || (clauseDawg.getValue(subs) != InstanceValue.TRUE)) {
					conflictAndUnitSubs.add(subs);
				}
			}
		}
		return conflictAndUnitSubs;
	}

	/**
	 * Build a MutableAffineTerm from an SMTAffineTerm that may contain quantifiers, using the SubstitutionInfo that was
	 * build for the patterns included in this term.
	 * 
	 * TODO Use only buildMutableAffineTerm(final SMTAffineTerm smtAff, final Map<Term, SharedTerm> sharedForQuantSmds,
	 * SourceAnnotation source) below.
	 * 
	 * @param smtAff
	 *            an SMTAffineTerm including quantified terms.
	 * @param info
	 *            the substitution info that was built for this term.
	 * @return a MutableAffineTerm if each summand of the SMTAffineTerm either is ground or has an equivalent CCTerm for
	 *         the substitution in info, null otherwise.
	 */
	private MutableAffineTerm buildMutableAffineTerm(final SMTAffineTerm smtAff, SubstitutionInfo info,
			SourceAnnotation source) {
		MutableAffineTerm at = new MutableAffineTerm();
		for (Entry<Term, Rational> entry : smtAff.getSummands().entrySet()) {
			final SharedTerm sharedTerm;
			if (entry.getKey().getFreeVars().length == 0) {
				sharedTerm = mClausifier.getSharedTerm(entry.getKey(), source);
			} else {
				final CCTerm equivCC = info.getEquivalentCCTerms().get(entry.getKey());
				if (equivCC == null) {
					return null; // We don't have relevant information on this term.
				} else {
					sharedTerm = equivCC.getSharedTerm() != null ? equivCC.getSharedTerm() : equivCC.getFlatTerm();
				}
			}
			Rational coeff = entry.getValue();
			if (sharedTerm.getOffset() != null) {
				LinVar var = sharedTerm.getLinVar();
				if (var != null) {
					at.add(coeff.mul(sharedTerm.getFactor()), var);
				}
				at.add(coeff.mul(sharedTerm.getOffset()));
			} else {
				return null;
			}
		}
		at.add(smtAff.getConstant());
		return at;
	}

	/**
	 * Build a MutableAffineTerm from an SMTAffineTerm that may contain quantifiers, using the SubstitutionInfo that was
	 * build for the patterns included in this term.
	 * 
	 * @param smtAff
	 *            an SMTAffineTerm including quantified terms.
	 * @param info
	 *            the substitution info that was built for this term.
	 * @return a MutableAffineTerm if each summand of the SMTAffineTerm either is ground or has an equivalent CCTerm for
	 *         the substitution in info, null otherwise.
	 */
	private MutableAffineTerm buildMutableAffineTerm(final SMTAffineTerm smtAff,
			final Map<Term, SharedTerm> sharedForQuantSmds, SourceAnnotation source) {
		MutableAffineTerm at = new MutableAffineTerm();
		for (Entry<Term, Rational> entry : smtAff.getSummands().entrySet()) {
			final SharedTerm sharedTerm;
			if (entry.getKey().getFreeVars().length == 0) {
				sharedTerm = mClausifier.getSharedTerm(entry.getKey(), source);
			} else {
				sharedTerm = sharedForQuantSmds.get(entry.getKey());
				if (sharedTerm == null) {
					return null;
				}
			}
			Rational coeff = entry.getValue();
			if (sharedTerm.getOffset() != null) {
				LinVar var = sharedTerm.getLinVar();
				if (var != null) {
					at.add(coeff.mul(sharedTerm.getFactor()), var);
				}
				at.add(coeff.mul(sharedTerm.getOffset()));
			} else {
				return null;
			}
		}
		return at;
	}

	/**
	 * Find all instances of clauses that would be a conflict or unit clause if the corresponding theories had known the
	 * literals at creation of the instance.
	 *
	 * @return A Set of potentially conflicting and unit instances.
	 */
	public Set<List<Literal>> findConflictAndUnitInstances() {
		final Set<List<Literal>> conflictAndUnitClauses = new LinkedHashSet<>();
		// New Quant Clauses may be added when new instances are computed (e.g. axioms for ite terms)
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.hasTrueGroundLits()) {
				continue;
			}
			final Set<SharedTerm[]> allInstantiations = computeAllInstantiations(quantClause);
			for (SharedTerm[] inst : allInstantiations) {
				if (mClausifier.getEngine().isTerminationRequested())
					return conflictAndUnitClauses;
				final InstanceValue clauseValue = evaluateClauseInstance(quantClause, inst);
				if (clauseValue != InstanceValue.TRUE) {
					final Literal[] instLits = computeClauseInstance(quantClause, inst);
					if (instLits != null) {
						conflictAndUnitClauses.add(Arrays.asList(instLits));
						mQuantTheory.getLogger().debug("Quant: instantiating quant clause %1s results in %2s",
								quantClause, Arrays.asList(instLits));
					}
				}
			}
		}
		return conflictAndUnitClauses;
	}

	/**
	 * In the final check, check if all interesting instantiations of all clauses lead to satisfied instances. As soon
	 * as an instance is found that is not yet satisfied, stop. The newly created literals will be decided by the ground
	 * theories next and may lead to new conflicts.
	 * 
	 * If an actual conflict is found, return it (TODO This should not happen, checkpoint should have found it).
	 * 
	 * @return an actual conflict clause, if it exists; null otherwise.
	 */
	public Clause instantiateAll() {
		final List<QuantClause> currentQuantClauses = new ArrayList<>();
		currentQuantClauses.addAll(mQuantTheory.getQuantClauses());
		for (QuantClause quantClause : currentQuantClauses) {
			if (quantClause.hasTrueGroundLits()) {
				continue;
			}
			final Set<SharedTerm[]> allInstantiations = computeAllInstantiations(quantClause);

			outer: for (SharedTerm[] inst : allInstantiations) {
				if (mClausifier.getEngine().isTerminationRequested())
					return null;
				final Literal[] instLits = computeClauseInstance(quantClause, inst);
				if (instLits != null) {
					boolean isConflict = true;
					for (Literal lit : instLits) {
						if (lit.getAtom().getDecideStatus() == lit) { // instance satisfied TODO Avoid creating those
							continue outer;
						}
						if (lit.getAtom().getDecideStatus() == null) {
							isConflict = false;
						}
					}
					if (isConflict) {
						// quantClause.addInstance(inst);
						return new Clause(instLits);
					} else { // a new not yet satisfied instance has been created
						return null;
					}
				}
			}
		}
		return null;
	}

	@SuppressWarnings("unchecked")
	private Map<QuantLiteral, Collection<SharedTerm[]>> computeSubsForArithmetical(final QuantClause clause,
			final Collection<QuantLiteral> arLits,
			final Dawg<SharedTerm, InstanceValue> clauseDawg) {

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
		final Set<SharedTerm>[] interestingTerms = new LinkedHashSet[nClauseVars];
		// All ground bounds are interesting terms
		for (int i = 0; i < nClauseVars; i++) {
			interestingTerms[i] = new LinkedHashSet<>();
			if (clauseVarsInArLits[i] != null) {
				interestingTerms[i].addAll(clause.getGroundBounds(clauseVarsInArLits[i]));
			}
		}
		// The substitutions for which the partial clause instance value is not yet true are interesting
		for (final Dawg.Entry<SharedTerm, InstanceValue> entry : clauseDawg.entrySet()) {
			if (entry.getValue() != InstanceValue.TRUE) {
				for (int i = 0; i < nClauseVars; i++) {
					if (clauseVarsInArLits[i] != null) {
						interestingTerms[i].add(entry.getKey().get(i)); // They are already the representatives.
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
					for (TermVariable t : clause.getVarBounds(var)) {
						int j = clause.getVarIndex(t);
						changed = interestingTerms[i].addAll(interestingTerms[j]);
					}
				}
			}
		}
		// Build all substitutions for the literals
		final Map<QuantLiteral, Collection<SharedTerm[]>> allSubs = new HashMap<>();
		for (final QuantLiteral lit : arLits) {
			allSubs.put(lit, new ArrayList<SharedTerm[]>());
			final TermVariable[] litVars = lit.getTerm().getFreeVars();
			assert litVars.length <= 2;
			final int firstVarPos = clause.getVarIndex(litVars[0]);
			for (final SharedTerm firstVarSub : interestingTerms[firstVarPos]) {
				final SharedTerm[] partialSubsFirstVar = new SharedTerm[nClauseVars];
				partialSubsFirstVar[firstVarPos] = firstVarSub;
				if (litVars.length == 1) {
					allSubs.get(lit).add(partialSubsFirstVar);
				} else {
					final int secondVarPos = clause.getVarIndex(litVars[1]);
					for (final SharedTerm secondVarSub : interestingTerms[secondVarPos]) {
						final SharedTerm[] partialSubsSecondVar = Arrays.copyOf(partialSubsFirstVar, nClauseVars);
						partialSubsSecondVar[secondVarPos] = secondVarSub;
						allSubs.get(lit).add(partialSubsSecondVar);
					}
				}
			}
		}
		return allSubs;
	}

	/**
	 * Compute all instantiations for a given clause.
	 *
	 * @return a Set containing interesting instantiations for the clause.
	 */
	private Set<SharedTerm[]> computeAllInstantiations(QuantClause quantClause) {
		Set<SharedTerm[]> allSubs = new LinkedHashSet<SharedTerm[]>();
		allSubs.add(new SharedTerm[quantClause.getVars().length]);
		for (int i = 0; i < quantClause.getVars().length; i++) {
			Set<SharedTerm[]> partialSubs = new LinkedHashSet<SharedTerm[]>();
			for (final SharedTerm[] oldSub : allSubs) {
				if (mClausifier.getEngine().isTerminationRequested()) {
					return Collections.emptySet();
				}
				assert !quantClause.getInterestingTerms()[i].isEmpty();
				for (final SharedTerm ground : quantClause.getInterestingTerms()[i].values()) {
					final SharedTerm[] newSub = Arrays.copyOf(oldSub, oldSub.length);
					newSub[i] = ground;
					partialSubs.add(newSub);
				}
			}
			allSubs.clear();
			allSubs.addAll(partialSubs);
		}
		return allSubs;
	}

	/**
	 * Evaluate which value a potential instance of a given clause would have. We distinguish three values: FALSE if all
	 * literals would be false, ONE_UNDEF if all but one literal would be false and this one undefined, and TRUE for all
	 * other cases.
	 *
	 * @param quantClause
	 *            the quantified clause which we evaluate an instance for.
	 * @param instantiation
	 *            the ground terms to instantiate.
	 * @return the value of the potential instance.
	 */
	private InstanceValue evaluateClauseInstance(final QuantClause quantClause, final SharedTerm[] instantiation) {
		InstanceValue clauseValue = InstanceValue.FALSE;

		// Check ground literals first.
		for (Literal groundLit : quantClause.getGroundLits()) {
			if (groundLit.getAtom().getDecideStatus() == groundLit) {
				return InstanceValue.TRUE;
			} else if (groundLit.getAtom().getDecideStatus() == null) {
				clauseValue = clauseValue.combine(InstanceValue.ONE_UNDEF);
			} else {
				assert groundLit.getAtom().getDecideStatus() != groundLit;
			}
		}
		// Only check clauses where all or all but one ground literals are set.
		if (clauseValue == InstanceValue.TRUE) {
			return clauseValue;
		}

		// Check quantified literals. TODO: Use SubstitutionHelper
		final SharedTermFinder finder =
				new SharedTermFinder(quantClause.getSource(), quantClause.getVars(), instantiation);
		for (QuantLiteral quantLit : quantClause.getQuantLits()) {
			InstanceValue litValue = InstanceValue.ONE_UNDEF;
			final boolean isNeg = quantLit.isNegated();
			final QuantLiteral atom = quantLit.getAtom();
			if (atom instanceof QuantEquality) {
				final QuantEquality eq = (QuantEquality) atom;
				final SharedTerm left = finder.findEquivalentShared(eq.getLhs());
				final SharedTerm right = finder.findEquivalentShared(eq.getRhs());
				if (left != null && right != null) {
					litValue = evaluateCCEquality(left, right);
				}
				if (litValue == InstanceValue.ONE_UNDEF && eq.getLhs().getSort().isNumericSort()) {
					final SMTAffineTerm sum = new SMTAffineTerm(eq.getLhs());
					sum.add(Rational.MONE, eq.getRhs());
					final SMTAffineTerm groundAff = finder.findEquivalentAffine(sum);
					if (groundAff != null) {
						litValue = evaluateLAEquality(groundAff);
					}
				}
			} else {
				final QuantBoundConstraint ineq = (QuantBoundConstraint) atom;
				final SMTAffineTerm lhs = finder.findEquivalentAffine(ineq.getAffineTerm());
				if (lhs != null) {
					litValue = evaluateBoundConstraint(lhs);
				}
			}

			if (isNeg) {
				litValue = litValue.negate();
			}
			clauseValue = clauseValue.combine(litValue);
			if (clauseValue == InstanceValue.TRUE) {
				return InstanceValue.TRUE;
			}
		}
		return clauseValue;
	}

	/**
	 * Instantiate a clause with a given substitution.
	 *
	 * @param clause
	 *            a clause containing at least one quantified literal
	 * @param sigma
	 *            pairs of variable and ground term that is used to instantiate the corresponding variable.
	 *
	 * @return the set of ground literals, or null if the clause would be true.
	 */
	private Literal[] computeClauseInstance(final QuantClause clause, final SharedTerm[] subs) {
		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		for (int i = 0; i < subs.length; i++) {
			sigma.put(clause.getVars()[i], subs[i].getTerm());
		}
		final SubstitutionHelper instHelper = new SubstitutionHelper(mQuantTheory, clause.getGroundLits(),
				clause.getQuantLits(), clause.getSource(), sigma);
		instHelper.substituteInClause();
		if (instHelper.getResultingClauseTerm() == mQuantTheory.getTheory().mTrue) {
			return null;
		} else {
			assert instHelper.getResultingQuantLits().length == 0;
			final Literal[] resultingLits = instHelper.getResultingGroundLits();
			return resultingLits;
		}
	}

	/**
	 * Determine the value that an equality literal between two given CCTerm would have.
	 *
	 * @param left
	 *            The left side of the equality.
	 * @param right
	 *            The right side of the equality.
	 * @return Value True if the two terms are in the same congruence class, False if they are definitely distinct,
	 *         Undef else.
	 */
	private InstanceValue evaluateCCEquality(final CCTerm leftCC, final CCTerm rightCC) {
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			}
		}
			return InstanceValue.ONE_UNDEF;
		}

	/**
	 * Determine the value that an equality literal between two given SharedTerm would have.
	 *
	 * @param left
	 *            The left side of the equality.
	 * @param right
	 *            The right side of the equality.
	 * @return Value True if the two terms are in the same congruence class, False if they are definitely distinct,
	 *         Undef else.
	 */
	private InstanceValue evaluateCCEquality(final SharedTerm left, final SharedTerm right) {
		final CCTerm leftCC = left.getCCTerm();
		final CCTerm rightCC = right.getCCTerm();
		if (leftCC != null && rightCC != null) {
			if (mQuantTheory.getCClosure().isEqSet(leftCC, rightCC)) {
				return InstanceValue.TRUE;
			} else if (mQuantTheory.getCClosure().isDiseqSet(leftCC, rightCC)) {
				return InstanceValue.FALSE;
			}
		}
		return InstanceValue.ONE_UNDEF;
	}

	/**
	 * Determine the value that an equality MutableAffineTerm = 0 would have if instantiated.
	 * 
	 * @param at
	 *            a MutableAffineTerm representing an LAEquality.
	 * @return Value True if both the lower and upper bound of at are 0, False if the lower bound is greater and the
	 *         upper bound is smaller than 0, Undef else.
	 */
	private InstanceValue evaluateLAEquality(final MutableAffineTerm at) {
		if (at == null) {
			return InstanceValue.ONE_UNDEF;
		}
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(at);
		at.negate();
		final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(at);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO) && lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else if (!upperBound.isInfinity() && !upperBound.lesseq(InfinitesimalNumber.ZERO)
				|| !lowerBound.isInfinity() && !lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.FALSE;
		}
		return InstanceValue.ONE_UNDEF;
	}

	/**
	 * Determine the value that an equality SMTAffineTerm = 0 would have if instantiated.
	 * 
	 * @param at
	 *            a MutableAffineTerm representing an LAEquality.
	 * @return Value True if both the lower and upper bound of at exist and are equal to 0, False if the lower bound
	 *         exists and is greater than 0. and the upper bound exists and is smaller than 0, Undef else.
	 */
	private InstanceValue evaluateLAEquality(final SMTAffineTerm smtAff) {
		final InfinitesimalNumber upperBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
		smtAff.negate();
		final InfinitesimalNumber lowerBound = mQuantTheory.mLinArSolve.getUpperBound(mClausifier, smtAff);
		if (upperBound.lesseq(InfinitesimalNumber.ZERO) && lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.TRUE;
		} else if (!upperBound.isInfinity() && !upperBound.lesseq(InfinitesimalNumber.ZERO)
				|| !lowerBound.isInfinity() && !lowerBound.lesseq(InfinitesimalNumber.ZERO)) {
			return InstanceValue.FALSE;
		}
		return InstanceValue.ONE_UNDEF;
	}

	/**
	 * Determine the value that a bound constraint "term <= 0" would have.
	 *
	 * @param affine
	 *            The linear term for a constraint "term <= 0".
	 * @return Value True if the term has an upper bound <= 0, False if -term has a lower bound < 0, or Undef otherwise.
	 */
	private InstanceValue evaluateBoundConstraint(final MutableAffineTerm at) {
		if (at == null) {
			return InstanceValue.ONE_UNDEF;
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
	 * Determine the value that a bound constraint "term <= 0" would have.
	 *
	 * @param affine
	 *            The linear term for a constraint "term <= 0".
	 * @return Value True if the term has an upper bound <= 0, False if -term has a lower bound < 0, or Undef otherwise.
	 */
	private InstanceValue evaluateBoundConstraint(final SMTAffineTerm affine) {
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

	private class SharedTermFinder extends NonRecursive {
		private final SourceAnnotation mSource;
		private final List<TermVariable> mVars;
		private final List<SharedTerm> mInstantiation;
		private final Map<Term, SharedTerm> mSharedTerms;

		SharedTermFinder(final SourceAnnotation source, final TermVariable[] vars,
				final SharedTerm[] instantiation) {
			mSource = source;
			mVars = Arrays.asList(vars);
			mInstantiation = Arrays.asList(instantiation);
			mSharedTerms = new HashMap<>();
		}

		SharedTerm findEquivalentShared(final Term term) {
			enqueueWalker(new FindSharedTerm(term));
			run();
			return mSharedTerms.get(term);
		}

		SMTAffineTerm findEquivalentAffine(final SMTAffineTerm smtAff) {
			for (final Term smd : smtAff.getSummands().keySet()) {
				enqueueWalker(new FindSharedTerm(smd));
			}
			run();
			return buildEquivalentAffine(smtAff);
		}

		private SMTAffineTerm buildEquivalentAffine(final SMTAffineTerm smtAff) {
			final SMTAffineTerm instAff = new SMTAffineTerm();
			for (final Entry<Term, Rational> smd : smtAff.getSummands().entrySet()) {
				final SharedTerm inst = mSharedTerms.get(smd.getKey());
				if (inst == null) {
					return null;
				}
				instAff.add(smd.getValue(), inst.getTerm());
			}
			instAff.add(smtAff.getConstant());
			return instAff;
		}

		class FindSharedTerm implements Walker {
			private final Term mTerm;

			public FindSharedTerm(final Term term) {
				mTerm = term;
			}

			@Override
			public void walk(final NonRecursive engine) {
				if (!mSharedTerms.containsKey(mTerm)) {
					if (mTerm.getFreeVars().length == 0) {
						mSharedTerms.put(mTerm, mClausifier.getSharedTerm(mTerm, mSource));
					} else if (mTerm instanceof TermVariable) {
						mSharedTerms.put(mTerm, mInstantiation.get(mVars.indexOf(mTerm)));
					} else {
						assert mTerm instanceof ApplicationTerm;
						final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
						final FunctionSymbol func = appTerm.getFunction();
						if (Clausifier.needCCTerm(func)) {
							final Term[] params = appTerm.getParameters();
							enqueueWalker(new FindSharedAppTerm(mTerm, func, params));
							for (final Term arg : params) {
								enqueueWalker(new FindSharedTerm(arg));
							}
						} else if (func.getName() == "+" || func.getName() == "*" || func.getName() == "-") {
							final SMTAffineTerm smtAff = new SMTAffineTerm(mTerm);
							enqueueWalker(new FindSharedAffine(mTerm, smtAff));
							for (final Term smd : smtAff.getSummands().keySet()) {
								enqueueWalker(new FindSharedTerm(smd));
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
					final SharedTerm sharedArg = mSharedTerms.get(mParams[i]);
					if (sharedArg == null) {
						return;
					} else {
						instArgs[i] = sharedArg.getTerm();
					}
				}
				final Term instAppTerm = mClausifier.getTheory().term(mFunc, instArgs);
				final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instAppTerm);
				if (ccTermRep != null) {
					mSharedTerms.put(mTerm,
							ccTermRep.getSharedTerm() != null ? ccTermRep.getSharedTerm() : ccTermRep.getFlatTerm());
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
					final Term instTerm = instAffine.toTerm(mTerm.getSort());
					final CCTerm ccTermRep = mQuantTheory.getCClosure().getCCTermRep(instTerm);
					if (ccTermRep != null) {
						mSharedTerms.put(mTerm, ccTermRep.getSharedTerm() != null ? ccTermRep.getSharedTerm()
								: ccTermRep.getFlatTerm());
					}
				}
			}
		}
	}

	private enum InstanceValue {
		TRUE, FALSE, ONE_UNDEF;

		private InstanceValue combine(InstanceValue other) {
			if (this == InstanceValue.TRUE) {
				return this;
			} else if (this == InstanceValue.FALSE) {
				return other;
			} else {
				if (other == InstanceValue.FALSE) {
					return this;
				} else { // Note: UNDEF + UNDEF = TRUE (not interesting)
					return InstanceValue.TRUE;
				}
			}
		}

		private InstanceValue negate() {
			if (this == TRUE) {
				return InstanceValue.FALSE;
			} else if (this == FALSE) {
				return InstanceValue.TRUE;
			} else {
				return this;
			}
		}
	}
}
