/*
 * Copyright (C) 2018-2019 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2018-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.NestedArrayStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayQuantifierEliminationMain {

	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final Script mScript;
	private final Set<TermVariable> mEliminatees;
	private final Set<TermVariable> mNewExistEliminatees;
	private final Set<TermVariable> mNewValueEliminatees;
	private final Set<TermVariable> mNewIndexEliminatees;
	private int mRecursiveCallCounter = 0;
	private ThreeValuedEquivalenceRelation<Term> mTVER;

	/*
	 * Uses the rules defined in my bachelor thesis to eliminate quantified arrays.
	 */
	public ArrayQuantifierEliminationMain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mMgdScript = mgdScript;
		mScript = mMgdScript.getScript();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mEliminatees = new HashSet<>();
		mNewExistEliminatees = new HashSet<>();
		mNewValueEliminatees = new HashSet<>();
		mNewIndexEliminatees = new HashSet<>();
		mTVER = new ThreeValuedEquivalenceRelation<>();
	}

	/*
	 * eliminates quantified arrays in every recursion. quantifier can change during
	 * recursion.
	 */
	public EliminationTask elimAllRec(final EliminationTask eTask) {
		mEliminatees.addAll(eTask.getEliminatees());
		mLogger.info("ArrayQuantifierEliminationMain: ");
		mLogger.debug("Recursion:" + mRecursiveCallCounter + " Eliminatees: " + mEliminatees);
		mRecursiveCallCounter += 1;
		mLogger.debug("Term: " + eTask.getTerm());
		EliminationTask recTask = eTask;

		recTask = elimQuantifiedArray(recTask);

		Term quantifiedTerm = recTask.getTerm();

		// quantified value variables. Selectterm Substitution
		quantifiedTerm = SmtUtils.quantifier(mScript, eTask.getQuantifier(), mNewValueEliminatees, quantifiedTerm);
		// quantified array variables. Storeterm Substitution
		quantifiedTerm = SmtUtils.quantifier(mScript, 0, mNewExistEliminatees, quantifiedTerm);
		// forall quantified index variables. Partial array equalities.
		quantifiedTerm = SmtUtils.quantifier(mScript, 1, mNewIndexEliminatees, quantifiedTerm);

		mEliminatees.addAll(mNewValueEliminatees);
		if (eTask.getQuantifier() == 0) {
			mEliminatees.addAll(mNewExistEliminatees);
		} else {
			mEliminatees.addAll(mNewIndexEliminatees);
		}
		mLogger.debug("Result term: " + recTask.getTerm());

		recTask = recursivCall(eTask, quantifiedTerm);

		return recTask;

	}

	/*
	 * recursive call of elimAllRec. PNF needed for quantifier alternations
	 * SmtUtils.simplify in every recursion
	 */
	private EliminationTask recursivCall(final EliminationTask eTask, final Term quantifiedTerm) {

		final Term nnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP).transform(quantifiedTerm);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ALL_LOCAL).transform(nnf);
		final Term pnf = new PrenexNormalForm(mMgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
		Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();
		for (int i = qvs.size() - 1; i >= 0; i--) {
			final QuantifiedVariables qv = qvs.get(i);
			final Set<TermVariable> eliminatees = new HashSet<>(qv.getVariables());
			if (!eliminatees.equals(eTask.getEliminatees())) {
				matrix = SmtUtils.simplify(mMgdScript, matrix, mServices, mSimplificationTechnique);
				EliminationTask recResult = new EliminationTask(qv.getQuantifier(), eliminatees, matrix);
				recResult = elimAllRec(recResult);
				matrix = recResult.getTerm();
				matrix = SmtUtils.quantifier(mMgdScript.getScript(), qv.getQuantifier(), eliminatees, matrix);
				matrix = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ONLY_DER).transform(matrix);
			}
		}
		return new EliminationTask(eTask.getQuantifier(), mEliminatees, matrix);

	}

	/*
	 * eliminates quantified arrays possible optimization: Array selection
	 */
	private EliminationTask elimQuantifiedArray(EliminationTask recTask) {
		if (recTask.getTerm() instanceof ApplicationTerm) {
			mTVER = calcThreeValuedEquiRel(recTask);
			for (final TermVariable array : recTask.getEliminatees()) {
				Term taskTerm = recTask.getTerm();
				taskTerm = selectOverStore(taskTerm, array);
				taskTerm = storeOverStore(taskTerm, array);
				recTask = new EliminationTask(recTask.getQuantifier(), mEliminatees, taskTerm);
				recTask = elimStores(recTask, array);
			}
		}
		return recTask;
	}

	/*
	 * optimization for eliminating store over store terms. Nested Store over stores
	 * will be eliminated recursive.
	 */
	private Term storeOverStore(final Term term, final TermVariable qarray) {
		final MultiDimensionalStore mds = MultiDimensionalStore.convert(term);
		final List<MultiDimensionalStore> storeterms = mds.extractArrayStoresShallow(term);
		for (final MultiDimensionalStore storeOuter : storeterms) {

			final NestedArrayStore nas = NestedArrayStore.convert(storeOuter.getStoreTerm());
			if (nas.getIndices().size() > 1) {
				// if indices are equal, optimize
				if ((qarray.equals(nas.getArray()))
						&& (testIndexVarTerm(nas.getIndices().get(0), nas.getIndices().get(1)))
						&& (mTVER.getEqualityStatus(nas.getIndices().get(0),
								nas.getIndices().get(1)) == (EqualityStatus.EQUAL))) {

					final Term newStore = SmtUtils.store(mScript, nas.getArray(), nas.getIndices().get(0),
							nas.getValues().get(1));

					// Substitude newStore
					final Substitution sub = new Substitution(mMgdScript,
							Collections.singletonMap(storeOuter.getStoreTerm(), newStore));
					final Term noSOSterm = sub.transform(term);

					return storeOverStore(noSOSterm, qarray);

				}
				// else factor out store
				final TermVariable newarrayvar = mMgdScript.constructFreshTermVariable("a_sos",
						storeOuter.getArray().getSort());
				final Term innerStore = SmtUtils.store(mScript, nas.getArray(), nas.getIndices().get(0),
						nas.getValues().get(0));
				final Substitution sub = new Substitution(mMgdScript,
						Collections.singletonMap(innerStore, newarrayvar));

				final Term noSOSterm = sub.transform(term);
				mNewExistEliminatees.add(newarrayvar);
				// Index comparison Equality
				final Term factorOutStore = SmtUtils.binaryEquality(mScript, newarrayvar, innerStore);
				final Term newTerm = SmtUtils.and(mScript, factorOutStore, noSOSterm);

				return storeOverStore(newTerm, qarray);
			}
		}
		return term;
	}

	/*
	 * tries to simplifies an equality using informations from mTVER
	 */
	private Term indexEQ(final Term index, final MultiDimensionalSelect select) {
		Term indexeq = SmtUtils.binaryEquality(mScript, index, select.getIndex().get(0));

		if (testIndexVarTerm(index, select.getIndex().get(0))) {

			if (mTVER.getDisequalities().containsPair(index, select.getIndex().get(0))) {
				indexeq = mScript.term("false");

			} else if (mTVER.getEqualityStatus(index, select.getIndex().get(0)).compareTo(EqualityStatus.EQUAL) == 0) {
				indexeq = mScript.term("true");

			}
		}
		return indexeq;
	}

	/*
	 * tries to simplify select over nested store terms.
	 */
	private Term selectOverStore(final Term term, final TermVariable qarray) {
		final MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
		final List<MultiDimensionalSelect> selectterms = mds.extractSelectDeep(term, false);
		for (final MultiDimensionalSelect select : selectterms) {
			// if Array is BasicArray, its no SelectOverStore
			if (!SmtUtils.isBasicArrayTerm(select.getArray())) {
				final MultiDimensionalStore innerStore = MultiDimensionalStore.convert(select.getArray());

				final NestedArrayStore nas = NestedArrayStore.convert(innerStore.getStoreTerm());

				if (qarray.equals(nas.getArray())) {
					Term disjunction = mScript.term("false");
					Term allindexnoteq = mScript.term("true");
					for (int i = nas.getIndices().size() - 1; i >= 0; i--) {
						final Term index = nas.getIndices().get(i);
						final Term indexeq = indexEQ(index, select);

						final Term indexnoteq = SmtUtils.not(mScript, indexeq);

						final Substitution sub = new Substitution(mMgdScript, Collections.singletonMap(
								select.getSelectTerm(), nas.getValues().get(nas.getIndices().indexOf(index))));
						final Term subtermlhs = sub.transform(term);
						final Term lhs = SmtUtils.and(mScript, indexeq, subtermlhs, allindexnoteq);
						disjunction = SmtUtils.or(mScript, lhs, disjunction);
						allindexnoteq = SmtUtils.and(mScript, indexnoteq, allindexnoteq);
					}

					final Substitution sub = new Substitution(mMgdScript,
							Collections.singletonMap(select.getSelectTerm(),
									SmtUtils.select(mScript, nas.getArray(), select.getIndex().get(0))));
					final Term subtermrhs = sub.transform(term);

					final Term rhs = SmtUtils.and(mScript, allindexnoteq, subtermrhs);
					return SmtUtils.or(mScript, disjunction, rhs);
				}
			}

		}
		return term;

	}

	/*
	 * checks, if mTVER has informations about two indices
	 */
	private boolean testIndexVarTerm(final Term index1, final Term index2) {
		return ((mTVER.getAllElements().contains(index1)) && (mTVER.getAllElements().contains(index2))
				&& (!(index1 instanceof ConstantTerm)) && (!(index2 instanceof ConstantTerm)));

	}

	/*
	 * stores all equalities of an conjunction in a ThreeValuedEquivalenceRelation
	 */

	private ThreeValuedEquivalenceRelation<Term> calcThreeValuedEquiRel(final EliminationTask eTask) {
		final ApplicationTerm appterm = (ApplicationTerm) eTask.getTerm();
		final ThreeValuedEquivalenceRelation<Term> tVER = new ThreeValuedEquivalenceRelation<>();
		if (SmtUtils.isFunctionApplication(eTask.getTerm(), "and")) {
			for (final Term term : appterm.getParameters()) {
				if (term.getSort().getName().equals("Bool")) {
					final ApplicationTerm boolterm = (ApplicationTerm) term;
					if (SmtUtils.isFunctionApplication(boolterm, "=")) {
						// add equality
						tVER.addElement(boolterm.getParameters()[0]);
						tVER.addElement(boolterm.getParameters()[1]);
						tVER.reportEquality(boolterm.getParameters()[0], boolterm.getParameters()[1]);
					} else if (SmtUtils.isFunctionApplication(boolterm, "not")) {
						// add disequality
						final ApplicationTerm eqterm = (ApplicationTerm) boolterm.getParameters()[0];
						if (SmtUtils.isFunctionApplication(eqterm, "=")) {
							tVER.addElement(eqterm.getParameters()[0]);
							tVER.addElement(eqterm.getParameters()[1]);
							tVER.reportDisequality(eqterm.getParameters()[0], eqterm.getParameters()[1]);
						}
					}
				}
			}
		}
		return tVER;
	}

	/*
	 * build select term combinations, with the quantified array "eliminate" as
	 * first argument. For selectterms.size() = n, indexCombinations contains (n *
	 * (n - 1))/2 combinations.
	 */

	private Set<Pair<ApplicationTerm, ApplicationTerm>> calcIndexCombinations(final Set<ApplicationTerm> selectterms,
			final TermVariable eliminate) {
		final Set<Pair<ApplicationTerm, ApplicationTerm>> indexCombinations = new HashSet<>();
		final List<ApplicationTerm> selecttermList = new ArrayList<>(selectterms);
		for (int l = 1; l < selecttermList.size(); l++) {
			for (int i = 0; i < l; i++) {
				if ((eliminate.equals(selecttermList.get(i).getParameters()[0]))
						&& (eliminate.equals(selecttermList.get(l).getParameters()[0]))) {
					indexCombinations.add(
							new Pair<ApplicationTerm, ApplicationTerm>(selecttermList.get(i), selecttermList.get(l)));
				}
			}
		}
		if (indexCombinations.isEmpty()) {
			for (final ApplicationTerm i : selectterms) {
				if (eliminate.equals(i.getParameters()[0])) {
					indexCombinations.add(new Pair<ApplicationTerm, ApplicationTerm>(i, i));
				}
			}
		}
		return indexCombinations;
	}

	/*
	 * builds a Term: index equality implies value equality
	 */
	private Term indexEQvalueEQ(final Pair<ApplicationTerm, ApplicationTerm> comb, final TermVariable si,
			final TermVariable sj, final int quantifier) {

		final Term lhs = SmtUtils.binaryEquality(mScript, comb.getFirst().getParameters()[1],
				comb.getSecond().getParameters()[1]);
		final Term rhs = SmtUtils.binaryEquality(mScript, si, sj);

		Term iEvE = SmtUtils.or(mScript, SmtUtils.not(mScript, lhs), rhs);
		if (quantifier == QuantifiedFormula.FORALL) {
			iEvE = SmtUtils.not(mScript, iEvE);
		}
		return iEvE;
	}

	/*
	 * tries to eliminate the array "eliminate" by substitution.
	 */
	public EliminationTask elimArrayBySelects(final Term eTerm, final TermVariable eliminate, final int quantifier) {

		// Get select terms
		final Set<ApplicationTerm> selectterms = new ApplicationTermFinder("select", false).findMatchingSubterms(eTerm);

		final Set<Pair<ApplicationTerm, ApplicationTerm>> indexCombinations = calcIndexCombinations(selectterms,
				eliminate);

		// Build up term: implikation
		final Set<TermVariable> neweliminatees = new HashSet<>();
		Term newTerm = mScript.term("true");
		final Map<Term, Term> submap = new HashMap<>();
		if (!indexCombinations.isEmpty()) {
			for (final Pair<ApplicationTerm, ApplicationTerm> comb : indexCombinations) {
				// new Exists Quantified variables: si_counter / sj_counter
				TermVariable si = mMgdScript.constructFreshTermVariable("si", comb.getFirst().getSort());
				TermVariable sj = mMgdScript.constructFreshTermVariable("sj", comb.getSecond().getSort());

				if (!submap.containsKey(comb.getFirst())) {
					neweliminatees.add(si);
					submap.put(comb.getFirst(), si);
				} else {
					si = (TermVariable) submap.get(comb.getFirst());
				}
				if (!submap.containsKey(comb.getSecond())) {
					neweliminatees.add(sj);
					submap.put(comb.getSecond(), sj);
				} else {
					sj = (TermVariable) submap.get(comb.getSecond());
				}

				final Term iEvE = indexEQvalueEQ(comb, si, sj, quantifier);
				newTerm = SmtUtils.and(mScript, iEvE, newTerm);

			}

			final Substitution sub = new Substitution(mMgdScript, submap);
			final Term newTerm2 = sub.transform(eTerm);

			newTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, newTerm2, newTerm);
			neweliminatees.add(eliminate); // add remaining eliminate
			mNewValueEliminatees.addAll(neweliminatees);
			return new EliminationTask(quantifier, neweliminatees, newTerm);
		}

		final Set<TermVariable> oldeliminatees = new HashSet<>();
		oldeliminatees.add(eliminate);
		mEliminatees.addAll(oldeliminatees);
		return new EliminationTask(quantifier, oldeliminatees, eTerm);
	}

	private Term elimStoreEQ(final TermVariable newindexvar, final TermVariable newarrayvar,
			final ApplicationTerm store, final Term storeEQ, Term newterm) {
		// Build new term forall indices of indexSet
		// Term 1: ((i != j) => (a_new[i] = a[i]))
		final Term indexnoteq = SmtUtils.not(mScript,
				SmtUtils.binaryEquality(mScript, newindexvar, store.getParameters()[1]));
		final Term arrayeq = SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, newarrayvar, newindexvar),
				SmtUtils.select(mScript, store.getParameters()[0], newindexvar));
		final Term elimtermlhs = SmtUtils.implies(mScript, indexnoteq, arrayeq);
		// Term 2: ((i = j) => (a_new[i] = v))
		final Term indexeq = SmtUtils.binaryEquality(mScript, newindexvar, store.getParameters()[1]);
		final Term selectvalue = SmtUtils.binaryEquality(mScript,
				SmtUtils.select(mScript, newarrayvar, store.getParameters()[1]), store.getParameters()[2]);
		final Term elimtermrhs = SmtUtils.implies(mScript, indexeq, selectvalue);
		// Term 3: Term 1 AND Term 2
		final Term elimterm = SmtUtils.and(mScript, elimtermlhs, elimtermrhs);
		// Substitute store term equality with the new term "elimForall"
		final Substitution sub = new Substitution(mMgdScript, Collections.singletonMap(storeEQ, elimterm));
		newterm = sub.transform(newterm);
		return newterm;
	}

	/*
	 * tries to eliminate newarrayvar in newterm with DER
	 */
	private Term dER(Term newterm, final TermVariable newarrayvar) {
		// DER on a_new. To eliminate the new exist quantifier: "Exists a_new"
		final XnfDer xnfDer = new XnfDer(mMgdScript, mServices);
		final Term[] oldParams = QuantifierUtils.getXjunctsOuter(0, newterm);
		final Term[] newParams = new Term[oldParams.length];
		final Set<TermVariable> eliminateesDER = new HashSet<>();
		eliminateesDER.add(newarrayvar);
		for (int i = 0; i < oldParams.length; i++) {

			final Term[] oldAtoms = QuantifierUtils.getXjunctsInner(0, oldParams[i]);
			newParams[i] = QuantifierUtils.applyDualFiniteConnective(mScript, 0,
					Arrays.asList(xnfDer.tryToEliminate(0, oldAtoms, eliminateesDER)));
		}

		newterm = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, 0, newParams);

		return newterm;
	}

	/*
	 * Eliminates all store functions with qarray as first argument. newarrayvar is
	 * a new exist quantified variable with array sort. newindexvar is a new forall
	 * quantified variable with index sort. newindexvar is used to represent partial
	 * equalities.
	 */

	private EliminationTask elimStores(final EliminationTask eTask, final TermVariable qarray) {
		final Set<ApplicationTerm> storeterms = new ApplicationTermFinder("store", false)
				.findMatchingSubterms(eTask.getTerm());

		Term newterm = eTask.getTerm();
		final Set<TermVariable> neweliminatees2 = new HashSet<>();
		// for store new exists array a1 quantifier
		for (final ApplicationTerm term : storeterms) {
			if (qarray.equals(term.getParameters()[0])) {
				// FactorStore
				final TermVariable newarrayvar = mMgdScript.constructFreshTermVariable("a_new",
						term.getParameters()[0].getSort());
				// Substitute ttore term with new exist quantified array variable a_new
				final Substitution sub = new Substitution(mMgdScript, Collections.singletonMap(term, newarrayvar));
				newterm = sub.transform(newterm);
				// Add conjunct a1 = (eliminated store term)
				final Term eqterm = SmtUtils.binaryEquality(mScript, newarrayvar, term);
				newterm = SmtUtils.and(mScript, newterm, eqterm);

				final TermVariable newindexvar = mMgdScript.constructFreshTermVariable("j",
						term.getParameters()[1].getSort());
				neweliminatees2.add(newindexvar);
				newterm = elimStoreEQ(newindexvar, newarrayvar, term, eqterm, newterm);

				newterm = dER(newterm, newarrayvar);

				if (Arrays.asList(newterm.getFreeVars()).contains(newarrayvar)) {
					mNewExistEliminatees.add(newarrayvar);
				}
			}
		}
		// eliminiate qarray in newterm
		final EliminationTask newETask = elimArrayBySelects(newterm, qarray, eTask.getQuantifier());
		mNewIndexEliminatees.addAll(neweliminatees2);
		return newETask;
	}
}